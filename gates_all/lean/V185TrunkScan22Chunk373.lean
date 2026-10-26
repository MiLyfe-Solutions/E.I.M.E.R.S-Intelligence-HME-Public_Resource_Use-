import V185TrunkScan22Chunk372

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3325706 : List Nat := [3, 1, 2, 2, 1, 4, 1, 1, 4, 3]
def baseStart_3325706 : Nat := 118140960795 + 3325706 * 2 ^ 59
def prefixEnd_3325706 : Nat := 4983230072969 + 3 ^ 40 * 3325706 * 2
def baseEnd_3325706 : Nat := 1138457129027780262453575

theorem tailTrace_3325706 : CollatzResearch.WordTrace tailWord_3325706 prefixEnd_3325706 1138457129027780262453575 := by
  unfold tailWord_3325706
  simp only [CollatzResearch.WordTrace]
  refine ⟨30324615722385655552571243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80865641926361748140189981 30324615722385655552571243)
  ·
    refine ⟨45486923583578483328856865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30324615722385655552571243 45486923583578483328856865)
    ·
      refine ⟨34115192687683862496642649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45486923583578483328856865 34115192687683862496642649)
      ·
        refine ⟨25586394515762896872481987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34115192687683862496642649 25586394515762896872481987)
        ·
          refine ⟨38379591773644345308722981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25586394515762896872481987 38379591773644345308722981)
          ·
            refine ⟨7196173457558314745385559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38379591773644345308722981 7196173457558314745385559)
            ·
              refine ⟨10794260186337472118078339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7196173457558314745385559 10794260186337472118078339)
              ·
                refine ⟨16191390279506208177117509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10794260186337472118078339 16191390279506208177117509)
                ·
                  refine ⟨3035885677407414033209533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16191390279506208177117509 3035885677407414033209533)
                  ·
                    refine ⟨1138457129027780262453575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3035885677407414033209533 1138457129027780262453575)
                    ·
                      rfl

theorem cell22_3325706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 1, 4, 3].length) (baseStart_3325706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3325706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3325706 prefixEnd_3325706 := by exact prefixLift 3325706
  have htrace : WordTrace (prefixWord ++ tailWord_3325706) baseStart_3325706 baseEnd_3325706 := by
    simpa [prefixWord, tailWord_3325706, baseEnd_3325706] using wordTrace_append hprefix tailTrace_3325706
  have hstable : (prefixWord ++ tailWord_3325706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325706).length < 2 ^ (prefixWord ++ tailWord_3325706).sum := by decide
  have hdescent : baseEnd_3325706 < baseStart_3325706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325736 : List Nat := [2, 1, 5, 1, 1, 2, 4, 6]
def baseStart_3325736 : Nat := 118140960795 + 3325736 * 2 ^ 59
def prefixEnd_3325736 : Nat := 4983230072969 + 3 ^ 40 * 3325736 * 2
def baseEnd_3325736 : Nat := 126496377626763353800387

theorem tailTrace_3325736 : CollatzResearch.WordTrace tailWord_3325736 prefixEnd_3325736 126496377626763353800387 := by
  unfold tailWord_3325736
  simp only [CollatzResearch.WordTrace]
  refine ⟨60649778539716968666938531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80866371386289291555918041 60649778539716968666938531)
  ·
    refine ⟨90974667809575453000407797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60649778539716968666938531 90974667809575453000407797)
    ·
      refine ⟨8528875107147698718788231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90974667809575453000407797 8528875107147698718788231)
      ·
        refine ⟨12793312660721548078182347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8528875107147698718788231 12793312660721548078182347)
        ·
          refine ⟨19189968991082322117273521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12793312660721548078182347 19189968991082322117273521)
          ·
            refine ⟨14392476743311741587955141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19189968991082322117273521 14392476743311741587955141)
            ·
              refine ⟨2698589389370951547741589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14392476743311741587955141 2698589389370951547741589)
              ·
                refine ⟨126496377626763353800387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2698589389370951547741589 126496377626763353800387)
                ·
                  rfl

theorem cell22_3325736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 4, 6].length) (baseStart_3325736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3325736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3325736 prefixEnd_3325736 := by exact prefixLift 3325736
  have htrace : WordTrace (prefixWord ++ tailWord_3325736) baseStart_3325736 baseEnd_3325736 := by
    simpa [prefixWord, tailWord_3325736, baseEnd_3325736] using wordTrace_append hprefix tailTrace_3325736
  have hstable : (prefixWord ++ tailWord_3325736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325736).length < 2 ^ (prefixWord ++ tailWord_3325736).sum := by decide
  have hdescent : baseEnd_3325736 < baseStart_3325736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325742 : List Nat := [4, 1, 3, 2, 3, 1, 1, 3, 4]
def baseStart_3325742 : Nat := 118140960795 + 3325742 * 2 ^ 59
def prefixEnd_3325742 : Nat := 4983230072969 + 3 ^ 40 * 3325742 * 2
def baseEnd_3325742 : Nat := 379489817521162722851155

theorem tailTrace_3325742 : CollatzResearch.WordTrace tailWord_3325742 prefixEnd_3325742 379489817521162722851155 := by
  unfold tailWord_3325742
  simp only [CollatzResearch.WordTrace]
  refine ⟨15162471989676525044824435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80866517278274800239063653 15162471989676525044824435)
  ·
    refine ⟨22743707984514787567236653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15162471989676525044824435 22743707984514787567236653)
    ·
      refine ⟨8528890494193045337713745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22743707984514787567236653 8528890494193045337713745)
      ·
        refine ⟨6396667870644784003285309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8528890494193045337713745 6396667870644784003285309)
        ·
          refine ⟨2398750451491794001231991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6396667870644784003285309 2398750451491794001231991)
          ·
            refine ⟨3598125677237691001847987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2398750451491794001231991 3598125677237691001847987)
            ·
              refine ⟨5397188515856536502771981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3598125677237691001847987 5397188515856536502771981)
              ·
                refine ⟨2023945693446201188539493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5397188515856536502771981 2023945693446201188539493)
                ·
                  refine ⟨379489817521162722851155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2023945693446201188539493 379489817521162722851155)
                  ·
                    rfl

theorem cell22_3325742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 3, 4].length) (baseStart_3325742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3325742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3325742 prefixEnd_3325742 := by exact prefixLift 3325742
  have htrace : WordTrace (prefixWord ++ tailWord_3325742) baseStart_3325742 baseEnd_3325742 := by
    simpa [prefixWord, tailWord_3325742, baseEnd_3325742] using wordTrace_append hprefix tailTrace_3325742
  have hstable : (prefixWord ++ tailWord_3325742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325742).length < 2 ^ (prefixWord ++ tailWord_3325742).sum := by decide
  have hdescent : baseEnd_3325742 < baseStart_3325742 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325753 : List Nat := [1, 2, 1, 7, 2, 1, 8]
def baseStart_3325753 : Nat := 118140960795 + 3325753 * 2 ^ 59
def prefixEnd_3325753 : Nat := 4983230072969 + 3 ^ 40 * 3325753 * 2
def baseEnd_3325753 : Nat := 42165674744010659501053

theorem tailTrace_3325753 : CollatzResearch.WordTrace tailWord_3325753 prefixEnd_3325753 42165674744010659501053 := by
  unfold tailWord_3325753
  simp only [CollatzResearch.WordTrace]
  refine ⟨121300177120372349237245913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80866784746914899491497275 121300177120372349237245913)
  ·
    refine ⟨90975132840279261927934435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121300177120372349237245913 90975132840279261927934435)
    ·
      refine ⟨136462699260418892891901653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90975132840279261927934435 136462699260418892891901653)
      ·
        refine ⟨3198344513916067802153945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 136462699260418892891901653 3198344513916067802153945)
        ·
          refine ⟨2398758385437050851615459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3198344513916067802153945 2398758385437050851615459)
          ·
            refine ⟨3598137578155576277423189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2398758385437050851615459 3598137578155576277423189)
            ·
              refine ⟨42165674744010659501053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3598137578155576277423189 42165674744010659501053)
              ·
                rfl

theorem cell22_3325753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 8].length) (baseStart_3325753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3325753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3325753 prefixEnd_3325753 := by exact prefixLift 3325753
  have htrace : WordTrace (prefixWord ++ tailWord_3325753) baseStart_3325753 baseEnd_3325753 := by
    simpa [prefixWord, tailWord_3325753, baseEnd_3325753] using wordTrace_append hprefix tailTrace_3325753
  have hstable : (prefixWord ++ tailWord_3325753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325753).length < 2 ^ (prefixWord ++ tailWord_3325753).sum := by decide
  have hdescent : baseEnd_3325753 < baseStart_3325753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325768 : List Nat := [2, 1, 3, 1, 1, 6, 1, 1, 3, 3]
def baseStart_3325768 : Nat := 118140960795 + 3325768 * 2 ^ 59
def prefixEnd_3325768 : Nat := 4983230072969 + 3 ^ 40 * 3325768 * 2
def baseEnd_3325768 : Nat := 1138478352894832767403385

theorem tailTrace_3325768 : CollatzResearch.WordTrace tailWord_3325768 prefixEnd_3325768 1138478352894832767403385 := by
  unfold tailWord_3325768
  simp only [CollatzResearch.WordTrace]
  refine ⟨60650362107659003399520979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80867149476878671199361305 60650362107659003399520979)
  ·
    refine ⟨90975543161488505099281469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60650362107659003399520979 90975543161488505099281469)
    ·
      refine ⟨34115828685558189412230551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90975543161488505099281469 34115828685558189412230551)
      ·
        refine ⟨51173743028337284118345827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34115828685558189412230551 51173743028337284118345827)
        ·
          refine ⟨76760614542505926177518741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51173743028337284118345827 76760614542505926177518741)
          ·
            refine ⟨3598153806679965289571191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 76760614542505926177518741 3598153806679965289571191)
            ·
              refine ⟨5397230710019947934356787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3598153806679965289571191 5397230710019947934356787)
              ·
                refine ⟨8095846065029921901535181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5397230710019947934356787 8095846065029921901535181)
                ·
                  refine ⟨3035942274386220713075693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8095846065029921901535181 3035942274386220713075693)
                  ·
                    refine ⟨1138478352894832767403385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3035942274386220713075693 1138478352894832767403385)
                    ·
                      rfl

theorem cell22_3325768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 1, 3, 3].length) (baseStart_3325768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3325768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3325768 prefixEnd_3325768 := by exact prefixLift 3325768
  have htrace : WordTrace (prefixWord ++ tailWord_3325768) baseStart_3325768 baseEnd_3325768 := by
    simpa [prefixWord, tailWord_3325768, baseEnd_3325768] using wordTrace_append hprefix tailTrace_3325768
  have hstable : (prefixWord ++ tailWord_3325768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325768).length < 2 ^ (prefixWord ++ tailWord_3325768).sum := by decide
  have hdescent : baseEnd_3325768 < baseStart_3325768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325781 : List Nat := [1, 3, 2, 2, 2, 3, 1, 3, 5]
def baseStart_3325781 : Nat := 118140960795 + 3325781 * 2 ^ 59
def prefixEnd_3325781 : Nat := 4983230072969 + 3 ^ 40 * 3325781 * 2
def baseEnd_3325781 : Nat := 379494267686835022276115

theorem tailTrace_3325781 : CollatzResearch.WordTrace tailWord_3325781 prefixEnd_3325781 379494267686835022276115 := by
  unfold tailWord_3325781
  simp only [CollatzResearch.WordTrace]
  refine ⟨121301198364270910019265197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80867465576180606679510131 121301198364270910019265197)
  ·
    refine ⟨45487949386601591257224449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121301198364270910019265197 45487949386601591257224449)
    ·
      refine ⟨34115962039951193442918337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45487949386601591257224449 34115962039951193442918337)
      ·
        refine ⟨25586971529963395082188753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34115962039951193442918337 25586971529963395082188753)
        ·
          refine ⟨19190228647472546311641565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25586971529963395082188753 19190228647472546311641565)
          ·
            refine ⟨7196335742802204866865587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19190228647472546311641565 7196335742802204866865587)
            ·
              refine ⟨10794503614203307300298381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7196335742802204866865587 10794503614203307300298381)
              ·
                refine ⟨4047938855326240237611893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10794503614203307300298381 4047938855326240237611893)
                ·
                  refine ⟨379494267686835022276115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4047938855326240237611893 379494267686835022276115)
                  ·
                    rfl

theorem cell22_3325781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 3, 5].length) (baseStart_3325781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3325781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3325781 prefixEnd_3325781 := by exact prefixLift 3325781
  have htrace : WordTrace (prefixWord ++ tailWord_3325781) baseStart_3325781 baseEnd_3325781 := by
    simpa [prefixWord, tailWord_3325781, baseEnd_3325781] using wordTrace_append hprefix tailTrace_3325781
  have hstable : (prefixWord ++ tailWord_3325781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325781).length < 2 ^ (prefixWord ++ tailWord_3325781).sum := by decide
  have hdescent : baseEnd_3325781 < baseStart_3325781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325824 : List Nat := [2, 1, 1, 2, 1, 2, 3, 2, 3, 5]
def baseStart_3325824 : Nat := 118140960795 + 3325824 * 2 ^ 59
def prefixEnd_3325824 : Nat := 4983230072969 + 3 ^ 40 * 3325824 * 2
def baseEnd_3325824 : Nat := 1138497522839267288003213

theorem tailTrace_3325824 : CollatzResearch.WordTrace tailWord_3325824 prefixEnd_3325824 1138497522839267288003213 := by
  unfold tailWord_3325824
  simp only [CollatzResearch.WordTrace]
  refine ⟨60651383351557564181540263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80868511135410085575387017 60651383351557564181540263)
  ·
    refine ⟨90977075027336346272310395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60651383351557564181540263 90977075027336346272310395)
    ·
      refine ⟨136465612541004519408465593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90977075027336346272310395 136465612541004519408465593)
      ·
        refine ⟨102349209405753389556349195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136465612541004519408465593 102349209405753389556349195)
        ·
          refine ⟨153523814108630084334523793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102349209405753389556349195 153523814108630084334523793)
          ·
            refine ⟨115142860581472563250892845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153523814108630084334523793 115142860581472563250892845)
            ·
              refine ⟨43178572718052211219084817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115142860581472563250892845 43178572718052211219084817)
              ·
                refine ⟨32383929538539158414313613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43178572718052211219084817 32383929538539158414313613)
                ·
                  refine ⟨12143973576952184405367605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32383929538539158414313613 12143973576952184405367605)
                  ·
                    refine ⟨1138497522839267288003213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12143973576952184405367605 1138497522839267288003213)
                    ·
                      rfl

theorem cell22_3325824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 3, 5].length) (baseStart_3325824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3325824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3325824 prefixEnd_3325824 := by exact prefixLift 3325824
  have htrace : WordTrace (prefixWord ++ tailWord_3325824) baseStart_3325824 baseEnd_3325824 := by
    simpa [prefixWord, tailWord_3325824, baseEnd_3325824] using wordTrace_append hprefix tailTrace_3325824
  have hstable : (prefixWord ++ tailWord_3325824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325824).length < 2 ^ (prefixWord ++ tailWord_3325824).sum := by decide
  have hdescent : baseEnd_3325824 < baseStart_3325824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325937 : List Nat := [1, 2, 2, 2, 6, 1, 1, 1, 3, 3]
def baseStart_3325937 : Nat := 118140960795 + 3325937 * 2 ^ 59
def prefixEnd_3325937 : Nat := 4983230072969 + 3 ^ 40 * 3325937 * 2
def baseEnd_3325937 : Nat := 1138536205048572659927867

theorem tailTrace_3325937 : CollatzResearch.WordTrace tailWord_3325937 prefixEnd_3325937 1138536205048572659927867 := by
  unfold tailWord_3325937
  simp only [CollatzResearch.WordTrace]
  refine ⟨121306888151705748661944065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80871258767803832441296043 121306888151705748661944065)
  ·
    refine ⟨90980166113779311496458049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121306888151705748661944065 90980166113779311496458049)
    ·
      refine ⟨68235124585334483622343537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90980166113779311496458049 68235124585334483622343537)
      ·
        refine ⟨51176343439000862716757653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68235124585334483622343537 51176343439000862716757653)
        ·
          refine ⟨2398891098703165439848015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 51176343439000862716757653 2398891098703165439848015)
          ·
            refine ⟨3598336648054748159772023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2398891098703165439848015 3598336648054748159772023)
            ·
              refine ⟨5397504972082122239658035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3598336648054748159772023 5397504972082122239658035)
              ·
                refine ⟨8096257458123183359487053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5397504972082122239658035 8096257458123183359487053)
                ·
                  refine ⟨3036096546796193759807645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8096257458123183359487053 3036096546796193759807645)
                  ·
                    refine ⟨1138536205048572659927867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3036096546796193759807645 1138536205048572659927867)
                    ·
                      rfl

theorem cell22_3325937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 1, 3, 3].length) (baseStart_3325937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3325937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3325937 prefixEnd_3325937 := by exact prefixLift 3325937
  have htrace : WordTrace (prefixWord ++ tailWord_3325937) baseStart_3325937 baseEnd_3325937 := by
    simpa [prefixWord, tailWord_3325937, baseEnd_3325937] using wordTrace_append hprefix tailTrace_3325937
  have hstable : (prefixWord ++ tailWord_3325937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325937).length < 2 ^ (prefixWord ++ tailWord_3325937).sum := by decide
  have hdescent : baseEnd_3325937 < baseStart_3325937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325950 : List Nat := [4, 2, 2, 2, 1, 2, 1, 3, 5]
def baseStart_3325950 : Nat := 118140960795 + 3325950 * 2 ^ 59
def prefixEnd_3325950 : Nat := 4983230072969 + 3 ^ 40 * 3325950 * 2
def baseEnd_3325950 : Nat := 379513551738081653117609

theorem tailTrace_3325950 : CollatzResearch.WordTrace tailWord_3325950 prefixEnd_3325950 379513551738081653117609 := by
  unfold tailWord_3325950
  simp only [CollatzResearch.WordTrace]
  refine ⟨15163420287582331485270913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80871574867105767921444869 15163420287582331485270913)
  ·
    refine ⟨11372565215686748613953185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15163420287582331485270913 11372565215686748613953185)
    ·
      refine ⟨8529423911765061460464889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11372565215686748613953185 8529423911765061460464889)
      ·
        refine ⟨6397067933823796095348667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8529423911765061460464889 6397067933823796095348667)
        ·
          refine ⟨9595601900735694143023001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6397067933823796095348667 9595601900735694143023001)
          ·
            refine ⟨7196701425551770607267251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9595601900735694143023001 7196701425551770607267251)
            ·
              refine ⟨10795052138327655910900877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7196701425551770607267251 10795052138327655910900877)
              ·
                refine ⟨4048144551872870966587829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10795052138327655910900877 4048144551872870966587829)
                ·
                  refine ⟨379513551738081653117609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4048144551872870966587829 379513551738081653117609)
                  ·
                    rfl

theorem cell22_3325950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 3, 5].length) (baseStart_3325950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3325950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3325950 prefixEnd_3325950 := by exact prefixLift 3325950
  have htrace : WordTrace (prefixWord ++ tailWord_3325950) baseStart_3325950 baseEnd_3325950 := by
    simpa [prefixWord, tailWord_3325950, baseEnd_3325950] using wordTrace_append hprefix tailTrace_3325950
  have hstable : (prefixWord ++ tailWord_3325950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325950).length < 2 ^ (prefixWord ++ tailWord_3325950).sum := by decide
  have hdescent : baseEnd_3325950 < baseStart_3325950 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3326023 : List Nat := [1, 1, 4, 1, 3, 1, 5, 6]
def baseStart_3326023 : Nat := 118140960795 + 3326023 * 2 ^ 59
def prefixEnd_3326023 : Nat := 4983230072969 + 3 ^ 40 * 3326023 * 2
def baseEnd_3326023 : Nat := 126507293845121900253067

theorem tailTrace_3326023 : CollatzResearch.WordTrace tailWord_3326023 prefixEnd_3326023 126507293845121900253067 := by
  unfold tailWord_3326023
  simp only [CollatzResearch.WordTrace]
  refine ⟨121310024829394185349574723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80873349886262790233049815 121310024829394185349574723)
  ·
    refine ⟨181965037244091278024362085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121310024829394185349574723 181965037244091278024362085)
    ·
      refine ⟨34118444483267114629567891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 181965037244091278024362085 34118444483267114629567891)
      ·
        refine ⟨51177666724900671944351837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34118444483267114629567891 51177666724900671944351837)
        ·
          refine ⟨19191625021837751979131939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51177666724900671944351837 19191625021837751979131939)
          ·
            refine ⟨28787437532756627968697909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19191625021837751979131939 28787437532756627968697909)
            ·
              refine ⟨2698822268695933872065429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28787437532756627968697909 2698822268695933872065429)
              ·
                refine ⟨126507293845121900253067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2698822268695933872065429 126507293845121900253067)
                ·
                  rfl

theorem cell22_3326023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 5, 6].length) (baseStart_3326023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3326023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3326023 prefixEnd_3326023 := by exact prefixLift 3326023
  have htrace : WordTrace (prefixWord ++ tailWord_3326023) baseStart_3326023 baseEnd_3326023 := by
    simpa [prefixWord, tailWord_3326023, baseEnd_3326023] using wordTrace_append hprefix tailTrace_3326023
  have hstable : (prefixWord ++ tailWord_3326023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3326023).length < 2 ^ (prefixWord ++ tailWord_3326023).sum := by decide
  have hdescent : baseEnd_3326023 < baseStart_3326023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3326023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3326055 : List Nat := [1, 1, 5, 1, 1, 2, 4, 1, 3, 3]
def baseStart_3326055 : Nat := 118140960795 + 3326055 * 2 ^ 59
def prefixEnd_3326055 : Nat := 4983230072969 + 3 ^ 40 * 3326055 * 2
def baseEnd_3326055 : Nat := 1138576598860059685477505

theorem tailTrace_3326055 : CollatzResearch.WordTrace tailWord_3326055 prefixEnd_3326055 1138576598860059685477505 := by
  unfold tailWord_3326055
  simp only [CollatzResearch.WordTrace]
  refine ⟨121311191965278254814739619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80874127976852169876493079 121311191965278254814739619)
  ·
    refine ⟨181966787947917382222109429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121311191965278254814739619 181966787947917382222109429)
    ·
      refine ⟨17059386370117254583322759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 181966787947917382222109429 17059386370117254583322759)
      ·
        refine ⟨25589079555175881874984139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17059386370117254583322759 25589079555175881874984139)
        ·
          refine ⟨38383619332763822812476209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25589079555175881874984139 38383619332763822812476209)
          ·
            refine ⟨28787714499572867109357157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38383619332763822812476209 28787714499572867109357157)
            ·
              refine ⟨5397696468669912583004467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28787714499572867109357157 5397696468669912583004467)
              ·
                refine ⟨8096544703004868874506701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5397696468669912583004467 8096544703004868874506701)
                ·
                  refine ⟨3036204263626825827940013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8096544703004868874506701 3036204263626825827940013)
                  ·
                    refine ⟨1138576598860059685477505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3036204263626825827940013 1138576598860059685477505)
                    ·
                      rfl

theorem cell22_3326055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 1, 3, 3].length) (baseStart_3326055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3326055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3326055 prefixEnd_3326055 := by exact prefixLift 3326055
  have htrace : WordTrace (prefixWord ++ tailWord_3326055) baseStart_3326055 baseEnd_3326055 := by
    simpa [prefixWord, tailWord_3326055, baseEnd_3326055] using wordTrace_append hprefix tailTrace_3326055
  have hstable : (prefixWord ++ tailWord_3326055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3326055).length < 2 ^ (prefixWord ++ tailWord_3326055).sum := by decide
  have hdescent : baseEnd_3326055 < baseStart_3326055 := by decide
  rcases family_descends (prefixWord ++ tailWord_3326055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3326106 : List Nat := [3, 1, 1, 5, 2, 1, 3, 2, 1, 3]
def baseStart_3326106 : Nat := 118140960795 + 3326106 * 2 ^ 59
def prefixEnd_3326106 : Nat := 4983230072969 + 3 ^ 40 * 3326106 * 2
def baseEnd_3326106 : Nat := 1138594057202312552452349

theorem tailTrace_3326106 : CollatzResearch.WordTrace tailWord_3326106 prefixEnd_3326106 1138594057202312552452349 := by
  unfold tailWord_3326106
  simp only [CollatzResearch.WordTrace]
  refine ⟨30328263022023372631211543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80875368058728993683230781 30328263022023372631211543)
  ·
    refine ⟨45492394533035058946817315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30328263022023372631211543 45492394533035058946817315)
    ·
      refine ⟨68238591799552588420225973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45492394533035058946817315 68238591799552588420225973)
      ·
        refine ⟨6397367981208055164396185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68238591799552588420225973 6397367981208055164396185)
        ·
          refine ⟨4798025985906041373297139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6397367981208055164396185 4798025985906041373297139)
          ·
            refine ⟨7197038978859062059945709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4798025985906041373297139 7197038978859062059945709)
            ·
              refine ⟨2698889617072148272479641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7197038978859062059945709 2698889617072148272479641)
              ·
                refine ⟨2024167212804111204359731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2698889617072148272479641 2024167212804111204359731)
                ·
                  refine ⟨3036250819206166806539597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2024167212804111204359731 3036250819206166806539597)
                  ·
                    refine ⟨1138594057202312552452349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3036250819206166806539597 1138594057202312552452349)
                    ·
                      rfl

theorem cell22_3326106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 3, 2, 1, 3].length) (baseStart_3326106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3326106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3326106 prefixEnd_3326106 := by exact prefixLift 3326106
  have htrace : WordTrace (prefixWord ++ tailWord_3326106) baseStart_3326106 baseEnd_3326106 := by
    simpa [prefixWord, tailWord_3326106, baseEnd_3326106] using wordTrace_append hprefix tailTrace_3326106
  have hstable : (prefixWord ++ tailWord_3326106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3326106).length < 2 ^ (prefixWord ++ tailWord_3326106).sum := by decide
  have hdescent : baseEnd_3326106 < baseStart_3326106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3326106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3326119 : List Nat := [1, 1, 6, 2, 2, 2, 2, 1, 5]
def baseStart_3326119 : Nat := 118140960795 + 3326119 * 2 ^ 59
def prefixEnd_3326119 : Nat := 4983230072969 + 3 ^ 40 * 3326119 * 2
def baseEnd_3326119 : Nat := 379532835789328283959103

theorem tailTrace_3326119 : CollatzResearch.WordTrace tailWord_3326119 prefixEnd_3326119 379532835789328283959103 := by
  unfold tailWord_3326119
  simp only [CollatzResearch.WordTrace]
  refine ⟨121313526237046393745069411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80875684158030929163379607 121313526237046393745069411)
  ·
    refine ⟨181970289355569590617604117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121313526237046393745069411 181970289355569590617604117)
    ·
      refine ⟨8529857313542324560200193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 181970289355569590617604117 8529857313542324560200193)
      ·
        refine ⟨6397392985156743420150145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8529857313542324560200193 6397392985156743420150145)
        ·
          refine ⟨4798044738867557565112609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6397392985156743420150145 4798044738867557565112609)
          ·
            refine ⟨3598533554150668173834457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4798044738867557565112609 3598533554150668173834457)
            ·
              refine ⟨2698900165613001130375843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3598533554150668173834457 2698900165613001130375843)
              ·
                refine ⟨4048350248419501695563765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2698900165613001130375843 4048350248419501695563765)
                ·
                  refine ⟨379532835789328283959103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4048350248419501695563765 379532835789328283959103)
                  ·
                    rfl

theorem cell22_3326119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 2, 1, 5].length) (baseStart_3326119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3326119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3326119 prefixEnd_3326119 := by exact prefixLift 3326119
  have htrace : WordTrace (prefixWord ++ tailWord_3326119) baseStart_3326119 baseEnd_3326119 := by
    simpa [prefixWord, tailWord_3326119, baseEnd_3326119] using wordTrace_append hprefix tailTrace_3326119
  have hstable : (prefixWord ++ tailWord_3326119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3326119).length < 2 ^ (prefixWord ++ tailWord_3326119).sum := by decide
  have hdescent : baseEnd_3326119 < baseStart_3326119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3326119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3326158 : List Nat := [4, 1, 1, 1, 4, 11]
def baseStart_3326158 : Nat := 118140960795 + 3326158 * 2 ^ 59
def prefixEnd_3326158 : Nat := 4983230072969 + 3 ^ 40 * 3326158 * 2
def baseEnd_3326158 : Nat := 14056936516851873458669

theorem tailTrace_3326158 : CollatzResearch.WordTrace tailWord_3326158 prefixEnd_3326158 14056936516851873458669 := by
  unfold tailWord_3326158
  simp only [CollatzResearch.WordTrace]
  refine ⟨15164368585488137925717391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80876632455936735603826085 15164368585488137925717391)
  ·
    refine ⟨22746552878232206888576087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15164368585488137925717391 22746552878232206888576087)
    ·
      refine ⟨34119829317348310332864131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22746552878232206888576087 34119829317348310332864131)
      ·
        refine ⟨51179743976022465499296197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34119829317348310332864131 51179743976022465499296197)
        ·
          refine ⟨9596201995504212281118037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51179743976022465499296197 9596201995504212281118037)
          ·
            refine ⟨14056936516851873458669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 9596201995504212281118037 14056936516851873458669)
            ·
              rfl

theorem cell22_3326158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 11].length) (baseStart_3326158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3326158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3326158 prefixEnd_3326158 := by exact prefixLift 3326158
  have htrace : WordTrace (prefixWord ++ tailWord_3326158) baseStart_3326158 baseEnd_3326158 := by
    simpa [prefixWord, tailWord_3326158, baseEnd_3326158] using wordTrace_append hprefix tailTrace_3326158
  have hstable : (prefixWord ++ tailWord_3326158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3326158).length < 2 ^ (prefixWord ++ tailWord_3326158).sum := by decide
  have hdescent : baseEnd_3326158 < baseStart_3326158 := by decide
  rcases family_descends (prefixWord ++ tailWord_3326158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3326162 : List Nat := [3, 2, 2, 2, 1, 2, 1, 4, 2, 3]
def baseStart_3326162 : Nat := 118140960795 + 3326162 * 2 ^ 59
def prefixEnd_3326162 : Nat := 4983230072969 + 3 ^ 40 * 3326162 * 2
def baseEnd_3326162 : Nat := 1138613227146747073052177

theorem tailTrace_3326162 : CollatzResearch.WordTrace tailWord_3326162 prefixEnd_3326162 1138613227146747073052177 := by
  unfold tailWord_3326162
  simp only [CollatzResearch.WordTrace]
  refine ⟨30328773643972653022221185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80876729717260408059256493 30328773643972653022221185)
  ·
    refine ⟨22746580232979489766665889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30328773643972653022221185 22746580232979489766665889)
    ·
      refine ⟨17059935174734617324999417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22746580232979489766665889 17059935174734617324999417)
      ·
        refine ⟨12794951381050962993749563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17059935174734617324999417 12794951381050962993749563)
        ·
          refine ⟨19192427071576444490624345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12794951381050962993749563 19192427071576444490624345)
          ·
            refine ⟨14394320303682333367968259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19192427071576444490624345 14394320303682333367968259)
            ·
              refine ⟨21591480455523500051952389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14394320303682333367968259 21591480455523500051952389)
              ·
                refine ⟨4048402585410656259741073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21591480455523500051952389 4048402585410656259741073)
                ·
                  refine ⟨3036301939057992194805805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4048402585410656259741073 3036301939057992194805805)
                  ·
                    refine ⟨1138613227146747073052177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3036301939057992194805805 1138613227146747073052177)
                    ·
                      rfl

theorem cell22_3326162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 4, 2, 3].length) (baseStart_3326162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3326162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3326162 prefixEnd_3326162 := by exact prefixLift 3326162
  have htrace : WordTrace (prefixWord ++ tailWord_3326162) baseStart_3326162 baseEnd_3326162 := by
    simpa [prefixWord, tailWord_3326162, baseEnd_3326162] using wordTrace_append hprefix tailTrace_3326162
  have hstable : (prefixWord ++ tailWord_3326162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3326162).length < 2 ^ (prefixWord ++ tailWord_3326162).sum := by decide
  have hdescent : baseEnd_3326162 < baseStart_3326162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3326162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3326188 : List Nat := [2, 2, 1, 1, 2, 3, 1, 2, 2, 6]
def baseStart_3326188 : Nat := 118140960795 + 3326188 * 2 ^ 59
def prefixEnd_3326188 : Nat := 4983230072969 + 3 ^ 40 * 3326188 * 2
def baseEnd_3326188 : Nat := 1138622127478091671902097

theorem tailTrace_3326188 : CollatzResearch.WordTrace tailWord_3326188 prefixEnd_3326188 1138622127478091671902097 := by
  unfold tailWord_3326188
  simp only [CollatzResearch.WordTrace]
  refine ⟨60658021436898209264665609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80877361915864279019554145 60658021436898209264665609)
  ·
    refine ⟨45493516077673656948499207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60658021436898209264665609 45493516077673656948499207)
    ·
      refine ⟨68240274116510485422748811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45493516077673656948499207 68240274116510485422748811)
      ·
        refine ⟨102360411174765728134123217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68240274116510485422748811 102360411174765728134123217)
        ·
          refine ⟨76770308381074296100592413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102360411174765728134123217 76770308381074296100592413)
          ·
            refine ⟨28788865642902861037722155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76770308381074296100592413 28788865642902861037722155)
            ·
              refine ⟨43183298464354291556583233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28788865642902861037722155 43183298464354291556583233)
              ·
                refine ⟨32387473848265718667437425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43183298464354291556583233 32387473848265718667437425)
                ·
                  refine ⟨24290605386199289000578069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32387473848265718667437425 24290605386199289000578069)
                  ·
                    refine ⟨1138622127478091671902097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24290605386199289000578069 1138622127478091671902097)
                    ·
                      rfl

theorem cell22_3326188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 6].length) (baseStart_3326188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3326188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3326188 prefixEnd_3326188 := by exact prefixLift 3326188
  have htrace : WordTrace (prefixWord ++ tailWord_3326188) baseStart_3326188 baseEnd_3326188 := by
    simpa [prefixWord, tailWord_3326188, baseEnd_3326188] using wordTrace_append hprefix tailTrace_3326188
  have hstable : (prefixWord ++ tailWord_3326188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3326188).length < 2 ^ (prefixWord ++ tailWord_3326188).sum := by decide
  have hdescent : baseEnd_3326188 < baseStart_3326188 := by decide
  rcases family_descends (prefixWord ++ tailWord_3326188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3326258 : List Nat := [3, 2, 1, 1, 6, 1, 1, 3, 1, 3]
def baseStart_3326258 : Nat := 118140960795 + 3326258 * 2 ^ 59
def prefixEnd_3326258 : Nat := 4983230072969 + 3 ^ 40 * 3326258 * 2
def baseEnd_3326258 : Nat := 1138646089908634822651883

theorem tailTrace_3326258 : CollatzResearch.WordTrace tailWord_3326258 prefixEnd_3326258 1138646089908634822651883 := by
  unfold tailWord_3326258
  simp only [CollatzResearch.WordTrace]
  refine ⟨30329648995885705121094857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80879063989028546989586285 30329648995885705121094857)
  ·
    refine ⟨22747236746914278840821143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30329648995885705121094857 22747236746914278840821143)
    ·
      refine ⟨34120855120371418261231715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22747236746914278840821143 34120855120371418261231715)
      ·
        refine ⟨51181282680557127391847573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34120855120371418261231715 51181282680557127391847573)
        ·
          refine ⟨2399122625651115346492855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 51181282680557127391847573 2399122625651115346492855)
          ·
            refine ⟨3598683938476673019739283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2399122625651115346492855 3598683938476673019739283)
            ·
              refine ⟨5398025907715009529608925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3598683938476673019739283 5398025907715009529608925)
              ·
                refine ⟨2024259715393128573603347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5398025907715009529608925 2024259715393128573603347)
                ·
                  refine ⟨3036389573089692860405021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2024259715393128573603347 3036389573089692860405021)
                  ·
                    refine ⟨1138646089908634822651883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3036389573089692860405021 1138646089908634822651883)
                    ·
                      rfl

theorem cell22_3326258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 3, 1, 3].length) (baseStart_3326258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3326258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3326258 prefixEnd_3326258 := by exact prefixLift 3326258
  have htrace : WordTrace (prefixWord ++ tailWord_3326258) baseStart_3326258 baseEnd_3326258 := by
    simpa [prefixWord, tailWord_3326258, baseEnd_3326258] using wordTrace_append hprefix tailTrace_3326258
  have hstable : (prefixWord ++ tailWord_3326258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3326258).length < 2 ^ (prefixWord ++ tailWord_3326258).sum := by decide
  have hdescent : baseEnd_3326258 < baseStart_3326258 := by decide
  rcases family_descends (prefixWord ++ tailWord_3326258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3326295 : List Nat := [1, 1, 3, 2, 3, 1, 1, 2, 4, 4]
def baseStart_3326295 : Nat := 118140960795 + 3326295 * 2 ^ 59
def prefixEnd_3326295 : Nat := 4983230072969 + 3 ^ 40 * 3326295 * 2
def baseEnd_3326295 : Nat := 1138658755764779059476769

theorem tailTrace_3326295 : CollatzResearch.WordTrace tailWord_3326295 prefixEnd_3326295 1138658755764779059476769 := by
  unfold tailWord_3326295
  simp only [CollatzResearch.WordTrace]
  refine ⟨121319945484408775803476339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80879963656272517202317559 121319945484408775803476339)
  ·
    refine ⟨181979918226613163705214509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121319945484408775803476339 181979918226613163705214509)
    ·
      refine ⟨68242469334979936389455441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181979918226613163705214509 68242469334979936389455441)
      ·
        refine ⟨51181852001234952292091581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68242469334979936389455441 51181852001234952292091581)
        ·
          refine ⟨19193194500463107109534343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51181852001234952292091581 19193194500463107109534343)
          ·
            refine ⟨28789791750694660664301515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19193194500463107109534343 28789791750694660664301515)
            ·
              refine ⟨43184687626041990996452273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28789791750694660664301515 43184687626041990996452273)
              ·
                refine ⟨32388515719531493247339205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43184687626041990996452273 32388515719531493247339205)
                ·
                  refine ⟨6072846697412154983876101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32388515719531493247339205 6072846697412154983876101)
                  ·
                    refine ⟨1138658755764779059476769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6072846697412154983876101 1138658755764779059476769)
                    ·
                      rfl

theorem cell22_3326295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 4, 4].length) (baseStart_3326295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3326295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3326295 prefixEnd_3326295 := by exact prefixLift 3326295
  have htrace : WordTrace (prefixWord ++ tailWord_3326295) baseStart_3326295 baseEnd_3326295 := by
    simpa [prefixWord, tailWord_3326295, baseEnd_3326295] using wordTrace_append hprefix tailTrace_3326295
  have hstable : (prefixWord ++ tailWord_3326295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3326295).length < 2 ^ (prefixWord ++ tailWord_3326295).sum := by decide
  have hdescent : baseEnd_3326295 < baseStart_3326295 := by decide
  rcases family_descends (prefixWord ++ tailWord_3326295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3326312 : List Nat := [2, 1, 4, 2, 2, 1, 1, 3, 2, 4]
def baseStart_3326312 : Nat := 118140960795 + 3326312 * 2 ^ 59
def prefixEnd_3326312 : Nat := 4983230072969 + 3 ^ 40 * 3326312 * 2
def baseEnd_3326312 : Nat := 1138664575212196681801717

theorem tailTrace_3326312 : CollatzResearch.WordTrace tailWord_3326312 prefixEnd_3326312 1138664575212196681801717 := by
  unfold tailWord_3326312
  simp only [CollatzResearch.WordTrace]
  refine ⟨60660282762673593853422595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80880377016898125137896793 60660282762673593853422595)
  ·
    refine ⟨90990424144010390780133893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60660282762673593853422595 90990424144010390780133893)
    ·
      refine ⟨17060704527001948271275105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90990424144010390780133893 17060704527001948271275105)
      ·
        refine ⟨12795528395251461203456329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17060704527001948271275105 12795528395251461203456329)
        ·
          refine ⟨9596646296438595902592247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12795528395251461203456329 9596646296438595902592247)
          ·
            refine ⟨14394969444657893853888371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9596646296438595902592247 14394969444657893853888371)
            ·
              refine ⟨21592454166986840780832557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14394969444657893853888371 21592454166986840780832557)
              ·
                refine ⟨8097170312620065292812209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21592454166986840780832557 8097170312620065292812209)
                ·
                  refine ⟨6072877734465048969609157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8097170312620065292812209 6072877734465048969609157)
                  ·
                    refine ⟨1138664575212196681801717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6072877734465048969609157 1138664575212196681801717)
                    ·
                      rfl

theorem cell22_3326312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_3326312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3326312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3326312 prefixEnd_3326312 := by exact prefixLift 3326312
  have htrace : WordTrace (prefixWord ++ tailWord_3326312) baseStart_3326312 baseEnd_3326312 := by
    simpa [prefixWord, tailWord_3326312, baseEnd_3326312] using wordTrace_append hprefix tailTrace_3326312
  have hstable : (prefixWord ++ tailWord_3326312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3326312).length < 2 ^ (prefixWord ++ tailWord_3326312).sum := by decide
  have hdescent : baseEnd_3326312 < baseStart_3326312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3326312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3326340 : List Nat := [2, 3, 2, 1, 1, 2, 1, 1, 1, 8]
def baseStart_3326340 : Nat := 118140960795 + 3326340 * 2 ^ 59
def prefixEnd_3326340 : Nat := 4983230072969 + 3 ^ 40 * 3326340 * 2
def baseEnd_3326340 : Nat := 1138674160184413942101631

theorem tailTrace_3326340 : CollatzResearch.WordTrace tailWord_3326340 prefixEnd_3326340 1138674160184413942101631 := by
  unfold tailWord_3326340
  simp only [CollatzResearch.WordTrace]
  refine ⟨60660793384622874244432237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80881057846163832325909649 60660793384622874244432237)
  ·
    refine ⟨22747797519233577841662089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60660793384622874244432237 22747797519233577841662089)
    ·
      refine ⟨17060848139425183381246567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22747797519233577841662089 17060848139425183381246567)
      ·
        refine ⟨25591272209137775071869851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17060848139425183381246567 25591272209137775071869851)
        ·
          refine ⟨38386908313706662607804777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25591272209137775071869851 38386908313706662607804777)
          ·
            refine ⟨28790181235279996955853583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38386908313706662607804777 28790181235279996955853583)
            ·
              refine ⟨43185271852919995433780375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28790181235279996955853583 43185271852919995433780375)
              ·
                refine ⟨64777907779379993150670563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43185271852919995433780375 64777907779379993150670563)
                ·
                  refine ⟨97166861669069989726005845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64777907779379993150670563 97166861669069989726005845)
                  ·
                    refine ⟨1138674160184413942101631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 97166861669069989726005845 1138674160184413942101631)
                    ·
                      rfl

theorem cell22_3326340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_3326340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3326340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3326340 prefixEnd_3326340 := by exact prefixLift 3326340
  have htrace : WordTrace (prefixWord ++ tailWord_3326340) baseStart_3326340 baseEnd_3326340 := by
    simpa [prefixWord, tailWord_3326340, baseEnd_3326340] using wordTrace_append hprefix tailTrace_3326340
  have hstable : (prefixWord ++ tailWord_3326340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3326340).length < 2 ^ (prefixWord ++ tailWord_3326340).sum := by decide
  have hdescent : baseEnd_3326340 < baseStart_3326340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3326340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3326432 : List Nat := [2, 1, 1, 3, 1, 1, 3, 1, 6, 3]
def baseStart_3326432 : Nat := 118140960795 + 3326432 * 2 ^ 59
def prefixEnd_3326432 : Nat := 4983230072969 + 3 ^ 40 * 3326432 * 2
def baseEnd_3326432 : Nat := 1138705653664556368801349

theorem tailTrace_3326432 : CollatzResearch.WordTrace tailWord_3326432 prefixEnd_3326432 1138705653664556368801349 := by
  unfold tailWord_3326432
  simp only [CollatzResearch.WordTrace]
  refine ⟨60662471142456224100606775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80883294856608298800809033 60662471142456224100606775)
  ·
    refine ⟨90993706713684336150910163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60662471142456224100606775 90993706713684336150910163)
    ·
      refine ⟨136490560070526504226365245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90993706713684336150910163 136490560070526504226365245)
      ·
        refine ⟨51183960026447439084886967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136490560070526504226365245 51183960026447439084886967)
        ·
          refine ⟨76775940039671158627330451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51183960026447439084886967 76775940039671158627330451)
          ·
            refine ⟨115163910059506737940995677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76775940039671158627330451 115163910059506737940995677)
            ·
              refine ⟨43186466272315026727873379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115163910059506737940995677 43186466272315026727873379)
              ·
                refine ⟨64779699408472540091810069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43186466272315026727873379 64779699408472540091810069)
                ·
                  refine ⟨3036548409772150316803597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 64779699408472540091810069 3036548409772150316803597)
                  ·
                    refine ⟨1138705653664556368801349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3036548409772150316803597 1138705653664556368801349)
                    ·
                      rfl

theorem cell22_3326432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 6, 3].length) (baseStart_3326432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3326432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3326432 prefixEnd_3326432 := by exact prefixLift 3326432
  have htrace : WordTrace (prefixWord ++ tailWord_3326432) baseStart_3326432 baseEnd_3326432 := by
    simpa [prefixWord, tailWord_3326432, baseEnd_3326432] using wordTrace_append hprefix tailTrace_3326432
  have hstable : (prefixWord ++ tailWord_3326432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3326432).length < 2 ^ (prefixWord ++ tailWord_3326432).sum := by decide
  have hdescent : baseEnd_3326432 < baseStart_3326432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3326432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3326449 : List Nat := [1, 2, 2, 2, 3, 1, 2, 4, 2, 3]
def baseStart_3326449 : Nat := 118140960795 + 3326449 * 2 ^ 59
def prefixEnd_3326449 : Nat := 4983230072969 + 3 ^ 40 * 3326449 * 2
def baseEnd_3326449 : Nat := 1138711473111973991126297

theorem tailTrace_3326449 : CollatzResearch.WordTrace tailWord_3326449 prefixEnd_3326449 1138711473111973991126297 := by
  unfold tailWord_3326449
  simp only [CollatzResearch.WordTrace]
  refine ⟨121325562325850860104582401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80883708217233906736388267 121325562325850860104582401)
  ·
    refine ⟨90994171744388145078436801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121325562325850860104582401 90994171744388145078436801)
    ·
      refine ⟨68245628808291108808827601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90994171744388145078436801 68245628808291108808827601)
      ·
        refine ⟨51184221606218331606620701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68245628808291108808827601 51184221606218331606620701)
        ·
          refine ⟨19194083102331874352482763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51184221606218331606620701 19194083102331874352482763)
          ·
            refine ⟨28791124653497811528724145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19194083102331874352482763 28791124653497811528724145)
            ·
              refine ⟨21593343490123358646543109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28791124653497811528724145 21593343490123358646543109)
              ·
                refine ⟨4048751904398129746226833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21593343490123358646543109 4048751904398129746226833)
                ·
                  refine ⟨3036563928298597309670125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4048751904398129746226833 3036563928298597309670125)
                  ·
                    refine ⟨1138711473111973991126297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3036563928298597309670125 1138711473111973991126297)
                    ·
                      rfl

theorem cell22_3326449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 4, 2, 3].length) (baseStart_3326449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3326449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3326449 prefixEnd_3326449 := by exact prefixLift 3326449
  have htrace : WordTrace (prefixWord ++ tailWord_3326449) baseStart_3326449 baseEnd_3326449 := by
    simpa [prefixWord, tailWord_3326449, baseEnd_3326449] using wordTrace_append hprefix tailTrace_3326449
  have hstable : (prefixWord ++ tailWord_3326449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3326449).length < 2 ^ (prefixWord ++ tailWord_3326449).sum := by decide
  have hdescent : baseEnd_3326449 < baseStart_3326449 := by decide
  rcases family_descends (prefixWord ++ tailWord_3326449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3326470 : List Nat := [6, 2, 1, 1, 1, 1, 3, 2, 1, 4]
def baseStart_3326470 : Nat := 118140960795 + 3326470 * 2 ^ 59
def prefixEnd_3326470 : Nat := 4983230072969 + 3 ^ 40 * 3326470 * 2
def baseEnd_3326470 : Nat := 1138718661841136936351233

theorem tailTrace_3326470 : CollatzResearch.WordTrace tailWord_3326470 prefixEnd_3326470 1138718661841136936351233 := by
  unfold tailWord_3326470
  simp only [CollatzResearch.WordTrace]
  refine ⟨3791447758086711896596777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 80884218839183187127397909 3791447758086711896596777)
  ·
    refine ⟨2843585818565033922447583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3791447758086711896596777 2843585818565033922447583)
    ·
      refine ⟨4265378727847550883671375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2843585818565033922447583 4265378727847550883671375)
      ·
        refine ⟨6398068091771326325507063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4265378727847550883671375 6398068091771326325507063)
        ·
          refine ⟨9597102137656989488260595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6398068091771326325507063 9597102137656989488260595)
          ·
            refine ⟨14395653206485484232390893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9597102137656989488260595 14395653206485484232390893)
            ·
              refine ⟨5398369952432056587146585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14395653206485484232390893 5398369952432056587146585)
              ·
                refine ⟨4048777464324042440359939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5398369952432056587146585 4048777464324042440359939)
                ·
                  refine ⟨6073166196486063660539909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4048777464324042440359939 6073166196486063660539909)
                  ·
                    refine ⟨1138718661841136936351233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6073166196486063660539909 1138718661841136936351233)
                    ·
                      rfl

theorem cell22_3326470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_3326470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3326470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3326470 prefixEnd_3326470 := by exact prefixLift 3326470
  have htrace : WordTrace (prefixWord ++ tailWord_3326470) baseStart_3326470 baseEnd_3326470 := by
    simpa [prefixWord, tailWord_3326470, baseEnd_3326470] using wordTrace_append hprefix tailTrace_3326470
  have hstable : (prefixWord ++ tailWord_3326470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3326470).length < 2 ^ (prefixWord ++ tailWord_3326470).sum := by decide
  have hdescent : baseEnd_3326470 < baseStart_3326470 := by decide
  rcases family_descends (prefixWord ++ tailWord_3326470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3326522 : List Nat := [3, 1, 1, 1, 3, 3, 1, 1, 1, 7]
def baseStart_3326522 : Nat := 118140960795 + 3326522 * 2 ^ 59
def prefixEnd_3326522 : Nat := 4983230072969 + 3 ^ 40 * 3326522 * 2
def baseEnd_3326522 : Nat := 1138736462503826134051073

theorem tailTrace_3326522 : CollatzResearch.WordTrace tailWord_3326522 prefixEnd_3326522 1138736462503826134051073 := by
  unfold tailWord_3326522
  simp only [CollatzResearch.WordTrace]
  refine ⟨30332056213646598392997455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80885483236390929047993213 30332056213646598392997455)
  ·
    refine ⟨45498084320469897589496183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30332056213646598392997455 45498084320469897589496183)
    ·
      refine ⟨68247126480704846384244275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45498084320469897589496183 68247126480704846384244275)
      ·
        refine ⟨102370689721057269576366413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68247126480704846384244275 102370689721057269576366413)
        ·
          refine ⟨38389008645396476091137405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102370689721057269576366413 38389008645396476091137405)
          ·
            refine ⟨14395878242023678534176527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38389008645396476091137405 14395878242023678534176527)
            ·
              refine ⟨21593817363035517801264791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14395878242023678534176527 21593817363035517801264791)
              ·
                refine ⟨32390726044553276701897187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21593817363035517801264791 32390726044553276701897187)
                ·
                  refine ⟨48586089066829915052845781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32390726044553276701897187 48586089066829915052845781)
                  ·
                    refine ⟨1138736462503826134051073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48586089066829915052845781 1138736462503826134051073)
                    ·
                      rfl

theorem cell22_3326522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 1, 7].length) (baseStart_3326522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3326522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3326522 prefixEnd_3326522 := by exact prefixLift 3326522
  have htrace : WordTrace (prefixWord ++ tailWord_3326522) baseStart_3326522 baseEnd_3326522 := by
    simpa [prefixWord, tailWord_3326522, baseEnd_3326522] using wordTrace_append hprefix tailTrace_3326522
  have hstable : (prefixWord ++ tailWord_3326522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3326522).length < 2 ^ (prefixWord ++ tailWord_3326522).sum := by decide
  have hdescent : baseEnd_3326522 < baseStart_3326522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3326522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3326524 : List Nat := [2, 2, 2, 2, 3, 1, 2, 3, 5]
def baseStart_3326524 : Nat := 118140960795 + 3326524 * 2 ^ 59
def prefixEnd_3326524 : Nat := 4983230072969 + 3 ^ 40 * 3326524 * 2
def baseEnd_3326524 : Nat := 379579049048232931833689

theorem tailTrace_3326524 : CollatzResearch.WordTrace tailWord_3326524 prefixEnd_3326524 379579049048232931833689 := by
  unfold tailWord_3326524
  simp only [CollatzResearch.WordTrace]
  refine ⟨60664148900289573956781313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80885531867052765275708417 60664148900289573956781313)
  ·
    refine ⟨45498111675217180467585985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60664148900289573956781313 45498111675217180467585985)
    ·
      refine ⟨34123583756412885350689489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45498111675217180467585985 34123583756412885350689489)
      ·
        refine ⟨25592687817309664013017117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34123583756412885350689489 25592687817309664013017117)
        ·
          refine ⟨9597257931491124004881419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25592687817309664013017117 9597257931491124004881419)
          ·
            refine ⟨14395886897236686007322129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9597257931491124004881419 14395886897236686007322129)
            ·
              refine ⟨10796915172927514505491597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14395886897236686007322129 10796915172927514505491597)
              ·
                refine ⟨4048843189847817939559349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10796915172927514505491597 4048843189847817939559349)
                ·
                  refine ⟨379579049048232931833689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4048843189847817939559349 379579049048232931833689)
                  ·
                    rfl

theorem cell22_3326524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 3, 5].length) (baseStart_3326524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3326524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3326524 prefixEnd_3326524 := by exact prefixLift 3326524
  have htrace : WordTrace (prefixWord ++ tailWord_3326524) baseStart_3326524 baseEnd_3326524 := by
    simpa [prefixWord, tailWord_3326524, baseEnd_3326524] using wordTrace_append hprefix tailTrace_3326524
  have hstable : (prefixWord ++ tailWord_3326524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3326524).length < 2 ^ (prefixWord ++ tailWord_3326524).sum := by decide
  have hdescent : baseEnd_3326524 < baseStart_3326524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3326524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3326532 : List Nat := [2, 3, 5, 1, 2, 1, 1, 1, 2, 4]
def baseStart_3326532 : Nat := 118140960795 + 3326532 * 2 ^ 59
def prefixEnd_3326532 : Nat := 4983230072969 + 3 ^ 40 * 3326532 * 2
def baseEnd_3326532 : Nat := 1138739885708189441301043

theorem tailTrace_3326532 : CollatzResearch.WordTrace tailWord_3326532 prefixEnd_3326532 1138739885708189441301043 := by
  unfold tailWord_3326532
  simp only [CollatzResearch.WordTrace]
  refine ⟨60664294792275082639926925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80885726389700110186569233 60664294792275082639926925)
  ·
    refine ⟨22749110547103155989972597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60664294792275082639926925 22749110547103155989972597)
    ·
      refine ⟨2132729113790920874059931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22749110547103155989972597 2132729113790920874059931)
      ·
        refine ⟨3199093670686381311089897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2132729113790920874059931 3199093670686381311089897)
        ·
          refine ⟨2399320253014785983317423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3199093670686381311089897 2399320253014785983317423)
          ·
            refine ⟨3598980379522178974976135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2399320253014785983317423 3598980379522178974976135)
            ·
              refine ⟨5398470569283268462464203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3598980379522178974976135 5398470569283268462464203)
              ·
                refine ⟨8097705853924902693696305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5398470569283268462464203 8097705853924902693696305)
                ·
                  refine ⟨6073279390443677020272229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8097705853924902693696305 6073279390443677020272229)
                  ·
                    refine ⟨1138739885708189441301043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6073279390443677020272229 1138739885708189441301043)
                    ·
                      rfl

theorem cell22_3326532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_3326532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3326532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3326532 prefixEnd_3326532 := by exact prefixLift 3326532
  have htrace : WordTrace (prefixWord ++ tailWord_3326532) baseStart_3326532 baseEnd_3326532 := by
    simpa [prefixWord, tailWord_3326532, baseEnd_3326532] using wordTrace_append hprefix tailTrace_3326532
  have hstable : (prefixWord ++ tailWord_3326532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3326532).length < 2 ^ (prefixWord ++ tailWord_3326532).sum := by decide
  have hdescent : baseEnd_3326532 < baseStart_3326532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3326532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3326599 : List Nat := [1, 1, 4, 2, 1, 2, 2, 3, 2, 4]
def baseStart_3326599 : Nat := 118140960795 + 3326599 * 2 ^ 59
def prefixEnd_3326599 : Nat := 4983230072969 + 3 ^ 40 * 3326599 * 2
def baseEnd_3326599 : Nat := 1138762821177423599875837

theorem tailTrace_3326599 : CollatzResearch.WordTrace tailWord_3326599 prefixEnd_3326599 1138762821177423599875837 := by
  unfold tailWord_3326599
  simp only [CollatzResearch.WordTrace]
  refine ⟨121331033275307435722542851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80887355516871623815028567 121331033275307435722542851)
  ·
    refine ⟨181996549912961153583814277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121331033275307435722542851 181996549912961153583814277)
    ·
      refine ⟨34124353108680216296965177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 181996549912961153583814277 34124353108680216296965177)
      ·
        refine ⟨25593264831510162222723883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34124353108680216296965177 25593264831510162222723883)
        ·
          refine ⟨38389897247265243334085825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25593264831510162222723883 38389897247265243334085825)
          ·
            refine ⟨28792422935448932500564369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38389897247265243334085825 28792422935448932500564369)
            ·
              refine ⟨21594317201586699375423277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28792422935448932500564369 21594317201586699375423277)
              ·
                refine ⟨8097868950595012265783729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21594317201586699375423277 8097868950595012265783729)
                ·
                  refine ⟨6073401712946259199337797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8097868950595012265783729 6073401712946259199337797)
                  ·
                    refine ⟨1138762821177423599875837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6073401712946259199337797 1138762821177423599875837)
                    ·
                      rfl

theorem cell22_3326599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 3, 2, 4].length) (baseStart_3326599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3326599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3326599 prefixEnd_3326599 := by exact prefixLift 3326599
  have htrace : WordTrace (prefixWord ++ tailWord_3326599) baseStart_3326599 baseEnd_3326599 := by
    simpa [prefixWord, tailWord_3326599, baseEnd_3326599] using wordTrace_append hprefix tailTrace_3326599
  have hstable : (prefixWord ++ tailWord_3326599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3326599).length < 2 ^ (prefixWord ++ tailWord_3326599).sum := by decide
  have hdescent : baseEnd_3326599 < baseStart_3326599 := by decide
  rcases family_descends (prefixWord ++ tailWord_3326599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3326680 : List Nat := [2, 1, 2, 2, 3, 2, 4, 2, 1, 3]
def baseStart_3326680 : Nat := 118140960795 + 3326680 * 2 ^ 59
def prefixEnd_3326680 : Nat := 4983230072969 + 3 ^ 40 * 3326680 * 2
def baseEnd_3326680 : Nat := 1138790549132766388600589

theorem tailTrace_3326680 : CollatzResearch.WordTrace tailWord_3326680 prefixEnd_3326680 1138790549132766388600589 := by
  unfold tailWord_3326680
  simp only [CollatzResearch.WordTrace]
  refine ⟨60666993794006993278120747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80889325058675991037494329 60666993794006993278120747)
  ·
    refine ⟨91000490691010489917181121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60666993794006993278120747 91000490691010489917181121)
    ·
      refine ⟨68250368018257867437885841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91000490691010489917181121 68250368018257867437885841)
      ·
        refine ⟨51187776013693400578414381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68250368018257867437885841 51187776013693400578414381)
        ·
          refine ⟨19195416005135025216905393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51187776013693400578414381 19195416005135025216905393)
          ·
            refine ⟨14396562003851268912679045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19195416005135025216905393 14396562003851268912679045)
            ·
              refine ⟨2699355375722112921127321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14396562003851268912679045 2699355375722112921127321)
              ·
                refine ⟨2024516531791584690845491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2699355375722112921127321 2024516531791584690845491)
                ·
                  refine ⟨3036774797687377036268237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2024516531791584690845491 3036774797687377036268237)
                  ·
                    refine ⟨1138790549132766388600589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3036774797687377036268237 1138790549132766388600589)
                    ·
                      rfl

theorem cell22_3326680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 4, 2, 1, 3].length) (baseStart_3326680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3326680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3326680 prefixEnd_3326680 := by exact prefixLift 3326680
  have htrace : WordTrace (prefixWord ++ tailWord_3326680) baseStart_3326680 baseEnd_3326680 := by
    simpa [prefixWord, tailWord_3326680, baseEnd_3326680] using wordTrace_append hprefix tailTrace_3326680
  have hstable : (prefixWord ++ tailWord_3326680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3326680).length < 2 ^ (prefixWord ++ tailWord_3326680).sum := by decide
  have hdescent : baseEnd_3326680 < baseStart_3326680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3326680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3326691 : List Nat := [1, 1, 1, 7, 1, 2, 1, 1, 2, 5]
def baseStart_3326691 : Nat := 118140960795 + 3326691 * 2 ^ 59
def prefixEnd_3326691 : Nat := 4983230072969 + 3 ^ 40 * 3326691 * 2
def baseEnd_3326691 : Nat := 1138794314657566026575555

theorem tailTrace_3326691 : CollatzResearch.WordTrace tailWord_3326691 prefixEnd_3326691 1138794314657566026575555 := by
  unfold tailWord_3326691
  simp only [CollatzResearch.WordTrace]
  refine ⟨121334388790974135434891927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80889592527316090289927951 121334388790974135434891927)
  ·
    refine ⟨182001583186461203152337891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121334388790974135434891927 182001583186461203152337891)
    ·
      refine ⟨273002374779691804728506837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182001583186461203152337891 273002374779691804728506837)
      ·
        refine ⟨6398493158899026673324379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 273002374779691804728506837 6398493158899026673324379)
        ·
          refine ⟨9597739738348540009986569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6398493158899026673324379 9597739738348540009986569)
          ·
            refine ⟨7198304803761405007489927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9597739738348540009986569 7198304803761405007489927)
            ·
              refine ⟨10797457205642107511234891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7198304803761405007489927 10797457205642107511234891)
              ·
                refine ⟨16196185808463161266852337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10797457205642107511234891 16196185808463161266852337)
                ·
                  refine ⟨12147139356347370950139253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16196185808463161266852337 12147139356347370950139253)
                  ·
                    refine ⟨1138794314657566026575555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12147139356347370950139253 1138794314657566026575555)
                    ·
                      rfl

theorem cell22_3326691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 1, 2, 5].length) (baseStart_3326691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3326691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3326691 prefixEnd_3326691 := by exact prefixLift 3326691
  have htrace : WordTrace (prefixWord ++ tailWord_3326691) baseStart_3326691 baseEnd_3326691 := by
    simpa [prefixWord, tailWord_3326691, baseEnd_3326691] using wordTrace_append hprefix tailTrace_3326691
  have hstable : (prefixWord ++ tailWord_3326691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3326691).length < 2 ^ (prefixWord ++ tailWord_3326691).sum := by decide
  have hdescent : baseEnd_3326691 < baseStart_3326691 := by decide
  rcases family_descends (prefixWord ++ tailWord_3326691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3326704 : List Nat := [2, 1, 1, 1, 3, 1, 5, 2, 6]
def baseStart_3326704 : Nat := 118140960795 + 3326704 * 2 ^ 59
def prefixEnd_3326704 : Nat := 4983230072969 + 3 ^ 40 * 3326704 * 2
def baseEnd_3326704 : Nat := 379599588274412775333505

theorem tailTrace_3326704 : CollatzResearch.WordTrace tailWord_3326704 prefixEnd_3326704 379599588274412775333505 := by
  unfold tailWord_3326704
  simp only [CollatzResearch.WordTrace]
  refine ⟨60667431469963519327557583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80889908626618025770076777 60667431469963519327557583)
  ·
    refine ⟨91001147204945278991336375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60667431469963519327557583 91001147204945278991336375)
    ·
      refine ⟨136501720807417918487004563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91001147204945278991336375 136501720807417918487004563)
      ·
        refine ⟨204752581211126877730506845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136501720807417918487004563 204752581211126877730506845)
        ·
          refine ⟨76782217954172579148940067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204752581211126877730506845 76782217954172579148940067)
          ·
            refine ⟨115173326931258868723410101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76782217954172579148940067 115173326931258868723410101)
            ·
              refine ⟨10797499399805518942819697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 115173326931258868723410101 10797499399805518942819697)
              ·
                refine ⟨8098124549854139207114773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10797499399805518942819697 8098124549854139207114773)
                ·
                  refine ⟨379599588274412775333505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8098124549854139207114773 379599588274412775333505)
                  ·
                    rfl

theorem cell22_3326704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 2, 6].length) (baseStart_3326704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3326704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3326704 prefixEnd_3326704 := by exact prefixLift 3326704
  have htrace : WordTrace (prefixWord ++ tailWord_3326704) baseStart_3326704 baseEnd_3326704 := by
    simpa [prefixWord, tailWord_3326704, baseEnd_3326704] using wordTrace_append hprefix tailTrace_3326704
  have hstable : (prefixWord ++ tailWord_3326704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3326704).length < 2 ^ (prefixWord ++ tailWord_3326704).sum := by decide
  have hdescent : baseEnd_3326704 < baseStart_3326704 := by decide
  rcases family_descends (prefixWord ++ tailWord_3326704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3326706 : List Nat := [3, 2, 1, 3, 1, 2, 2, 1, 3, 4]
def baseStart_3326706 : Nat := 118140960795 + 3326706 * 2 ^ 59
def prefixEnd_3326706 : Nat := 4983230072969 + 3 ^ 40 * 3326706 * 2
def baseEnd_3326706 : Nat := 1138799449464110987450509

theorem tailTrace_3326706 : CollatzResearch.WordTrace tailWord_3326706 prefixEnd_3326706 1138799449464110987450509 := by
  unfold tailWord_3326706
  simp only [CollatzResearch.WordTrace]
  refine ⟨30333733971479948249171993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80889957257279861997791981 30333733971479948249171993)
  ·
    refine ⟨22750300478609961186878995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30333733971479948249171993 22750300478609961186878995)
    ·
      refine ⟨34125450717914941780318493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22750300478609961186878995 34125450717914941780318493)
      ·
        refine ⟨12797044019218103167619435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34125450717914941780318493 12797044019218103167619435)
        ·
          refine ⟨19195566028827154751429153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12797044019218103167619435 19195566028827154751429153)
          ·
            refine ⟨14396674521620366063571865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19195566028827154751429153 14396674521620366063571865)
            ·
              refine ⟨10797505891215274547678899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14396674521620366063571865 10797505891215274547678899)
              ·
                refine ⟨16196258836822911821518349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10797505891215274547678899 16196258836822911821518349)
                ·
                  refine ⟨6073597063808591933069381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16196258836822911821518349 6073597063808591933069381)
                  ·
                    refine ⟨1138799449464110987450509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6073597063808591933069381 1138799449464110987450509)
                    ·
                      rfl

theorem cell22_3326706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 1, 3, 4].length) (baseStart_3326706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3326706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3326706 prefixEnd_3326706 := by exact prefixLift 3326706
  have htrace : WordTrace (prefixWord ++ tailWord_3326706) baseStart_3326706 baseEnd_3326706 := by
    simpa [prefixWord, tailWord_3326706, baseEnd_3326706] using wordTrace_append hprefix tailTrace_3326706
  have hstable : (prefixWord ++ tailWord_3326706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3326706).length < 2 ^ (prefixWord ++ tailWord_3326706).sum := by decide
  have hdescent : baseEnd_3326706 < baseStart_3326706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3326706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3326764 : List Nat := [2, 2, 1, 1, 1, 4, 1, 1, 2, 7]
def baseStart_3326764 : Nat := 118140960795 + 3326764 * 2 ^ 59
def prefixEnd_3326764 : Nat := 4983230072969 + 3 ^ 40 * 3326764 * 2
def baseEnd_3326764 : Nat := 1138819304049418169500331

theorem tailTrace_3326764 : CollatzResearch.WordTrace tailWord_3326764 prefixEnd_3326764 1138819304049418169500331 := by
  unfold tailWord_3326764
  simp only [CollatzResearch.WordTrace]
  refine ⟨60668525659854834451149673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80891367546473112601532897 60668525659854834451149673)
  ·
    refine ⟨45501394244891125838362255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60668525659854834451149673 45501394244891125838362255)
    ·
      refine ⟨68252091367336688757543383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45501394244891125838362255 68252091367336688757543383)
      ·
        refine ⟨102378137051005033136315075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68252091367336688757543383 102378137051005033136315075)
        ·
          refine ⟨153567205576507549704472613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102378137051005033136315075 153567205576507549704472613)
          ·
            refine ⟨28793851045595165569588615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 153567205576507549704472613 28793851045595165569588615)
            ·
              refine ⟨43190776568392748354382923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28793851045595165569588615 43190776568392748354382923)
              ·
                refine ⟨64786164852589122531574385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43190776568392748354382923 64786164852589122531574385)
                ·
                  refine ⟨48589623639441841898680789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64786164852589122531574385 48589623639441841898680789)
                  ·
                    refine ⟨1138819304049418169500331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48589623639441841898680789 1138819304049418169500331)
                    ·
                      rfl

theorem cell22_3326764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 7].length) (baseStart_3326764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3326764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3326764 prefixEnd_3326764 := by exact prefixLift 3326764
  have htrace : WordTrace (prefixWord ++ tailWord_3326764) baseStart_3326764 baseEnd_3326764 := by
    simpa [prefixWord, tailWord_3326764, baseEnd_3326764] using wordTrace_append hprefix tailTrace_3326764
  have hstable : (prefixWord ++ tailWord_3326764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3326764).length < 2 ^ (prefixWord ++ tailWord_3326764).sum := by decide
  have hdescent : baseEnd_3326764 < baseStart_3326764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3326764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3326772 : List Nat := [2, 5, 1, 1, 3, 2, 1, 3, 4]
def baseStart_3326772 : Nat := 118140960795 + 3326772 * 2 ^ 59
def prefixEnd_3326772 : Nat := 4983230072969 + 3 ^ 40 * 3326772 * 2
def baseEnd_3326772 : Nat := 379607347537636271766769

theorem tailTrace_3326772 : CollatzResearch.WordTrace tailWord_3326772 prefixEnd_3326772 379607347537636271766769 := by
  unfold tailWord_3326772
  simp only [CollatzResearch.WordTrace]
  refine ⟨60668671551840343134295285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80891562069120457512393713 60668671551840343134295285)
  ·
    refine ⟨5687687957985032168840183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60668671551840343134295285 5687687957985032168840183)
    ·
      refine ⟨8531531936977548253260275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5687687957985032168840183 8531531936977548253260275)
      ·
        refine ⟨12797297905466322379890413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8531531936977548253260275 12797297905466322379890413)
        ·
          refine ⟨4798986714549870892458905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12797297905466322379890413 4798986714549870892458905)
          ·
            refine ⟨3599240035912403169344179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4798986714549870892458905 3599240035912403169344179)
            ·
              refine ⟨5398860053868604754016269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3599240035912403169344179 5398860053868604754016269)
              ·
                refine ⟨2024572520200726782756101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5398860053868604754016269 2024572520200726782756101)
                ·
                  refine ⟨379607347537636271766769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2024572520200726782756101 379607347537636271766769)
                  ·
                    rfl

theorem cell22_3326772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_3326772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3326772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3326772 prefixEnd_3326772 := by exact prefixLift 3326772
  have htrace : WordTrace (prefixWord ++ tailWord_3326772) baseStart_3326772 baseEnd_3326772 := by
    simpa [prefixWord, tailWord_3326772, baseEnd_3326772] using wordTrace_append hprefix tailTrace_3326772
  have hstable : (prefixWord ++ tailWord_3326772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3326772).length < 2 ^ (prefixWord ++ tailWord_3326772).sum := by decide
  have hdescent : baseEnd_3326772 < baseStart_3326772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3326772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3326785 : List Nat := [1, 2, 5, 3, 1, 1, 1, 2, 2, 4]
def baseStart_3326785 : Nat := 118140960795 + 3326785 * 2 ^ 59
def prefixEnd_3326785 : Nat := 4983230072969 + 3 ^ 40 * 3326785 * 2
def baseEnd_3326785 : Nat := 1138826492778581114725267

theorem tailTrace_3326785 : CollatzResearch.WordTrace tailWord_3326785 prefixEnd_3326785 1138826492778581114725267 := by
  unfold tailWord_3326785
  simp only [CollatzResearch.WordTrace]
  refine ⟨121337817252633589488813809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80891878168422392992542539 121337817252633589488813809)
  ·
    refine ⟨91003362939475192116610357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121337817252633589488813809 91003362939475192116610357)
    ·
      refine ⟨8531565275575799260932221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 91003362939475192116610357 8531565275575799260932221)
      ·
        refine ⟨3199336978340924722849583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8531565275575799260932221 3199336978340924722849583)
        ·
          refine ⟨4799005467511387084274375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3199336978340924722849583 4799005467511387084274375)
          ·
            refine ⟨7198508201267080626411563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4799005467511387084274375 7198508201267080626411563)
            ·
              refine ⟨10797762301900620939617345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7198508201267080626411563 10797762301900620939617345)
              ·
                refine ⟨8098321726425465704713009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10797762301900620939617345 8098321726425465704713009)
                ·
                  refine ⟨6073741294819099278534757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8098321726425465704713009 6073741294819099278534757)
                  ·
                    refine ⟨1138826492778581114725267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6073741294819099278534757 1138826492778581114725267)
                    ·
                      rfl

theorem cell22_3326785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_3326785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3326785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3326785 prefixEnd_3326785 := by exact prefixLift 3326785
  have htrace : WordTrace (prefixWord ++ tailWord_3326785) baseStart_3326785 baseEnd_3326785 := by
    simpa [prefixWord, tailWord_3326785, baseEnd_3326785] using wordTrace_append hprefix tailTrace_3326785
  have hstable : (prefixWord ++ tailWord_3326785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3326785).length < 2 ^ (prefixWord ++ tailWord_3326785).sum := by decide
  have hdescent : baseEnd_3326785 < baseStart_3326785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3326785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3326804 : List Nat := [2, 4, 1, 1, 5, 1, 2, 1, 2, 3]
def baseStart_3326804 : Nat := 118140960795 + 3326804 * 2 ^ 59
def prefixEnd_3326804 : Nat := 4983230072969 + 3 ^ 40 * 3326804 * 2
def baseEnd_3326804 : Nat := 1138832996866871398500209

theorem tailTrace_3326804 : CollatzResearch.WordTrace tailWord_3326804 prefixEnd_3326804 1138832996866871398500209 := by
  unfold tailWord_3326804
  simp only [CollatzResearch.WordTrace]
  refine ⟨60669255119782377866877733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80892340159709837155836977 60669255119782377866877733)
  ·
    refine ⟨11375485334959195850039575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60669255119782377866877733 11375485334959195850039575)
    ·
      refine ⟨17063228002438793775059363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11375485334959195850039575 17063228002438793775059363)
      ·
        refine ⟨25594842003658190662589045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17063228002438793775059363 25594842003658190662589045)
        ·
          refine ⟨2399516437842955374617723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25594842003658190662589045 2399516437842955374617723)
          ·
            refine ⟨3599274656764433061926585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2399516437842955374617723 3599274656764433061926585)
            ·
              refine ⟨2699455992573324796444939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3599274656764433061926585 2699455992573324796444939)
              ·
                refine ⟨4049183988859987194667409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2699455992573324796444939 4049183988859987194667409)
                ·
                  refine ⟨3036887991644990396000557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4049183988859987194667409 3036887991644990396000557)
                  ·
                    refine ⟨1138832996866871398500209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3036887991644990396000557 1138832996866871398500209)
                    ·
                      rfl

theorem cell22_3326804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 2, 1, 2, 3].length) (baseStart_3326804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3326804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3326804 prefixEnd_3326804 := by exact prefixLift 3326804
  have htrace : WordTrace (prefixWord ++ tailWord_3326804) baseStart_3326804 baseEnd_3326804 := by
    simpa [prefixWord, tailWord_3326804, baseEnd_3326804] using wordTrace_append hprefix tailTrace_3326804
  have hstable : (prefixWord ++ tailWord_3326804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3326804).length < 2 ^ (prefixWord ++ tailWord_3326804).sum := by decide
  have hdescent : baseEnd_3326804 < baseStart_3326804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3326804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3326858 : List Nat := [3, 1, 2, 4, 1, 1, 1, 2, 3, 4]
def baseStart_3326858 : Nat := 118140960795 + 3326858 * 2 ^ 59
def prefixEnd_3326858 : Nat := 4983230072969 + 3 ^ 40 * 3326858 * 2
def baseEnd_3326858 : Nat := 1138851482170433257650043

theorem tailTrace_3326858 : CollatzResearch.WordTrace tailWord_3326858 prefixEnd_3326858 1138851482170433257650043 := by
  unfold tailWord_3326858
  simp only [CollatzResearch.WordTrace]
  refine ⟨30335119945342280739055307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80893653187579415304147485 30335119945342280739055307)
  ·
    refine ⟨45502679918013421108582961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30335119945342280739055307 45502679918013421108582961)
    ·
      refine ⟨34127009938510065831437221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45502679918013421108582961 34127009938510065831437221)
      ·
        refine ⟨6398814363470637343394479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34127009938510065831437221 6398814363470637343394479)
        ·
          refine ⟨9598221545205956015091719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6398814363470637343394479 9598221545205956015091719)
          ·
            refine ⟨14397332317808934022637579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9598221545205956015091719 14397332317808934022637579)
            ·
              refine ⟨21595998476713401033956369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14397332317808934022637579 21595998476713401033956369)
              ·
                refine ⟨16196998857535050775467277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21595998476713401033956369 16196998857535050775467277)
                ·
                  refine ⟨6073874571575644040800229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16196998857535050775467277 6073874571575644040800229)
                  ·
                    refine ⟨1138851482170433257650043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6073874571575644040800229 1138851482170433257650043)
                    ·
                      rfl

theorem cell22_3326858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 2, 3, 4].length) (baseStart_3326858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3326858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3326858 prefixEnd_3326858 := by exact prefixLift 3326858
  have htrace : WordTrace (prefixWord ++ tailWord_3326858) baseStart_3326858 baseEnd_3326858 := by
    simpa [prefixWord, tailWord_3326858, baseEnd_3326858] using wordTrace_append hprefix tailTrace_3326858
  have hstable : (prefixWord ++ tailWord_3326858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3326858).length < 2 ^ (prefixWord ++ tailWord_3326858).sum := by decide
  have hdescent : baseEnd_3326858 < baseStart_3326858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3326858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3326901 : List Nat := [1, 3, 3, 2, 1, 1, 11]
def baseStart_3326901 : Nat := 118140960795 + 3326901 * 2 ^ 59
def prefixEnd_3326901 : Nat := 4983230072969 + 3 ^ 40 * 3326901 * 2
def baseEnd_3326901 : Nat := 42180229701822054771293

theorem tailTrace_3326901 : CollatzResearch.WordTrace tailWord_3326901 prefixEnd_3326901 42180229701822054771293 := by
  unfold tailWord_3326901
  simp only [CollatzResearch.WordTrace]
  refine ⟨121342048120213341300036557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80894698746808894200024371 121342048120213341300036557)
  ·
    refine ⟨45503268045080002987513709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121342048120213341300036557 45503268045080002987513709)
    ·
      refine ⟨17063725516905001120317641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45503268045080002987513709 17063725516905001120317641)
      ·
        refine ⟨12797794137678750840238231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17063725516905001120317641 12797794137678750840238231)
        ·
          refine ⟨19196691206518126260357347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12797794137678750840238231 19196691206518126260357347)
          ·
            refine ⟨28795036809777189390536021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19196691206518126260357347 28795036809777189390536021)
            ·
              refine ⟨42180229701822054771293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 28795036809777189390536021 42180229701822054771293)
              ·
                rfl

theorem cell22_3326901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 11].length) (baseStart_3326901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3326901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3326901 prefixEnd_3326901 := by exact prefixLift 3326901
  have htrace : WordTrace (prefixWord ++ tailWord_3326901) baseStart_3326901 baseEnd_3326901 := by
    simpa [prefixWord, tailWord_3326901, baseEnd_3326901] using wordTrace_append hprefix tailTrace_3326901
  have hstable : (prefixWord ++ tailWord_3326901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3326901).length < 2 ^ (prefixWord ++ tailWord_3326901).sum := by decide
  have hdescent : baseEnd_3326901 < baseStart_3326901 := by decide
  rcases family_descends (prefixWord ++ tailWord_3326901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3326905 : List Nat := [1, 2, 1, 4, 2, 2, 3, 2, 2, 3]
def baseStart_3326905 : Nat := 118140960795 + 3326905 * 2 ^ 59
def prefixEnd_3326905 : Nat := 4983230072969 + 3 ^ 40 * 3326905 * 2
def baseEnd_3326905 : Nat := 1138867571230940801724899

theorem tailTrace_3326905 : CollatzResearch.WordTrace tailWord_3326905 prefixEnd_3326905 1138867571230940801724899 := by
  unfold tailWord_3326905
  simp only [CollatzResearch.WordTrace]
  refine ⟨121342194012198849983182169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80894796008132566655454779 121342194012198849983182169)
  ·
    refine ⟨91006645509149137487386627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121342194012198849983182169 91006645509149137487386627)
    ·
      refine ⟨136509968263723706231079941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91006645509149137487386627 136509968263723706231079941)
      ·
        refine ⟨25595619049448194918327489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136509968263723706231079941 25595619049448194918327489)
        ·
          refine ⟨19196714287086146188745617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25595619049448194918327489 19196714287086146188745617)
          ·
            refine ⟨14397535715314609641559213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19196714287086146188745617 14397535715314609641559213)
            ·
              refine ⟨5399075893242978615584705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14397535715314609641559213 5399075893242978615584705)
              ·
                refine ⟨4049306919932233961688529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5399075893242978615584705 4049306919932233961688529)
                ·
                  refine ⟨3036980189949175471266397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4049306919932233961688529 3036980189949175471266397)
                  ·
                    refine ⟨1138867571230940801724899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3036980189949175471266397 1138867571230940801724899)
                    ·
                      rfl

theorem cell22_3326905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 2, 2, 3].length) (baseStart_3326905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3326905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3326905 prefixEnd_3326905 := by exact prefixLift 3326905
  have htrace : WordTrace (prefixWord ++ tailWord_3326905) baseStart_3326905 baseEnd_3326905 := by
    simpa [prefixWord, tailWord_3326905, baseEnd_3326905] using wordTrace_append hprefix tailTrace_3326905
  have hstable : (prefixWord ++ tailWord_3326905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3326905).length < 2 ^ (prefixWord ++ tailWord_3326905).sum := by decide
  have hdescent : baseEnd_3326905 < baseStart_3326905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3326905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3327018 : List Nat := [3, 1, 4, 1, 4, 1, 2, 2, 1, 3]
def baseStart_3327018 : Nat := 118140960795 + 3327018 * 2 ^ 59
def prefixEnd_3327018 : Nat := 4983230072969 + 3 ^ 40 * 3327018 * 2
def baseEnd_3327018 : Nat := 1138906253440246173649553

theorem tailTrace_3327018 : CollatzResearch.WordTrace tailWord_3327018 prefixEnd_3327018 1138906253440246173649553 := by
  unfold tailWord_3327018
  simp only [CollatzResearch.WordTrace]
  refine ⟨30336578865197367570511427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80897543640526313521363805 30336578865197367570511427)
  ·
    refine ⟨45504868297796051355767141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30336578865197367570511427 45504868297796051355767141)
    ·
      refine ⟨8532162805836759629206339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45504868297796051355767141 8532162805836759629206339)
      ·
        refine ⟨12798244208755139443809509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8532162805836759629206339 12798244208755139443809509)
        ·
          refine ⟨2399670789141588645714283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12798244208755139443809509 2399670789141588645714283)
          ·
            refine ⟨3599506183712382968571425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2399670789141588645714283 3599506183712382968571425)
            ·
              refine ⟨2699629637784287226428569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3599506183712382968571425 2699629637784287226428569)
              ·
                refine ⟨2024722228338215419821427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2699629637784287226428569 2024722228338215419821427)
                ·
                  refine ⟨3037083342507323129732141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2024722228338215419821427 3037083342507323129732141)
                  ·
                    refine ⟨1138906253440246173649553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3037083342507323129732141 1138906253440246173649553)
                    ·
                      rfl

theorem cell22_3327018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_3327018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3327018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3327018 prefixEnd_3327018 := by exact prefixLift 3327018
  have htrace : WordTrace (prefixWord ++ tailWord_3327018) baseStart_3327018 baseEnd_3327018 := by
    simpa [prefixWord, tailWord_3327018, baseEnd_3327018] using wordTrace_append hprefix tailTrace_3327018
  have hstable : (prefixWord ++ tailWord_3327018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3327018).length < 2 ^ (prefixWord ++ tailWord_3327018).sum := by decide
  have hdescent : baseEnd_3327018 < baseStart_3327018 := by decide
  rcases family_descends (prefixWord ++ tailWord_3327018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3327023 : List Nat := [1, 1, 2, 1, 2, 1, 1, 2, 8, 3]
def baseStart_3327023 : Nat := 118140960795 + 3327023 * 2 ^ 59
def prefixEnd_3327023 : Nat := 4983230072969 + 3 ^ 40 * 3327023 * 2
def baseEnd_3327023 : Nat := 1138907965042427827274537

theorem tailTrace_3327023 : CollatzResearch.WordTrace tailWord_3327023 prefixEnd_3327023 1138907965042427827274537 := by
  unfold tailWord_3327023
  simp only [CollatzResearch.WordTrace]
  refine ⟨121346497825771356135977723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80897665217180904090651815 121346497825771356135977723)
  ·
    refine ⟨182019746738657034203966585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121346497825771356135977723 182019746738657034203966585)
    ·
      refine ⟨136514810053992775652974939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182019746738657034203966585 136514810053992775652974939)
      ·
        refine ⟨204772215080989163479462409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136514810053992775652974939 204772215080989163479462409)
        ·
          refine ⟨153579161310741872609596807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204772215080989163479462409 153579161310741872609596807)
          ·
            refine ⟨230368741966112808914395211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153579161310741872609596807 230368741966112808914395211)
            ·
              refine ⟨345553112949169213371592817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230368741966112808914395211 345553112949169213371592817)
              ·
                refine ⟨259164834711876910028694613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 345553112949169213371592817 259164834711876910028694613)
                ·
                  refine ⟨3037087906779807539398765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 259164834711876910028694613 3037087906779807539398765)
                  ·
                    refine ⟨1138907965042427827274537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3037087906779807539398765 1138907965042427827274537)
                    ·
                      rfl

theorem cell22_3327023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 8, 3].length) (baseStart_3327023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3327023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3327023 prefixEnd_3327023 := by exact prefixLift 3327023
  have htrace : WordTrace (prefixWord ++ tailWord_3327023) baseStart_3327023 baseEnd_3327023 := by
    simpa [prefixWord, tailWord_3327023, baseEnd_3327023] using wordTrace_append hprefix tailTrace_3327023
  have hstable : (prefixWord ++ tailWord_3327023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3327023).length < 2 ^ (prefixWord ++ tailWord_3327023).sum := by decide
  have hdescent : baseEnd_3327023 < baseStart_3327023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3327023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3327025 : List Nat := [1, 2, 2, 3, 1, 2, 3, 4, 4]
def baseStart_3327025 : Nat := 118140960795 + 3327025 * 2 ^ 59
def prefixEnd_3327025 : Nat := 4983230072969 + 3 ^ 40 * 3327025 * 2
def baseEnd_3327025 : Nat := 379636216561100162908177

theorem tailTrace_3327025 : CollatzResearch.WordTrace tailWord_3327025 prefixEnd_3327025 379636216561100162908177 := by
  unfold tailWord_3327025
  simp only [CollatzResearch.WordTrace]
  refine ⟨121346570771764110477550529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80897713847842740318367019 121346570771764110477550529)
  ·
    refine ⟨91009928078823082858162897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121346570771764110477550529 91009928078823082858162897)
    ·
      refine ⟨68257446059117312143622173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91009928078823082858162897 68257446059117312143622173)
      ·
        refine ⟨25596542272168992053858315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68257446059117312143622173 25596542272168992053858315)
        ·
          refine ⟨38394813408253488080787473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25596542272168992053858315 38394813408253488080787473)
          ·
            refine ⟨28796110056190116060590605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38394813408253488080787473 28796110056190116060590605)
            ·
              refine ⟨10798541271071293522721477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28796110056190116060590605 10798541271071293522721477)
              ·
                refine ⟨2024726488325867535510277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10798541271071293522721477 2024726488325867535510277)
                ·
                  refine ⟨379636216561100162908177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2024726488325867535510277 379636216561100162908177)
                  ·
                    rfl

theorem cell22_3327025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 4, 4].length) (baseStart_3327025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3327025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3327025 prefixEnd_3327025 := by exact prefixLift 3327025
  have htrace : WordTrace (prefixWord ++ tailWord_3327025) baseStart_3327025 baseEnd_3327025 := by
    simpa [prefixWord, tailWord_3327025, baseEnd_3327025] using wordTrace_append hprefix tailTrace_3327025
  have hstable : (prefixWord ++ tailWord_3327025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3327025).length < 2 ^ (prefixWord ++ tailWord_3327025).sum := by decide
  have hdescent : baseEnd_3327025 < baseStart_3327025 := by decide
  rcases family_descends (prefixWord ++ tailWord_3327025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3327040 : List Nat := [2, 1, 1, 2, 2, 3, 1, 5, 2, 3]
def baseStart_3327040 : Nat := 118140960795 + 3327040 * 2 ^ 59
def prefixEnd_3327040 : Nat := 4983230072969 + 3 ^ 40 * 3327040 * 2
def baseEnd_3327040 : Nat := 1138913784489845449599485

theorem tailTrace_3327040 : CollatzResearch.WordTrace tailWord_3327040 prefixEnd_3327040 1138913784489845449599485 := by
  unfold tailWord_3327040
  simp only [CollatzResearch.WordTrace]
  refine ⟨60673558933354884019673287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80898078577806512026231049 60673558933354884019673287)
  ·
    refine ⟨91010338400032326029509931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60673558933354884019673287 91010338400032326029509931)
    ·
      refine ⟨136515507600048489044264897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91010338400032326029509931 136515507600048489044264897)
      ·
        refine ⟨102386630700036366783198673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136515507600048489044264897 102386630700036366783198673)
        ·
          refine ⟨76789973025027275087399005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102386630700036366783198673 76789973025027275087399005)
          ·
            refine ⟨28796239884385228157774627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76789973025027275087399005 28796239884385228157774627)
            ·
              refine ⟨43194359826577842236661941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28796239884385228157774627 43194359826577842236661941)
              ·
                refine ⟨4049471233741672709687057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43194359826577842236661941 4049471233741672709687057)
                ·
                  refine ⟨3037103425306254532265293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4049471233741672709687057 3037103425306254532265293)
                  ·
                    refine ⟨1138913784489845449599485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3037103425306254532265293 1138913784489845449599485)
                    ·
                      rfl

theorem cell22_3327040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 5, 2, 3].length) (baseStart_3327040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3327040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3327040 prefixEnd_3327040 := by exact prefixLift 3327040
  have htrace : WordTrace (prefixWord ++ tailWord_3327040) baseStart_3327040 baseEnd_3327040 := by
    simpa [prefixWord, tailWord_3327040, baseEnd_3327040] using wordTrace_append hprefix tailTrace_3327040
  have hstable : (prefixWord ++ tailWord_3327040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3327040).length < 2 ^ (prefixWord ++ tailWord_3327040).sum := by decide
  have hdescent : baseEnd_3327040 < baseStart_3327040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3327040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3327074 : List Nat := [3, 3, 2, 2, 1, 1, 3, 2, 2, 3]
def baseStart_3327074 : Nat := 118140960795 + 3327074 * 2 ^ 59
def prefixEnd_3327074 : Nat := 4983230072969 + 3 ^ 40 * 3327074 * 2
def baseEnd_3327074 : Nat := 1138925423384680694249381

theorem tailTrace_3327074 : CollatzResearch.WordTrace tailWord_3327074 prefixEnd_3327074 1138925423384680694249381 := by
  unfold tailWord_3327074
  simp only [CollatzResearch.WordTrace]
  refine ⟨30337089487146647961521069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80898905299057727897389517 30337089487146647961521069)
  ·
    refine ⟨11376408557679992985570401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30337089487146647961521069 11376408557679992985570401)
    ·
      refine ⟨8532306418259994739177801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11376408557679992985570401 8532306418259994739177801)
      ·
        refine ⟨6399229813694996054383351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8532306418259994739177801 6399229813694996054383351)
        ·
          refine ⟨9598844720542494081575027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6399229813694996054383351 9598844720542494081575027)
          ·
            refine ⟨14398267080813741122362541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9598844720542494081575027 14398267080813741122362541)
            ·
              refine ⟨5399350155305152920885953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14398267080813741122362541 5399350155305152920885953)
              ·
                refine ⟨4049512616478864690664465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5399350155305152920885953 4049512616478864690664465)
                ·
                  refine ⟨3037134462359148517998349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4049512616478864690664465 3037134462359148517998349)
                  ·
                    refine ⟨1138925423384680694249381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3037134462359148517998349 1138925423384680694249381)
                    ·
                      rfl

theorem cell22_3327074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_3327074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3327074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3327074 prefixEnd_3327074 := by exact prefixLift 3327074
  have htrace : WordTrace (prefixWord ++ tailWord_3327074) baseStart_3327074 baseEnd_3327074 := by
    simpa [prefixWord, tailWord_3327074, baseEnd_3327074] using wordTrace_append hprefix tailTrace_3327074
  have hstable : (prefixWord ++ tailWord_3327074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3327074).length < 2 ^ (prefixWord ++ tailWord_3327074).sum := by decide
  have hdescent : baseEnd_3327074 < baseStart_3327074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3327074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3327175 : List Nat := [1, 1, 4, 1, 1, 1, 1, 3, 6, 3]
def baseStart_3327175 : Nat := 118140960795 + 3327175 * 2 ^ 59
def prefixEnd_3327175 : Nat := 4983230072969 + 3 ^ 40 * 3327175 * 2
def baseEnd_3327175 : Nat := 1138959997748750097474071

theorem tailTrace_3327175 : CollatzResearch.WordTrace tailWord_3327175 prefixEnd_3327175 1138959997748750097474071 := by
  unfold tailWord_3327175
  simp only [CollatzResearch.WordTrace]
  refine ⟨121352041721220686095510979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80901361147480457397007319 121352041721220686095510979)
  ·
    refine ⟨182028062581831029143266469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121352041721220686095510979 182028062581831029143266469)
    ·
      refine ⟨34130261734093317964362463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 182028062581831029143266469 34130261734093317964362463)
      ·
        refine ⟨51195392601139976946543695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34130261734093317964362463 51195392601139976946543695)
        ·
          refine ⟨76793088901709965419815543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51195392601139976946543695 76793088901709965419815543)
          ·
            refine ⟨115189633352564948129723315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76793088901709965419815543 115189633352564948129723315)
            ·
              refine ⟨172784450028847422194584973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115189633352564948129723315 172784450028847422194584973)
              ·
                refine ⟨64794168760817783322969365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 172784450028847422194584973 64794168760817783322969365)
                ·
                  refine ⟨3037226660663333593264189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 64794168760817783322969365 3037226660663333593264189)
                  ·
                    refine ⟨1138959997748750097474071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3037226660663333593264189 1138959997748750097474071)
                    ·
                      rfl

theorem cell22_3327175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 6, 3].length) (baseStart_3327175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3327175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3327175 prefixEnd_3327175 := by exact prefixLift 3327175
  have htrace : WordTrace (prefixWord ++ tailWord_3327175) baseStart_3327175 baseEnd_3327175 := by
    simpa [prefixWord, tailWord_3327175, baseEnd_3327175] using wordTrace_append hprefix tailTrace_3327175
  have hstable : (prefixWord ++ tailWord_3327175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3327175).length < 2 ^ (prefixWord ++ tailWord_3327175).sum := by decide
  have hdescent : baseEnd_3327175 < baseStart_3327175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3327175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3327389 : List Nat := [1, 4, 2, 1, 3, 1, 1, 1, 5, 3]
def baseStart_3327389 : Nat := 118140960795 + 3327389 * 2 ^ 59
def prefixEnd_3327389 : Nat := 4983230072969 + 3 ^ 40 * 3327389 * 2
def baseEnd_3327389 : Nat := 1139033254322124872623415

theorem tailTrace_3327389 : CollatzResearch.WordTrace tailWord_3327389 prefixEnd_3327389 1139033254322124872623415 := by
  unfold tailWord_3327389
  simp only [CollatzResearch.WordTrace]
  refine ⟨121359846942445400643801221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80906564628296933762534147 121359846942445400643801221)
  ·
    refine ⟨22754971301708512620712729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121359846942445400643801221 22754971301708512620712729)
    ·
      refine ⟨17066228476281384465534547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22754971301708512620712729 17066228476281384465534547)
      ·
        refine ⟨25599342714422076698301821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17066228476281384465534547 25599342714422076698301821)
        ·
          refine ⟨9599753517908278761863183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25599342714422076698301821 9599753517908278761863183)
          ·
            refine ⟨14399630276862418142794775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9599753517908278761863183 14399630276862418142794775)
            ·
              refine ⟨21599445415293627214192163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14399630276862418142794775 21599445415293627214192163)
              ·
                refine ⟨32399168122940440821288245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21599445415293627214192163 32399168122940440821288245)
                ·
                  refine ⟨3037422011525666326995773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32399168122940440821288245 3037422011525666326995773)
                  ·
                    refine ⟨1139033254322124872623415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3037422011525666326995773 1139033254322124872623415)
                    ·
                      rfl

theorem cell22_3327389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 5, 3].length) (baseStart_3327389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3327389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3327389 prefixEnd_3327389 := by exact prefixLift 3327389
  have htrace : WordTrace (prefixWord ++ tailWord_3327389) baseStart_3327389 baseEnd_3327389 := by
    simpa [prefixWord, tailWord_3327389, baseEnd_3327389] using wordTrace_append hprefix tailTrace_3327389
  have hstable : (prefixWord ++ tailWord_3327389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3327389).length < 2 ^ (prefixWord ++ tailWord_3327389).sum := by decide
  have hdescent : baseEnd_3327389 < baseStart_3327389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3327389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3327436 : List Nat := [2, 2, 1, 4, 2, 2, 3, 1, 5]
def baseStart_3327436 : Nat := 118140960795 + 3327436 * 2 ^ 59
def prefixEnd_3327436 : Nat := 4983230072969 + 3 ^ 40 * 3327436 * 2
def baseEnd_3327436 : Nat := 379683114460877472232757

theorem tailTrace_3327436 : CollatzResearch.WordTrace tailWord_3327436 prefixEnd_3327436 379683114460877472232757 := by
  unfold tailWord_3327436
  simp only [CollatzResearch.WordTrace]
  refine ⟨60680780586637563835381081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80907707448850085113841441 60680780586637563835381081)
  ·
    refine ⟨45510585439978172876535811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60680780586637563835381081 45510585439978172876535811)
    ·
      refine ⟨68265878159967259314803717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45510585439978172876535811 68265878159967259314803717)
      ·
        refine ⟨12799852154993861121525697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68265878159967259314803717 12799852154993861121525697)
        ·
          refine ⟨9599889116245395841144273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12799852154993861121525697 9599889116245395841144273)
          ·
            refine ⟨7199916837184046880858205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9599889116245395841144273 7199916837184046880858205)
            ·
              refine ⟨2699968813944017580321827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7199916837184046880858205 2699968813944017580321827)
              ·
                refine ⟨4049953220916026370482741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2699968813944017580321827 4049953220916026370482741)
                ·
                  refine ⟨379683114460877472232757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4049953220916026370482741 379683114460877472232757)
                  ·
                    rfl

theorem cell22_3327436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 3, 1, 5].length) (baseStart_3327436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3327436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3327436 prefixEnd_3327436 := by exact prefixLift 3327436
  have htrace : WordTrace (prefixWord ++ tailWord_3327436) baseStart_3327436 baseEnd_3327436 := by
    simpa [prefixWord, tailWord_3327436, baseEnd_3327436] using wordTrace_append hprefix tailTrace_3327436
  have hstable : (prefixWord ++ tailWord_3327436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3327436).length < 2 ^ (prefixWord ++ tailWord_3327436).sum := by decide
  have hdescent : baseEnd_3327436 < baseStart_3327436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3327436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3327449 : List Nat := [1, 2, 1, 2, 4, 2, 1, 4, 1, 4]
def baseStart_3327449 : Nat := 118140960795 + 3327449 * 2 ^ 59
def prefixEnd_3327449 : Nat := 4983230072969 + 3 ^ 40 * 3327449 * 2
def baseEnd_3327449 : Nat := 1139053793548304716123231

theorem tailTrace_3327449 : CollatzResearch.WordTrace tailWord_3327449 prefixEnd_3327449 1139053793548304716123231 := by
  unfold tailWord_3327449
  simp only [CollatzResearch.WordTrace]
  refine ⟨121362035322228030890985401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80908023548152020593990267 121362035322228030890985401)
  ·
    refine ⟨91021526491671023168239051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121362035322228030890985401 91021526491671023168239051)
    ·
      refine ⟨136532289737506534752358577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91021526491671023168239051 136532289737506534752358577)
      ·
        refine ⟨102399217303129901064268933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136532289737506534752358577 102399217303129901064268933)
        ·
          refine ⟨19199853244336856449550425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102399217303129901064268933 19199853244336856449550425)
          ·
            refine ⟨14399889933252642337162819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19199853244336856449550425 14399889933252642337162819)
            ·
              refine ⟨21599834899878963505744229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14399889933252642337162819 21599834899878963505744229)
              ·
                refine ⟨4049969043727305657327043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21599834899878963505744229 4049969043727305657327043)
                ·
                  refine ⟨6074953565590958485990565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4049969043727305657327043 6074953565590958485990565)
                  ·
                    refine ⟨1139053793548304716123231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6074953565590958485990565 1139053793548304716123231)
                    ·
                      rfl

theorem cell22_3327449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 4, 1, 4].length) (baseStart_3327449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3327449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3327449 prefixEnd_3327449 := by exact prefixLift 3327449
  have htrace : WordTrace (prefixWord ++ tailWord_3327449) baseStart_3327449 baseEnd_3327449 := by
    simpa [prefixWord, tailWord_3327449, baseEnd_3327449] using wordTrace_append hprefix tailTrace_3327449
  have hstable : (prefixWord ++ tailWord_3327449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3327449).length < 2 ^ (prefixWord ++ tailWord_3327449).sum := by decide
  have hdescent : baseEnd_3327449 < baseStart_3327449 := by decide
  rcases family_descends (prefixWord ++ tailWord_3327449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3327650 : List Nat := [3, 3, 1, 4, 1, 2, 1, 1, 6]
def baseStart_3327650 : Nat := 118140960795 + 3327650 * 2 ^ 59
def prefixEnd_3327650 : Nat := 4983230072969 + 3 ^ 40 * 3327650 * 2
def baseEnd_3327650 : Nat := 379707533318669063949205

theorem tailTrace_3327650 : CollatzResearch.WordTrace tailWord_3327650 prefixEnd_3327650 379707533318669063949205 := by
  unfold tailWord_3327650
  simp only [CollatzResearch.WordTrace]
  refine ⟨30342341598624960554763101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80912910929666561479368269 30342341598624960554763101)
  ·
    refine ⟨11378378099484360208036163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30342341598624960554763101 11378378099484360208036163)
    ·
      refine ⟨17067567149226540312054245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11378378099484360208036163 17067567149226540312054245)
      ·
        refine ⟨3200168840479976308510171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17067567149226540312054245 3200168840479976308510171)
        ·
          refine ⟨4800253260719964462765257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3200168840479976308510171 4800253260719964462765257)
          ·
            refine ⟨3600189945539973347073943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4800253260719964462765257 3600189945539973347073943)
            ·
              refine ⟨5400284918309960020610915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3600189945539973347073943 5400284918309960020610915)
              ·
                refine ⟨8100427377464940030916373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5400284918309960020610915 8100427377464940030916373)
                ·
                  refine ⟨379707533318669063949205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8100427377464940030916373 379707533318669063949205)
                  ·
                    rfl

theorem cell22_3327650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 1, 6].length) (baseStart_3327650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3327650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3327650 prefixEnd_3327650 := by exact prefixLift 3327650
  have htrace : WordTrace (prefixWord ++ tailWord_3327650) baseStart_3327650 baseEnd_3327650 := by
    simpa [prefixWord, tailWord_3327650, baseEnd_3327650] using wordTrace_append hprefix tailTrace_3327650
  have hstable : (prefixWord ++ tailWord_3327650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3327650).length < 2 ^ (prefixWord ++ tailWord_3327650).sum := by decide
  have hdescent : baseEnd_3327650 < baseStart_3327650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3327650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3327661 : List Nat := [1, 5, 2, 1, 1, 1, 4, 7]
def baseStart_3327661 : Nat := 118140960795 + 3327661 * 2 ^ 59
def prefixEnd_3327661 : Nat := 4983230072969 + 3 ^ 40 * 3327661 * 2
def baseEnd_3327661 : Nat := 126569596164534092202509

theorem tailTrace_3327661 : CollatzResearch.WordTrace tailWord_3327661 prefixEnd_3327661 126569596164534092202509 := by
  unfold tailWord_3327661
  simp only [CollatzResearch.WordTrace]
  refine ⟨121369767597459991097702837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80913178398306660731801891 121369767597459991097702837)
  ·
    refine ⟨11378415712261874165409641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 121369767597459991097702837 11378415712261874165409641)
    ·
      refine ⟨8533811784196405624057231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11378415712261874165409641 8533811784196405624057231)
      ·
        refine ⟨12800717676294608436085847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8533811784196405624057231 12800717676294608436085847)
        ·
          refine ⟨19201076514441912654128771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12800717676294608436085847 19201076514441912654128771)
          ·
            refine ⟨28801614771662868981193157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19201076514441912654128771 28801614771662868981193157)
            ·
              refine ⟨5400302769686787933973717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28801614771662868981193157 5400302769686787933973717)
              ·
                refine ⟨126569596164534092202509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5400302769686787933973717 126569596164534092202509)
                ·
                  rfl

theorem cell22_3327661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 7].length) (baseStart_3327661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3327661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3327661 prefixEnd_3327661 := by exact prefixLift 3327661
  have htrace : WordTrace (prefixWord ++ tailWord_3327661) baseStart_3327661 baseEnd_3327661 := by
    simpa [prefixWord, tailWord_3327661, baseEnd_3327661] using wordTrace_append hprefix tailTrace_3327661
  have hstable : (prefixWord ++ tailWord_3327661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3327661).length < 2 ^ (prefixWord ++ tailWord_3327661).sum := by decide
  have hdescent : baseEnd_3327661 < baseStart_3327661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3327661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3327682 : List Nat := [3, 5, 1, 2, 1, 1, 1, 2, 1, 5]
def baseStart_3327682 : Nat := 118140960795 + 3327682 * 2 ^ 59
def prefixEnd_3327682 : Nat := 4983230072969 + 3 ^ 40 * 3327682 * 2
def baseEnd_3327682 : Nat := 1139133554209969775047517

theorem tailTrace_3327682 : CollatzResearch.WordTrace tailWord_3327682 prefixEnd_3327682 1139133554209969775047517 := by
  unfold tailWord_3327682
  simp only [CollatzResearch.WordTrace]
  refine ⟨30342633382595977921054325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80913689020255941122811533 30342633382595977921054325)
  ·
    refine ⟨2844621879618372930098843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30342633382595977921054325 2844621879618372930098843)
    ·
      refine ⟨4266932819427559395148265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2844621879618372930098843 4266932819427559395148265)
      ·
        refine ⟨3200199614570669546361199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4266932819427559395148265 3200199614570669546361199)
        ·
          refine ⟨4800299421856004319541799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3200199614570669546361199 4800299421856004319541799)
          ·
            refine ⟨7200449132784006479312699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4800299421856004319541799 7200449132784006479312699)
            ·
              refine ⟨10800673699176009718969049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7200449132784006479312699 10800673699176009718969049)
              ·
                refine ⟨8100505274382007289226787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10800673699176009718969049 8100505274382007289226787)
                ·
                  refine ⟨12150757911573010933840181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8100505274382007289226787 12150757911573010933840181)
                  ·
                    refine ⟨1139133554209969775047517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12150757911573010933840181 1139133554209969775047517)
                    ·
                      rfl

theorem cell22_3327682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_3327682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3327682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3327682 prefixEnd_3327682 := by exact prefixLift 3327682
  have htrace : WordTrace (prefixWord ++ tailWord_3327682) baseStart_3327682 baseEnd_3327682 := by
    simpa [prefixWord, tailWord_3327682, baseEnd_3327682] using wordTrace_append hprefix tailTrace_3327682
  have hstable : (prefixWord ++ tailWord_3327682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3327682).length < 2 ^ (prefixWord ++ tailWord_3327682).sum := by decide
  have hdescent : baseEnd_3327682 < baseStart_3327682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3327682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3327706 : List Nat := [3, 1, 1, 2, 2, 3, 1, 4, 5]
def baseStart_3327706 : Nat := 118140960795 + 3327706 * 2 ^ 59
def prefixEnd_3327706 : Nat := 4983230072969 + 3 ^ 40 * 3327706 * 2
def baseEnd_3327706 : Nat := 379713923300147237482481

theorem tailTrace_3327706 : CollatzResearch.WordTrace tailWord_3327706 prefixEnd_3327706 379713923300147237482481 := by
  unfold tailWord_3327706
  simp only [CollatzResearch.WordTrace]
  refine ⟨30342852220574240945772743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80914272588197975855393981 30342852220574240945772743)
  ·
    refine ⟨45514278330861361418659115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30342852220574240945772743 45514278330861361418659115)
    ·
      refine ⟨68271417496292042127988673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45514278330861361418659115 68271417496292042127988673)
      ·
        refine ⟨51203563122219031595991505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68271417496292042127988673 51203563122219031595991505)
        ·
          refine ⟨38402672341664273696993629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51203563122219031595991505 38402672341664273696993629)
          ·
            refine ⟨14401002128124102636372611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38402672341664273696993629 14401002128124102636372611)
            ·
              refine ⟨21601503192186153954558917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14401002128124102636372611 21601503192186153954558917)
              ·
                refine ⟨4050281848534903866479797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21601503192186153954558917 4050281848534903866479797)
                ·
                  refine ⟨379713923300147237482481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4050281848534903866479797 379713923300147237482481)
                  ·
                    rfl

theorem cell22_3327706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 4, 5].length) (baseStart_3327706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3327706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3327706 prefixEnd_3327706 := by exact prefixLift 3327706
  have htrace : WordTrace (prefixWord ++ tailWord_3327706) baseStart_3327706 baseEnd_3327706 := by
    simpa [prefixWord, tailWord_3327706, baseEnd_3327706] using wordTrace_append hprefix tailTrace_3327706
  have hstable : (prefixWord ++ tailWord_3327706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3327706).length < 2 ^ (prefixWord ++ tailWord_3327706).sum := by decide
  have hdescent : baseEnd_3327706 < baseStart_3327706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3327706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3327750 : List Nat := [6, 2, 2, 1, 2, 1, 1, 2, 2, 3]
def baseStart_3327750 : Nat := 118140960795 + 3327750 * 2 ^ 59
def prefixEnd_3327750 : Nat := 4983230072969 + 3 ^ 40 * 3327750 * 2
def baseEnd_3327750 : Nat := 1139156831999640264347309

theorem tailTrace_3327750 : CollatzResearch.WordTrace tailWord_3327750 prefixEnd_3327750 1139156831999640264347309 := by
  unfold tailWord_3327750
  simp only [CollatzResearch.WordTrace]
  refine ⟨3792906677941798728052897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 80915342462758372865128469 3792906677941798728052897)
  ·
    refine ⟨2844680008456349046039673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3792906677941798728052897 2844680008456349046039673)
    ·
      refine ⟨2133510006342261784529755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2844680008456349046039673 2133510006342261784529755)
      ·
        refine ⟨3200265009513392676794633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2133510006342261784529755 3200265009513392676794633)
        ·
          refine ⟨2400198757135044507595975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3200265009513392676794633 2400198757135044507595975)
          ·
            refine ⟨3600298135702566761393963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2400198757135044507595975 3600298135702566761393963)
            ·
              refine ⟨5400447203553850142090945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3600298135702566761393963 5400447203553850142090945)
              ·
                refine ⟨4050335402665387606568209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5400447203553850142090945 4050335402665387606568209)
                ·
                  refine ⟨3037751551999040704926157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4050335402665387606568209 3037751551999040704926157)
                  ·
                    refine ⟨1139156831999640264347309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3037751551999040704926157 1139156831999640264347309)
                    ·
                      rfl

theorem cell22_3327750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_3327750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3327750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3327750 prefixEnd_3327750 := by exact prefixLift 3327750
  have htrace : WordTrace (prefixWord ++ tailWord_3327750) baseStart_3327750 baseEnd_3327750 := by
    simpa [prefixWord, tailWord_3327750, baseEnd_3327750] using wordTrace_append hprefix tailTrace_3327750
  have hstable : (prefixWord ++ tailWord_3327750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3327750).length < 2 ^ (prefixWord ++ tailWord_3327750).sum := by decide
  have hdescent : baseEnd_3327750 < baseStart_3327750 := by decide
  rcases family_descends (prefixWord ++ tailWord_3327750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3327768 : List Nat := [2, 1, 2, 3, 1, 1, 4, 4, 4]
def baseStart_3327768 : Nat := 118140960795 + 3327768 * 2 ^ 59
def prefixEnd_3327768 : Nat := 4983230072969 + 3 ^ 40 * 3327768 * 2
def baseEnd_3327768 : Nat := 379720997922498072465751

theorem tailTrace_3327768 : CollatzResearch.WordTrace tailWord_3327768 prefixEnd_3327768 379720997922498072465751 := by
  unfold tailWord_3327768
  simp only [CollatzResearch.WordTrace]
  refine ⟨60686835104036174185923979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80915780138714898914565305 60686835104036174185923979)
  ·
    refine ⟨91030252656054261278885969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60686835104036174185923979 91030252656054261278885969)
    ·
      refine ⟨68272689492040695959164477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91030252656054261278885969 68272689492040695959164477)
      ·
        refine ⟨25602258559515260984686679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68272689492040695959164477 25602258559515260984686679)
        ·
          refine ⟨38403387839272891477030019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25602258559515260984686679 38403387839272891477030019)
          ·
            refine ⟨57605081758909337215545029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38403387839272891477030019 57605081758909337215545029)
            ·
              refine ⟨10800952829795500727914693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57605081758909337215545029 10800952829795500727914693)
              ·
                refine ⟨2025178655586656386484005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10800952829795500727914693 2025178655586656386484005)
                ·
                  refine ⟨379720997922498072465751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2025178655586656386484005 379720997922498072465751)
                  ·
                    rfl

theorem cell22_3327768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 4, 4].length) (baseStart_3327768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3327768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3327768 prefixEnd_3327768 := by exact prefixLift 3327768
  have htrace : WordTrace (prefixWord ++ tailWord_3327768) baseStart_3327768 baseEnd_3327768 := by
    simpa [prefixWord, tailWord_3327768, baseEnd_3327768] using wordTrace_append hprefix tailTrace_3327768
  have hstable : (prefixWord ++ tailWord_3327768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3327768).length < 2 ^ (prefixWord ++ tailWord_3327768).sum := by decide
  have hdescent : baseEnd_3327768 < baseStart_3327768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3327768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3327774 : List Nat := [4, 3, 2, 2, 1, 1, 3, 1, 5]
def baseStart_3327774 : Nat := 118140960795 + 3327774 * 2 ^ 59
def prefixEnd_3327774 : Nat := 4983230072969 + 3 ^ 40 * 3327774 * 2
def baseEnd_3327774 : Nat := 379721682563370733915745

theorem tailTrace_3327774 : CollatzResearch.WordTrace tailWord_3327774 prefixEnd_3327774 379721682563370733915745 := by
  unfold tailWord_3327774
  simp only [CollatzResearch.WordTrace]
  refine ⟨15171736130756326424570797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80915926030700407597710917 15171736130756326424570797)
  ·
    refine ⟨5689401049033622409214049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15171736130756326424570797 5689401049033622409214049)
    ·
      refine ⟨4267050786775216806910537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5689401049033622409214049 4267050786775216806910537)
      ·
        refine ⟨3200288090081412605182903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4267050786775216806910537 3200288090081412605182903)
        ·
          refine ⟨4800432135122118907774355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3200288090081412605182903 4800432135122118907774355)
          ·
            refine ⟨7200648202683178361661533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4800432135122118907774355 7200648202683178361661533)
            ·
              refine ⟨2700243076006191885623075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7200648202683178361661533 2700243076006191885623075)
              ·
                refine ⟨4050364614009287828434613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2700243076006191885623075 4050364614009287828434613)
                ·
                  refine ⟨379721682563370733915745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4050364614009287828434613 379721682563370733915745)
                  ·
                    rfl

theorem cell22_3327774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_3327774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3327774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3327774 prefixEnd_3327774 := by exact prefixLift 3327774
  have htrace : WordTrace (prefixWord ++ tailWord_3327774) baseStart_3327774 baseEnd_3327774 := by
    simpa [prefixWord, tailWord_3327774, baseEnd_3327774] using wordTrace_append hprefix tailTrace_3327774
  have hstable : (prefixWord ++ tailWord_3327774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3327774).length < 2 ^ (prefixWord ++ tailWord_3327774).sum := by decide
  have hdescent : baseEnd_3327774 < baseStart_3327774 := by decide
  rcases family_descends (prefixWord ++ tailWord_3327774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3327781 : List Nat := [1, 3, 1, 2, 3, 2, 1, 2, 1, 6]
def baseStart_3327781 : Nat := 118140960795 + 3327781 * 2 ^ 59
def prefixEnd_3327781 : Nat := 4983230072969 + 3 ^ 40 * 3327781 * 2
def baseEnd_3327781 : Nat := 1139167443933166516822213

theorem tailTrace_3327781 : CollatzResearch.WordTrace tailWord_3327781 prefixEnd_3327781 1139167443933166516822213 := by
  unfold tailWord_3327781
  simp only [CollatzResearch.WordTrace]
  refine ⟨121374144357025251592071197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80916096238016834394714131 121374144357025251592071197)
  ·
    refine ⟨45515304133884469347026699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121374144357025251592071197 45515304133884469347026699)
    ·
      refine ⟨68272956200826704020540049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45515304133884469347026699 68272956200826704020540049)
      ·
        refine ⟨51204717150620028015405037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68272956200826704020540049 51204717150620028015405037)
        ·
          refine ⟨19201768931482510505776889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51204717150620028015405037 19201768931482510505776889)
          ·
            refine ⟨14401326698611882879332667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19201768931482510505776889 14401326698611882879332667)
            ·
              refine ⟨21601990047917824318999001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14401326698611882879332667 21601990047917824318999001)
              ·
                refine ⟨16201492535938368239249251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21601990047917824318999001 16201492535938368239249251)
                ·
                  refine ⟨24302238803907552358873877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16201492535938368239249251 24302238803907552358873877)
                  ·
                    refine ⟨1139167443933166516822213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24302238803907552358873877 1139167443933166516822213)
                    ·
                      rfl

theorem cell22_3327781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 2, 1, 6].length) (baseStart_3327781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3327781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3327781 prefixEnd_3327781 := by exact prefixLift 3327781
  have htrace : WordTrace (prefixWord ++ tailWord_3327781) baseStart_3327781 baseEnd_3327781 := by
    simpa [prefixWord, tailWord_3327781, baseEnd_3327781] using wordTrace_append hprefix tailTrace_3327781
  have hstable : (prefixWord ++ tailWord_3327781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3327781).length < 2 ^ (prefixWord ++ tailWord_3327781).sum := by decide
  have hdescent : baseEnd_3327781 < baseStart_3327781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3327781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3327856 : List Nat := [2, 1, 1, 1, 4, 1, 1, 2, 4, 5]
def baseStart_3327856 : Nat := 118140960795 + 3327856 * 2 ^ 59
def prefixEnd_3327856 : Nat := 4983230072969 + 3 ^ 40 * 3327856 * 2
def baseEnd_3327856 : Nat := 1139193117965891321196983

theorem tailTrace_3327856 : CollatzResearch.WordTrace tailWord_3327856 prefixEnd_3327856 1139193117965891321196983 := by
  unfold tailWord_3327856
  simp only [CollatzResearch.WordTrace]
  refine ⟨60688439915876769700525711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80917919887835692934034281 60688439915876769700525711)
  ·
    refine ⟨91032659873815154550788567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60688439915876769700525711 91032659873815154550788567)
    ·
      refine ⟨136548989810722731826182851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91032659873815154550788567 136548989810722731826182851)
      ·
        refine ⟨204823484716084097739274277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136548989810722731826182851 204823484716084097739274277)
        ·
          refine ⟨38404403384265768326113927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 204823484716084097739274277 38404403384265768326113927)
          ·
            refine ⟨57606605076398652489170891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38404403384265768326113927 57606605076398652489170891)
            ·
              refine ⟨86409907614597978733756337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57606605076398652489170891 86409907614597978733756337)
              ·
                refine ⟨64807430710948484050317253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86409907614597978733756337 64807430710948484050317253)
                ·
                  refine ⟨12151393258302840759434485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64807430710948484050317253 12151393258302840759434485)
                  ·
                    refine ⟨1139193117965891321196983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12151393258302840759434485 1139193117965891321196983)
                    ·
                      rfl

theorem cell22_3327856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 4, 5].length) (baseStart_3327856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3327856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3327856 prefixEnd_3327856 := by exact prefixLift 3327856
  have htrace : WordTrace (prefixWord ++ tailWord_3327856) baseStart_3327856 baseEnd_3327856 := by
    simpa [prefixWord, tailWord_3327856, baseEnd_3327856] using wordTrace_append hprefix tailTrace_3327856
  have hstable : (prefixWord ++ tailWord_3327856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3327856).length < 2 ^ (prefixWord ++ tailWord_3327856).sum := by decide
  have hdescent : baseEnd_3327856 < baseStart_3327856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3327856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3327890 : List Nat := [3, 2, 3, 2, 1, 2, 1, 1, 2, 5]
def baseStart_3327890 : Nat := 118140960795 + 3327890 * 2 ^ 59
def prefixEnd_3327890 : Nat := 4983230072969 + 3 ^ 40 * 3327890 * 2
def baseEnd_3327890 : Nat := 1139204756860726565846879

theorem tailTrace_3327890 : CollatzResearch.WordTrace tailWord_3327890 prefixEnd_3327890 1139204756860726565846879 := by
  unfold tailWord_3327890
  simp only [CollatzResearch.WordTrace]
  refine ⟨30344529978407590801947281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80918746609086908805192749 30344529978407590801947281)
  ·
    refine ⟨22758397483805693101460461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30344529978407590801947281 22758397483805693101460461)
    ·
      refine ⟨8534399056427134913047673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22758397483805693101460461 8534399056427134913047673)
      ·
        refine ⟨6400799292320351184785755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8534399056427134913047673 6400799292320351184785755)
        ·
          refine ⟨9601198938480526777178633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6400799292320351184785755 9601198938480526777178633)
          ·
            refine ⟨7200899203860395082883975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9601198938480526777178633 7200899203860395082883975)
            ·
              refine ⟨10801348805790592624325963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7200899203860395082883975 10801348805790592624325963)
              ·
                refine ⟨16202023208685888936488945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10801348805790592624325963 16202023208685888936488945)
                ·
                  refine ⟨12151517406514416702366709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16202023208685888936488945 12151517406514416702366709)
                  ·
                    refine ⟨1139204756860726565846879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12151517406514416702366709 1139204756860726565846879)
                    ·
                      rfl

theorem cell22_3327890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_3327890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3327890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3327890 prefixEnd_3327890 := by exact prefixLift 3327890
  have htrace : WordTrace (prefixWord ++ tailWord_3327890) baseStart_3327890 baseEnd_3327890 := by
    simpa [prefixWord, tailWord_3327890, baseEnd_3327890] using wordTrace_append hprefix tailTrace_3327890
  have hstable : (prefixWord ++ tailWord_3327890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3327890).length < 2 ^ (prefixWord ++ tailWord_3327890).sum := by decide
  have hdescent : baseEnd_3327890 < baseStart_3327890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3327890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3327965 : List Nat := [1, 4, 3, 1, 3, 1, 1, 8]
def baseStart_3327965 : Nat := 118140960795 + 3327965 * 2 ^ 59
def prefixEnd_3327965 : Nat := 4983230072969 + 3 ^ 40 * 3327965 * 2
def baseEnd_3327965 : Nat := 126581158988161263357961

theorem tailTrace_3327965 : CollatzResearch.WordTrace tailWord_3327965 prefixEnd_3327965 126581158988161263357961 := by
  unfold tailWord_3327965
  simp only [CollatzResearch.WordTrace]
  refine ⟨121380855388358651016769349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80920570258905767344512899 121380855388358651016769349)
  ·
    refine ⟨22758910385317247065644253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121380855388358651016769349 22758910385317247065644253)
    ·
      refine ⟨8534591394493967649616595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22758910385317247065644253 8534591394493967649616595)
      ·
        refine ⟨12801887091740951474424893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8534591394493967649616595 12801887091740951474424893)
        ·
          refine ⟨4800707659402856802909335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12801887091740951474424893 4800707659402856802909335)
          ·
            refine ⟨7201061489104285204364003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4800707659402856802909335 7201061489104285204364003)
            ·
              refine ⟨10801592233656427806546005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7201061489104285204364003 10801592233656427806546005)
              ·
                refine ⟨126581158988161263357961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10801592233656427806546005 126581158988161263357961)
                ·
                  rfl

theorem cell22_3327965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 8].length) (baseStart_3327965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3327965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3327965 prefixEnd_3327965 := by exact prefixLift 3327965
  have htrace : WordTrace (prefixWord ++ tailWord_3327965) baseStart_3327965 baseEnd_3327965 := by
    simpa [prefixWord, tailWord_3327965, baseEnd_3327965] using wordTrace_append hprefix tailTrace_3327965
  have hstable : (prefixWord ++ tailWord_3327965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3327965).length < 2 ^ (prefixWord ++ tailWord_3327965).sum := by decide
  have hdescent : baseEnd_3327965 < baseStart_3327965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3327965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3327993 : List Nat := [1, 2, 1, 3, 1, 4, 2, 1, 7]
def baseStart_3327993 : Nat := 118140960795 + 3327993 * 2 ^ 59
def prefixEnd_3327993 : Nat := 4983230072969 + 3 ^ 40 * 3327993 * 2
def baseEnd_3327993 : Nat := 379746671955222876840521

theorem tailTrace_3327993 : CollatzResearch.WordTrace tailWord_3327993 prefixEnd_3327993 379746671955222876840521 := by
  unfold tailWord_3327993
  simp only [CollatzResearch.WordTrace]
  refine ⟨121381876632257211798788633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80921251088171474532525755 121381876632257211798788633)
  ·
    refine ⟨91036407474192908849091475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121381876632257211798788633 91036407474192908849091475)
    ·
      refine ⟨136554611211289363273637213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91036407474192908849091475 136554611211289363273637213)
      ·
        refine ⟨51207979204233511227613955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136554611211289363273637213 51207979204233511227613955)
        ·
          refine ⟨76811968806350266841420933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51207979204233511227613955 76811968806350266841420933)
          ·
            refine ⟨14402244151190675032766425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76811968806350266841420933 14402244151190675032766425)
            ·
              refine ⟨10801683113393006274574819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14402244151190675032766425 10801683113393006274574819)
              ·
                refine ⟨16202524670089509411862229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10801683113393006274574819 16202524670089509411862229)
                ·
                  refine ⟨379746671955222876840521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16202524670089509411862229 379746671955222876840521)
                  ·
                    rfl

theorem cell22_3327993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 1, 7].length) (baseStart_3327993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3327993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3327993 prefixEnd_3327993 := by exact prefixLift 3327993
  have htrace : WordTrace (prefixWord ++ tailWord_3327993) baseStart_3327993 baseEnd_3327993 := by
    simpa [prefixWord, tailWord_3327993, baseEnd_3327993] using wordTrace_append hprefix tailTrace_3327993
  have hstable : (prefixWord ++ tailWord_3327993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3327993).length < 2 ^ (prefixWord ++ tailWord_3327993).sum := by decide
  have hdescent : baseEnd_3327993 < baseStart_3327993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3327993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3327997 : List Nat := [1, 4, 1, 1, 1, 2, 2, 6, 1, 3]
def baseStart_3327997 : Nat := 118140960795 + 3327997 * 2 ^ 59
def prefixEnd_3327997 : Nat := 4983230072969 + 3 ^ 40 * 3327997 * 2
def baseEnd_3327997 : Nat := 1139241385147413953421551

theorem tailTrace_3327997 : CollatzResearch.WordTrace tailWord_3327997 prefixEnd_3327997 1139241385147413953421551 := by
  unfold tailWord_3327997
  simp only [CollatzResearch.WordTrace]
  refine ⟨121382022524242720481934245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80921348349495146987956163 121382022524242720481934245)
  ·
    refine ⟨22759129223295510090362671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121382022524242720481934245 22759129223295510090362671)
    ·
      refine ⟨34138693834943265135544007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22759129223295510090362671 34138693834943265135544007)
      ·
        refine ⟨51208040752414897703316011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34138693834943265135544007 51208040752414897703316011)
        ·
          refine ⟨76812061128622346554974017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51208040752414897703316011 76812061128622346554974017)
          ·
            refine ⟨57609045846466759916230513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76812061128622346554974017 57609045846466759916230513)
            ·
              refine ⟨43206784384850069937172885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57609045846466759916230513 43206784384850069937172885)
              ·
                refine ⟨2025318018039847028304979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 43206784384850069937172885 2025318018039847028304979)
                ·
                  refine ⟨3037977027059770542457469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2025318018039847028304979 3037977027059770542457469)
                  ·
                    refine ⟨1139241385147413953421551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3037977027059770542457469 1139241385147413953421551)
                    ·
                      rfl

theorem cell22_3327997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 6, 1, 3].length) (baseStart_3327997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3327997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3327997 prefixEnd_3327997 := by exact prefixLift 3327997
  have htrace : WordTrace (prefixWord ++ tailWord_3327997) baseStart_3327997 baseEnd_3327997 := by
    simpa [prefixWord, tailWord_3327997, baseEnd_3327997] using wordTrace_append hprefix tailTrace_3327997
  have hstable : (prefixWord ++ tailWord_3327997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3327997).length < 2 ^ (prefixWord ++ tailWord_3327997).sum := by decide
  have hdescent : baseEnd_3327997 < baseStart_3327997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3327997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3328008 : List Nat := [2, 1, 3, 2, 1, 2, 2, 1, 1, 7]
def baseStart_3328008 : Nat := 118140960795 + 3328008 * 2 ^ 59
def prefixEnd_3328008 : Nat := 4983230072969 + 3 ^ 40 * 3328008 * 2
def baseEnd_3328008 : Nat := 1139245150672213591396517

theorem tailTrace_3328008 : CollatzResearch.WordTrace tailWord_3328008 prefixEnd_3328008 1139245150672213591396517 := by
  unfold tailWord_3328008
  simp only [CollatzResearch.WordTrace]
  refine ⟨60691211863601434680292339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80921615818135246240389785 60691211863601434680292339)
  ·
    refine ⟨91036817795402152020438509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60691211863601434680292339 91036817795402152020438509)
    ·
      refine ⟨34138806673275807007664441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91036817795402152020438509 34138806673275807007664441)
      ·
        refine ⟨25604105004956855255748331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34138806673275807007664441 25604105004956855255748331)
        ·
          refine ⟨38406157507435282883622497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25604105004956855255748331 38406157507435282883622497)
          ·
            refine ⟨28804618130576462162716873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38406157507435282883622497 28804618130576462162716873)
            ·
              refine ⟨21603463597932346622037655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28804618130576462162716873 21603463597932346622037655)
              ·
                refine ⟨32405195396898519933056483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21603463597932346622037655 32405195396898519933056483)
                ·
                  refine ⟨48607793095347779899584725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32405195396898519933056483 48607793095347779899584725)
                  ·
                    refine ⟨1139245150672213591396517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48607793095347779899584725 1139245150672213591396517)
                    ·
                      rfl

theorem cell22_3328008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 1, 7].length) (baseStart_3328008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3328008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3328008 prefixEnd_3328008 := by exact prefixLift 3328008
  have htrace : WordTrace (prefixWord ++ tailWord_3328008) baseStart_3328008 baseEnd_3328008 := by
    simpa [prefixWord, tailWord_3328008, baseEnd_3328008] using wordTrace_append hprefix tailTrace_3328008
  have hstable : (prefixWord ++ tailWord_3328008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3328008).length < 2 ^ (prefixWord ++ tailWord_3328008).sum := by decide
  have hdescent : baseEnd_3328008 < baseStart_3328008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3328008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3328085 : List Nat := [1, 3, 2, 2, 1, 4, 1, 1, 1, 6]
def baseStart_3328085 : Nat := 118140960795 + 3328085 * 2 ^ 59
def prefixEnd_3328085 : Nat := 4983230072969 + 3 ^ 40 * 3328085 * 2
def baseEnd_3328085 : Nat := 1139271509345811057221281

theorem tailTrace_3328085 : CollatzResearch.WordTrace tailWord_3328085 prefixEnd_3328085 1139271509345811057221281 := by
  unfold tailWord_3328085
  simp only [CollatzResearch.WordTrace]
  refine ⟨121385232147923911511137709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80923488098615941007425139 121385232147923911511137709)
  ·
    refine ⟨45519462055471466816676641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121385232147923911511137709 45519462055471466816676641)
    ·
      refine ⟨34139596541603600112507481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45519462055471466816676641 34139596541603600112507481)
      ·
        refine ⟨25604697406202700084380611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34139596541603600112507481 25604697406202700084380611)
        ·
          refine ⟨38407046109304050126570917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25604697406202700084380611 38407046109304050126570917)
          ·
            refine ⟨7201321145494509398732047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38407046109304050126570917 7201321145494509398732047)
            ·
              refine ⟨10801981718241764098098071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7201321145494509398732047 10801981718241764098098071)
              ·
                refine ⟨16202972577362646147147107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10801981718241764098098071 16202972577362646147147107)
                ·
                  refine ⟨24304458866043969220720661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16202972577362646147147107 24304458866043969220720661)
                  ·
                    refine ⟨1139271509345811057221281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24304458866043969220720661 1139271509345811057221281)
                    ·
                      rfl

theorem cell22_3328085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 1, 1, 6].length) (baseStart_3328085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3328085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3328085 prefixEnd_3328085 := by exact prefixLift 3328085
  have htrace : WordTrace (prefixWord ++ tailWord_3328085) baseStart_3328085 baseEnd_3328085 := by
    simpa [prefixWord, tailWord_3328085, baseEnd_3328085] using wordTrace_append hprefix tailTrace_3328085
  have hstable : (prefixWord ++ tailWord_3328085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3328085).length < 2 ^ (prefixWord ++ tailWord_3328085).sum := by decide
  have hdescent : baseEnd_3328085 < baseStart_3328085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3328085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3328132 : List Nat := [2, 3, 2, 1, 2, 1, 1, 4, 3, 3]
def baseStart_3328132 : Nat := 118140960795 + 3328132 * 2 ^ 59
def prefixEnd_3328132 : Nat := 4983230072969 + 3 ^ 40 * 3328132 * 2
def baseEnd_3328132 : Nat := 1139287598406318601296137

theorem tailTrace_3328132 : CollatzResearch.WordTrace tailWord_3328132 prefixEnd_3328132 1139287598406318601296137 := by
  unfold tailWord_3328132
  simp only [CollatzResearch.WordTrace]
  refine ⟨60693473189376819269049325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80924630919169092358732433 60693473189376819269049325)
  ·
    refine ⟨22760052446016307225893497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60693473189376819269049325 22760052446016307225893497)
    ·
      refine ⟨17070039334512230419420123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22760052446016307225893497 17070039334512230419420123)
      ·
        refine ⟨25605059001768345629130185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17070039334512230419420123 25605059001768345629130185)
        ·
          refine ⟨19203794251326259221847639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25605059001768345629130185 19203794251326259221847639)
          ·
            refine ⟨28805691376989388832771459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19203794251326259221847639 28805691376989388832771459)
            ·
              refine ⟨43208537065484083249157189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28805691376989388832771459 43208537065484083249157189)
              ·
                refine ⟨8101600699778265609216973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43208537065484083249157189 8101600699778265609216973)
                ·
                  refine ⟨3038100262416849603456365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8101600699778265609216973 3038100262416849603456365)
                  ·
                    refine ⟨1139287598406318601296137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3038100262416849603456365 1139287598406318601296137)
                    ·
                      rfl

theorem cell22_3328132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 4, 3, 3].length) (baseStart_3328132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3328132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3328132 prefixEnd_3328132 := by exact prefixLift 3328132
  have htrace : WordTrace (prefixWord ++ tailWord_3328132) baseStart_3328132 baseEnd_3328132 := by
    simpa [prefixWord, tailWord_3328132, baseEnd_3328132] using wordTrace_append hprefix tailTrace_3328132
  have hstable : (prefixWord ++ tailWord_3328132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3328132).length < 2 ^ (prefixWord ++ tailWord_3328132).sum := by decide
  have hdescent : baseEnd_3328132 < baseStart_3328132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3328132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3328162 : List Nat := [3, 3, 1, 3, 1, 1, 2, 1, 7]
def baseStart_3328162 : Nat := 118140960795 + 3328162 * 2 ^ 59
def prefixEnd_3328162 : Nat := 4983230072969 + 3 ^ 40 * 3328162 * 2
def baseEnd_3328162 : Nat := 379765956006469507682015

theorem tailTrace_3328162 : CollatzResearch.WordTrace tailWord_3328162 prefixEnd_3328162 379765956006469507682015 := by
  unfold tailWord_3328162
  simp only [CollatzResearch.WordTrace]
  refine ⟨30347010142161238415422685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80925360379096635774460493 30347010142161238415422685)
  ·
    refine ⟨11380128803310464405783507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30347010142161238415422685 11380128803310464405783507)
    ·
      refine ⟨17070193204965696608675261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11380128803310464405783507 17070193204965696608675261)
      ·
        refine ⟨6401322451862136228253223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17070193204965696608675261 6401322451862136228253223)
        ·
          refine ⟨9601983677793204342379835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6401322451862136228253223 9601983677793204342379835)
          ·
            refine ⟨14402975516689806513569753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9601983677793204342379835 14402975516689806513569753)
            ·
              refine ⟨10802231637517354885177315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14402975516689806513569753 10802231637517354885177315)
              ·
                refine ⟨16203347456276032327765973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10802231637517354885177315 16203347456276032327765973)
                ·
                  refine ⟨379765956006469507682015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16203347456276032327765973 379765956006469507682015)
                  ·
                    rfl

theorem cell22_3328162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 1, 7].length) (baseStart_3328162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3328162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3328162 prefixEnd_3328162 := by exact prefixLift 3328162
  have htrace : WordTrace (prefixWord ++ tailWord_3328162) baseStart_3328162 baseEnd_3328162 := by
    simpa [prefixWord, tailWord_3328162, baseEnd_3328162] using wordTrace_append hprefix tailTrace_3328162
  have hstable : (prefixWord ++ tailWord_3328162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3328162).length < 2 ^ (prefixWord ++ tailWord_3328162).sum := by decide
  have hdescent : baseEnd_3328162 < baseStart_3328162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3328162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3328175 : List Nat := [1, 1, 2, 1, 2, 3, 1, 4, 3, 4]
def baseStart_3328175 : Nat := 118140960795 + 3328175 * 2 ^ 59
def prefixEnd_3328175 : Nat := 4983230072969 + 3 ^ 40 * 3328175 * 2
def baseEnd_3328175 : Nat := 1139302318185080822471005

theorem tailTrace_3328175 : CollatzResearch.WordTrace tailWord_3328175 prefixEnd_3328175 1139302318185080822471005 := by
  unfold tailWord_3328175
  simp only [CollatzResearch.WordTrace]
  refine ⟨121388514717597856881913979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80925676478398571254609319 121388514717597856881913979)
  ·
    refine ⟨182082772076396785322870969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121388514717597856881913979 182082772076396785322870969)
    ·
      refine ⟨136562079057297588992153227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182082772076396785322870969 136562079057297588992153227)
      ·
        refine ⟨204843118585946383488229841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136562079057297588992153227 204843118585946383488229841)
        ·
          refine ⟨153632338939459787616172381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204843118585946383488229841 153632338939459787616172381)
          ·
            refine ⟨57612127102297420356064643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153632338939459787616172381 57612127102297420356064643)
            ·
              refine ⟨86418190653446130534096965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57612127102297420356064643 86418190653446130534096965)
              ·
                refine ⟨16203410747521149475143181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86418190653446130534096965 16203410747521149475143181)
                ·
                  refine ⟨6076279030320431053178693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16203410747521149475143181 6076279030320431053178693)
                  ·
                    refine ⟨1139302318185080822471005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6076279030320431053178693 1139302318185080822471005)
                    ·
                      rfl

theorem cell22_3328175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 4, 3, 4].length) (baseStart_3328175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3328175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3328175 prefixEnd_3328175 := by exact prefixLift 3328175
  have htrace : WordTrace (prefixWord ++ tailWord_3328175) baseStart_3328175 baseEnd_3328175 := by
    simpa [prefixWord, tailWord_3328175, baseEnd_3328175] using wordTrace_append hprefix tailTrace_3328175
  have hstable : (prefixWord ++ tailWord_3328175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3328175).length < 2 ^ (prefixWord ++ tailWord_3328175).sum := by decide
  have hdescent : baseEnd_3328175 < baseStart_3328175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3328175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3328192 : List Nat := [2, 1, 1, 2, 5, 2, 1, 1, 3, 4]
def baseStart_3328192 : Nat := 118140960795 + 3328192 * 2 ^ 59
def prefixEnd_3328192 : Nat := 4983230072969 + 3 ^ 40 * 3328192 * 2
def baseEnd_3328192 : Nat := 1139308137632498444795953

theorem tailTrace_3328192 : CollatzResearch.WordTrace tailWord_3328192 prefixEnd_3328192 1139308137632498444795953 := by
  unfold tailWord_3328192
  simp only [CollatzResearch.WordTrace]
  refine ⟨60694567379268134392641415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80926089839024179190188553 60694567379268134392641415)
  ·
    refine ⟨91041851068902201588962123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60694567379268134392641415 91041851068902201588962123)
    ·
      refine ⟨136562776603353302383443185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91041851068902201588962123 136562776603353302383443185)
      ·
        refine ⟨102422082452514976787582389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136562776603353302383443185 102422082452514976787582389)
        ·
          refine ⟨9602070229923279073835849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 102422082452514976787582389 9602070229923279073835849)
          ·
            refine ⟨7201552672442459305376887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9602070229923279073835849 7201552672442459305376887)
            ·
              refine ⟨10802329008663688958065331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7201552672442459305376887 10802329008663688958065331)
              ·
                refine ⟨16203493512995533437097997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10802329008663688958065331 16203493512995533437097997)
                ·
                  refine ⟨6076310067373325038911749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16203493512995533437097997 6076310067373325038911749)
                  ·
                    refine ⟨1139308137632498444795953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6076310067373325038911749 1139308137632498444795953)
                    ·
                      rfl

theorem cell22_3328192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 1, 3, 4].length) (baseStart_3328192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3328192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3328192 prefixEnd_3328192 := by exact prefixLift 3328192
  have htrace : WordTrace (prefixWord ++ tailWord_3328192) baseStart_3328192 baseEnd_3328192 := by
    simpa [prefixWord, tailWord_3328192, baseEnd_3328192] using wordTrace_append hprefix tailTrace_3328192
  have hstable : (prefixWord ++ tailWord_3328192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3328192).length < 2 ^ (prefixWord ++ tailWord_3328192).sum := by decide
  have hdescent : baseEnd_3328192 < baseStart_3328192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3328192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3328207 : List Nat := [1, 1, 2, 1, 1, 3, 4, 5, 4]
def baseStart_3328207 : Nat := 118140960795 + 3328207 * 2 ^ 59
def prefixEnd_3328207 : Nat := 4983230072969 + 3 ^ 40 * 3328207 * 2
def baseEnd_3328207 : Nat := 379771090813014468556969

theorem tailTrace_3328207 : CollatzResearch.WordTrace tailWord_3328207 prefixEnd_3328207 379771090813014468556969 := by
  unfold tailWord_3328207
  simp only [CollatzResearch.WordTrace]
  refine ⟨121389681853481926347078875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80926454568987950898052583 121389681853481926347078875)
  ·
    refine ⟨182084522780222889520618313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121389681853481926347078875 182084522780222889520618313)
    ·
      refine ⟨136563392085167167140463735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182084522780222889520618313 136563392085167167140463735)
      ·
        refine ⟨204845088127750750710695603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136563392085167167140463735 204845088127750750710695603)
        ·
          refine ⟨307267632191626126066043405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204845088127750750710695603 307267632191626126066043405)
          ·
            refine ⟨115225362071859797274766277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 307267632191626126066043405 115225362071859797274766277)
            ·
              refine ⟨21604755388473711989018677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115225362071859797274766277 21604755388473711989018677)
              ·
                refine ⟨2025445817669410498970501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21604755388473711989018677 2025445817669410498970501)
                ·
                  refine ⟨379771090813014468556969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2025445817669410498970501 379771090813014468556969)
                  ·
                    rfl

theorem cell22_3328207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 5, 4].length) (baseStart_3328207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3328207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3328207 prefixEnd_3328207 := by exact prefixLift 3328207
  have htrace : WordTrace (prefixWord ++ tailWord_3328207) baseStart_3328207 baseEnd_3328207 := by
    simpa [prefixWord, tailWord_3328207, baseEnd_3328207] using wordTrace_append hprefix tailTrace_3328207
  have hstable : (prefixWord ++ tailWord_3328207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3328207).length < 2 ^ (prefixWord ++ tailWord_3328207).sum := by decide
  have hdescent : baseEnd_3328207 < baseStart_3328207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3328207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3328239 : List Nat := [1, 1, 2, 1, 6, 1, 2, 3, 2, 3]
def baseStart_3328239 : Nat := 118140960795 + 3328239 * 2 ^ 59
def prefixEnd_3328239 : Nat := 4983230072969 + 3 ^ 40 * 3328239 * 2
def baseEnd_3328239 : Nat := 1139324226693005988870809

theorem tailTrace_3328239 : CollatzResearch.WordTrace tailWord_3328239 prefixEnd_3328239 1139324226693005988870809 := by
  unfold tailWord_3328239
  simp only [CollatzResearch.WordTrace]
  refine ⟨121390848989365995812243771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80927232659577330541495847 121390848989365995812243771)
  ·
    refine ⟨182086273484048993718365657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121390848989365995812243771 182086273484048993718365657)
    ·
      refine ⟨136564705113036745288774243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182086273484048993718365657 136564705113036745288774243)
      ·
        refine ⟨204847057669555117933161365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136564705113036745288774243 204847057669555117933161365)
        ·
          refine ⟨9602205828260396153116939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 204847057669555117933161365 9602205828260396153116939)
          ·
            refine ⟨14403308742390594229675409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9602205828260396153116939 14403308742390594229675409)
            ·
              refine ⟨10802481556792945672256557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14403308742390594229675409 10802481556792945672256557)
              ·
                refine ⟨4050930583797354627096209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10802481556792945672256557 4050930583797354627096209)
                ·
                  refine ⟨3038197937848015970322157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4050930583797354627096209 3038197937848015970322157)
                  ·
                    refine ⟨1139324226693005988870809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3038197937848015970322157 1139324226693005988870809)
                    ·
                      rfl

theorem cell22_3328239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 3, 2, 3].length) (baseStart_3328239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3328239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3328239 prefixEnd_3328239 := by exact prefixLift 3328239
  have htrace : WordTrace (prefixWord ++ tailWord_3328239) baseStart_3328239 baseEnd_3328239 := by
    simpa [prefixWord, tailWord_3328239, baseEnd_3328239] using wordTrace_append hprefix tailTrace_3328239
  have hstable : (prefixWord ++ tailWord_3328239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3328239).length < 2 ^ (prefixWord ++ tailWord_3328239).sum := by decide
  have hdescent : baseEnd_3328239 < baseStart_3328239 := by decide
  rcases family_descends (prefixWord ++ tailWord_3328239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3328267 : List Nat := [1, 1, 1, 1, 5, 2, 1, 2, 5, 3]
def baseStart_3328267 : Nat := 118140960795 + 3328267 * 2 ^ 59
def prefixEnd_3328267 : Nat := 4983230072969 + 3 ^ 40 * 3328267 * 2
def baseEnd_3328267 : Nat := 1139333811665223249170723

theorem tailTrace_3328267 : CollatzResearch.WordTrace tailWord_3328267 prefixEnd_3328267 1139333811665223249170723 := by
  unfold tailWord_3328267
  simp only [CollatzResearch.WordTrace]
  refine ⟨121391870233264556594263055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80927913488843037729508703 121391870233264556594263055)
  ·
    refine ⟨182087805349896834891394583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121391870233264556594263055 182087805349896834891394583)
    ·
      refine ⟨273131708024845252337091875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182087805349896834891394583 273131708024845252337091875)
      ·
        refine ⟨409697562037267878505637813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273131708024845252337091875 409697562037267878505637813)
        ·
          refine ⟨38409146440993863609903545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 409697562037267878505637813 38409146440993863609903545)
          ·
            refine ⟨28806859830745397707427659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38409146440993863609903545 28806859830745397707427659)
            ·
              refine ⟨43210289746118096561141489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28806859830745397707427659 43210289746118096561141489)
              ·
                refine ⟨32407717309588572420856117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43210289746118096561141489 32407717309588572420856117)
                ·
                  refine ⟨3038223497773928664455261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32407717309588572420856117 3038223497773928664455261)
                  ·
                    refine ⟨1139333811665223249170723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3038223497773928664455261 1139333811665223249170723)
                    ·
                      rfl

theorem cell22_3328267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 5, 3].length) (baseStart_3328267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3328267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3328267 prefixEnd_3328267 := by exact prefixLift 3328267
  have htrace : WordTrace (prefixWord ++ tailWord_3328267) baseStart_3328267 baseEnd_3328267 := by
    simpa [prefixWord, tailWord_3328267, baseEnd_3328267] using wordTrace_append hprefix tailTrace_3328267
  have hstable : (prefixWord ++ tailWord_3328267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3328267).length < 2 ^ (prefixWord ++ tailWord_3328267).sum := by decide
  have hdescent : baseEnd_3328267 < baseStart_3328267 := by decide
  rcases family_descends (prefixWord ++ tailWord_3328267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3328318 : List Nat := [4, 2, 1, 2, 1, 2, 3, 3, 1, 3]
def baseStart_3328318 : Nat := 118140960795 + 3328318 * 2 ^ 59
def prefixEnd_3328318 : Nat := 4983230072969 + 3 ^ 40 * 3328318 * 2
def baseEnd_3328318 : Nat := 1139351270007476116145567

theorem tailTrace_3328318 : CollatzResearch.WordTrace tailWord_3328318 prefixEnd_3328318 1139351270007476116145567 := by
  unfold tailWord_3328318
  simp only [CollatzResearch.WordTrace]
  refine ⟨15174216294509974038046201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80929153570719861536246405 15174216294509974038046201)
  ·
    refine ⟨11380662220882480528534651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15174216294509974038046201 11380662220882480528534651)
    ·
      refine ⟨17070993331323720792801977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11380662220882480528534651 17070993331323720792801977)
      ·
        refine ⟨12803244998492790594601483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17070993331323720792801977 12803244998492790594601483)
        ·
          refine ⟨19204867497739185891902225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12803244998492790594601483 19204867497739185891902225)
          ·
            refine ⟨14403650623304389418926669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19204867497739185891902225 14403650623304389418926669)
            ·
              refine ⟨5401368983739146032097501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14403650623304389418926669 5401368983739146032097501)
              ·
                refine ⟨2025513368902179762036563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5401368983739146032097501 2025513368902179762036563)
                ·
                  refine ⟨3038270053353269643054845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2025513368902179762036563 3038270053353269643054845)
                  ·
                    refine ⟨1139351270007476116145567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3038270053353269643054845 1139351270007476116145567)
                    ·
                      rfl

theorem cell22_3328318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 3, 1, 3].length) (baseStart_3328318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3328318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3328318 prefixEnd_3328318 := by exact prefixLift 3328318
  have htrace : WordTrace (prefixWord ++ tailWord_3328318) baseStart_3328318 baseEnd_3328318 := by
    simpa [prefixWord, tailWord_3328318, baseEnd_3328318] using wordTrace_append hprefix tailTrace_3328318
  have hstable : (prefixWord ++ tailWord_3328318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3328318).length < 2 ^ (prefixWord ++ tailWord_3328318).sum := by decide
  have hdescent : baseEnd_3328318 < baseStart_3328318 := by decide
  rcases family_descends (prefixWord ++ tailWord_3328318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3328387 : List Nat := [1, 1, 1, 3, 6, 10]
def baseStart_3328387 : Nat := 118140960795 + 3328387 * 2 ^ 59
def prefixEnd_3328387 : Nat := 4983230072969 + 3 ^ 40 * 3328387 * 2
def baseEnd_3328387 : Nat := 14066356668118307853955

theorem tailTrace_3328387 : CollatzResearch.WordTrace tailWord_3328387 prefixEnd_3328387 14066356668118307853955 := by
  unfold tailWord_3328387
  simp only [CollatzResearch.WordTrace]
  refine ⟨121396246992829817088631415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80930831328553211392420943 121396246992829817088631415)
  ·
    refine ⟨182094370489244725632947123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121396246992829817088631415 182094370489244725632947123)
    ·
      refine ⟨273141555733867088449420685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182094370489244725632947123 273141555733867088449420685)
      ·
        refine ⟨102428083400200158168532757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 273141555733867088449420685 102428083400200158168532757)
        ·
          refine ⟨4801316409384382414149973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 102428083400200158168532757 4801316409384382414149973)
          ·
            refine ⟨14066356668118307853955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4801316409384382414149973 14066356668118307853955)
            ·
              rfl

theorem cell22_3328387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 10].length) (baseStart_3328387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3328387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3328387 prefixEnd_3328387 := by exact prefixLift 3328387
  have htrace : WordTrace (prefixWord ++ tailWord_3328387) baseStart_3328387 baseEnd_3328387 := by
    simpa [prefixWord, tailWord_3328387, baseEnd_3328387] using wordTrace_append hprefix tailTrace_3328387
  have hstable : (prefixWord ++ tailWord_3328387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3328387).length < 2 ^ (prefixWord ++ tailWord_3328387).sum := by decide
  have hdescent : baseEnd_3328387 < baseStart_3328387 := by decide
  rcases family_descends (prefixWord ++ tailWord_3328387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3328391 : List Nat := [1, 1, 4, 2, 2, 1, 4, 2, 2, 3]
def baseStart_3328391 : Nat := 118140960795 + 3328391 * 2 ^ 59
def prefixEnd_3328391 : Nat := 4983230072969 + 3 ^ 40 * 3328391 * 2
def baseEnd_3328391 : Nat := 1139376259399328259070343

theorem tailTrace_3328391 : CollatzResearch.WordTrace tailWord_3328391 prefixEnd_3328391 1139376259399328259070343 := by
  unfold tailWord_3328391
  simp only [CollatzResearch.WordTrace]
  refine ⟨121396392884815325771777027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80930928589876883847851351 121396392884815325771777027)
  ·
    refine ⟨182094589327222988657665541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121396392884815325771777027 182094589327222988657665541)
    ·
      refine ⟨34142735498854310373312289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 182094589327222988657665541 34142735498854310373312289)
      ·
        refine ⟨25607051624140732779984217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34142735498854310373312289 25607051624140732779984217)
        ·
          refine ⟨19205288718105549584988163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25607051624140732779984217 19205288718105549584988163)
          ·
            refine ⟨28807933077158324377482245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19205288718105549584988163 28807933077158324377482245)
            ·
              refine ⟨5401487451967185820777921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28807933077158324377482245 5401487451967185820777921)
              ·
                refine ⟨4051115588975389365583441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5401487451967185820777921 4051115588975389365583441)
                ·
                  refine ⟨3038336691731542024187581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4051115588975389365583441 3038336691731542024187581)
                  ·
                    refine ⟨1139376259399328259070343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3038336691731542024187581 1139376259399328259070343)
                    ·
                      rfl

theorem cell22_3328391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 2, 2, 3].length) (baseStart_3328391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3328391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3328391 prefixEnd_3328391 := by exact prefixLift 3328391
  have htrace : WordTrace (prefixWord ++ tailWord_3328391) baseStart_3328391 baseEnd_3328391 := by
    simpa [prefixWord, tailWord_3328391, baseEnd_3328391] using wordTrace_append hprefix tailTrace_3328391
  have hstable : (prefixWord ++ tailWord_3328391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3328391).length < 2 ^ (prefixWord ++ tailWord_3328391).sum := by decide
  have hdescent : baseEnd_3328391 < baseStart_3328391 := by decide
  rcases family_descends (prefixWord ++ tailWord_3328391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3328393 : List Nat := [1, 2, 1, 1, 6, 3, 2, 2, 4]
def baseStart_3328393 : Nat := 118140960795 + 3328393 * 2 ^ 59
def prefixEnd_3328393 : Nat := 4983230072969 + 3 ^ 40 * 3328393 * 2
def baseEnd_3328393 : Nat := 379792314680066973506779

theorem tailTrace_3328393 : CollatzResearch.WordTrace tailWord_3328393 prefixEnd_3328393 379792314680066973506779 := by
  unfold tailWord_3328393
  simp only [CollatzResearch.WordTrace]
  refine ⟨121396465830808080113349833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80930977220538720075566555 121396465830808080113349833)
  ·
    refine ⟨91047349373106060085012375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121396465830808080113349833 91047349373106060085012375)
    ·
      refine ⟨136571024059659090127518563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91047349373106060085012375 136571024059659090127518563)
      ·
        refine ⟨204856536089488635191277845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136571024059659090127518563 204856536089488635191277845)
        ·
          refine ⟨9602650129194779774591149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 204856536089488635191277845 9602650129194779774591149)
          ·
            refine ⟨3600993798448042415471681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9602650129194779774591149 3600993798448042415471681)
            ·
              refine ⟨2700745348836031811603761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3600993798448042415471681 2700745348836031811603761)
              ·
                refine ⟨2025559011627023858702821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2700745348836031811603761 2025559011627023858702821)
                ·
                  refine ⟨379792314680066973506779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2025559011627023858702821 379792314680066973506779)
                  ·
                    rfl

theorem cell22_3328393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 2, 2, 4].length) (baseStart_3328393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3328393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3328393 prefixEnd_3328393 := by exact prefixLift 3328393
  have htrace : WordTrace (prefixWord ++ tailWord_3328393) baseStart_3328393 baseEnd_3328393 := by
    simpa [prefixWord, tailWord_3328393, baseEnd_3328393] using wordTrace_append hprefix tailTrace_3328393
  have hstable : (prefixWord ++ tailWord_3328393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3328393).length < 2 ^ (prefixWord ++ tailWord_3328393).sum := by decide
  have hdescent : baseEnd_3328393 < baseStart_3328393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3328393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3328419 : List Nat := [1, 1, 1, 4, 1, 4, 1, 1, 5, 3]
def baseStart_3328419 : Nat := 118140960795 + 3328419 * 2 ^ 59
def prefixEnd_3328419 : Nat := 4983230072969 + 3 ^ 40 * 3328419 * 2
def baseEnd_3328419 : Nat := 1139385844371545519370257

theorem tailTrace_3328419 : CollatzResearch.WordTrace tailWord_3328419 prefixEnd_3328419 1139385844371545519370257 := by
  unfold tailWord_3328419
  simp only [CollatzResearch.WordTrace]
  refine ⟨121397414128713886553796311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80931609419142591035864207 121397414128713886553796311)
  ·
    refine ⟨182096121193070829830694467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121397414128713886553796311 182096121193070829830694467)
    ·
      refine ⟨273144181789606244746041701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182096121193070829830694467 273144181789606244746041701)
      ·
        refine ⟨51214534085551170889882819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 273144181789606244746041701 51214534085551170889882819)
        ·
          refine ⟨76821801128326756334824229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51214534085551170889882819 76821801128326756334824229)
          ·
            refine ⟨14404087711561266812779543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76821801128326756334824229 14404087711561266812779543)
            ·
              refine ⟨21606131567341900219169315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14404087711561266812779543 21606131567341900219169315)
              ·
                refine ⟨32409197351012850328753973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21606131567341900219169315 32409197351012850328753973)
                ·
                  refine ⟨3038362251657454718320685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32409197351012850328753973 3038362251657454718320685)
                  ·
                    refine ⟨1139385844371545519370257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3038362251657454718320685 1139385844371545519370257)
                    ·
                      rfl

theorem cell22_3328419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 5, 3].length) (baseStart_3328419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3328419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3328419 prefixEnd_3328419 := by exact prefixLift 3328419
  have htrace : WordTrace (prefixWord ++ tailWord_3328419) baseStart_3328419 baseEnd_3328419 := by
    simpa [prefixWord, tailWord_3328419, baseEnd_3328419] using wordTrace_append hprefix tailTrace_3328419
  have hstable : (prefixWord ++ tailWord_3328419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3328419).length < 2 ^ (prefixWord ++ tailWord_3328419).sum := by decide
  have hdescent : baseEnd_3328419 < baseStart_3328419 := by decide
  rcases family_descends (prefixWord ++ tailWord_3328419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3328541 : List Nat := [1, 4, 2, 2, 1, 2, 1, 3, 2, 4]
def baseStart_3328541 : Nat := 118140960795 + 3328541 * 2 ^ 59
def prefixEnd_3328541 : Nat := 4983230072969 + 3 ^ 40 * 3328541 * 2
def baseEnd_3328541 : Nat := 1139427607464777867819883

theorem tailTrace_3328541 : CollatzResearch.WordTrace tailWord_3328541 prefixEnd_3328541 1139427607464777867819883 := by
  unfold tailWord_3328541
  simp only [CollatzResearch.WordTrace]
  refine ⟨121401863834271901389737477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80934575889514600926491651 121401863834271901389737477)
  ·
    refine ⟨22762849468925981510575777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121401863834271901389737477 22762849468925981510575777)
    ·
      refine ⟨17072137101694486132931833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22762849468925981510575777 17072137101694486132931833)
      ·
        refine ⟨12804102826270864599698875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17072137101694486132931833 12804102826270864599698875)
        ·
          refine ⟨19206154239406296899548313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12804102826270864599698875 19206154239406296899548313)
          ·
            refine ⟨14404615679554722674661235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19206154239406296899548313 14404615679554722674661235)
            ·
              refine ⟨21606923519332084011991853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14404615679554722674661235 21606923519332084011991853)
              ·
                refine ⟨8102596319749531504496945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21606923519332084011991853 8102596319749531504496945)
                ·
                  refine ⟨6076947239812148628372709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8102596319749531504496945 6076947239812148628372709)
                  ·
                    refine ⟨1139427607464777867819883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6076947239812148628372709 1139427607464777867819883)
                    ·
                      rfl

theorem cell22_3328541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_3328541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3328541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3328541 prefixEnd_3328541 := by exact prefixLift 3328541
  have htrace : WordTrace (prefixWord ++ tailWord_3328541) baseStart_3328541 baseEnd_3328541 := by
    simpa [prefixWord, tailWord_3328541, baseEnd_3328541] using wordTrace_append hprefix tailTrace_3328541
  have hstable : (prefixWord ++ tailWord_3328541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3328541).length < 2 ^ (prefixWord ++ tailWord_3328541).sum := by decide
  have hdescent : baseEnd_3328541 < baseStart_3328541 := by decide
  rcases family_descends (prefixWord ++ tailWord_3328541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3328569 : List Nat := [1, 2, 1, 5, 1, 1, 1, 1, 1, 8]
def baseStart_3328569 : Nat := 118140960795 + 3328569 * 2 ^ 59
def prefixEnd_3328569 : Nat := 4983230072969 + 3 ^ 40 * 3328569 * 2
def baseEnd_3328569 : Nat := 1139437192436995128119797

theorem tailTrace_3328569 : CollatzResearch.WordTrace tailWord_3328569 prefixEnd_3328569 1139437192436995128119797 := by
  unfold tailWord_3328569
  simp only [CollatzResearch.WordTrace]
  refine ⟨121402885078170462171756761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80935256718780308114504507 121402885078170462171756761)
  ·
    refine ⟨91052163808627846628817571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121402885078170462171756761 91052163808627846628817571)
    ·
      refine ⟨136578245712941769943226357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91052163808627846628817571 136578245712941769943226357)
      ·
        refine ⟨12804210535588290932177471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 136578245712941769943226357 12804210535588290932177471)
        ·
          refine ⟨19206315803382436398266207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12804210535588290932177471 19206315803382436398266207)
          ·
            refine ⟨28809473705073654597399311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19206315803382436398266207 28809473705073654597399311)
            ·
              refine ⟨43214210557610481896098967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28809473705073654597399311 43214210557610481896098967)
              ·
                refine ⟨64821315836415722844148451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43214210557610481896098967 64821315836415722844148451)
                ·
                  refine ⟨97231973754623584266222677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64821315836415722844148451 97231973754623584266222677)
                  ·
                    refine ⟨1139437192436995128119797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 97231973754623584266222677 1139437192436995128119797)
                    ·
                      rfl

theorem cell22_3328569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 8].length) (baseStart_3328569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3328569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3328569 prefixEnd_3328569 := by exact prefixLift 3328569
  have htrace : WordTrace (prefixWord ++ tailWord_3328569) baseStart_3328569 baseEnd_3328569 := by
    simpa [prefixWord, tailWord_3328569, baseEnd_3328569] using wordTrace_append hprefix tailTrace_3328569
  have hstable : (prefixWord ++ tailWord_3328569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3328569).length < 2 ^ (prefixWord ++ tailWord_3328569).sum := by decide
  have hdescent : baseEnd_3328569 < baseStart_3328569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3328569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3328599 : List Nat := [1, 1, 3, 2, 2, 2, 1, 2, 1, 7]
def baseStart_3328599 : Nat := 118140960795 + 3328599 * 2 ^ 59
def prefixEnd_3328599 : Nat := 4983230072969 + 3 ^ 40 * 3328599 * 2
def baseEnd_3328599 : Nat := 1139447462050085049869705

theorem tailTrace_3328599 : CollatzResearch.WordTrace tailWord_3328599 prefixEnd_3328599 1139447462050085049869705 := by
  unfold tailWord_3328599
  simp only [CollatzResearch.WordTrace]
  refine ⟨121403979268061777295348851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80935986178707851530232567 121403979268061777295348851)
  ·
    refine ⟨182105968902092665943023277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121403979268061777295348851 182105968902092665943023277)
    ·
      refine ⟨68289738338284749728633729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182105968902092665943023277 68289738338284749728633729)
      ·
        refine ⟨51217303753713562296475297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68289738338284749728633729 51217303753713562296475297)
        ·
          refine ⟨38412977815285171722356473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51217303753713562296475297 38412977815285171722356473)
          ·
            refine ⟨28809733361463878791767355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38412977815285171722356473 28809733361463878791767355)
            ·
              refine ⟨43214600042195818187651033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28809733361463878791767355 43214600042195818187651033)
              ·
                refine ⟨32410950031646863640738275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43214600042195818187651033 32410950031646863640738275)
                ·
                  refine ⟨48616425047470295461107413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32410950031646863640738275 48616425047470295461107413)
                  ·
                    refine ⟨1139447462050085049869705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48616425047470295461107413 1139447462050085049869705)
                    ·
                      rfl

theorem cell22_3328599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 7].length) (baseStart_3328599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3328599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3328599 prefixEnd_3328599 := by exact prefixLift 3328599
  have htrace : WordTrace (prefixWord ++ tailWord_3328599) baseStart_3328599 baseEnd_3328599 := by
    simpa [prefixWord, tailWord_3328599, baseEnd_3328599] using wordTrace_append hprefix tailTrace_3328599
  have hstable : (prefixWord ++ tailWord_3328599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3328599).length < 2 ^ (prefixWord ++ tailWord_3328599).sum := by decide
  have hdescent : baseEnd_3328599 < baseStart_3328599 := by decide
  rcases family_descends (prefixWord ++ tailWord_3328599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3328691 : List Nat := [1, 1, 1, 2, 3, 5, 2, 7]
def baseStart_3328691 : Nat := 118140960795 + 3328691 * 2 ^ 59
def prefixEnd_3328691 : Nat := 4983230072969 + 3 ^ 40 * 3328691 * 2
def baseEnd_3328691 : Nat := 126608772836691941841047

theorem tailTrace_3328691 : CollatzResearch.WordTrace tailWord_3328691 prefixEnd_3328691 126608772836691941841047 := by
  unfold tailWord_3328691
  simp only [CollatzResearch.WordTrace]
  refine ⟨121407334783728477007697927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80938223189152318005131951 121407334783728477007697927)
  ·
    refine ⟨182111002175592715511546891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121407334783728477007697927 182111002175592715511546891)
    ·
      refine ⟨273166503263389073267320337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182111002175592715511546891 273166503263389073267320337)
      ·
        refine ⟨204874877447541804950490253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273166503263389073267320337 204874877447541804950490253)
        ·
          refine ⟨76828079042828176856433845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204874877447541804950490253 76828079042828176856433845)
          ·
            refine ⟨7202632410265141580290673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76828079042828176856433845 7202632410265141580290673)
            ·
              refine ⟨5401974307698856185218005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7202632410265141580290673 5401974307698856185218005)
              ·
                refine ⟨126608772836691941841047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5401974307698856185218005 126608772836691941841047)
                ·
                  rfl

theorem cell22_3328691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 7].length) (baseStart_3328691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3328691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3328691 prefixEnd_3328691 := by exact prefixLift 3328691
  have htrace : WordTrace (prefixWord ++ tailWord_3328691) baseStart_3328691 baseEnd_3328691 := by
    simpa [prefixWord, tailWord_3328691, baseEnd_3328691] using wordTrace_append hprefix tailTrace_3328691
  have hstable : (prefixWord ++ tailWord_3328691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3328691).length < 2 ^ (prefixWord ++ tailWord_3328691).sum := by decide
  have hdescent : baseEnd_3328691 < baseStart_3328691 := by decide
  rcases family_descends (prefixWord ++ tailWord_3328691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3328695 : List Nat := [1, 1, 3, 1, 6, 1, 1, 3, 2, 3]
def baseStart_3328695 : Nat := 118140960795 + 3328695 * 2 ^ 59
def prefixEnd_3328695 : Nat := 4983230072969 + 3 ^ 40 * 3328695 * 2
def baseEnd_3328695 : Nat := 1139480324811972799469411

theorem tailTrace_3328695 : CollatzResearch.WordTrace tailWord_3328695 prefixEnd_3328695 1139480324811972799469411 := by
  unfold tailWord_3328695
  simp only [CollatzResearch.WordTrace]
  refine ⟨121407480675713985690843539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80938320450475990460562359 121407480675713985690843539)
  ·
    refine ⟨182111221013570978536265309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121407480675713985690843539 182111221013570978536265309)
    ·
      refine ⟨68291707880089116951099491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182111221013570978536265309 68291707880089116951099491)
      ·
        refine ⟨102437561820133675426649237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68291707880089116951099491 102437561820133675426649237)
        ·
          refine ⟨4801760710318766035624183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 102437561820133675426649237 4801760710318766035624183)
          ·
            refine ⟨7202641065478149053436275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4801760710318766035624183 7202641065478149053436275)
            ·
              refine ⟨10803961598217223580154413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7202641065478149053436275 10803961598217223580154413)
              ·
                refine ⟨4051485599331458842557905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10803961598217223580154413 4051485599331458842557905)
                ·
                  refine ⟨3038614199498594131918429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4051485599331458842557905 3038614199498594131918429)
                  ·
                    refine ⟨1139480324811972799469411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3038614199498594131918429 1139480324811972799469411)
                    ·
                      rfl

theorem cell22_3328695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 3, 2, 3].length) (baseStart_3328695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3328695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3328695 prefixEnd_3328695 := by exact prefixLift 3328695
  have htrace : WordTrace (prefixWord ++ tailWord_3328695) baseStart_3328695 baseEnd_3328695 := by
    simpa [prefixWord, tailWord_3328695, baseEnd_3328695] using wordTrace_append hprefix tailTrace_3328695
  have hstable : (prefixWord ++ tailWord_3328695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3328695).length < 2 ^ (prefixWord ++ tailWord_3328695).sum := by decide
  have hdescent : baseEnd_3328695 < baseStart_3328695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3328695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3328751 : List Nat := [1, 1, 2, 1, 5, 2, 1, 1, 1, 7]
def baseStart_3328751 : Nat := 118140960795 + 3328751 * 2 ^ 59
def prefixEnd_3328751 : Nat := 4983230072969 + 3 ^ 40 * 3328751 * 2
def baseEnd_3328751 : Nat := 1139499494756407320069239

theorem tailTrace_3328751 : CollatzResearch.WordTrace tailWord_3328751 prefixEnd_3328751 1139499494756407320069239 := by
  unfold tailWord_3328751
  simp only [CollatzResearch.WordTrace]
  refine ⟨121409523163511107254882107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80939682109007404836588071 121409523163511107254882107)
  ·
    refine ⟨182114284745266660882323161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121409523163511107254882107 182114284745266660882323161)
    ·
      refine ⟨136585713558949995661742371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182114284745266660882323161 136585713558949995661742371)
      ·
        refine ⟨204878570338424993492613557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136585713558949995661742371 204878570338424993492613557)
        ·
          refine ⟨19207365969227343139932521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 204878570338424993492613557 19207365969227343139932521)
          ·
            refine ⟨14405524476920507354949391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19207365969227343139932521 14405524476920507354949391)
            ·
              refine ⟨21608286715380761032424087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14405524476920507354949391 21608286715380761032424087)
              ·
                refine ⟨32412430073071141548636131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21608286715380761032424087 32412430073071141548636131)
                ·
                  refine ⟨48618645109606712322954197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32412430073071141548636131 48618645109606712322954197)
                  ·
                    refine ⟨1139499494756407320069239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48618645109606712322954197 1139499494756407320069239)
                    ·
                      rfl

theorem cell22_3328751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 7].length) (baseStart_3328751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3328751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3328751 prefixEnd_3328751 := by exact prefixLift 3328751
  have htrace : WordTrace (prefixWord ++ tailWord_3328751) baseStart_3328751 baseEnd_3328751 := by
    simpa [prefixWord, tailWord_3328751, baseEnd_3328751] using wordTrace_append hprefix tailTrace_3328751
  have hstable : (prefixWord ++ tailWord_3328751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3328751).length < 2 ^ (prefixWord ++ tailWord_3328751).sum := by decide
  have hdescent : baseEnd_3328751 < baseStart_3328751 := by decide
  rcases family_descends (prefixWord ++ tailWord_3328751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3328783 : List Nat := [1, 1, 2, 1, 1, 1, 7, 3, 1, 4]
def baseStart_3328783 : Nat := 118140960795 + 3328783 * 2 ^ 59
def prefixEnd_3328783 : Nat := 4983230072969 + 3 ^ 40 * 3328783 * 2
def baseEnd_3328783 : Nat := 1139510449010369903269141

theorem tailTrace_3328783 : CollatzResearch.WordTrace tailWord_3328783 prefixEnd_3328783 1139510449010369903269141 := by
  unfold tailWord_3328783
  simp only [CollatzResearch.WordTrace]
  refine ⟨121410690299395176720047003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80940460199596784480031335 121410690299395176720047003)
  ·
    refine ⟨182116035449092765080070505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121410690299395176720047003 182116035449092765080070505)
    ·
      refine ⟨136587026586819573810052879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182116035449092765080070505 136587026586819573810052879)
      ·
        refine ⟨204880539880229360715079319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136587026586819573810052879 204880539880229360715079319)
        ·
          refine ⟨307320809820344041072618979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204880539880229360715079319 307320809820344041072618979)
          ·
            refine ⟨460981214730516061608928469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307320809820344041072618979 460981214730516061608928469)
            ·
              refine ⟨10804247220246470193959261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 460981214730516061608928469 10804247220246470193959261)
              ·
                refine ⟨4051592707592426322734723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10804247220246470193959261 4051592707592426322734723)
                ·
                  refine ⟨6077389061388639484102085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4051592707592426322734723 6077389061388639484102085)
                  ·
                    refine ⟨1139510449010369903269141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6077389061388639484102085 1139510449010369903269141)
                    ·
                      rfl

theorem cell22_3328783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 3, 1, 4].length) (baseStart_3328783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3328783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3328783 prefixEnd_3328783 := by exact prefixLift 3328783
  have htrace : WordTrace (prefixWord ++ tailWord_3328783) baseStart_3328783 baseEnd_3328783 := by
    simpa [prefixWord, tailWord_3328783, baseEnd_3328783] using wordTrace_append hprefix tailTrace_3328783
  have hstable : (prefixWord ++ tailWord_3328783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3328783).length < 2 ^ (prefixWord ++ tailWord_3328783).sum := by decide
  have hdescent : baseEnd_3328783 < baseStart_3328783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3328783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3328811 : List Nat := [1, 1, 1, 1, 2, 1, 2, 6, 1, 6]
def baseStart_3328811 : Nat := 118140960795 + 3328811 * 2 ^ 59
def prefixEnd_3328811 : Nat := 4983230072969 + 3 ^ 40 * 3328811 * 2
def baseEnd_3328811 : Nat := 1139520033982587163569055

theorem tailTrace_3328811 : CollatzResearch.WordTrace tailWord_3328811 prefixEnd_3328811 1139520033982587163569055 := by
  unfold tailWord_3328811
  simp only [CollatzResearch.WordTrace]
  refine ⟨121411711543293737502066287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80941141028862491668044191 121411711543293737502066287)
  ·
    refine ⟨182117567314940606253099431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121411711543293737502066287 182117567314940606253099431)
    ·
      refine ⟨273176350972410909379649147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182117567314940606253099431 273176350972410909379649147)
      ·
        refine ⟨409764526458616364069473721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273176350972410909379649147 409764526458616364069473721)
        ·
          refine ⟨307323394843962273052105291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 409764526458616364069473721 307323394843962273052105291)
          ·
            refine ⟨460985092265943409578157937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307323394843962273052105291 460985092265943409578157937)
            ·
              refine ⟨345738819199457557183618453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 460985092265943409578157937 345738819199457557183618453)
              ·
                refine ⟨16206507149974572992982115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 345738819199457557183618453 16206507149974572992982115)
                ·
                  refine ⟨24309760724961859489473173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16206507149974572992982115 24309760724961859489473173)
                  ·
                    refine ⟨1139520033982587163569055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24309760724961859489473173 1139520033982587163569055)
                    ·
                      rfl

theorem cell22_3328811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 6, 1, 6].length) (baseStart_3328811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3328811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3328811 prefixEnd_3328811 := by exact prefixLift 3328811
  have htrace : WordTrace (prefixWord ++ tailWord_3328811) baseStart_3328811 baseEnd_3328811 := by
    simpa [prefixWord, tailWord_3328811, baseEnd_3328811] using wordTrace_append hprefix tailTrace_3328811
  have hstable : (prefixWord ++ tailWord_3328811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3328811).length < 2 ^ (prefixWord ++ tailWord_3328811).sum := by decide
  have hdescent : baseEnd_3328811 < baseStart_3328811 := by decide
  rcases family_descends (prefixWord ++ tailWord_3328811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3328828 : List Nat := [2, 2, 2, 2, 1, 1, 1, 5, 2, 4]
def baseStart_3328828 : Nat := 118140960795 + 3328828 * 2 ^ 59
def prefixEnd_3328828 : Nat := 4983230072969 + 3 ^ 40 * 3328828 * 2
def baseEnd_3328828 : Nat := 1139525853430004785894003

theorem tailTrace_3328828 : CollatzResearch.WordTrace tailWord_3328828 prefixEnd_3328828 1139525853430004785894003 := by
  unfold tailWord_3328828
  simp only [CollatzResearch.WordTrace]
  refine ⟨60706165792116074702717569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80941554389488099603623425 60706165792116074702717569)
  ·
    refine ⟨45529624344087056027038177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60706165792116074702717569 45529624344087056027038177)
    ·
      refine ⟨34147218258065292020278633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45529624344087056027038177 34147218258065292020278633)
      ·
        refine ⟨25610413693548969015208975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34147218258065292020278633 25610413693548969015208975)
        ·
          refine ⟨38415620540323453522813463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25610413693548969015208975 38415620540323453522813463)
          ·
            refine ⟨57623430810485180284220195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38415620540323453522813463 57623430810485180284220195)
            ·
              refine ⟨86435146215727770426330293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57623430810485180284220195 86435146215727770426330293)
              ·
                refine ⟨8103294957724478477468465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 86435146215727770426330293 8103294957724478477468465)
                ·
                  refine ⟨6077471218293358858101349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8103294957724478477468465 6077471218293358858101349)
                  ·
                    refine ⟨1139525853430004785894003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6077471218293358858101349 1139525853430004785894003)
                    ·
                      rfl

theorem cell22_3328828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 5, 2, 4].length) (baseStart_3328828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3328828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3328828 prefixEnd_3328828 := by exact prefixLift 3328828
  have htrace : WordTrace (prefixWord ++ tailWord_3328828) baseStart_3328828 baseEnd_3328828 := by
    simpa [prefixWord, tailWord_3328828, baseEnd_3328828] using wordTrace_append hprefix tailTrace_3328828
  have hstable : (prefixWord ++ tailWord_3328828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3328828).length < 2 ^ (prefixWord ++ tailWord_3328828).sum := by decide
  have hdescent : baseEnd_3328828 < baseStart_3328828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3328828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3328860 : List Nat := [2, 2, 4, 2, 1, 2, 2, 7]
def baseStart_3328860 : Nat := 118140960795 + 3328860 * 2 ^ 59
def prefixEnd_3328860 : Nat := 4983230072969 + 3 ^ 40 * 3328860 * 2
def baseEnd_3328860 : Nat := 126615200853774152121545

theorem tailTrace_3328860 : CollatzResearch.WordTrace tailWord_3328860 prefixEnd_3328860 126615200853774152121545 := by
  unfold tailWord_3328860
  simp only [CollatzResearch.WordTrace]
  refine ⟨60706749360058109435300017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80942332480077479247066689 60706749360058109435300017)
  ·
    refine ⟨45530062020043582076475013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60706749360058109435300017 45530062020043582076475013)
    ·
      refine ⟨8536886628758171639339065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45530062020043582076475013 8536886628758171639339065)
      ·
        refine ⟨6402664971568628729504299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8536886628758171639339065 6402664971568628729504299)
        ·
          refine ⟨9603997457352943094256449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6402664971568628729504299 9603997457352943094256449)
          ·
            refine ⟨7202998093014707320692337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9603997457352943094256449 7202998093014707320692337)
            ·
              refine ⟨5402248569761030490519253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7202998093014707320692337 5402248569761030490519253)
              ·
                refine ⟨126615200853774152121545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5402248569761030490519253 126615200853774152121545)
                ·
                  rfl

theorem cell22_3328860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 7].length) (baseStart_3328860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3328860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3328860 prefixEnd_3328860 := by exact prefixLift 3328860
  have htrace : WordTrace (prefixWord ++ tailWord_3328860) baseStart_3328860 baseEnd_3328860 := by
    simpa [prefixWord, tailWord_3328860, baseEnd_3328860] using wordTrace_append hprefix tailTrace_3328860
  have hstable : (prefixWord ++ tailWord_3328860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3328860).length < 2 ^ (prefixWord ++ tailWord_3328860).sum := by decide
  have hdescent : baseEnd_3328860 < baseStart_3328860 := by decide
  rcases family_descends (prefixWord ++ tailWord_3328860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3328905 : List Nat := [1, 2, 1, 1, 5, 3, 2, 2, 5]
def baseStart_3328905 : Nat := 118140960795 + 3328905 * 2 ^ 59
def prefixEnd_3328905 : Nat := 4983230072969 + 3 ^ 40 * 3328905 * 2
def baseEnd_3328905 : Nat := 379850737367867417239589

theorem tailTrace_3328905 : CollatzResearch.WordTrace tailWord_3328905 prefixEnd_3328905 379850737367867417239589 := by
  unfold tailWord_3328905
  simp only [CollatzResearch.WordTrace]
  refine ⟨121415140004953191555988169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80943426669968794370658779 121415140004953191555988169)
  ·
    refine ⟨91061355003714893666991127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121415140004953191555988169 91061355003714893666991127)
    ·
      refine ⟨136592032505572340500486691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91061355003714893666991127 136592032505572340500486691)
      ·
        refine ⟨204888048758358510750730037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136592032505572340500486691 204888048758358510750730037)
        ·
          refine ⟨19208254571096110382880941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 204888048758358510750730037 19208254571096110382880941)
          ·
            refine ⟨7203095464161041393580353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19208254571096110382880941 7203095464161041393580353)
            ·
              refine ⟨5402321598120781045185265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7203095464161041393580353 5402321598120781045185265)
              ·
                refine ⟨4051741198590585783888949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5402321598120781045185265 4051741198590585783888949)
                ·
                  refine ⟨379850737367867417239589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4051741198590585783888949 379850737367867417239589)
                  ·
                    rfl

theorem cell22_3328905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 2, 5].length) (baseStart_3328905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3328905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3328905 prefixEnd_3328905 := by exact prefixLift 3328905
  have htrace : WordTrace (prefixWord ++ tailWord_3328905) baseStart_3328905 baseEnd_3328905 := by
    simpa [prefixWord, tailWord_3328905, baseEnd_3328905] using wordTrace_append hprefix tailTrace_3328905
  have hstable : (prefixWord ++ tailWord_3328905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3328905).length < 2 ^ (prefixWord ++ tailWord_3328905).sum := by decide
  have hdescent : baseEnd_3328905 < baseStart_3328905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3328905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3328952 : List Nat := [2, 1, 2, 1, 2, 4, 4, 1, 1, 4]
def baseStart_3328952 : Nat := 118140960795 + 3328952 * 2 ^ 59
def prefixEnd_3328952 : Nat := 4983230072969 + 3 ^ 40 * 3328952 * 2
def baseEnd_3328952 : Nat := 1139568301164109795793623

theorem tailTrace_3328952 : CollatzResearch.WordTrace tailWord_3328952 prefixEnd_3328952 1139568301164109795793623 := by
  unfold tailWord_3328952
  simp only [CollatzResearch.WordTrace]
  refine ⟨60708427117891459291474555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80944569490521945721966073 60708427117891459291474555)
  ·
    refine ⟨91062640676837188937211833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60708427117891459291474555 91062640676837188937211833)
    ·
      refine ⟨68296980507627891702908875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91062640676837188937211833 68296980507627891702908875)
      ·
        refine ⟨102445470761441837554363313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68296980507627891702908875 102445470761441837554363313)
        ·
          refine ⟨76834103071081378165772485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102445470761441837554363313 76834103071081378165772485)
          ·
            refine ⟨14406394325827758406082341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76834103071081378165772485 14406394325827758406082341)
            ·
              refine ⟨2701198936092704701140439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14406394325827758406082341 2701198936092704701140439)
              ·
                refine ⟨4051798404139057051710659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2701198936092704701140439 4051798404139057051710659)
                ·
                  refine ⟨6077697606208585577565989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4051798404139057051710659 6077697606208585577565989)
                  ·
                    refine ⟨1139568301164109795793623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6077697606208585577565989 1139568301164109795793623)
                    ·
                      rfl

theorem cell22_3328952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 4, 1, 1, 4].length) (baseStart_3328952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3328952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3328952 prefixEnd_3328952 := by exact prefixLift 3328952
  have htrace : WordTrace (prefixWord ++ tailWord_3328952) baseStart_3328952 baseEnd_3328952 := by
    simpa [prefixWord, tailWord_3328952, baseEnd_3328952] using wordTrace_append hprefix tailTrace_3328952
  have hstable : (prefixWord ++ tailWord_3328952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3328952).length < 2 ^ (prefixWord ++ tailWord_3328952).sum := by decide
  have hdescent : baseEnd_3328952 < baseStart_3328952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3328952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3328973 : List Nat := [1, 6, 3, 1, 1, 1, 3, 1, 5]
def baseStart_3328973 : Nat := 118140960795 + 3328973 * 2 ^ 59
def prefixEnd_3328973 : Nat := 4983230072969 + 3 ^ 40 * 3328973 * 2
def baseEnd_3328973 : Nat := 379858496631090913672853

theorem tailTrace_3328973 : CollatzResearch.WordTrace tailWord_3328973 prefixEnd_3328973 379858496631090913672853 := by
  unfold tailWord_3328973
  simp only [CollatzResearch.WordTrace]
  refine ⟨121417620168706839169463573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80945080112471226112975715 121417620168706839169463573)
  ·
    refine ⟨5691450945408133086068605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 121417620168706839169463573 5691450945408133086068605)
    ·
      refine ⟨2134294104528049907275727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5691450945408133086068605 2134294104528049907275727)
      ·
        refine ⟨3201441156792074860913591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2134294104528049907275727 3201441156792074860913591)
        ·
          refine ⟨4802161735188112291370387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3201441156792074860913591 4802161735188112291370387)
          ·
            refine ⟨7203242602782168437055581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4802161735188112291370387 7203242602782168437055581)
            ·
              refine ⟨2701215976043313163895843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7203242602782168437055581 2701215976043313163895843)
              ·
                refine ⟨4051823964064969745843765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2701215976043313163895843 4051823964064969745843765)
                ·
                  refine ⟨379858496631090913672853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4051823964064969745843765 379858496631090913672853)
                  ·
                    rfl

theorem cell22_3328973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_3328973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3328973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3328973 prefixEnd_3328973 := by exact prefixLift 3328973
  have htrace : WordTrace (prefixWord ++ tailWord_3328973) baseStart_3328973 baseEnd_3328973 := by
    simpa [prefixWord, tailWord_3328973, baseEnd_3328973] using wordTrace_append hprefix tailTrace_3328973
  have hstable : (prefixWord ++ tailWord_3328973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3328973).length < 2 ^ (prefixWord ++ tailWord_3328973).sum := by decide
  have hdescent : baseEnd_3328973 < baseStart_3328973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3328973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3328980 : List Nat := [2, 4, 1, 2, 1, 2, 1, 2, 1, 6]
def baseStart_3328980 : Nat := 118140960795 + 3328980 * 2 ^ 59
def prefixEnd_3328980 : Nat := 4983230072969 + 3 ^ 40 * 3328980 * 2
def baseEnd_3328980 : Nat := 1139577886136327056093537

theorem tailTrace_3328980 : CollatzResearch.WordTrace tailWord_3328980 prefixEnd_3328980 1139577886136327056093537 := by
  unfold tailWord_3328980
  simp only [CollatzResearch.WordTrace]
  refine ⟨60708937739840739682484197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80945250319787652909978929 60708937739840739682484197)
  ·
    refine ⟨11382925826220138690465787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60708937739840739682484197 11382925826220138690465787)
    ·
      refine ⟨17074388739330208035698681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11382925826220138690465787 17074388739330208035698681)
      ·
        refine ⟨12805791554497656026774011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17074388739330208035698681 12805791554497656026774011)
        ·
          refine ⟨19208687331746484040161017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12805791554497656026774011 19208687331746484040161017)
          ·
            refine ⟨14406515498809863030120763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19208687331746484040161017 14406515498809863030120763)
            ·
              refine ⟨21609773248214794545181145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14406515498809863030120763 21609773248214794545181145)
              ·
                refine ⟨16207329936161095908885859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21609773248214794545181145 16207329936161095908885859)
                ·
                  refine ⟨24310994904241643863328789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16207329936161095908885859 24310994904241643863328789)
                  ·
                    refine ⟨1139577886136327056093537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24310994904241643863328789 1139577886136327056093537)
                    ·
                      rfl

theorem cell22_3328980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_3328980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3328980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3328980 prefixEnd_3328980 := by exact prefixLift 3328980
  have htrace : WordTrace (prefixWord ++ tailWord_3328980) baseStart_3328980 baseEnd_3328980 := by
    simpa [prefixWord, tailWord_3328980, baseEnd_3328980] using wordTrace_append hprefix tailTrace_3328980
  have hstable : (prefixWord ++ tailWord_3328980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3328980).length < 2 ^ (prefixWord ++ tailWord_3328980).sum := by decide
  have hdescent : baseEnd_3328980 < baseStart_3328980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3328980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3328993 : List Nat := [1, 2, 3, 1, 2, 1, 1, 1, 1, 9]
def baseStart_3328993 : Nat := 118140960795 + 3328993 * 2 ^ 59
def prefixEnd_3328993 : Nat := 4983230072969 + 3 ^ 40 * 3328993 * 2
def baseEnd_3328993 : Nat := 1139582336301999355518497

theorem tailTrace_3328993 : CollatzResearch.WordTrace tailWord_3328993 prefixEnd_3328993 1139582336301999355518497 := by
  unfold tailWord_3328993
  simp only [CollatzResearch.WordTrace]
  refine ⟨121418349628634382585191633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80945566419089588390127755 121418349628634382585191633)
  ·
    refine ⟨91063762221475786938893725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121418349628634382585191633 91063762221475786938893725)
    ·
      refine ⟨34148910833053420102085147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91063762221475786938893725 34148910833053420102085147)
      ·
        refine ⟨51223366249580130153127721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34148910833053420102085147 51223366249580130153127721)
        ·
          refine ⟨38417524687185097614845791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51223366249580130153127721 38417524687185097614845791)
          ·
            refine ⟨57626287030777646422268687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38417524687185097614845791 57626287030777646422268687)
            ·
              refine ⟨86439430546166469633403031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57626287030777646422268687 86439430546166469633403031)
              ·
                refine ⟨129659145819249704450104547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86439430546166469633403031 129659145819249704450104547)
                ·
                  refine ⟨194488718728874556675156821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129659145819249704450104547 194488718728874556675156821)
                  ·
                    refine ⟨1139582336301999355518497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 194488718728874556675156821 1139582336301999355518497)
                    ·
                      rfl

theorem cell22_3328993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 9].length) (baseStart_3328993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3328993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3328993 prefixEnd_3328993 := by exact prefixLift 3328993
  have htrace : WordTrace (prefixWord ++ tailWord_3328993) baseStart_3328993 baseEnd_3328993 := by
    simpa [prefixWord, tailWord_3328993, baseEnd_3328993] using wordTrace_append hprefix tailTrace_3328993
  have hstable : (prefixWord ++ tailWord_3328993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3328993).length < 2 ^ (prefixWord ++ tailWord_3328993).sum := by decide
  have hdescent : baseEnd_3328993 < baseStart_3328993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3328993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329008 : List Nat := [2, 1, 1, 1, 3, 2, 1, 2, 1, 8]
def baseStart_3329008 : Nat := 118140960795 + 3329008 * 2 ^ 59
def prefixEnd_3329008 : Nat := 4983230072969 + 3 ^ 40 * 3329008 * 2
def baseEnd_3329008 : Nat := 1139587471108544316393451

theorem tailTrace_3329008 : CollatzResearch.WordTrace tailWord_3329008 prefixEnd_3329008 1139587471108544316393451 := by
  unfold tailWord_3329008
  simp only [CollatzResearch.WordTrace]
  refine ⟨60709448361790020073493839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80945931149053360097991785 60709448361790020073493839)
  ·
    refine ⟨91064172542685030110240759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60709448361790020073493839 91064172542685030110240759)
    ·
      refine ⟨136596258814027545165361139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91064172542685030110240759 136596258814027545165361139)
      ·
        refine ⟨204894388221041317748041709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136596258814027545165361139 204894388221041317748041709)
        ·
          refine ⟨76835395582890494155515641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204894388221041317748041709 76835395582890494155515641)
          ·
            refine ⟨57626546687167870616636731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76835395582890494155515641 57626546687167870616636731)
            ·
              refine ⟨86439820030751805924955097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57626546687167870616636731 86439820030751805924955097)
              ·
                refine ⟨64829865023063854443716323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86439820030751805924955097 64829865023063854443716323)
                ·
                  refine ⟨97244797534595781665574485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64829865023063854443716323 97244797534595781665574485)
                  ·
                    refine ⟨1139587471108544316393451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 97244797534595781665574485 1139587471108544316393451)
                    ·
                      rfl

theorem cell22_3329008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 1, 8].length) (baseStart_3329008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3329008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3329008 prefixEnd_3329008 := by exact prefixLift 3329008
  have htrace : WordTrace (prefixWord ++ tailWord_3329008) baseStart_3329008 baseEnd_3329008 := by
    simpa [prefixWord, tailWord_3329008, baseEnd_3329008] using wordTrace_append hprefix tailTrace_3329008
  have hstable : (prefixWord ++ tailWord_3329008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329008).length < 2 ^ (prefixWord ++ tailWord_3329008).sum := by decide
  have hdescent : baseEnd_3329008 < baseStart_3329008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329078 : List Nat := [5, 1, 2, 1, 1, 2, 4, 2, 1, 3]
def baseStart_3329078 : Nat := 118140960795 + 3329078 * 2 ^ 59
def prefixEnd_3329078 : Nat := 4983230072969 + 3 ^ 40 * 3329078 * 2
def baseEnd_3329078 : Nat := 1139611433539087467143237

theorem tailTrace_3329078 : CollatzResearch.WordTrace tailWord_3329078 prefixEnd_3329078 1139611433539087467143237 := by
  unfold tailWord_3329078
  simp only [CollatzResearch.WordTrace]
  refine ⟨7588840614582902631377243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80947633222217628068023925 7588840614582902631377243)
  ·
    refine ⟨11383260921874353947065865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7588840614582902631377243 11383260921874353947065865)
    ·
      refine ⟨8537445691405765460299399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11383260921874353947065865 8537445691405765460299399)
      ·
        refine ⟨12806168537108648190449099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8537445691405765460299399 12806168537108648190449099)
        ·
          refine ⟨19209252805662972285673649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12806168537108648190449099 19209252805662972285673649)
          ·
            refine ⟨14406939604247229214255237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19209252805662972285673649 14406939604247229214255237)
            ·
              refine ⟨2701301175796355477672857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14406939604247229214255237 2701301175796355477672857)
              ·
                refine ⟨2025975881847266608254643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2701301175796355477672857 2025975881847266608254643)
                ·
                  refine ⟨3038963822770899912381965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2025975881847266608254643 3038963822770899912381965)
                  ·
                    refine ⟨1139611433539087467143237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3038963822770899912381965 1139611433539087467143237)
                    ·
                      rfl

theorem cell22_3329078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_3329078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3329078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3329078 prefixEnd_3329078 := by exact prefixLift 3329078
  have htrace : WordTrace (prefixWord ++ tailWord_3329078) baseStart_3329078 baseEnd_3329078 := by
    simpa [prefixWord, tailWord_3329078, baseEnd_3329078] using wordTrace_append hprefix tailTrace_3329078
  have hstable : (prefixWord ++ tailWord_3329078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329078).length < 2 ^ (prefixWord ++ tailWord_3329078).sum := by decide
  have hdescent : baseEnd_3329078 < baseStart_3329078 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329134 : List Nat := [4, 1, 2, 2, 1, 3, 1, 1, 4, 3]
def baseStart_3329134 : Nat := 118140960795 + 3329134 * 2 ^ 59
def prefixEnd_3329134 : Nat := 4983230072969 + 3 ^ 40 * 3329134 * 2
def baseEnd_3329134 : Nat := 1139630603483521987743065

theorem tailTrace_3329134 : CollatzResearch.WordTrace tailWord_3329134 prefixEnd_3329134 1139630603483521987743065 := by
  unfold tailWord_3329134
  simp only [CollatzResearch.WordTrace]
  refine ⟨15177936540140445458259307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80948994880749042444049637 15177936540140445458259307)
  ·
    refine ⟨22766904810210668187388961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15177936540140445458259307 22766904810210668187388961)
    ·
      refine ⟨17075178607658001140541721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22766904810210668187388961 17075178607658001140541721)
      ·
        refine ⟨12806383955743500855406291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17075178607658001140541721 12806383955743500855406291)
        ·
          refine ⟨19209575933615251283109437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12806383955743500855406291 19209575933615251283109437)
          ·
            refine ⟨7203590975105719231166039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19209575933615251283109437 7203590975105719231166039)
            ·
              refine ⟨10805386462658578846749059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7203590975105719231166039 10805386462658578846749059)
              ·
                refine ⟨16208079693987868270123589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10805386462658578846749059 16208079693987868270123589)
                ·
                  refine ⟨3039014942622725300648173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16208079693987868270123589 3039014942622725300648173)
                  ·
                    refine ⟨1139630603483521987743065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3039014942622725300648173 1139630603483521987743065)
                    ·
                      rfl

theorem cell22_3329134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 1, 4, 3].length) (baseStart_3329134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3329134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3329134 prefixEnd_3329134 := by exact prefixLift 3329134
  have htrace : WordTrace (prefixWord ++ tailWord_3329134) baseStart_3329134 baseEnd_3329134 := by
    simpa [prefixWord, tailWord_3329134, baseEnd_3329134] using wordTrace_append hprefix tailTrace_3329134
  have hstable : (prefixWord ++ tailWord_3329134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329134).length < 2 ^ (prefixWord ++ tailWord_3329134).sum := by decide
  have hdescent : baseEnd_3329134 < baseStart_3329134 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329209 : List Nat := [1, 2, 1, 4, 1, 3, 4, 1, 5]
def baseStart_3329209 : Nat := 118140960795 + 3329209 * 2 ^ 59
def prefixEnd_3329209 : Nat := 4983230072969 + 3 ^ 40 * 3329209 * 2
def baseEnd_3329209 : Nat := 379885425838748930705945

theorem tailTrace_3329209 : CollatzResearch.WordTrace tailWord_3329209 prefixEnd_3329209 379885425838748930705945 := by
  unfold tailWord_3329209
  simp only [CollatzResearch.WordTrace]
  refine ⟨121426227795851851475054681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80950818530567900983369787 121426227795851851475054681)
  ·
    refine ⟨91069670846888888606291011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121426227795851851475054681 91069670846888888606291011)
    ·
      refine ⟨136604506270333332909436517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91069670846888888606291011 136604506270333332909436517)
      ·
        refine ⟨25613344925687499920519347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136604506270333332909436517 25613344925687499920519347)
        ·
          refine ⟨38420017388531249880779021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25613344925687499920519347 38420017388531249880779021)
          ·
            refine ⟨14407506520699218705292133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38420017388531249880779021 14407506520699218705292133)
            ·
              refine ⟨2701407472631103507242275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14407506520699218705292133 2701407472631103507242275)
              ·
                refine ⟨4052111208946655260863413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2701407472631103507242275 4052111208946655260863413)
                ·
                  refine ⟨379885425838748930705945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4052111208946655260863413 379885425838748930705945)
                  ·
                    rfl

theorem cell22_3329209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 4, 1, 5].length) (baseStart_3329209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3329209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3329209 prefixEnd_3329209 := by exact prefixLift 3329209
  have htrace : WordTrace (prefixWord ++ tailWord_3329209) baseStart_3329209 baseEnd_3329209 := by
    simpa [prefixWord, tailWord_3329209, baseEnd_3329209] using wordTrace_append hprefix tailTrace_3329209
  have hstable : (prefixWord ++ tailWord_3329209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329209).length < 2 ^ (prefixWord ++ tailWord_3329209).sum := by decide
  have hdescent : baseEnd_3329209 < baseStart_3329209 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329284 : List Nat := [2, 3, 2, 2, 2, 2, 1, 1, 1, 6]
def baseStart_3329284 : Nat := 118140960795 + 3329284 * 2 ^ 59
def prefixEnd_3329284 : Nat := 4983230072969 + 3 ^ 40 * 3329284 * 2
def baseEnd_3329284 : Nat := 1139681951548971596492605

theorem tailTrace_3329284 : CollatzResearch.WordTrace tailWord_3329284 prefixEnd_3329284 1139681951548971596492605 := by
  unfold tailWord_3329284
  simp only [CollatzResearch.WordTrace]
  refine ⟨60714481635290069642017453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80952642180386759522689937 60714481635290069642017453)
  ·
    refine ⟨22767930613233776115756545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60714481635290069642017453 22767930613233776115756545)
    ·
      refine ⟨17075947959925332086817409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22767930613233776115756545 17075947959925332086817409)
      ·
        refine ⟨12806960969943999065113057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17075947959925332086817409 12806960969943999065113057)
        ·
          refine ⟨9605220727457999298834793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12806960969943999065113057 9605220727457999298834793)
          ·
            refine ⟨7203915545593499474126095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9605220727457999298834793 7203915545593499474126095)
            ·
              refine ⟨10805873318390249211189143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7203915545593499474126095 10805873318390249211189143)
              ·
                refine ⟨16208809977585373816783715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10805873318390249211189143 16208809977585373816783715)
                ·
                  refine ⟨24313214966378060725175573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16208809977585373816783715 24313214966378060725175573)
                  ·
                    refine ⟨1139681951548971596492605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24313214966378060725175573 1139681951548971596492605)
                    ·
                      rfl

theorem cell22_3329284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_3329284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3329284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3329284 prefixEnd_3329284 := by exact prefixLift 3329284
  have htrace : WordTrace (prefixWord ++ tailWord_3329284) baseStart_3329284 baseEnd_3329284 := by
    simpa [prefixWord, tailWord_3329284, baseEnd_3329284] using wordTrace_append hprefix tailTrace_3329284
  have hstable : (prefixWord ++ tailWord_3329284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329284).length < 2 ^ (prefixWord ++ tailWord_3329284).sum := by decide
  have hdescent : baseEnd_3329284 < baseStart_3329284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329350 : List Nat := [6, 1, 1, 3, 2, 1, 8]
def baseStart_3329350 : Nat := 118140960795 + 3329350 * 2 ^ 59
def prefixEnd_3329350 : Nat := 4983230072969 + 3 ^ 40 * 3329350 * 2
def baseEnd_3329350 : Nat := 42211279433250719420089

theorem tailTrace_3329350 : CollatzResearch.WordTrace tailWord_3329350 prefixEnd_3329350 42211279433250719420089 := by
  unfold tailWord_3329350
  simp only [CollatzResearch.WordTrace]
  refine ⟨3794730327760657267373047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 80954246992227355037291669 3794730327760657267373047)
  ·
    refine ⟨5692095491640985901059571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3794730327760657267373047 5692095491640985901059571)
    ·
      refine ⟨8538143237461478851589357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5692095491640985901059571 8538143237461478851589357)
      ·
        refine ⟨3201803714048054569346009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8538143237461478851589357 3201803714048054569346009)
        ·
          refine ⟨2401352785536040927009507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3201803714048054569346009 2401352785536040927009507)
          ·
            refine ⟨3602029178304061390514261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2401352785536040927009507 3602029178304061390514261)
            ·
              refine ⟨42211279433250719420089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3602029178304061390514261 42211279433250719420089)
              ·
                rfl

theorem cell22_3329350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 8].length) (baseStart_3329350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3329350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3329350 prefixEnd_3329350 := by exact prefixLift 3329350
  have htrace : WordTrace (prefixWord ++ tailWord_3329350) baseStart_3329350 baseEnd_3329350 := by
    simpa [prefixWord, tailWord_3329350, baseEnd_3329350] using wordTrace_append hprefix tailTrace_3329350
  have hstable : (prefixWord ++ tailWord_3329350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329350).length < 2 ^ (prefixWord ++ tailWord_3329350).sum := by decide
  have hdescent : baseEnd_3329350 < baseStart_3329350 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329365 : List Nat := [1, 3, 2, 2, 3, 2, 3, 2, 1, 3]
def baseStart_3329365 : Nat := 118140960795 + 3329365 * 2 ^ 59
def prefixEnd_3329365 : Nat := 4983230072969 + 3 ^ 40 * 3329365 * 2
def baseEnd_3329365 : Nat := 1139709679504314385217357

theorem tailTrace_3329365 : CollatzResearch.WordTrace tailWord_3329365 prefixEnd_3329365 1139709679504314385217357 := by
  unfold tailWord_3329365
  simp only [CollatzResearch.WordTrace]
  refine ⟨121431917583286690117733549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80954611722191126745155699 121431917583286690117733549)
  ·
    refine ⟨45536969093732508794150081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121431917583286690117733549 45536969093732508794150081)
    ·
      refine ⟨34152726820299381595612561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45536969093732508794150081 34152726820299381595612561)
      ·
        refine ⟨25614545115224536196709421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34152726820299381595612561 25614545115224536196709421)
        ·
          refine ⟨9605454418209201073766033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25614545115224536196709421 9605454418209201073766033)
          ·
            refine ⟨7204090813656900805324525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9605454418209201073766033 7204090813656900805324525)
            ·
              refine ⟨2701534055121337801996697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7204090813656900805324525 2701534055121337801996697)
              ·
                refine ⟨2026150541341003351497523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2701534055121337801996697 2026150541341003351497523)
                ·
                  refine ⟨3039225812011505027246285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2026150541341003351497523 3039225812011505027246285)
                  ·
                    refine ⟨1139709679504314385217357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3039225812011505027246285 1139709679504314385217357)
                    ·
                      rfl

theorem cell22_3329365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 3, 2, 1, 3].length) (baseStart_3329365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3329365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3329365 prefixEnd_3329365 := by exact prefixLift 3329365
  have htrace : WordTrace (prefixWord ++ tailWord_3329365) baseStart_3329365 baseEnd_3329365 := by
    simpa [prefixWord, tailWord_3329365, baseEnd_3329365] using wordTrace_append hprefix tailTrace_3329365
  have hstable : (prefixWord ++ tailWord_3329365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329365).length < 2 ^ (prefixWord ++ tailWord_3329365).sum := by decide
  have hdescent : baseEnd_3329365 < baseStart_3329365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329404 : List Nat := [2, 2, 2, 1, 1, 1, 5, 2, 1, 5]
def baseStart_3329404 : Nat := 118140960795 + 3329404 * 2 ^ 59
def prefixEnd_3329404 : Nat := 4983230072969 + 3 ^ 40 * 3329404 * 2
def baseEnd_3329404 : Nat := 1139723030001331283492237

theorem tailTrace_3329404 : CollatzResearch.WordTrace tailWord_3329404 prefixEnd_3329404 1139723030001331283492237 := by
  unfold tailWord_3329404
  simp only [CollatzResearch.WordTrace]
  refine ⟨60716670015072699889201633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80955560020096933185602177 60716670015072699889201633)
  ·
    refine ⟨45537502511304524916901225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60716670015072699889201633 45537502511304524916901225)
    ·
      refine ⟨34153126883478393687675919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45537502511304524916901225 34153126883478393687675919)
      ·
        refine ⟨51229690325217590531513879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34153126883478393687675919 51229690325217590531513879)
        ·
          refine ⟨76844535487826385797270819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51229690325217590531513879 76844535487826385797270819)
          ·
            refine ⟨115266803231739578695906229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76844535487826385797270819 115266803231739578695906229)
            ·
              refine ⟨10806262802975585502741209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 115266803231739578695906229 10806262802975585502741209)
              ·
                refine ⟨8104697102231689127055907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10806262802975585502741209 8104697102231689127055907)
                ·
                  refine ⟨12157045653347533690583861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8104697102231689127055907 12157045653347533690583861)
                  ·
                    refine ⟨1139723030001331283492237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12157045653347533690583861 1139723030001331283492237)
                    ·
                      rfl

theorem cell22_3329404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 2, 1, 5].length) (baseStart_3329404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3329404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3329404 prefixEnd_3329404 := by exact prefixLift 3329404
  have htrace : WordTrace (prefixWord ++ tailWord_3329404) baseStart_3329404 baseEnd_3329404 := by
    simpa [prefixWord, tailWord_3329404, baseEnd_3329404] using wordTrace_append hprefix tailTrace_3329404
  have hstable : (prefixWord ++ tailWord_3329404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329404).length < 2 ^ (prefixWord ++ tailWord_3329404).sum := by decide
  have hdescent : baseEnd_3329404 < baseStart_3329404 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329417 : List Nat := [1, 2, 1, 1, 17]
def baseStart_3329417 : Nat := 118140960795 + 3329417 * 2 ^ 59
def prefixEnd_3329417 : Nat := 4983230072969 + 3 ^ 40 * 3329417 * 2
def baseEnd_3329417 : Nat := 4690236543897134086079

theorem tailTrace_3329417 : CollatzResearch.WordTrace tailWord_3329417 prefixEnd_3329417 4690236543897134086079 := by
  unfold tailWord_3329417
  simp only [CollatzResearch.WordTrace]
  refine ⟨121433814179098302998626505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80955876119398868665751003 121433814179098302998626505)
  ·
    refine ⟨91075360634323727248969879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121433814179098302998626505 91075360634323727248969879)
    ·
      refine ⟨136613040951485590873454819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91075360634323727248969879 136613040951485590873454819)
      ·
        refine ⟨204919561427228386310182229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136613040951485590873454819 204919561427228386310182229)
        ·
          refine ⟨4690236543897134086079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 17 204919561427228386310182229 4690236543897134086079)
          ·
            rfl

theorem cell22_3329417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 17].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 17].length) (baseStart_3329417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3329417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3329417 prefixEnd_3329417 := by exact prefixLift 3329417
  have htrace : WordTrace (prefixWord ++ tailWord_3329417) baseStart_3329417 baseEnd_3329417 := by
    simpa [prefixWord, tailWord_3329417, baseEnd_3329417] using wordTrace_append hprefix tailTrace_3329417
  have hstable : (prefixWord ++ tailWord_3329417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329417).length < 2 ^ (prefixWord ++ tailWord_3329417).sum := by decide
  have hdescent : baseEnd_3329417 < baseStart_3329417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329419 : List Nat := [1, 1, 1, 1, 4, 3, 1, 4, 2, 4]
def baseStart_3329419 : Nat := 118140960795 + 3329419 * 2 ^ 59
def prefixEnd_3329419 : Nat := 4983230072969 + 3 ^ 40 * 3329419 * 2
def baseEnd_3329419 : Nat := 1139728164807876244367191

theorem tailTrace_3329419 : CollatzResearch.WordTrace tailWord_3329419 prefixEnd_3329419 1139728164807876244367191 := by
  unfold tailWord_3329419
  simp only [CollatzResearch.WordTrace]
  refine ⟨121433887125091057340199311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80955924750060704893466207 121433887125091057340199311)
  ·
    refine ⟨182150830687636586010298967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121433887125091057340199311 182150830687636586010298967)
    ·
      refine ⟨273226246031454879015448451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182150830687636586010298967 273226246031454879015448451)
      ·
        refine ⟨409839369047182318523172677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273226246031454879015448451 409839369047182318523172677)
        ·
          refine ⟨76844881696346684723094877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 409839369047182318523172677 76844881696346684723094877)
          ·
            refine ⟨28816830636130006771160579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76844881696346684723094877 28816830636130006771160579)
            ·
              refine ⟨43225245954195010156740869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28816830636130006771160579 43225245954195010156740869)
              ·
                refine ⟨8104733616411564404388913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43225245954195010156740869 8104733616411564404388913)
                ·
                  refine ⟨6078550212308673303291685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8104733616411564404388913 6078550212308673303291685)
                  ·
                    refine ⟨1139728164807876244367191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6078550212308673303291685 1139728164807876244367191)
                    ·
                      rfl

theorem cell22_3329419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 4, 2, 4].length) (baseStart_3329419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3329419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3329419 prefixEnd_3329419 := by exact prefixLift 3329419
  have htrace : WordTrace (prefixWord ++ tailWord_3329419) baseStart_3329419 baseEnd_3329419 := by
    simpa [prefixWord, tailWord_3329419, baseEnd_3329419] using wordTrace_append hprefix tailTrace_3329419
  have hstable : (prefixWord ++ tailWord_3329419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329419).length < 2 ^ (prefixWord ++ tailWord_3329419).sum := by decide
  have hdescent : baseEnd_3329419 < baseStart_3329419 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329453 : List Nat := [1, 5, 2, 2, 1, 1, 3, 1, 2, 4]
def baseStart_3329453 : Nat := 118140960795 + 3329453 * 2 ^ 59
def prefixEnd_3329453 : Nat := 4983230072969 + 3 ^ 40 * 3329453 * 2
def baseEnd_3329453 : Nat := 1139739803702711489017087

theorem tailTrace_3329453 : CollatzResearch.WordTrace tailWord_3329453 prefixEnd_3329453 1139739803702711489017087 := by
  unfold tailWord_3329453
  simp only [CollatzResearch.WordTrace]
  refine ⟨121435127206967881146937013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80956751471311920764624675 121435127206967881146937013)
  ·
    refine ⟨11384543175653238857525345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 121435127206967881146937013 11384543175653238857525345)
    ·
      refine ⟨8538407381739929143144009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11384543175653238857525345 8538407381739929143144009)
      ·
        refine ⟨6403805536304946857358007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8538407381739929143144009 6403805536304946857358007)
        ·
          refine ⟨9605708304457420286037011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6403805536304946857358007 9605708304457420286037011)
          ·
            refine ⟨14408562456686130429055517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9605708304457420286037011 14408562456686130429055517)
            ·
              refine ⟨5403210921257298910895819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14408562456686130429055517 5403210921257298910895819)
              ·
                refine ⟨8104816381885948366343729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5403210921257298910895819 8104816381885948366343729)
                ·
                  refine ⟨6078612286414461274757797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8104816381885948366343729 6078612286414461274757797)
                  ·
                    refine ⟨1139739803702711489017087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6078612286414461274757797 1139739803702711489017087)
                    ·
                      rfl

theorem cell22_3329453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_3329453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3329453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3329453 prefixEnd_3329453 := by exact prefixLift 3329453
  have htrace : WordTrace (prefixWord ++ tailWord_3329453) baseStart_3329453 baseEnd_3329453 := by
    simpa [prefixWord, tailWord_3329453, baseEnd_3329453] using wordTrace_append hprefix tailTrace_3329453
  have hstable : (prefixWord ++ tailWord_3329453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329453).length < 2 ^ (prefixWord ++ tailWord_3329453).sum := by decide
  have hdescent : baseEnd_3329453 < baseStart_3329453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329479 : List Nat := [1, 1, 4, 1, 1, 3, 3, 1, 7]
def baseStart_3329479 : Nat := 118140960795 + 3329479 * 2 ^ 59
def prefixEnd_3329479 : Nat := 4983230072969 + 3 ^ 40 * 3329479 * 2
def baseEnd_3329479 : Nat := 379916234678018695955669

theorem tailTrace_3329479 : CollatzResearch.WordTrace tailWord_3329479 prefixEnd_3329479 379916234678018695955669 := by
  unfold tailWord_3329479
  simp only [CollatzResearch.WordTrace]
  refine ⟨121436075504873687587383491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80957383669915791724922327 121436075504873687587383491)
  ·
    refine ⟨182154113257310531381075237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121436075504873687587383491 182154113257310531381075237)
    ·
      refine ⟨34153896235745724633951607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 182154113257310531381075237 34153896235745724633951607)
      ·
        refine ⟨51230844353618586950927411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34153896235745724633951607 51230844353618586950927411)
        ·
          refine ⟨76846266530427880426391117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51230844353618586950927411 76846266530427880426391117)
          ·
            refine ⟨28817349948910455159896669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76846266530427880426391117 28817349948910455159896669)
            ·
              refine ⟨10806506230841420684961251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28817349948910455159896669 10806506230841420684961251)
              ·
                refine ⟨16209759346262131027441877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10806506230841420684961251 16209759346262131027441877)
                ·
                  refine ⟨379916234678018695955669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16209759346262131027441877 379916234678018695955669)
                  ·
                    rfl

theorem cell22_3329479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 1, 7].length) (baseStart_3329479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3329479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3329479 prefixEnd_3329479 := by exact prefixLift 3329479
  have htrace : WordTrace (prefixWord ++ tailWord_3329479) baseStart_3329479 baseEnd_3329479 := by
    simpa [prefixWord, tailWord_3329479, baseEnd_3329479] using wordTrace_append hprefix tailTrace_3329479
  have hstable : (prefixWord ++ tailWord_3329479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329479).length < 2 ^ (prefixWord ++ tailWord_3329479).sum := by decide
  have hdescent : baseEnd_3329479 < baseStart_3329479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329483 : List Nat := [1, 1, 1, 1, 3, 3, 4, 4, 1, 3]
def baseStart_3329483 : Nat := 118140960795 + 3329483 * 2 ^ 59
def prefixEnd_3329483 : Nat := 4983230072969 + 3 ^ 40 * 3329483 * 2
def baseEnd_3329483 : Nat := 1139750073315801410766995

theorem tailTrace_3329483 : CollatzResearch.WordTrace tailWord_3329483 prefixEnd_3329483 1139750073315801410766995 := by
  unfold tailWord_3329483
  simp only [CollatzResearch.WordTrace]
  refine ⟨121436221396859196270529103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80957480931239464180352735 121436221396859196270529103)
  ·
    refine ⟨182154332095288794405793655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121436221396859196270529103 182154332095288794405793655)
    ·
      refine ⟨273231498142933191608690483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182154332095288794405793655 273231498142933191608690483)
      ·
        refine ⟨409847247214399787413035725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273231498142933191608690483 409847247214399787413035725)
        ·
          refine ⟨153692717705399920279888397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 409847247214399787413035725 153692717705399920279888397)
          ·
            refine ⟨57634769139524970104958149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153692717705399920279888397 57634769139524970104958149)
            ·
              refine ⟨10806519213660931894679653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57634769139524970104958149 10806519213660931894679653)
              ·
                refine ⟨2026222352561424730252435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10806519213660931894679653 2026222352561424730252435)
                ·
                  refine ⟨3039333528842137095378653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2026222352561424730252435 3039333528842137095378653)
                  ·
                    refine ⟨1139750073315801410766995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3039333528842137095378653 1139750073315801410766995)
                    ·
                      rfl

theorem cell22_3329483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 4, 1, 3].length) (baseStart_3329483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3329483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3329483 prefixEnd_3329483 := by exact prefixLift 3329483
  have htrace : WordTrace (prefixWord ++ tailWord_3329483) baseStart_3329483 baseEnd_3329483 := by
    simpa [prefixWord, tailWord_3329483, baseEnd_3329483] using wordTrace_append hprefix tailTrace_3329483
  have hstable : (prefixWord ++ tailWord_3329483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329483).length < 2 ^ (prefixWord ++ tailWord_3329483).sum := by decide
  have hdescent : baseEnd_3329483 < baseStart_3329483 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329534 : List Nat := [4, 2, 2, 3, 2, 1, 1, 1, 3, 3]
def baseStart_3329534 : Nat := 118140960795 + 3329534 * 2 ^ 59
def prefixEnd_3329534 : Nat := 4983230072969 + 3 ^ 40 * 3329534 * 2
def baseEnd_3329534 : Nat := 1139767531658054277741839

theorem tailTrace_3329534 : CollatzResearch.WordTrace tailWord_3329534 prefixEnd_3329534 1139767531658054277741839 := by
  unfold tailWord_3329534
  simp only [CollatzResearch.WordTrace]
  refine ⟨15179760189959303997579457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80958721013116287987090437 15179760189959303997579457)
  ·
    refine ⟨11384820142469477998184593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15179760189959303997579457 11384820142469477998184593)
    ·
      refine ⟨8538615106852108498638445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11384820142469477998184593 8538615106852108498638445)
      ·
        refine ⟨3201980665069540686989417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8538615106852108498638445 3201980665069540686989417)
        ·
          refine ⟨2401485498802155515242063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3201980665069540686989417 2401485498802155515242063)
          ·
            refine ⟨3602228248203233272863095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2401485498802155515242063 3602228248203233272863095)
            ·
              refine ⟨5403342372304849909294643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3602228248203233272863095 5403342372304849909294643)
              ·
                refine ⟨8105013558457274863941965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5403342372304849909294643 8105013558457274863941965)
                ·
                  refine ⟨3039380084421478073978237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8105013558457274863941965 3039380084421478073978237)
                  ·
                    refine ⟨1139767531658054277741839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3039380084421478073978237 1139767531658054277741839)
                    ·
                      rfl

theorem cell22_3329534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_3329534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3329534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3329534 prefixEnd_3329534 := by exact prefixLift 3329534
  have htrace : WordTrace (prefixWord ++ tailWord_3329534) baseStart_3329534 baseEnd_3329534 := by
    simpa [prefixWord, tailWord_3329534, baseEnd_3329534] using wordTrace_append hprefix tailTrace_3329534
  have hstable : (prefixWord ++ tailWord_3329534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329534).length < 2 ^ (prefixWord ++ tailWord_3329534).sum := by decide
  have hdescent : baseEnd_3329534 < baseStart_3329534 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329539 : List Nat := [1, 1, 1, 3, 2, 1, 2, 1, 5, 5]
def baseStart_3329539 : Nat := 118140960795 + 3329539 * 2 ^ 59
def prefixEnd_3329539 : Nat := 4983230072969 + 3 ^ 40 * 3329539 * 2
def baseEnd_3329539 : Nat := 1139769243260235931366823

theorem tailTrace_3329539 : CollatzResearch.WordTrace tailWord_3329539 prefixEnd_3329539 1139769243260235931366823 := by
  unfold tailWord_3329539
  simp only [CollatzResearch.WordTrace]
  refine ⟨121438263884656317834567671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80958842589770878556378447 121438263884656317834567671)
  ·
    refine ⟨182157395826984476751851507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121438263884656317834567671 182157395826984476751851507)
    ·
      refine ⟨273236093740476715127777261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182157395826984476751851507 273236093740476715127777261)
      ·
        refine ⟨102463535152678768172916473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 273236093740476715127777261 102463535152678768172916473)
        ·
          refine ⟨76847651364509076129687355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102463535152678768172916473 76847651364509076129687355)
          ·
            refine ⟨115271477046763614194531033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76847651364509076129687355 115271477046763614194531033)
            ·
              refine ⟨86453607785072710645898275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115271477046763614194531033 86453607785072710645898275)
              ·
                refine ⟨129680411677609065968847413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86453607785072710645898275 129680411677609065968847413)
                ·
                  refine ⟨12157538594775849934579445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 129680411677609065968847413 12157538594775849934579445)
                  ·
                    refine ⟨1139769243260235931366823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12157538594775849934579445 1139769243260235931366823)
                    ·
                      rfl

theorem cell22_3329539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 5, 5].length) (baseStart_3329539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3329539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3329539 prefixEnd_3329539 := by exact prefixLift 3329539
  have htrace : WordTrace (prefixWord ++ tailWord_3329539) baseStart_3329539 baseEnd_3329539 := by
    simpa [prefixWord, tailWord_3329539, baseEnd_3329539] using wordTrace_append hprefix tailTrace_3329539
  have hstable : (prefixWord ++ tailWord_3329539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329539).length < 2 ^ (prefixWord ++ tailWord_3329539).sum := by decide
  have hdescent : baseEnd_3329539 < baseStart_3329539 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329560 : List Nat := [2, 1, 2, 3, 4, 2, 1, 2, 1, 4]
def baseStart_3329560 : Nat := 118140960795 + 3329560 * 2 ^ 59
def prefixEnd_3329560 : Nat := 4983230072969 + 3 ^ 40 * 3329560 * 2
def baseEnd_3329560 : Nat := 1139776431989398876591759

theorem tailTrace_3329560 : CollatzResearch.WordTrace tailWord_3329560 prefixEnd_3329560 1139776431989398876591759 := by
  unfold tailWord_3329560
  simp only [CollatzResearch.WordTrace]
  refine ⟨60719514908790119210541067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80959353211720158947388089 60719514908790119210541067)
  ·
    refine ⟨91079272363185178815811601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60719514908790119210541067 91079272363185178815811601)
    ·
      refine ⟨68309454272388884111858701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91079272363185178815811601 68309454272388884111858701)
      ·
        refine ⟨25616045352145831541947013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68309454272388884111858701 25616045352145831541947013)
        ·
          refine ⟨4803008503527343414115065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25616045352145831541947013 4803008503527343414115065)
          ·
            refine ⟨3602256377645507560586299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4803008503527343414115065 3602256377645507560586299)
            ·
              refine ⟨5403384566468261340879449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3602256377645507560586299 5403384566468261340879449)
              ·
                refine ⟨4052538424851196005659587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5403384566468261340879449 4052538424851196005659587)
                ·
                  refine ⟨6078807637276794008489381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4052538424851196005659587 6078807637276794008489381)
                  ·
                    refine ⟨1139776431989398876591759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6078807637276794008489381 1139776431989398876591759)
                    ·
                      rfl

theorem cell22_3329560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 2, 1, 4].length) (baseStart_3329560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3329560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3329560 prefixEnd_3329560 := by exact prefixLift 3329560
  have htrace : WordTrace (prefixWord ++ tailWord_3329560) baseStart_3329560 baseEnd_3329560 := by
    simpa [prefixWord, tailWord_3329560, baseEnd_3329560] using wordTrace_append hprefix tailTrace_3329560
  have hstable : (prefixWord ++ tailWord_3329560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329560).length < 2 ^ (prefixWord ++ tailWord_3329560).sum := by decide
  have hdescent : baseEnd_3329560 < baseStart_3329560 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329618 : List Nat := [3, 2, 2, 1, 2, 2, 1, 1, 5, 3]
def baseStart_3329618 : Nat := 118140960795 + 3329618 * 2 ^ 59
def prefixEnd_3329618 : Nat := 4983230072969 + 3 ^ 40 * 3329618 * 2
def baseEnd_3329618 : Nat := 1139796286574706058641581

theorem tailTrace_3329618 : CollatzResearch.WordTrace tailWord_3329618 prefixEnd_3329618 1139796286574706058641581 := by
  unfold tailWord_3329618
  simp only [CollatzResearch.WordTrace]
  refine ⟨30360286312842528581673377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80960763500913409551129005 30360286312842528581673377)
  ·
    refine ⟨22770214734631896436255033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30360286312842528581673377 22770214734631896436255033)
    ·
      refine ⟨17077661050973922327191275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22770214734631896436255033 17077661050973922327191275)
      ·
        refine ⟨25616491576460883490786913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17077661050973922327191275 25616491576460883490786913)
        ·
          refine ⟨19212368682345662618090185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25616491576460883490786913 19212368682345662618090185)
          ·
            refine ⟨14409276511759246963567639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19212368682345662618090185 14409276511759246963567639)
            ·
              refine ⟨21613914767638870445351459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14409276511759246963567639 21613914767638870445351459)
              ·
                refine ⟨32420872151458305668027189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21613914767638870445351459 32420872151458305668027189)
                ·
                  refine ⟨3039456764199216156377549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32420872151458305668027189 3039456764199216156377549)
                  ·
                    refine ⟨1139796286574706058641581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3039456764199216156377549 1139796286574706058641581)
                    ·
                      rfl

theorem cell22_3329618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 5, 3].length) (baseStart_3329618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3329618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3329618 prefixEnd_3329618 := by exact prefixLift 3329618
  have htrace : WordTrace (prefixWord ++ tailWord_3329618) baseStart_3329618 baseEnd_3329618 := by
    simpa [prefixWord, tailWord_3329618, baseEnd_3329618] using wordTrace_append hprefix tailTrace_3329618
  have hstable : (prefixWord ++ tailWord_3329618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329618).length < 2 ^ (prefixWord ++ tailWord_3329618).sum := by decide
  have hdescent : baseEnd_3329618 < baseStart_3329618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329622 : List Nat := [5, 2, 2, 2, 1, 1, 1, 1, 1, 6]
def baseStart_3329622 : Nat := 118140960795 + 3329622 * 2 ^ 59
def prefixEnd_3329622 : Nat := 4983230072969 + 3 ^ 40 * 3329622 * 2
def baseEnd_3329622 : Nat := 1139797655856451381541569

theorem tailTrace_3329622 : CollatzResearch.WordTrace tailWord_3329622 prefixEnd_3329622 1139797655856451381541569 := by
  unfold tailWord_3329622
  simp only [CollatzResearch.WordTrace]
  refine ⟨7590080696459726438114945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80960860762237082006559413 7590080696459726438114945)
  ·
    refine ⟨5692560522344794828586209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7590080696459726438114945 5692560522344794828586209)
    ·
      refine ⟨4269420391758596121439657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5692560522344794828586209 4269420391758596121439657)
      ·
        refine ⟨3202065293818947091079743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4269420391758596121439657 3202065293818947091079743)
        ·
          refine ⟨4803097940728420636619615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3202065293818947091079743 4803097940728420636619615)
          ·
            refine ⟨7204646911092630954929423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4803097940728420636619615 7204646911092630954929423)
            ·
              refine ⟨10806970366638946432394135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7204646911092630954929423 10806970366638946432394135)
              ·
                refine ⟨16210455549958419648591203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10806970366638946432394135 16210455549958419648591203)
                ·
                  refine ⟨24315683324937629472886805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16210455549958419648591203 24315683324937629472886805)
                  ·
                    refine ⟨1139797655856451381541569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24315683324937629472886805 1139797655856451381541569)
                    ·
                      rfl

theorem cell22_3329622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_3329622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3329622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3329622 prefixEnd_3329622 := by exact prefixLift 3329622
  have htrace : WordTrace (prefixWord ++ tailWord_3329622) baseStart_3329622 baseEnd_3329622 := by
    simpa [prefixWord, tailWord_3329622, baseEnd_3329622] using wordTrace_append hprefix tailTrace_3329622
  have hstable : (prefixWord ++ tailWord_3329622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329622).length < 2 ^ (prefixWord ++ tailWord_3329622).sum := by decide
  have hdescent : baseEnd_3329622 < baseStart_3329622 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329635 : List Nat := [1, 1, 1, 5, 1, 3, 1, 5, 1, 3]
def baseStart_3329635 : Nat := 118140960795 + 3329635 * 2 ^ 59
def prefixEnd_3329635 : Nat := 4983230072969 + 3 ^ 40 * 3329635 * 2
def baseEnd_3329635 : Nat := 1139802106022123680966529

theorem tailTrace_3329635 : CollatzResearch.WordTrace tailWord_3329635 prefixEnd_3329635 1139802106022123680966529 := by
  unfold tailWord_3329635
  simp only [CollatzResearch.WordTrace]
  refine ⟨121441765292308526230062359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80961176861539017486708239 121441765292308526230062359)
  ·
    refine ⟨182162647938462789345093539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121441765292308526230062359 182162647938462789345093539)
    ·
      refine ⟨273243971907694184017640309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182162647938462789345093539 273243971907694184017640309)
      ·
        refine ⟨25616622366346329751653779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 273243971907694184017640309 25616622366346329751653779)
        ·
          refine ⟨38424933549519494627480669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25616622366346329751653779 38424933549519494627480669)
          ·
            refine ⟨14409350081069810485305251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38424933549519494627480669 14409350081069810485305251)
            ·
              refine ⟨21614025121604715727957877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14409350081069810485305251 21614025121604715727957877)
              ·
                refine ⟨2026314855150442099496051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21614025121604715727957877 2026314855150442099496051)
                ·
                  refine ⟨3039472282725663149244077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2026314855150442099496051 3039472282725663149244077)
                  ·
                    refine ⟨1139802106022123680966529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3039472282725663149244077 1139802106022123680966529)
                    ·
                      rfl

theorem cell22_3329635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 5, 1, 3].length) (baseStart_3329635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3329635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3329635 prefixEnd_3329635 := by exact prefixLift 3329635
  have htrace : WordTrace (prefixWord ++ tailWord_3329635) baseStart_3329635 baseEnd_3329635 := by
    simpa [prefixWord, tailWord_3329635, baseEnd_3329635] using wordTrace_append hprefix tailTrace_3329635
  have hstable : (prefixWord ++ tailWord_3329635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329635).length < 2 ^ (prefixWord ++ tailWord_3329635).sum := by decide
  have hdescent : baseEnd_3329635 < baseStart_3329635 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329648 : List Nat := [2, 1, 1, 1, 6, 1, 3, 2, 5]
def baseStart_3329648 : Nat := 118140960795 + 3329648 * 2 ^ 59
def prefixEnd_3329648 : Nat := 4983230072969 + 3 ^ 40 * 3329648 * 2
def baseEnd_3329648 : Nat := 379935518729265326797163

theorem tailTrace_3329648 : CollatzResearch.WordTrace tailWord_3329648 prefixEnd_3329648 379935518729265326797163 := by
  unfold tailWord_3329648
  simp only [CollatzResearch.WordTrace]
  refine ⟨60721119720630714725142799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80961492960840952966857065 60721119720630714725142799)
  ·
    refine ⟨91081679580946072087714199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60721119720630714725142799 91081679580946072087714199)
    ·
      refine ⟨136622519371419108131571299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91081679580946072087714199 136622519371419108131571299)
      ·
        refine ⟨204933779057128662197356949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136622519371419108131571299 204933779057128662197356949)
        ·
          refine ⟨9606270893302906040501107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 204933779057128662197356949 9606270893302906040501107)
          ·
            refine ⟨14409406339954359060751661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9606270893302906040501107 14409406339954359060751661)
            ·
              refine ⟨5403527377482884647781873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14409406339954359060751661 5403527377482884647781873)
              ·
                refine ⟨4052645533112163485836405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5403527377482884647781873 4052645533112163485836405)
                ·
                  refine ⟨379935518729265326797163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4052645533112163485836405 379935518729265326797163)
                  ·
                    rfl

theorem cell22_3329648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 2, 5].length) (baseStart_3329648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3329648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3329648 prefixEnd_3329648 := by exact prefixLift 3329648
  have htrace : WordTrace (prefixWord ++ tailWord_3329648) baseStart_3329648 baseEnd_3329648 := by
    simpa [prefixWord, tailWord_3329648, baseEnd_3329648] using wordTrace_append hprefix tailTrace_3329648
  have hstable : (prefixWord ++ tailWord_3329648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329648).length < 2 ^ (prefixWord ++ tailWord_3329648).sum := by decide
  have hdescent : baseEnd_3329648 < baseStart_3329648 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329665 : List Nat := [1, 2, 4, 2, 1, 3, 3, 1, 5]
def baseStart_3329665 : Nat := 118140960795 + 3329665 * 2 ^ 59
def prefixEnd_3329665 : Nat := 4983230072969 + 3 ^ 40 * 3329665 * 2
def baseEnd_3329665 : Nat := 379937458545071200905479

theorem tailTrace_3329665 : CollatzResearch.WordTrace tailWord_3329665 prefixEnd_3329665 379937458545071200905479 := by
  unfold tailWord_3329665
  simp only [CollatzResearch.WordTrace]
  refine ⟨121442859482199841353654449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80961906321466560902436299 121442859482199841353654449)
  ·
    refine ⟨91082144611649881015240837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121442859482199841353654449 91082144611649881015240837)
    ·
      refine ⟨17077902114684352690357657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91082144611649881015240837 17077902114684352690357657)
      ·
        refine ⟨12808426586013264517768243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17077902114684352690357657 12808426586013264517768243)
        ·
          refine ⟨19212639879019896776652365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12808426586013264517768243 19212639879019896776652365)
          ·
            refine ⟨7204739954632461291244637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19212639879019896776652365 7204739954632461291244637)
            ·
              refine ⟨2701777482987172984216739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7204739954632461291244637 2701777482987172984216739)
              ·
                refine ⟨4052666224480759476325109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2701777482987172984216739 4052666224480759476325109)
                ·
                  refine ⟨379937458545071200905479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4052666224480759476325109 379937458545071200905479)
                  ·
                    rfl

theorem cell22_3329665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 3, 1, 5].length) (baseStart_3329665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3329665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3329665 prefixEnd_3329665 := by exact prefixLift 3329665
  have htrace : WordTrace (prefixWord ++ tailWord_3329665) baseStart_3329665 baseEnd_3329665 := by
    simpa [prefixWord, tailWord_3329665, baseEnd_3329665] using wordTrace_append hprefix tailTrace_3329665
  have hstable : (prefixWord ++ tailWord_3329665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329665).length < 2 ^ (prefixWord ++ tailWord_3329665).sum := by decide
  have hdescent : baseEnd_3329665 < baseStart_3329665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329676 : List Nat := [2, 2, 1, 2, 1, 1, 3, 4, 6]
def baseStart_3329676 : Nat := 118140960795 + 3329676 * 2 ^ 59
def prefixEnd_3329676 : Nat := 4983230072969 + 3 ^ 40 * 3329676 * 2
def baseEnd_3329676 : Nat := 379938713720004413563801

theorem tailTrace_3329676 : CollatzResearch.WordTrace tailWord_3329676 prefixEnd_3329676 379938713720004413563801 := by
  unfold tailWord_3329676
  simp only [CollatzResearch.WordTrace]
  refine ⟨60721630342579995116152441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80962173790106660154869921 60721630342579995116152441)
  ·
    refine ⟨45541222756934996337114331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60721630342579995116152441 45541222756934996337114331)
    ·
      refine ⟨68311834135402494505671497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45541222756934996337114331 68311834135402494505671497)
      ·
        refine ⟨51233875601551870879253623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68311834135402494505671497 51233875601551870879253623)
        ·
          refine ⟨76850813402327806318880435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51233875601551870879253623 76850813402327806318880435)
          ·
            refine ⟨115276220103491709478320653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76850813402327806318880435 115276220103491709478320653)
            ·
              refine ⟨43228582538809391054370245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115276220103491709478320653 43228582538809391054370245)
              ·
                refine ⟨8105359226026760822694421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43228582538809391054370245 8105359226026760822694421)
                ·
                  refine ⟨379938713720004413563801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8105359226026760822694421 379938713720004413563801)
                  ·
                    rfl

theorem cell22_3329676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 4, 6].length) (baseStart_3329676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3329676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3329676 prefixEnd_3329676 := by exact prefixLift 3329676
  have htrace : WordTrace (prefixWord ++ tailWord_3329676) baseStart_3329676 baseEnd_3329676 := by
    simpa [prefixWord, tailWord_3329676, baseEnd_3329676] using wordTrace_append hprefix tailTrace_3329676
  have hstable : (prefixWord ++ tailWord_3329676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329676).length < 2 ^ (prefixWord ++ tailWord_3329676).sum := by decide
  have hdescent : baseEnd_3329676 < baseStart_3329676 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329721 : List Nat := [1, 2, 1, 4, 1, 1, 3, 9]
def baseStart_3329721 : Nat := 118140960795 + 3329721 * 2 ^ 59
def prefixEnd_3329721 : Nat := 4983230072969 + 3 ^ 40 * 3329721 * 2
def baseEnd_3329721 : Nat := 126647949508849791479585

theorem tailTrace_3329721 : CollatzResearch.WordTrace tailWord_3329721 prefixEnd_3329721 126647949508849791479585 := by
  unfold tailWord_3329721
  simp only [CollatzResearch.WordTrace]
  refine ⟨121444901969996962917693017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80963267979997975278462011 121444901969996962917693017)
  ·
    refine ⟨91083676477497722188269763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121444901969996962917693017 91083676477497722188269763)
    ·
      refine ⟨136625514716246583282404645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91083676477497722188269763 136625514716246583282404645)
      ·
        refine ⟨25617284009296234365450871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136625514716246583282404645 25617284009296234365450871)
        ·
          refine ⟨38425926013944351548176307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25617284009296234365450871 38425926013944351548176307)
          ·
            refine ⟨57638889020916527322264461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38425926013944351548176307 57638889020916527322264461)
            ·
              refine ⟨21614583382843697745849173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57638889020916527322264461 21614583382843697745849173)
              ·
                refine ⟨126647949508849791479585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21614583382843697745849173 126647949508849791479585)
                ·
                  rfl

theorem cell22_3329721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 9].length) (baseStart_3329721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3329721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3329721 prefixEnd_3329721 := by exact prefixLift 3329721
  have htrace : WordTrace (prefixWord ++ tailWord_3329721) baseStart_3329721 baseEnd_3329721 := by
    simpa [prefixWord, tailWord_3329721, baseEnd_3329721] using wordTrace_append hprefix tailTrace_3329721
  have hstable : (prefixWord ++ tailWord_3329721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329721).length < 2 ^ (prefixWord ++ tailWord_3329721).sum := by decide
  have hdescent : baseEnd_3329721 < baseStart_3329721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329725 : List Nat := [1, 4, 1, 2, 1, 2, 3, 3, 2, 3]
def baseStart_3329725 : Nat := 118140960795 + 3329725 * 2 ^ 59
def prefixEnd_3329725 : Nat := 4983230072969 + 3 ^ 40 * 3329725 * 2
def baseEnd_3329725 : Nat := 1139832914861393446216253

theorem tailTrace_3329725 : CollatzResearch.WordTrace tailWord_3329725 prefixEnd_3329725 1139832914861393446216253 := by
  unfold tailWord_3329725
  simp only [CollatzResearch.WordTrace]
  refine ⟨121445047861982471600838629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80963365241321647733892419 121445047861982471600838629)
  ·
    refine ⟨22770946474121713425157243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121445047861982471600838629 22770946474121713425157243)
    ·
      refine ⟨34156419711182570137735865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22770946474121713425157243 34156419711182570137735865)
      ·
        refine ⟨25617314783386927603301899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34156419711182570137735865 25617314783386927603301899)
        ·
          refine ⟨38425972175080391404952849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25617314783386927603301899 38425972175080391404952849)
          ·
            refine ⟨28819479131310293553714637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38425972175080391404952849 28819479131310293553714637)
            ·
              refine ⟨10807304674241360082642989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28819479131310293553714637 10807304674241360082642989)
              ·
                refine ⟨4052739252840510030991121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10807304674241360082642989 4052739252840510030991121)
                ·
                  refine ⟨3039554439630382523243341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4052739252840510030991121 3039554439630382523243341)
                  ·
                    refine ⟨1139832914861393446216253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3039554439630382523243341 1139832914861393446216253)
                    ·
                      rfl

theorem cell22_3329725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 3, 2, 3].length) (baseStart_3329725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3329725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3329725 prefixEnd_3329725 := by exact prefixLift 3329725
  have htrace : WordTrace (prefixWord ++ tailWord_3329725) baseStart_3329725 baseEnd_3329725 := by
    simpa [prefixWord, tailWord_3329725, baseEnd_3329725] using wordTrace_append hprefix tailTrace_3329725
  have hstable : (prefixWord ++ tailWord_3329725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329725).length < 2 ^ (prefixWord ++ tailWord_3329725).sum := by decide
  have hdescent : baseEnd_3329725 < baseStart_3329725 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329768 : List Nat := [2, 1, 4, 1, 3, 1, 1, 1, 2, 6]
def baseStart_3329768 : Nat := 118140960795 + 3329768 * 2 ^ 59
def prefixEnd_3329768 : Nat := 4983230072969 + 3 ^ 40 * 3329768 * 2
def baseEnd_3329768 : Nat := 1139847634640155667391121

theorem tailTrace_3329768 : CollatzResearch.WordTrace tailWord_3329768 prefixEnd_3329768 1139847634640155667391121 := by
  unfold tailWord_3329768
  simp only [CollatzResearch.WordTrace]
  refine ⟨60723308100413344972326979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80964410800551126629769305 60723308100413344972326979)
  ·
    refine ⟨91084962150620017458490469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60723308100413344972326979 91084962150620017458490469)
    ·
      refine ⟨17078430403241253273466963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91084962150620017458490469 17078430403241253273466963)
      ·
        refine ⟨25617645604861879910200445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17078430403241253273466963 25617645604861879910200445)
        ·
          refine ⟨9606617101823204966325167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25617645604861879910200445 9606617101823204966325167)
          ·
            refine ⟨14409925652734807449487751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9606617101823204966325167 14409925652734807449487751)
            ·
              refine ⟨21614888479102211174231627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14409925652734807449487751 21614888479102211174231627)
              ·
                refine ⟨32422332718653316761347441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21614888479102211174231627 32422332718653316761347441)
                ·
                  refine ⟨24316749538989987571010581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32422332718653316761347441 24316749538989987571010581)
                  ·
                    refine ⟨1139847634640155667391121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24316749538989987571010581 1139847634640155667391121)
                    ·
                      rfl

theorem cell22_3329768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_3329768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3329768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3329768 prefixEnd_3329768 := by exact prefixLift 3329768
  have htrace : WordTrace (prefixWord ++ tailWord_3329768) baseStart_3329768 baseEnd_3329768 := by
    simpa [prefixWord, tailWord_3329768, baseEnd_3329768] using wordTrace_append hprefix tailTrace_3329768
  have hstable : (prefixWord ++ tailWord_3329768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329768).length < 2 ^ (prefixWord ++ tailWord_3329768).sum := by decide
  have hdescent : baseEnd_3329768 < baseStart_3329768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329783 : List Nat := [1, 1, 3, 1, 1, 1, 6, 3, 5]
def baseStart_3329783 : Nat := 118140960795 + 3329783 * 2 ^ 59
def prefixEnd_3329783 : Nat := 4983230072969 + 3 ^ 40 * 3329783 * 2
def baseEnd_3329783 : Nat := 379950923148900209422025

theorem tailTrace_3329783 : CollatzResearch.WordTrace tailWord_3329783 prefixEnd_3329783 379950923148900209422025 := by
  unfold tailWord_3329783
  simp only [CollatzResearch.WordTrace]
  refine ⟨121447163295772347506450003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80964775530514898337633335 121447163295772347506450003)
  ·
    refine ⟨182170744943658521259675005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121447163295772347506450003 182170744943658521259675005)
    ·
      refine ⟨68314029353871945472378127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182170744943658521259675005 68314029353871945472378127)
      ·
        refine ⟨102471044030807918208567191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68314029353871945472378127 102471044030807918208567191)
        ·
          refine ⟨153706566046211877312850787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102471044030807918208567191 153706566046211877312850787)
          ·
            refine ⟨230559849069317815969276181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153706566046211877312850787 230559849069317815969276181)
            ·
              refine ⟨10807492925124272623559821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 230559849069317815969276181 10807492925124272623559821)
              ·
                refine ⟨4052809846921602233834933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10807492925124272623559821 4052809846921602233834933)
                ·
                  refine ⟨379950923148900209422025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4052809846921602233834933 379950923148900209422025)
                  ·
                    rfl

theorem cell22_3329783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 3, 5].length) (baseStart_3329783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3329783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3329783 prefixEnd_3329783 := by exact prefixLift 3329783
  have htrace : WordTrace (prefixWord ++ tailWord_3329783) baseStart_3329783 baseEnd_3329783 := by
    simpa [prefixWord, tailWord_3329783, baseEnd_3329783] using wordTrace_append hprefix tailTrace_3329783
  have hstable : (prefixWord ++ tailWord_3329783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329783).length < 2 ^ (prefixWord ++ tailWord_3329783).sum := by decide
  have hdescent : baseEnd_3329783 < baseStart_3329783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329873 : List Nat := [1, 2, 2, 1, 5, 1, 10]
def baseStart_3329873 : Nat := 118140960795 + 3329873 * 2 ^ 59
def prefixEnd_3329873 : Nat := 4983230072969 + 3 ^ 40 * 3329873 * 2
def baseEnd_3329873 : Nat := 42217910306887792352437

theorem tailTrace_3329873 : CollatzResearch.WordTrace tailWord_3329873 prefixEnd_3329873 42217910306887792352437 := by
  unfold tailWord_3329873
  simp only [CollatzResearch.WordTrace]
  refine ⟨121450445865446292877226273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80966963910297528584817515 121450445865446292877226273)
  ·
    refine ⟨91087834399084719657919705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121450445865446292877226273 91087834399084719657919705)
    ·
      refine ⟨68315875799313539743439779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91087834399084719657919705 68315875799313539743439779)
      ·
        refine ⟨102473813698970309615159669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68315875799313539743439779 102473813698970309615159669)
        ·
          refine ⟨9606920034278466526421219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 102473813698970309615159669 9606920034278466526421219)
          ·
            refine ⟨14410380051417699789631829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9606920034278466526421219 14410380051417699789631829)
            ·
              refine ⟨42217910306887792352437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14410380051417699789631829 42217910306887792352437)
              ·
                rfl

theorem cell22_3329873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 10].length) (baseStart_3329873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3329873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3329873 prefixEnd_3329873 := by exact prefixLift 3329873
  have htrace : WordTrace (prefixWord ++ tailWord_3329873) baseStart_3329873 baseEnd_3329873 := by
    simpa [prefixWord, tailWord_3329873, baseEnd_3329873] using wordTrace_append hprefix tailTrace_3329873
  have hstable : (prefixWord ++ tailWord_3329873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329873).length < 2 ^ (prefixWord ++ tailWord_3329873).sum := by decide
  have hdescent : baseEnd_3329873 < baseStart_3329873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329879 : List Nat := [1, 1, 3, 2, 5, 1, 3, 2, 4]
def baseStart_3329879 : Nat := 118140960795 + 3329879 * 2 ^ 59
def prefixEnd_3329879 : Nat := 4983230072969 + 3 ^ 40 * 3329879 * 2
def baseEnd_3329879 : Nat := 379961877402862792621927

theorem tailTrace_3329879 : CollatzResearch.WordTrace tailWord_3329879 prefixEnd_3329879 379961877402862792621927 := by
  unfold tailWord_3329879
  simp only [CollatzResearch.WordTrace]
  refine ⟨121450664703424555901944691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80967109802283037267963127 121450664703424555901944691)
  ·
    refine ⟨182175997055136833852917037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121450664703424555901944691 182175997055136833852917037)
    ·
      refine ⟨68315998895676312694843889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182175997055136833852917037 68315998895676312694843889)
      ·
        refine ⟨51236999171757234521132917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68315998895676312694843889 51236999171757234521132917)
        ·
          refine ⟨4803468672352240736356211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51236999171757234521132917 4803468672352240736356211)
          ·
            refine ⟨7205203008528361104534317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4803468672352240736356211 7205203008528361104534317)
            ·
              refine ⟨2701951128198135414200369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7205203008528361104534317 2701951128198135414200369)
              ·
                refine ⟨2026463346148601560650277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2701951128198135414200369 2026463346148601560650277)
                ·
                  refine ⟨379961877402862792621927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2026463346148601560650277 379961877402862792621927)
                  ·
                    rfl

theorem cell22_3329879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 3, 2, 4].length) (baseStart_3329879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3329879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3329879 prefixEnd_3329879 := by exact prefixLift 3329879
  have htrace : WordTrace (prefixWord ++ tailWord_3329879) baseStart_3329879 baseEnd_3329879 := by
    simpa [prefixWord, tailWord_3329879, baseEnd_3329879] using wordTrace_append hprefix tailTrace_3329879
  have hstable : (prefixWord ++ tailWord_3329879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329879).length < 2 ^ (prefixWord ++ tailWord_3329879).sum := by decide
  have hdescent : baseEnd_3329879 < baseStart_3329879 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329890 : List Nat := [3, 3, 2, 1, 2, 1, 1, 9]
def baseStart_3329890 : Nat := 118140960795 + 3329890 * 2 ^ 59
def prefixEnd_3329890 : Nat := 4983230072969 + 3 ^ 40 * 3329890 * 2
def baseEnd_3329890 : Nat := 126654377525932001760083

theorem tailTrace_3329890 : CollatzResearch.WordTrace tailWord_3329890 prefixEnd_3329890 126654377525932001760083 := by
  unfold tailWord_3329890
  simp only [CollatzResearch.WordTrace]
  refine ⟨30362766476596176195148781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80967377270923136520396749 30362766476596176195148781)
  ·
    refine ⟨11386037428723566073180793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30362766476596176195148781 11386037428723566073180793)
    ·
      refine ⟨8539528071542674554885595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11386037428723566073180793 8539528071542674554885595)
      ·
        refine ⟨12809292107314011832328393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8539528071542674554885595 12809292107314011832328393)
        ·
          refine ⟨9606969080485508874246295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12809292107314011832328393 9606969080485508874246295)
          ·
            refine ⟨14410453620728263311369443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9606969080485508874246295 14410453620728263311369443)
            ·
              refine ⟨21615680431092394967054165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14410453620728263311369443 21615680431092394967054165)
              ·
                refine ⟨126654377525932001760083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21615680431092394967054165 126654377525932001760083)
                ·
                  rfl

theorem cell22_3329890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 9].length) (baseStart_3329890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3329890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3329890 prefixEnd_3329890 := by exact prefixLift 3329890
  have htrace : WordTrace (prefixWord ++ tailWord_3329890) baseStart_3329890 baseEnd_3329890 := by
    simpa [prefixWord, tailWord_3329890, baseEnd_3329890] using wordTrace_append hprefix tailTrace_3329890
  have hstable : (prefixWord ++ tailWord_3329890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329890).length < 2 ^ (prefixWord ++ tailWord_3329890).sum := by decide
  have hdescent : baseEnd_3329890 < baseStart_3329890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329905 : List Nat := [1, 2, 2, 2, 1, 3, 2, 1, 5, 3]
def baseStart_3329905 : Nat := 118140960795 + 3329905 * 2 ^ 59
def prefixEnd_3329905 : Nat := 4983230072969 + 3 ^ 40 * 3329905 * 2
def baseEnd_3329905 : Nat := 1139894532539932976715701

theorem tailTrace_3329905 : CollatzResearch.WordTrace tailWord_3329905 prefixEnd_3329905 1139894532539932976715701 := by
  unfold tailWord_3329905
  simp only [CollatzResearch.WordTrace]
  refine ⟨121451613001330362342391169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80967742000886908228260779 121451613001330362342391169)
  ·
    refine ⟨91088709750997771756793377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121451613001330362342391169 91088709750997771756793377)
    ·
      refine ⟨68316532313248328817595033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91088709750997771756793377 68316532313248328817595033)
      ·
        refine ⟨51237399234936246613196275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68316532313248328817595033 51237399234936246613196275)
        ·
          refine ⟨76856098852404369919794413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51237399234936246613196275 76856098852404369919794413)
          ·
            refine ⟨28821037069651638719922905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76856098852404369919794413 28821037069651638719922905)
            ·
              refine ⟨21615777802238729039942179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28821037069651638719922905 21615777802238729039942179)
              ·
                refine ⟨32423666703358093559913269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21615777802238729039942179 32423666703358093559913269)
                ·
                  refine ⟨3039718753439821271241869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32423666703358093559913269 3039718753439821271241869)
                  ·
                    refine ⟨1139894532539932976715701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3039718753439821271241869 1139894532539932976715701)
                    ·
                      rfl

theorem cell22_3329905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 5, 3].length) (baseStart_3329905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3329905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3329905 prefixEnd_3329905 := by exact prefixLift 3329905
  have htrace : WordTrace (prefixWord ++ tailWord_3329905) baseStart_3329905 baseEnd_3329905 := by
    simpa [prefixWord, tailWord_3329905, baseEnd_3329905] using wordTrace_append hprefix tailTrace_3329905
  have hstable : (prefixWord ++ tailWord_3329905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329905).length < 2 ^ (prefixWord ++ tailWord_3329905).sum := by decide
  have hdescent : baseEnd_3329905 < baseStart_3329905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3330104 : List Nat := [2, 1, 2, 1, 6, 1, 2, 2, 5]
def baseStart_3330104 : Nat := 118140960795 + 3330104 * 2 ^ 59
def prefixEnd_3330104 : Nat := 4983230072969 + 3 ^ 40 * 3330104 * 2
def baseEnd_3330104 : Nat := 379987551435587596996697

theorem tailTrace_3330104 : CollatzResearch.WordTrace tailWord_3330104 prefixEnd_3330104 379987551435587596996697 := by
  unfold tailWord_3330104
  simp only [CollatzResearch.WordTrace]
  refine ⟨60729435563804709664442683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80972580751739612885923577 60729435563804709664442683)
  ·
    refine ⟨91094153345707064496664025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60729435563804709664442683 91094153345707064496664025)
    ·
      refine ⟨68320615009280298372498019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91094153345707064496664025 68320615009280298372498019)
      ·
        refine ⟨102480922513920447558747029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68320615009280298372498019 102480922513920447558747029)
        ·
          refine ⟨4803793242840020979316267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 102480922513920447558747029 4803793242840020979316267)
          ·
            refine ⟨7205689864260031468974401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4803793242840020979316267 7205689864260031468974401)
            ·
              refine ⟨5404267398195023601730801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7205689864260031468974401 5404267398195023601730801)
              ·
                refine ⟨4053200548646267701298101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5404267398195023601730801 4053200548646267701298101)
                ·
                  refine ⟨379987551435587596996697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4053200548646267701298101 379987551435587596996697)
                  ·
                    rfl

theorem cell22_3330104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 2, 5].length) (baseStart_3330104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3330104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3330104 prefixEnd_3330104 := by exact prefixLift 3330104
  have htrace : WordTrace (prefixWord ++ tailWord_3330104) baseStart_3330104 baseEnd_3330104 := by
    simpa [prefixWord, tailWord_3330104, baseEnd_3330104] using wordTrace_append hprefix tailTrace_3330104
  have hstable : (prefixWord ++ tailWord_3330104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3330104).length < 2 ^ (prefixWord ++ tailWord_3330104).sum := by decide
  have hdescent : baseEnd_3330104 < baseStart_3330104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3330104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3330142 : List Nat := [4, 4, 1, 1, 2, 1, 2, 3, 1, 3]
def baseStart_3330142 : Nat := 118140960795 + 3330142 * 2 ^ 59
def prefixEnd_3330142 : Nat := 4983230072969 + 3 ^ 40 * 3330142 * 2
def baseEnd_3330142 : Nat := 1139975662483343358539975

theorem tailTrace_3330142 : CollatzResearch.WordTrace tailWord_3330142 prefixEnd_3330142 1139975662483343358539975 := by
  unfold tailWord_3330142
  simp only [CollatzResearch.WordTrace]
  refine ⟨15182532137683968977346085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80973504734314501212512453 15182532137683968977346085)
  ·
    refine ⟨2846724775815744183252391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15182532137683968977346085 2846724775815744183252391)
    ·
      refine ⟨4270087163723616274878587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2846724775815744183252391 4270087163723616274878587)
      ·
        refine ⟨6405130745585424412317881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4270087163723616274878587 6405130745585424412317881)
        ·
          refine ⟨4803848059189068309238411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6405130745585424412317881 4803848059189068309238411)
          ·
            refine ⟨7205772088783602463857617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4803848059189068309238411 7205772088783602463857617)
            ·
              refine ⟨5404329066587701847893213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7205772088783602463857617 5404329066587701847893213)
              ·
                refine ⟨2026623399970388192959955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5404329066587701847893213 2026623399970388192959955)
                ·
                  refine ⟨3039935099955582289439933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2026623399970388192959955 3039935099955582289439933)
                  ·
                    refine ⟨1139975662483343358539975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3039935099955582289439933 1139975662483343358539975)
                    ·
                      rfl

theorem cell22_3330142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_3330142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3330142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3330142 prefixEnd_3330142 := by exact prefixLift 3330142
  have htrace : WordTrace (prefixWord ++ tailWord_3330142) baseStart_3330142 baseEnd_3330142 := by
    simpa [prefixWord, tailWord_3330142, baseEnd_3330142] using wordTrace_append hprefix tailTrace_3330142
  have hstable : (prefixWord ++ tailWord_3330142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3330142).length < 2 ^ (prefixWord ++ tailWord_3330142).sum := by decide
  have hdescent : baseEnd_3330142 < baseStart_3330142 := by decide
  rcases family_descends (prefixWord ++ tailWord_3330142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3330147 : List Nat := [1, 1, 1, 5, 1, 1, 4, 2, 1, 5]
def baseStart_3330147 : Nat := 118140960795 + 3330147 * 2 ^ 59
def prefixEnd_3330147 : Nat := 4983230072969 + 3 ^ 40 * 3330147 * 2
def baseEnd_3330147 : Nat := 1139977374085525012164959

theorem tailTrace_3330147 : CollatzResearch.WordTrace tailWord_3330147 prefixEnd_3330147 1139977374085525012164959 := by
  unfold tailWord_3330147
  simp only [CollatzResearch.WordTrace]
  refine ⟨121460439466453637672700695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80973626310969091781800463 121460439466453637672700695)
  ·
    refine ⟨182190659199680456509051043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121460439466453637672700695 182190659199680456509051043)
    ·
      refine ⟨273285988799520684763576565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182190659199680456509051043 273285988799520684763576565)
      ·
        refine ⟨25620561449955064196585303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 273285988799520684763576565 25620561449955064196585303)
        ·
          refine ⟨38430842174932596294877955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25620561449955064196585303 38430842174932596294877955)
          ·
            refine ⟨57646263262398894442316933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38430842174932596294877955 57646263262398894442316933)
            ·
              refine ⟨10808674361699792707934425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57646263262398894442316933 10808674361699792707934425)
              ·
                refine ⟨8106505771274844530950819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10808674361699792707934425 8106505771274844530950819)
                ·
                  refine ⟨12159758656912266796426229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8106505771274844530950819 12159758656912266796426229)
                  ·
                    refine ⟨1139977374085525012164959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12159758656912266796426229 1139977374085525012164959)
                    ·
                      rfl

theorem cell22_3330147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 2, 1, 5].length) (baseStart_3330147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3330147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3330147 prefixEnd_3330147 := by exact prefixLift 3330147
  have htrace : WordTrace (prefixWord ++ tailWord_3330147) baseStart_3330147 baseEnd_3330147 := by
    simpa [prefixWord, tailWord_3330147, baseEnd_3330147] using wordTrace_append hprefix tailTrace_3330147
  have hstable : (prefixWord ++ tailWord_3330147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3330147).length < 2 ^ (prefixWord ++ tailWord_3330147).sum := by decide
  have hdescent : baseEnd_3330147 < baseStart_3330147 := by decide
  rcases family_descends (prefixWord ++ tailWord_3330147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3330149 : List Nat := [1, 3, 1, 3, 2, 2, 1, 5, 4]
def baseStart_3330149 : Nat := 118140960795 + 3330149 * 2 ^ 59
def prefixEnd_3330149 : Nat := 4983230072969 + 3 ^ 40 * 3330149 * 2
def baseEnd_3330149 : Nat := 379992686242132557871651

theorem tailTrace_3330149 : CollatzResearch.WordTrace tailWord_3330149 prefixEnd_3330149 379992686242132557871651 := by
  unfold tailWord_3330149
  simp only [CollatzResearch.WordTrace]
  refine ⟨121460512412446392014273501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80973674941630928009515667 121460512412446392014273501)
  ·
    refine ⟨45547692154667397005352563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121460512412446392014273501 45547692154667397005352563)
    ·
      refine ⟨68321538232001095508028845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45547692154667397005352563 68321538232001095508028845)
      ·
        refine ⟨25620576837000410815510817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68321538232001095508028845 25620576837000410815510817)
        ·
          refine ⟨19215432627750308111633113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25620576837000410815510817 19215432627750308111633113)
          ·
            refine ⟨14411574470812731083724835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19215432627750308111633113 14411574470812731083724835)
            ·
              refine ⟨21617361706219096625587253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14411574470812731083724835 21617361706219096625587253)
              ·
                refine ⟨2026627659958040308648805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21617361706219096625587253 2026627659958040308648805)
                ·
                  refine ⟨379992686242132557871651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2026627659958040308648805 379992686242132557871651)
                  ·
                    rfl

theorem cell22_3330149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 5, 4].length) (baseStart_3330149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3330149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3330149 prefixEnd_3330149 := by exact prefixLift 3330149
  have htrace : WordTrace (prefixWord ++ tailWord_3330149) baseStart_3330149 baseEnd_3330149 := by
    simpa [prefixWord, tailWord_3330149, baseEnd_3330149] using wordTrace_append hprefix tailTrace_3330149
  have hstable : (prefixWord ++ tailWord_3330149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3330149).length < 2 ^ (prefixWord ++ tailWord_3330149).sum := by decide
  have hdescent : baseEnd_3330149 < baseStart_3330149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3330149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3330166 : List Nat := [5, 1, 1, 2, 1, 2, 2, 4, 4]
def baseStart_3330166 : Nat := 118140960795 + 3330166 * 2 ^ 59
def prefixEnd_3330166 : Nat := 4983230072969 + 3 ^ 40 * 3330166 * 2
def baseEnd_3330166 : Nat := 379994626057938431979967

theorem tailTrace_3330166 : CollatzResearch.WordTrace tailWord_3330166 prefixEnd_3330166 379994626057938431979967 := by
  unfold tailWord_3330166
  simp only [CollatzResearch.WordTrace]
  refine ⟨7591320778336550244852647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80974088302256535945094901 7591320778336550244852647)
  ·
    refine ⟨11386981167504825367278971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7591320778336550244852647 11386981167504825367278971)
    ·
      refine ⟨17080471751257238050918457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11386981167504825367278971 17080471751257238050918457)
      ·
        refine ⟨12810353813442928538188843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17080471751257238050918457 12810353813442928538188843)
        ·
          refine ⟨19215530720164392807283265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12810353813442928538188843 19215530720164392807283265)
          ·
            refine ⟨14411648040123294605462449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19215530720164392807283265 14411648040123294605462449)
            ·
              refine ⟨10808736030092470954096837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14411648040123294605462449 10808736030092470954096837)
              ·
                refine ⟨2026638005642338303893157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10808736030092470954096837 2026638005642338303893157)
                ·
                  refine ⟨379994626057938431979967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2026638005642338303893157 379994626057938431979967)
                  ·
                    rfl

theorem cell22_3330166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 4, 4].length) (baseStart_3330166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3330166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3330166 prefixEnd_3330166 := by exact prefixLift 3330166
  have htrace : WordTrace (prefixWord ++ tailWord_3330166) baseStart_3330166 baseEnd_3330166 := by
    simpa [prefixWord, tailWord_3330166, baseEnd_3330166] using wordTrace_append hprefix tailTrace_3330166
  have hstable : (prefixWord ++ tailWord_3330166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3330166).length < 2 ^ (prefixWord ++ tailWord_3330166).sum := by decide
  have hdescent : baseEnd_3330166 < baseStart_3330166 := by decide
  rcases family_descends (prefixWord ++ tailWord_3330166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3330237 : List Nat := [1, 4, 1, 2, 1, 1, 1, 3, 1, 7]
def baseStart_3330237 : Nat := 118140960795 + 3330237 * 2 ^ 59
def prefixEnd_3330237 : Nat := 4983230072969 + 3 ^ 40 * 3330237 * 2
def baseEnd_3330237 : Nat := 1140008182924794777414683

theorem tailTrace_3330237 : CollatzResearch.WordTrace tailWord_3330237 prefixEnd_3330237 1140008182924794777414683 := by
  unfold tailWord_3330237
  simp only [CollatzResearch.WordTrace]
  refine ⟨121463722036127583043476965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80975814690751722028984643 121463722036127583043476965)
  ·
    refine ⟨22774447881773921820651931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121463722036127583043476965 22774447881773921820651931)
    ·
      refine ⟨34161671822660882730977897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22774447881773921820651931 34161671822660882730977897)
      ·
        refine ⟨25621253866995662048233423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34161671822660882730977897 25621253866995662048233423)
        ·
          refine ⟨38431880800493493072350135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25621253866995662048233423 38431880800493493072350135)
          ·
            refine ⟨57647821200740239608525203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38431880800493493072350135 57647821200740239608525203)
            ·
              refine ⟨86471731801110359412787805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57647821200740239608525203 86471731801110359412787805)
              ·
                refine ⟨32426899425416384779795427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86471731801110359412787805 32426899425416384779795427)
                ·
                  refine ⟨48640349138124577169693141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32426899425416384779795427 48640349138124577169693141)
                  ·
                    refine ⟨1140008182924794777414683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48640349138124577169693141 1140008182924794777414683)
                    ·
                      rfl

theorem cell22_3330237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 7].length) (baseStart_3330237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3330237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3330237 prefixEnd_3330237 := by exact prefixLift 3330237
  have htrace : WordTrace (prefixWord ++ tailWord_3330237) baseStart_3330237 baseEnd_3330237 := by
    simpa [prefixWord, tailWord_3330237, baseEnd_3330237] using wordTrace_append hprefix tailTrace_3330237
  have hstable : (prefixWord ++ tailWord_3330237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3330237).length < 2 ^ (prefixWord ++ tailWord_3330237).sum := by decide
  have hdescent : baseEnd_3330237 < baseStart_3330237 := by decide
  rcases family_descends (prefixWord ++ tailWord_3330237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3330333 : List Nat := [1, 4, 2, 3, 2, 1, 1, 1, 4, 3]
def baseStart_3330333 : Nat := 118140960795 + 3330333 * 2 ^ 59
def prefixEnd_3330333 : Nat := 4983230072969 + 3 ^ 40 * 3330333 * 2
def baseEnd_3330333 : Nat := 1140041045686682527014389

theorem tailTrace_3330333 : CollatzResearch.WordTrace tailWord_3330333 prefixEnd_3330333 1140041045686682527014389 := by
  unfold tailWord_3330333
  simp only [CollatzResearch.WordTrace]
  refine ⟨121467223443779791438971653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80978148962519860959314435 121467223443779791438971653)
  ·
    refine ⟨22775104395708710894807185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121467223443779791438971653 22775104395708710894807185)
    ·
      refine ⟨17081328296781533171105389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22775104395708710894807185 17081328296781533171105389)
      ·
        refine ⟨6405498111293074939164521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17081328296781533171105389 6405498111293074939164521)
        ·
          refine ⟨4804123583469806204373391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6405498111293074939164521 4804123583469806204373391)
          ·
            refine ⟨7206185375204709306560087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4804123583469806204373391 7206185375204709306560087)
            ·
              refine ⟨10809278062807063959840131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7206185375204709306560087 10809278062807063959840131)
              ·
                refine ⟨16213917094210595939760197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10809278062807063959840131 16213917094210595939760197)
                ·
                  refine ⟨3040109455164486738705037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16213917094210595939760197 3040109455164486738705037)
                  ·
                    refine ⟨1140041045686682527014389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3040109455164486738705037 1140041045686682527014389)
                    ·
                      rfl

theorem cell22_3330333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 1, 4, 3].length) (baseStart_3330333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3330333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3330333 prefixEnd_3330333 := by exact prefixLift 3330333
  have htrace : WordTrace (prefixWord ++ tailWord_3330333) baseStart_3330333 baseEnd_3330333 := by
    simpa [prefixWord, tailWord_3330333, baseEnd_3330333] using wordTrace_append hprefix tailTrace_3330333
  have hstable : (prefixWord ++ tailWord_3330333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3330333).length < 2 ^ (prefixWord ++ tailWord_3330333).sum := by decide
  have hdescent : baseEnd_3330333 < baseStart_3330333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3330333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3330350 : List Nat := [4, 1, 3, 3, 1, 2, 1, 1, 1, 5]
def baseStart_3330350 : Nat := 118140960795 + 3330350 * 2 ^ 59
def prefixEnd_3330350 : Nat := 4983230072969 + 3 ^ 40 * 3330350 * 2
def baseEnd_3330350 : Nat := 1140046865134100149339337

theorem tailTrace_3330350 : CollatzResearch.WordTrace tailWord_3330350 prefixEnd_3330350 1140046865134100149339337 := by
  unfold tailWord_3330350
  simp only [CollatzResearch.WordTrace]
  refine ⟨15183480435589775417792563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80978562323145468894893669 15183480435589775417792563)
  ·
    refine ⟨22775220653384663126688845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15183480435589775417792563 22775220653384663126688845)
    ·
      refine ⟨8540707745019248672508317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22775220653384663126688845 8540707745019248672508317)
      ·
        refine ⟨3202765404382218252190619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8540707745019248672508317 3202765404382218252190619)
        ·
          refine ⟨4804148106573327378285929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3202765404382218252190619 4804148106573327378285929)
          ·
            refine ⟨3603111079929995533714447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4804148106573327378285929 3603111079929995533714447)
            ·
              refine ⟨5404666619894993300571671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3603111079929995533714447 5404666619894993300571671)
              ·
                refine ⟨8106999929842489950857507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5404666619894993300571671 8106999929842489950857507)
                ·
                  refine ⟨12160499894763734926286261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8106999929842489950857507 12160499894763734926286261)
                  ·
                    refine ⟨1140046865134100149339337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12160499894763734926286261 1140046865134100149339337)
                    ·
                      rfl

theorem cell22_3330350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_3330350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3330350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3330350 prefixEnd_3330350 := by exact prefixLift 3330350
  have htrace : WordTrace (prefixWord ++ tailWord_3330350) baseStart_3330350 baseEnd_3330350 := by
    simpa [prefixWord, tailWord_3330350, baseEnd_3330350] using wordTrace_append hprefix tailTrace_3330350
  have hstable : (prefixWord ++ tailWord_3330350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3330350).length < 2 ^ (prefixWord ++ tailWord_3330350).sum := by decide
  have hdescent : baseEnd_3330350 < baseStart_3330350 := by decide
  rcases family_descends (prefixWord ++ tailWord_3330350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3330408 : List Nat := [2, 1, 4, 2, 2, 1, 4, 1, 5]
def baseStart_3330408 : Nat := 118140960795 + 3330408 * 2 ^ 59
def prefixEnd_3330408 : Nat := 4983230072969 + 3 ^ 40 * 3330408 * 2
def baseEnd_3330408 : Nat := 380022239906469110463053

theorem tailTrace_3330408 : CollatzResearch.WordTrace tailWord_3330408 prefixEnd_3330408 380022239906469110463053 := by
  unfold tailWord_3330408
  simp only [CollatzResearch.WordTrace]
  refine ⟨60734979459254039623975939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80979972612338719498634585 60734979459254039623975939)
  ·
    refine ⟨91102469188881059435963909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60734979459254039623975939 91102469188881059435963909)
    ·
      refine ⟨17081712972915198644243233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91102469188881059435963909 17081712972915198644243233)
      ·
        refine ⟨12811284729686398983182425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17081712972915198644243233 12811284729686398983182425)
        ·
          refine ⟨9608463547264799237386819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12811284729686398983182425 9608463547264799237386819)
          ·
            refine ⟨14412695320897198856080229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9608463547264799237386819 14412695320897198856080229)
            ·
              refine ⟨2702380372668224785515043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14412695320897198856080229 2702380372668224785515043)
              ·
                refine ⟨4053570559002337178272565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2702380372668224785515043 4053570559002337178272565)
                ·
                  refine ⟨380022239906469110463053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4053570559002337178272565 380022239906469110463053)
                  ·
                    rfl

theorem cell22_3330408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 4, 1, 5].length) (baseStart_3330408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3330408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3330408 prefixEnd_3330408 := by exact prefixLift 3330408
  have htrace : WordTrace (prefixWord ++ tailWord_3330408) baseStart_3330408 baseEnd_3330408 := by
    simpa [prefixWord, tailWord_3330408, baseEnd_3330408] using wordTrace_append hprefix tailTrace_3330408
  have hstable : (prefixWord ++ tailWord_3330408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3330408).length < 2 ^ (prefixWord ++ tailWord_3330408).sum := by decide
  have hdescent : baseEnd_3330408 < baseStart_3330408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3330408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3330466 : List Nat := [3, 3, 1, 2, 1, 1, 2, 2, 1, 6]
def baseStart_3330466 : Nat := 118140960795 + 3330466 * 2 ^ 59
def prefixEnd_3330466 : Nat := 4983230072969 + 3 ^ 40 * 3330466 * 2
def baseEnd_3330466 : Nat := 1140086574304714513438981

theorem tailTrace_3330466 : CollatzResearch.WordTrace tailWord_3330466 prefixEnd_3330466 1140086574304714513438981 := by
  unfold tailWord_3330466
  simp only [CollatzResearch.WordTrace]
  refine ⟨30368018588074488788390813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80981382901531970102375501 30368018588074488788390813)
  ·
    refine ⟨11388006970527933295646555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30368018588074488788390813 11388006970527933295646555)
    ·
      refine ⟨17082010455791899943469833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11388006970527933295646555 17082010455791899943469833)
      ·
        refine ⟨12811507841843924957602375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17082010455791899943469833 12811507841843924957602375)
        ·
          refine ⟨19217261762765887436403563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12811507841843924957602375 19217261762765887436403563)
          ·
            refine ⟨28825892644148831154605345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19217261762765887436403563 28825892644148831154605345)
            ·
              refine ⟨21619419483111623365954009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28825892644148831154605345 21619419483111623365954009)
              ·
                refine ⟨16214564612333717524465507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21619419483111623365954009 16214564612333717524465507)
                ·
                  refine ⟨24321846918500576286698261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16214564612333717524465507 24321846918500576286698261)
                  ·
                    refine ⟨1140086574304714513438981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24321846918500576286698261 1140086574304714513438981)
                    ·
                      rfl

theorem cell22_3330466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_3330466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3330466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3330466 prefixEnd_3330466 := by exact prefixLift 3330466
  have htrace : WordTrace (prefixWord ++ tailWord_3330466) baseStart_3330466 baseEnd_3330466 := by
    simpa [prefixWord, tailWord_3330466, baseEnd_3330466] using wordTrace_append hprefix tailTrace_3330466
  have hstable : (prefixWord ++ tailWord_3330466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3330466).length < 2 ^ (prefixWord ++ tailWord_3330466).sum := by decide
  have hdescent : baseEnd_3330466 < baseStart_3330466 := by decide
  rcases family_descends (prefixWord ++ tailWord_3330466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3330468 : List Nat := [2, 3, 1, 2, 1, 1, 4, 3, 2, 3]
def baseStart_3330468 : Nat := 118140960795 + 3330468 * 2 ^ 59
def prefixEnd_3330468 : Nat := 4983230072969 + 3 ^ 40 * 3330468 * 2
def baseEnd_3330468 : Nat := 1140087258945587174888975

theorem tailTrace_3330468 : CollatzResearch.WordTrace tailWord_3330468 prefixEnd_3330468 1140087258945587174888975 := by
  unfold tailWord_3330468
  simp only [CollatzResearch.WordTrace]
  refine ⟨60736073649145354747568029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80981431532193806330090705 60736073649145354747568029)
  ·
    refine ⟨22776027618429508030338011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60736073649145354747568029 22776027618429508030338011)
    ·
      refine ⟨34164041427644262045507017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22776027618429508030338011 34164041427644262045507017)
      ·
        refine ⟨25623031070733196534130263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34164041427644262045507017 25623031070733196534130263)
        ·
          refine ⟨38434546606099794801195395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25623031070733196534130263 38434546606099794801195395)
          ·
            refine ⟨57651819909149692201793093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38434546606099794801195395 57651819909149692201793093)
            ·
              refine ⟨10809716232965567287836205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57651819909149692201793093 10809716232965567287836205)
              ·
                refine ⟨4053643587362087732938577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10809716232965567287836205 4053643587362087732938577)
                ·
                  refine ⟨3040232690521565799703933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4053643587362087732938577 3040232690521565799703933)
                  ·
                    refine ⟨1140087258945587174888975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3040232690521565799703933 1140087258945587174888975)
                    ·
                      rfl

theorem cell22_3330468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 3, 2, 3].length) (baseStart_3330468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3330468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3330468 prefixEnd_3330468 := by exact prefixLift 3330468
  have htrace : WordTrace (prefixWord ++ tailWord_3330468) baseStart_3330468 baseEnd_3330468 := by
    simpa [prefixWord, tailWord_3330468, baseEnd_3330468] using wordTrace_append hprefix tailTrace_3330468
  have hstable : (prefixWord ++ tailWord_3330468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3330468).length < 2 ^ (prefixWord ++ tailWord_3330468).sum := by decide
  have hdescent : baseEnd_3330468 < baseStart_3330468 := by decide
  rcases family_descends (prefixWord ++ tailWord_3330468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3330496 : List Nat := [2, 1, 1, 2, 3, 1, 1, 1, 7, 3]
def baseStart_3330496 : Nat := 118140960795 + 3330496 * 2 ^ 59
def prefixEnd_3330496 : Nat := 4983230072969 + 3 ^ 40 * 3330496 * 2
def baseEnd_3330496 : Nat := 1140096843917804435188889

theorem tailTrace_3330496 : CollatzResearch.WordTrace tailWord_3330496 prefixEnd_3330496 1140096843917804435188889 := by
  unfold tailWord_3330496
  simp only [CollatzResearch.WordTrace]
  refine ⟨60736584271094635138577671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80982112361459513518103561 60736584271094635138577671)
  ·
    refine ⟨91104876406641952707866507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60736584271094635138577671 91104876406641952707866507)
    ·
      refine ⟨136657314609962929061799761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91104876406641952707866507 136657314609962929061799761)
      ·
        refine ⟨102492985957472196796349821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136657314609962929061799761 102492985957472196796349821)
        ·
          refine ⟨38434869734052073798631183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102492985957472196796349821 38434869734052073798631183)
          ·
            refine ⟨57652304601078110697946775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38434869734052073798631183 57652304601078110697946775)
            ·
              refine ⟨86478456901617166046920163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57652304601078110697946775 86478456901617166046920163)
              ·
                refine ⟨129717685352425749070380245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86478456901617166046920163 129717685352425749070380245)
                ·
                  refine ⟨3040258250447478493837037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 129717685352425749070380245 3040258250447478493837037)
                  ·
                    refine ⟨1140096843917804435188889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3040258250447478493837037 1140096843917804435188889)
                    ·
                      rfl

theorem cell22_3330496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 7, 3].length) (baseStart_3330496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3330496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3330496 prefixEnd_3330496 := by exact prefixLift 3330496
  have htrace : WordTrace (prefixWord ++ tailWord_3330496) baseStart_3330496 baseEnd_3330496 := by
    simpa [prefixWord, tailWord_3330496, baseEnd_3330496] using wordTrace_append hprefix tailTrace_3330496
  have hstable : (prefixWord ++ tailWord_3330496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3330496).length < 2 ^ (prefixWord ++ tailWord_3330496).sum := by decide
  have hdescent : baseEnd_3330496 < baseStart_3330496 := by decide
  rcases family_descends (prefixWord ++ tailWord_3330496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3330556 : List Nat := [2, 2, 2, 1, 2, 1, 1, 2, 5, 4]
def baseStart_3330556 : Nat := 118140960795 + 3330556 * 2 ^ 59
def prefixEnd_3330556 : Nat := 4983230072969 + 3 ^ 40 * 3330556 * 2
def baseEnd_3330556 : Nat := 1140117383143984278688705

theorem tailTrace_3330556 : CollatzResearch.WordTrace tailWord_3330556 prefixEnd_3330556 1140117383143984278688705 := by
  unfold tailWord_3330556
  simp only [CollatzResearch.WordTrace]
  refine ⟨60737678460985950262169761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80983571281314600349559681 60737678460985950262169761)
  ·
    refine ⟨45553258845739462696627321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60737678460985950262169761 45553258845739462696627321)
    ·
      refine ⟨34164944134304597022470491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45553258845739462696627321 34164944134304597022470491)
      ·
        refine ⟨51247416201456895533705737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34164944134304597022470491 51247416201456895533705737)
        ·
          refine ⟨38435562151092671650279303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51247416201456895533705737 38435562151092671650279303)
          ·
            refine ⟨57653343226639007475418955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38435562151092671650279303 57653343226639007475418955)
            ·
              refine ⟨86480014839958511213128433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57653343226639007475418955 86480014839958511213128433)
              ·
                refine ⟨64860011129968883409846325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86480014839958511213128433 64860011129968883409846325)
                ·
                  refine ⟨6080626043434582819673093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64860011129968883409846325 6080626043434582819673093)
                  ·
                    refine ⟨1140117383143984278688705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6080626043434582819673093 1140117383143984278688705)
                    ·
                      rfl

theorem cell22_3330556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 5, 4].length) (baseStart_3330556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3330556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3330556 prefixEnd_3330556 := by exact prefixLift 3330556
  have htrace : WordTrace (prefixWord ++ tailWord_3330556) baseStart_3330556 baseEnd_3330556 := by
    simpa [prefixWord, tailWord_3330556, baseEnd_3330556] using wordTrace_append hprefix tailTrace_3330556
  have hstable : (prefixWord ++ tailWord_3330556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3330556).length < 2 ^ (prefixWord ++ tailWord_3330556).sum := by decide
  have hdescent : baseEnd_3330556 < baseStart_3330556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3330556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3330564 : List Nat := [2, 3, 2, 3, 1, 2, 3, 2, 1, 3]
def baseStart_3330564 : Nat := 118140960795 + 3330564 * 2 ^ 59
def prefixEnd_3330564 : Nat := 4983230072969 + 3 ^ 40 * 3330564 * 2
def baseEnd_3330564 : Nat := 1140120121707474924488681

theorem tailTrace_3330564 : CollatzResearch.WordTrace tailWord_3330564 prefixEnd_3330564 1140120121707474924488681 := by
  unfold tailWord_3330564
  simp only [CollatzResearch.WordTrace]
  refine ⟨60737824352971458945315373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80983765803961945260420497 60737824352971458945315373)
  ·
    refine ⟨22776684132364297104493265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60737824352971458945315373 22776684132364297104493265)
    ·
      refine ⟨17082513099273222828369949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22776684132364297104493265 17082513099273222828369949)
      ·
        refine ⟨6405942412227458560638731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17082513099273222828369949 6405942412227458560638731)
        ·
          refine ⟨9608913618341187840958097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6405942412227458560638731 9608913618341187840958097)
          ·
            refine ⟨7206685213755890880718573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9608913618341187840958097 7206685213755890880718573)
            ·
              refine ⟨2702506955158459080269465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7206685213755890880718573 2702506955158459080269465)
              ·
                refine ⟨2026880216368844310202099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2702506955158459080269465 2026880216368844310202099)
                ·
                  refine ⟨3040320324553266465303149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2026880216368844310202099 3040320324553266465303149)
                  ·
                    refine ⟨1140120121707474924488681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3040320324553266465303149 1140120121707474924488681)
                    ·
                      rfl

theorem cell22_3330564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 3, 2, 1, 3].length) (baseStart_3330564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3330564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3330564 prefixEnd_3330564 := by exact prefixLift 3330564
  have htrace : WordTrace (prefixWord ++ tailWord_3330564) baseStart_3330564 baseEnd_3330564 := by
    simpa [prefixWord, tailWord_3330564, baseEnd_3330564] using wordTrace_append hprefix tailTrace_3330564
  have hstable : (prefixWord ++ tailWord_3330564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3330564).length < 2 ^ (prefixWord ++ tailWord_3330564).sum := by decide
  have hdescent : baseEnd_3330564 < baseStart_3330564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3330564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3330618 : List Nat := [3, 1, 1, 1, 3, 3, 2, 2, 2, 4]
def baseStart_3330618 : Nat := 118140960795 + 3330618 * 2 ^ 59
def prefixEnd_3330618 : Nat := 4983230072969 + 3 ^ 40 * 3330618 * 2
def baseEnd_3330618 : Nat := 1140138607011036783638515

theorem tailTrace_3330618 : CollatzResearch.WordTrace tailWord_3330618 prefixEnd_3330618 1140138607011036783638515 := by
  unfold tailWord_3330618
  simp only [CollatzResearch.WordTrace]
  refine ⟨30369404561936821278274127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80985078831831523408731005 30369404561936821278274127)
  ·
    refine ⟨45554106842905231917411191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30369404561936821278274127 45554106842905231917411191)
    ·
      refine ⟨68331160264357847876116787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45554106842905231917411191 68331160264357847876116787)
      ·
        refine ⟨102496740396536771814175181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68331160264357847876116787 102496740396536771814175181)
        ·
          refine ⟨38436277648701289430315693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102496740396536771814175181 38436277648701289430315693)
          ·
            refine ⟨14413604118262983536368385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38436277648701289430315693 14413604118262983536368385)
            ·
              refine ⟨10810203088697237652276289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14413604118262983536368385 10810203088697237652276289)
              ·
                refine ⟨8107652316522928239207217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10810203088697237652276289 8107652316522928239207217)
                ·
                  refine ⟨6080739237392196179405413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8107652316522928239207217 6080739237392196179405413)
                  ·
                    refine ⟨1140138607011036783638515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6080739237392196179405413 1140138607011036783638515)
                    ·
                      rfl

theorem cell22_3330618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 2, 2, 4].length) (baseStart_3330618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3330618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3330618 prefixEnd_3330618 := by exact prefixLift 3330618
  have htrace : WordTrace (prefixWord ++ tailWord_3330618) baseStart_3330618 baseEnd_3330618 := by
    simpa [prefixWord, tailWord_3330618, baseEnd_3330618] using wordTrace_append hprefix tailTrace_3330618
  have hstable : (prefixWord ++ tailWord_3330618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3330618).length < 2 ^ (prefixWord ++ tailWord_3330618).sum := by decide
  have hdescent : baseEnd_3330618 < baseStart_3330618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3330618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3330620 : List Nat := [2, 2, 2, 2, 3, 1, 1, 4, 2, 3]
def baseStart_3330620 : Nat := 118140960795 + 3330620 * 2 ^ 59
def prefixEnd_3330620 : Nat := 4983230072969 + 3 ^ 40 * 3330620 * 2
def baseEnd_3330620 : Nat := 1140139291651909445088509

theorem tailTrace_3330620 : CollatzResearch.WordTrace tailWord_3330620 prefixEnd_3330620 1140139291651909445088509 := by
  unfold tailWord_3330620
  simp only [CollatzResearch.WordTrace]
  refine ⟨60738845596870019727334657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80985127462493359636446209 60738845596870019727334657)
  ·
    refine ⟨45554134197652514795500993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60738845596870019727334657 45554134197652514795500993)
    ·
      refine ⟨34165600648239386096625745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45554134197652514795500993 34165600648239386096625745)
      ·
        refine ⟨25624200486179539572469309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34165600648239386096625745 25624200486179539572469309)
        ·
          refine ⟨9609075182317327339675991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25624200486179539572469309 9609075182317327339675991)
          ·
            refine ⟨14413612773475991009513987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9609075182317327339675991 14413612773475991009513987)
            ·
              refine ⟨21620419160213986514270981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14413612773475991009513987 21620419160213986514270981)
              ·
                refine ⟨4053828592540122471425809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21620419160213986514270981 4053828592540122471425809)
                ·
                  refine ⟨3040371444405091853569357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4053828592540122471425809 3040371444405091853569357)
                  ·
                    refine ⟨1140139291651909445088509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3040371444405091853569357 1140139291651909445088509)
                    ·
                      rfl

theorem cell22_3330620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 4, 2, 3].length) (baseStart_3330620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3330620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3330620 prefixEnd_3330620 := by exact prefixLift 3330620
  have htrace : WordTrace (prefixWord ++ tailWord_3330620) baseStart_3330620 baseEnd_3330620 := by
    simpa [prefixWord, tailWord_3330620, baseEnd_3330620] using wordTrace_append hprefix tailTrace_3330620
  have hstable : (prefixWord ++ tailWord_3330620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3330620).length < 2 ^ (prefixWord ++ tailWord_3330620).sum := by decide
  have hdescent : baseEnd_3330620 < baseStart_3330620 := by decide
  rcases family_descends (prefixWord ++ tailWord_3330620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3330637 : List Nat := [1, 6, 1, 1, 2, 1, 2, 3, 2, 3]
def baseStart_3330637 : Nat := 118140960795 + 3330637 * 2 ^ 59
def prefixEnd_3330637 : Nat := 4983230072969 + 3 ^ 40 * 3330637 * 2
def baseEnd_3330637 : Nat := 1140145111099327067413457

theorem tailTrace_3330637 : CollatzResearch.WordTrace tailWord_3330637 prefixEnd_3330637 1140145111099327067413457 := by
  unfold tailWord_3330637
  simp only [CollatzResearch.WordTrace]
  refine ⟨121478311234678451358038165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80985540823118967572025443 121478311234678451358038165)
  ·
    refine ⟨5694295839125552407408039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 121478311234678451358038165 5694295839125552407408039)
    ·
      refine ⟨8541443758688328611112059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5694295839125552407408039 8541443758688328611112059)
      ·
        refine ⟨12812165638032492916668089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8541443758688328611112059 12812165638032492916668089)
        ·
          refine ⟨9609124228524369687501067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12812165638032492916668089 9609124228524369687501067)
          ·
            refine ⟨14413686342786554531251601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9609124228524369687501067 14413686342786554531251601)
            ·
              refine ⟨10810264757089915898438701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14413686342786554531251601 10810264757089915898438701)
              ·
                refine ⟨4053849283908718461914513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10810264757089915898438701 4053849283908718461914513)
                ·
                  refine ⟨3040386962931538846435885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4053849283908718461914513 3040386962931538846435885)
                  ·
                    refine ⟨1140145111099327067413457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3040386962931538846435885 1140145111099327067413457)
                    ·
                      rfl

theorem cell22_3330637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_3330637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3330637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3330637 prefixEnd_3330637 := by exact prefixLift 3330637
  have htrace : WordTrace (prefixWord ++ tailWord_3330637) baseStart_3330637 baseEnd_3330637 := by
    simpa [prefixWord, tailWord_3330637, baseEnd_3330637] using wordTrace_append hprefix tailTrace_3330637
  have hstable : (prefixWord ++ tailWord_3330637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3330637).length < 2 ^ (prefixWord ++ tailWord_3330637).sum := by decide
  have hdescent : baseEnd_3330637 < baseStart_3330637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3330637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3330648 : List Nat := [2, 1, 2, 2, 1, 2, 3, 1, 5, 3]
def baseStart_3330648 : Nat := 118140960795 + 3330648 * 2 ^ 59
def prefixEnd_3330648 : Nat := 4983230072969 + 3 ^ 40 * 3330648 * 2
def baseEnd_3330648 : Nat := 1140148876624126705388423

theorem tailTrace_3330648 : CollatzResearch.WordTrace tailWord_3330648 prefixEnd_3330648 1140148876624126705388423 := by
  unfold tailWord_3330648
  simp only [CollatzResearch.WordTrace]
  refine ⟨60739356218819300118344299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80985808291759066824459065 60739356218819300118344299)
  ·
    refine ⟨91109034328228950177516449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60739356218819300118344299 91109034328228950177516449)
    ·
      refine ⟨68331775746171712633137337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91109034328228950177516449 68331775746171712633137337)
      ·
        refine ⟨51248831809628784474853003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68331775746171712633137337 51248831809628784474853003)
        ·
          refine ⟨76873247714443176712279505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51248831809628784474853003 76873247714443176712279505)
          ·
            refine ⟨57654935785832382534209629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76873247714443176712279505 57654935785832382534209629)
            ·
              refine ⟨21620600919687143450328611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57654935785832382534209629 21620600919687143450328611)
              ·
                refine ⟨32430901379530715175492917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21620600919687143450328611 32430901379530715175492917)
                ·
                  refine ⟨3040397004331004547702461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32430901379530715175492917 3040397004331004547702461)
                  ·
                    refine ⟨1140148876624126705388423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3040397004331004547702461 1140148876624126705388423)
                    ·
                      rfl

theorem cell22_3330648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 5, 3].length) (baseStart_3330648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3330648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3330648 prefixEnd_3330648 := by exact prefixLift 3330648
  have htrace : WordTrace (prefixWord ++ tailWord_3330648) baseStart_3330648 baseEnd_3330648 := by
    simpa [prefixWord, tailWord_3330648, baseEnd_3330648] using wordTrace_append hprefix tailTrace_3330648
  have hstable : (prefixWord ++ tailWord_3330648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3330648).length < 2 ^ (prefixWord ++ tailWord_3330648).sum := by decide
  have hdescent : baseEnd_3330648 < baseStart_3330648 := by decide
  rcases family_descends (prefixWord ++ tailWord_3330648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3330652 : List Nat := [2, 2, 4, 1, 3, 2, 1, 1, 2, 4]
def baseStart_3330652 : Nat := 118140960795 + 3330652 * 2 ^ 59
def prefixEnd_3330652 : Nat := 4983230072969 + 3 ^ 40 * 3330652 * 2
def baseEnd_3330652 : Nat := 1140150245905872028288411

theorem tailTrace_3330652 : CollatzResearch.WordTrace tailWord_3330652 prefixEnd_3330652 1140150245905872028288411 := by
  unfold tailWord_3330652
  simp only [CollatzResearch.WordTrace]
  refine ⟨60739429164812054459917105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80985905553082739279889473 60739429164812054459917105)
  ·
    refine ⟨45554571873609040844937829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60739429164812054459917105 45554571873609040844937829)
    ·
      refine ⟨8541482226301695158425843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45554571873609040844937829 8541482226301695158425843)
      ·
        refine ⟨12812223339452542737638765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8541482226301695158425843 12812223339452542737638765)
        ·
          refine ⟨4804583752294703526614537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12812223339452542737638765 4804583752294703526614537)
          ·
            refine ⟨3603437814221027644960903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4804583752294703526614537 3603437814221027644960903)
            ·
              refine ⟨5405156721331541467441355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3603437814221027644960903 5405156721331541467441355)
              ·
                refine ⟨8107735081997312201162033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5405156721331541467441355 8107735081997312201162033)
                ·
                  refine ⟨6080801311497984150871525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8107735081997312201162033 6080801311497984150871525)
                  ·
                    refine ⟨1140150245905872028288411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6080801311497984150871525 1140150245905872028288411)
                    ·
                      rfl

theorem cell22_3330652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_3330652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3330652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3330652 prefixEnd_3330652 := by exact prefixLift 3330652
  have htrace : WordTrace (prefixWord ++ tailWord_3330652) baseStart_3330652 baseEnd_3330652 := by
    simpa [prefixWord, tailWord_3330652, baseEnd_3330652] using wordTrace_append hprefix tailTrace_3330652
  have hstable : (prefixWord ++ tailWord_3330652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3330652).length < 2 ^ (prefixWord ++ tailWord_3330652).sum := by decide
  have hdescent : baseEnd_3330652 < baseStart_3330652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3330652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3330693 : List Nat := [1, 3, 1, 1, 4, 2, 2, 1, 2, 5]
def baseStart_3330693 : Nat := 118140960795 + 3330693 * 2 ^ 59
def prefixEnd_3330693 : Nat := 4983230072969 + 3 ^ 40 * 3330693 * 2
def baseEnd_3330693 : Nat := 1140164281043761588013285

theorem tailTrace_3330693 : CollatzResearch.WordTrace tailWord_3330693 prefixEnd_3330693 1140164281043761588013285 := by
  unfold tailWord_3330693
  simp only [CollatzResearch.WordTrace]
  refine ⟨121480353722475572922076733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80986902481650381948051155 121480353722475572922076733)
  ·
    refine ⟨45555132645928339845778775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121480353722475572922076733 45555132645928339845778775)
    ·
      refine ⟨68332698968892509768668163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45555132645928339845778775 68332698968892509768668163)
      ·
        refine ⟨102499048453338764653002245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68332698968892509768668163 102499048453338764653002245)
        ·
          refine ⟨19218571585001018372437921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102499048453338764653002245 19218571585001018372437921)
          ·
            refine ⟨14413928688750763779328441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19218571585001018372437921 14413928688750763779328441)
            ·
              refine ⟨10810446516563072834496331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14413928688750763779328441 10810446516563072834496331)
              ·
                refine ⟨16215669774844609251744497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10810446516563072834496331 16215669774844609251744497)
                ·
                  refine ⟨12161752331133456938808373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16215669774844609251744497 12161752331133456938808373)
                  ·
                    refine ⟨1140164281043761588013285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12161752331133456938808373 1140164281043761588013285)
                    ·
                      rfl

theorem cell22_3330693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 1, 2, 5].length) (baseStart_3330693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3330693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3330693 prefixEnd_3330693 := by exact prefixLift 3330693
  have htrace : WordTrace (prefixWord ++ tailWord_3330693) baseStart_3330693 baseEnd_3330693 := by
    simpa [prefixWord, tailWord_3330693, baseEnd_3330693] using wordTrace_append hprefix tailTrace_3330693
  have hstable : (prefixWord ++ tailWord_3330693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3330693).length < 2 ^ (prefixWord ++ tailWord_3330693).sum := by decide
  have hdescent : baseEnd_3330693 < baseStart_3330693 := by decide
  rcases family_descends (prefixWord ++ tailWord_3330693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3330695 : List Nat := [1, 1, 4, 2, 1, 2, 5, 1, 5]
def baseStart_3330695 : Nat := 118140960795 + 3330695 * 2 ^ 59
def prefixEnd_3330695 : Nat := 4983230072969 + 3 ^ 40 * 3330695 * 2
def baseEnd_3330695 : Nat := 380054988561544749821093

theorem tailTrace_3330695 : CollatzResearch.WordTrace tailWord_3330695 prefixEnd_3330695 380054988561544749821093 := by
  unfold tailWord_3330695
  simp only [CollatzResearch.WordTrace]
  refine ⟨121480426668468327263649539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80986951112312218175766359 121480426668468327263649539)
  ·
    refine ⟨182220640002702490895474309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121480426668468327263649539 182220640002702490895474309)
    ·
      refine ⟨34166370000506717042901433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 182220640002702490895474309 34166370000506717042901433)
      ·
        refine ⟨25624777500380037782176075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34166370000506717042901433 25624777500380037782176075)
        ·
          refine ⟨38437166250570056673264113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25624777500380037782176075 38437166250570056673264113)
          ·
            refine ⟨28827874687927542504948085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38437166250570056673264113 28827874687927542504948085)
            ·
              refine ⟨2702613251993207109838883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28827874687927542504948085 2702613251993207109838883)
              ·
                refine ⟨4053919877989810664758325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2702613251993207109838883 4053919877989810664758325)
                ·
                  refine ⟨380054988561544749821093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4053919877989810664758325 380054988561544749821093)
                  ·
                    rfl

theorem cell22_3330695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 5, 1, 5].length) (baseStart_3330695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3330695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3330695 prefixEnd_3330695 := by exact prefixLift 3330695
  have htrace : WordTrace (prefixWord ++ tailWord_3330695) baseStart_3330695 baseEnd_3330695 := by
    simpa [prefixWord, tailWord_3330695, baseEnd_3330695] using wordTrace_append hprefix tailTrace_3330695
  have hstable : (prefixWord ++ tailWord_3330695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3330695).length < 2 ^ (prefixWord ++ tailWord_3330695).sum := by decide
  have hdescent : baseEnd_3330695 < baseStart_3330695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3330695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3330772 : List Nat := [2, 4, 1, 3, 2, 1, 1, 2, 1, 5]
def baseStart_3330772 : Nat := 118140960795 + 3330772 * 2 ^ 59
def prefixEnd_3330772 : Nat := 4983230072969 + 3 ^ 40 * 3330772 * 2
def baseEnd_3330772 : Nat := 1140191324358231715288043

theorem tailTrace_3330772 : CollatzResearch.WordTrace tailWord_3330772 prefixEnd_3330772 1140191324358231715288043 := by
  unfold tailWord_3330772
  simp only [CollatzResearch.WordTrace]
  refine ⟨60741617544594684707101285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80988823392792912942801713 60741617544594684707101285)
  ·
    refine ⟨11389053289611503382581491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60741617544594684707101285 11389053289611503382581491)
    ·
      refine ⟨17083579934417255073872237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11389053289611503382581491 17083579934417255073872237)
      ·
        refine ⟨6406342475406470652702089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17083579934417255073872237 6406342475406470652702089)
        ·
          refine ⟨4804756856554852989526567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6406342475406470652702089 4804756856554852989526567)
          ·
            refine ⟨7207135284832279484289851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4804756856554852989526567 7207135284832279484289851)
            ·
              refine ⟨10810702927248419226434777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7207135284832279484289851 10810702927248419226434777)
              ·
                refine ⟨8108027195436314419826083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10810702927248419226434777 8108027195436314419826083)
                ·
                  refine ⟨12162040793154471629739125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8108027195436314419826083 12162040793154471629739125)
                  ·
                    refine ⟨1140191324358231715288043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12162040793154471629739125 1140191324358231715288043)
                    ·
                      rfl

theorem cell22_3330772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_3330772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3330772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3330772 prefixEnd_3330772 := by exact prefixLift 3330772
  have htrace : WordTrace (prefixWord ++ tailWord_3330772) baseStart_3330772 baseEnd_3330772 := by
    simpa [prefixWord, tailWord_3330772, baseEnd_3330772] using wordTrace_append hprefix tailTrace_3330772
  have hstable : (prefixWord ++ tailWord_3330772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3330772).length < 2 ^ (prefixWord ++ tailWord_3330772).sum := by decide
  have hdescent : baseEnd_3330772 < baseStart_3330772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3330772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3330800 : List Nat := [2, 1, 1, 1, 3, 1, 4, 3, 3, 3]
def baseStart_3330800 : Nat := 118140960795 + 3330800 * 2 ^ 59
def prefixEnd_3330800 : Nat := 4983230072969 + 3 ^ 40 * 3330800 * 2
def baseEnd_3330800 : Nat := 1140200909330448975587957

theorem tailTrace_3330800 : CollatzResearch.WordTrace tailWord_3330800 prefixEnd_3330800 1140200909330448975587957 := by
  unfold tailWord_3330800
  simp only [CollatzResearch.WordTrace]
  refine ⟨60742128166543965098110927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80989504222058620130814569 60742128166543965098110927)
  ·
    refine ⟨91113192249815947647166391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60742128166543965098110927 91113192249815947647166391)
    ·
      refine ⟨136669788374723921470749587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91113192249815947647166391 136669788374723921470749587)
      ·
        refine ⟨205004682562085882206124381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136669788374723921470749587 205004682562085882206124381)
        ·
          refine ⟨76876755960782205827296643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 205004682562085882206124381 76876755960782205827296643)
          ·
            refine ⟨115315133941173308740944965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76876755960782205827296643 115315133941173308740944965)
            ·
              refine ⟨21621587613969995388927181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115315133941173308740944965 21621587613969995388927181)
              ·
                refine ⟨8108095355238748270847693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21621587613969995388927181 8108095355238748270847693)
                ·
                  refine ⟨3040535758214530601567885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8108095355238748270847693 3040535758214530601567885)
                  ·
                    refine ⟨1140200909330448975587957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3040535758214530601567885 1140200909330448975587957)
                    ·
                      rfl

theorem cell22_3330800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 3, 3, 3].length) (baseStart_3330800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3330800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3330800 prefixEnd_3330800 := by exact prefixLift 3330800
  have htrace : WordTrace (prefixWord ++ tailWord_3330800) baseStart_3330800 baseEnd_3330800 := by
    simpa [prefixWord, tailWord_3330800, baseEnd_3330800] using wordTrace_append hprefix tailTrace_3330800
  have hstable : (prefixWord ++ tailWord_3330800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3330800).length < 2 ^ (prefixWord ++ tailWord_3330800).sum := by decide
  have hdescent : baseEnd_3330800 < baseStart_3330800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3330800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3330828 : List Nat := [2, 2, 1, 2, 2, 1, 1, 1, 3, 7]
def baseStart_3330828 : Nat := 118140960795 + 3330828 * 2 ^ 59
def prefixEnd_3330828 : Nat := 4983230072969 + 3 ^ 40 * 3330828 * 2
def baseEnd_3330828 : Nat := 1140210494302666235887871

theorem tailTrace_3330828 : CollatzResearch.WordTrace tailWord_3330828 prefixEnd_3330828 1140210494302666235887871 := by
  unfold tailWord_3330828
  simp only [CollatzResearch.WordTrace]
  refine ⟨60742638788493245489120569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80990185051324327318827425 60742638788493245489120569)
  ·
    refine ⟨45556979091369934116840427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60742638788493245489120569 45556979091369934116840427)
    ·
      refine ⟨68335468637054901175260641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45556979091369934116840427 68335468637054901175260641)
      ·
        refine ⟨51251601477791175881445481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68335468637054901175260641 51251601477791175881445481)
        ·
          refine ⟨38438701108343381911084111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51251601477791175881445481 38438701108343381911084111)
          ·
            refine ⟨57658051662515072866626167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38438701108343381911084111 57658051662515072866626167)
            ·
              refine ⟨86487077493772609299939251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57658051662515072866626167 86487077493772609299939251)
              ·
                refine ⟨129730616240658913949908877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86487077493772609299939251 129730616240658913949908877)
                ·
                  refine ⟨48648981090247092731215829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 129730616240658913949908877 48648981090247092731215829)
                  ·
                    refine ⟨1140210494302666235887871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48648981090247092731215829 1140210494302666235887871)
                    ·
                      rfl

theorem cell22_3330828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 3, 7].length) (baseStart_3330828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3330828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3330828 prefixEnd_3330828 := by exact prefixLift 3330828
  have htrace : WordTrace (prefixWord ++ tailWord_3330828) baseStart_3330828 baseEnd_3330828 := by
    simpa [prefixWord, tailWord_3330828, baseEnd_3330828] using wordTrace_append hprefix tailTrace_3330828
  have hstable : (prefixWord ++ tailWord_3330828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3330828).length < 2 ^ (prefixWord ++ tailWord_3330828).sum := by decide
  have hdescent : baseEnd_3330828 < baseStart_3330828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3330828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3330847 : List Nat := [1, 1, 2, 4, 2, 4, 1, 2, 5]
def baseStart_3330847 : Nat := 118140960795 + 3330847 * 2 ^ 59
def prefixEnd_3330847 : Nat := 4983230072969 + 3 ^ 40 * 3330847 * 2
def baseEnd_3330847 : Nat := 380072332796985506554271

theorem tailTrace_3330847 : CollatzResearch.WordTrace tailWord_3330847 prefixEnd_3330847 380072332796985506554271 := by
  unfold tailWord_3330847
  simp only [CollatzResearch.WordTrace]
  refine ⟨121485970563917657223182795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80990647042611771482121863 121485970563917657223182795)
  ·
    refine ⟨182228955845876485834774193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121485970563917657223182795 182228955845876485834774193)
    ·
      refine ⟨136671716884407364376080645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182228955845876485834774193 136671716884407364376080645)
      ·
        refine ⟨25625946915826380820515121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136671716884407364376080645 25625946915826380820515121)
        ·
          refine ⟨19219460186869785615386341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25625946915826380820515121 19219460186869785615386341)
          ·
            refine ⟨3603648785038084802884939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19219460186869785615386341 3603648785038084802884939)
            ·
              refine ⟨5405473177557127204327409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3603648785038084802884939 5405473177557127204327409)
              ·
                refine ⟨4054104883167845403245557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5405473177557127204327409 4054104883167845403245557)
                ·
                  refine ⟨380072332796985506554271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4054104883167845403245557 380072332796985506554271)
                  ·
                    rfl

theorem cell22_3330847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 2, 5].length) (baseStart_3330847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3330847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3330847 prefixEnd_3330847 := by exact prefixLift 3330847
  have htrace : WordTrace (prefixWord ++ tailWord_3330847) baseStart_3330847 baseEnd_3330847 := by
    simpa [prefixWord, tailWord_3330847, baseEnd_3330847] using wordTrace_append hprefix tailTrace_3330847
  have hstable : (prefixWord ++ tailWord_3330847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3330847).length < 2 ^ (prefixWord ++ tailWord_3330847).sum := by decide
  have hdescent : baseEnd_3330847 < baseStart_3330847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3330847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3330862 : List Nat := [4, 1, 3, 2, 1, 1, 2, 1, 2, 5]
def baseStart_3330862 : Nat := 118140960795 + 3330862 * 2 ^ 59
def prefixEnd_3330862 : Nat := 4983230072969 + 3 ^ 40 * 3330862 * 2
def baseEnd_3330862 : Nat := 1140222133197501480537767

theorem tailTrace_3330862 : CollatzResearch.WordTrace tailWord_3330862 prefixEnd_3330862 1140222133197501480537767 := by
  unfold tailWord_3330862
  simp only [CollatzResearch.WordTrace]
  refine ⟨15185814707357914348122355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80991011772575543189985893 15185814707357914348122355)
  ·
    refine ⟨22778722061036871522183533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15185814707357914348122355 22778722061036871522183533)
    ·
      refine ⟨8542020772888826820818825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22778722061036871522183533 8542020772888826820818825)
      ·
        refine ⟨6406515579666620115614119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8542020772888826820818825 6406515579666620115614119)
        ·
          refine ⟨9609773369499930173421179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6406515579666620115614119 9609773369499930173421179)
          ·
            refine ⟨14414660054249895260131769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9609773369499930173421179 14414660054249895260131769)
            ·
              refine ⟨10810995040687421445098827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14414660054249895260131769 10810995040687421445098827)
              ·
                refine ⟨16216492561031132167648241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10810995040687421445098827 16216492561031132167648241)
                ·
                  refine ⟨12162369420773349125736181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16216492561031132167648241 12162369420773349125736181)
                  ·
                    refine ⟨1140222133197501480537767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12162369420773349125736181 1140222133197501480537767)
                    ·
                      rfl

theorem cell22_3330862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_3330862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3330862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3330862 prefixEnd_3330862 := by exact prefixLift 3330862
  have htrace : WordTrace (prefixWord ++ tailWord_3330862) baseStart_3330862 baseEnd_3330862 := by
    simpa [prefixWord, tailWord_3330862, baseEnd_3330862] using wordTrace_append hprefix tailTrace_3330862
  have hstable : (prefixWord ++ tailWord_3330862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3330862).length < 2 ^ (prefixWord ++ tailWord_3330862).sum := by decide
  have hdescent : baseEnd_3330862 < baseStart_3330862 := by decide
  rcases family_descends (prefixWord ++ tailWord_3330862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3330905 : List Nat := [1, 2, 1, 2, 2, 4, 1, 1, 4, 4]
def baseStart_3330905 : Nat := 118140960795 + 3330905 * 2 ^ 59
def prefixEnd_3330905 : Nat := 4983230072969 + 3 ^ 40 * 3330905 * 2
def baseEnd_3330905 : Nat := 1140236852976263701712635

theorem tailTrace_3330905 : CollatzResearch.WordTrace tailWord_3330905 prefixEnd_3330905 1140236852976263701712635 := by
  unfold tailWord_3330905
  simp only [CollatzResearch.WordTrace]
  refine ⟨121488085997707533128794169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80992057331805022085862779 121488085997707533128794169)
  ·
    refine ⟨91116064498280649846595627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121488085997707533128794169 91116064498280649846595627)
    ·
      refine ⟨136674096747420974769893441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91116064498280649846595627 136674096747420974769893441)
      ·
        refine ⟨102505572560565731077420081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136674096747420974769893441 102505572560565731077420081)
        ·
          refine ⟨76879179420424298308065061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102505572560565731077420081 76879179420424298308065061)
          ·
            refine ⟨14414846141329555932762199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76879179420424298308065061 14414846141329555932762199)
            ·
              refine ⟨21622269211994333899143299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14414846141329555932762199 21622269211994333899143299)
              ·
                refine ⟨32433403817991500848714949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21622269211994333899143299 32433403817991500848714949)
                ·
                  refine ⟨6081263215873406409134053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32433403817991500848714949 6081263215873406409134053)
                  ·
                    refine ⟨1140236852976263701712635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6081263215873406409134053 1140236852976263701712635)
                    ·
                      rfl

theorem cell22_3330905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 4, 4].length) (baseStart_3330905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3330905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3330905 prefixEnd_3330905 := by exact prefixLift 3330905
  have htrace : WordTrace (prefixWord ++ tailWord_3330905) baseStart_3330905 baseEnd_3330905 := by
    simpa [prefixWord, tailWord_3330905, baseEnd_3330905] using wordTrace_append hprefix tailTrace_3330905
  have hstable : (prefixWord ++ tailWord_3330905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3330905).length < 2 ^ (prefixWord ++ tailWord_3330905).sum := by decide
  have hdescent : baseEnd_3330905 < baseStart_3330905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3330905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3330920 : List Nat := [2, 1, 4, 2, 1, 2, 1, 9]
def baseStart_3330920 : Nat := 118140960795 + 3330920 * 2 ^ 59
def prefixEnd_3330920 : Nat := 4983230072969 + 3 ^ 40 * 3330920 * 2
def baseEnd_3330920 : Nat := 126693554198089851398621

theorem tailTrace_3330920 : CollatzResearch.WordTrace tailWord_3330920 prefixEnd_3330920 126693554198089851398621 := by
  unfold tailWord_3330920
  simp only [CollatzResearch.WordTrace]
  refine ⟨60744316546326595345295107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80992422061768793793726809 60744316546326595345295107)
  ·
    refine ⟨91116474819489893017942661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60744316546326595345295107 91116474819489893017942661)
    ·
      refine ⟨17084339028654354940864249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91116474819489893017942661 17084339028654354940864249)
      ·
        refine ⟨12813254271490766205648187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17084339028654354940864249 12813254271490766205648187)
        ·
          refine ⟨19219881407236149308472281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12813254271490766205648187 19219881407236149308472281)
          ·
            refine ⟨14414911055427111981354211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19219881407236149308472281 14414911055427111981354211)
            ·
              refine ⟨21622366583140667972031317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14414911055427111981354211 21622366583140667972031317)
              ·
                refine ⟨126693554198089851398621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21622366583140667972031317 126693554198089851398621)
                ·
                  rfl

theorem cell22_3330920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 9].length) (baseStart_3330920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3330920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3330920 prefixEnd_3330920 := by exact prefixLift 3330920
  have htrace : WordTrace (prefixWord ++ tailWord_3330920) baseStart_3330920 baseEnd_3330920 := by
    simpa [prefixWord, tailWord_3330920, baseEnd_3330920] using wordTrace_append hprefix tailTrace_3330920
  have hstable : (prefixWord ++ tailWord_3330920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3330920).length < 2 ^ (prefixWord ++ tailWord_3330920).sum := by decide
  have hdescent : baseEnd_3330920 < baseStart_3330920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3330920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331016 : List Nat := [2, 1, 3, 1, 6, 1, 1, 2, 5]
def baseStart_3331016 : Nat := 118140960795 + 3331016 * 2 ^ 59
def prefixEnd_3331016 : Nat := 4983230072969 + 3 ^ 40 * 3331016 * 2
def baseEnd_3331016 : Nat := 380091616848232137395765

theorem tailTrace_3331016 : CollatzResearch.WordTrace tailWord_3331016 prefixEnd_3331016 380091616848232137395765 := by
  unfold tailWord_3331016
  simp only [CollatzResearch.WordTrace]
  refine ⟨60746067250152699543042451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80994756333536932724056601 60746067250152699543042451)
  ·
    refine ⟨91119100875229049314563677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60746067250152699543042451 91119100875229049314563677)
    ·
      refine ⟨34169662828210893492961379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91119100875229049314563677 34169662828210893492961379)
      ·
        refine ⟨51254494242316340239442069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34169662828210893492961379 51254494242316340239442069)
        ·
          refine ⟨2402554417608578448723847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 51254494242316340239442069 2402554417608578448723847)
          ·
            refine ⟨3603831626412867673085771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2402554417608578448723847 3603831626412867673085771)
            ·
              refine ⟨5405747439619301509628657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3603831626412867673085771 5405747439619301509628657)
              ·
                refine ⟨4054310579714476132221493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5405747439619301509628657 4054310579714476132221493)
                ·
                  refine ⟨380091616848232137395765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4054310579714476132221493 380091616848232137395765)
                  ·
                    rfl

theorem cell22_3331016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 2, 5].length) (baseStart_3331016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3331016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3331016 prefixEnd_3331016 := by exact prefixLift 3331016
  have htrace : WordTrace (prefixWord ++ tailWord_3331016) baseStart_3331016 baseEnd_3331016 := by
    simpa [prefixWord, tailWord_3331016, baseEnd_3331016] using wordTrace_append hprefix tailTrace_3331016
  have hstable : (prefixWord ++ tailWord_3331016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331016).length < 2 ^ (prefixWord ++ tailWord_3331016).sum := by decide
  have hdescent : baseEnd_3331016 < baseStart_3331016 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331057 : List Nat := [1, 2, 2, 2, 4, 1, 2, 1, 1, 6]
def baseStart_3331057 : Nat := 118140960795 + 3331057 * 2 ^ 59
def prefixEnd_3331057 : Nat := 4983230072969 + 3 ^ 40 * 3331057 * 2
def baseEnd_3331057 : Nat := 1140288885682585971912169

theorem tailTrace_3331057 : CollatzResearch.WordTrace tailWord_3331057 prefixEnd_3331057 1140288885682585971912169 := by
  unfold tailWord_3331057
  simp only [CollatzResearch.WordTrace]
  refine ⟨121493629893156863088327425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80995753262104575392218283 121493629893156863088327425)
  ·
    refine ⟨91120222419867647316245569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121493629893156863088327425 91120222419867647316245569)
    ·
      refine ⟨68340166814900735487184177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91120222419867647316245569 68340166814900735487184177)
      ·
        refine ⟨51255125111175551615388133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68340166814900735487184177 51255125111175551615388133)
        ·
          refine ⟨9610335958345415927885275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51255125111175551615388133 9610335958345415927885275)
          ·
            refine ⟨14415503937518123891827913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9610335958345415927885275 14415503937518123891827913)
            ·
              refine ⟨10811627953138592918870935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14415503937518123891827913 10811627953138592918870935)
              ·
                refine ⟨16217441929707889378306403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10811627953138592918870935 16217441929707889378306403)
                ·
                  refine ⟨24326162894561834067459605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16217441929707889378306403 24326162894561834067459605)
                  ·
                    refine ⟨1140288885682585971912169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24326162894561834067459605 1140288885682585971912169)
                    ·
                      rfl

theorem cell22_3331057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 1, 1, 6].length) (baseStart_3331057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3331057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3331057 prefixEnd_3331057 := by exact prefixLift 3331057
  have htrace : WordTrace (prefixWord ++ tailWord_3331057) baseStart_3331057 baseEnd_3331057 := by
    simpa [prefixWord, tailWord_3331057, baseEnd_3331057] using wordTrace_append hprefix tailTrace_3331057
  have hstable : (prefixWord ++ tailWord_3331057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331057).length < 2 ^ (prefixWord ++ tailWord_3331057).sum := by decide
  have hdescent : baseEnd_3331057 < baseStart_3331057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331087 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 9, 3]
def baseStart_3331087 : Nat := 118140960795 + 3331087 * 2 ^ 59
def prefixEnd_3331087 : Nat := 4983230072969 + 3 ^ 40 * 3331087 * 2
def baseEnd_3331087 : Nat := 1140299155295675893662077

theorem tailTrace_3331087 : CollatzResearch.WordTrace tailWord_3331087 prefixEnd_3331087 1140299155295675893662077 := by
  unfold tailWord_3331087
  simp only [CollatzResearch.WordTrace]
  refine ⟨121494724083048178211919515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80996482722032118807946343 121494724083048178211919515)
  ·
    refine ⟨182242086124572267317879273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121494724083048178211919515 182242086124572267317879273)
    ·
      refine ⟨136681564593429200488409455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182242086124572267317879273 136681564593429200488409455)
      ·
        refine ⟨205022346890143800732614183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136681564593429200488409455 205022346890143800732614183)
        ·
          refine ⟨307533520335215701098921275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205022346890143800732614183 307533520335215701098921275)
          ·
            refine ⟨461300280502823551648381913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307533520335215701098921275 461300280502823551648381913)
            ·
              refine ⟨345975210377117663736286435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 461300280502823551648381913 345975210377117663736286435)
              ·
                refine ⟨518962815565676495604429653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 345975210377117663736286435 518962815565676495604429653)
                ·
                  refine ⟨3040797747455135716432205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 518962815565676495604429653 3040797747455135716432205)
                  ·
                    refine ⟨1140299155295675893662077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3040797747455135716432205 1140299155295675893662077)
                    ·
                      rfl

theorem cell22_3331087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 9, 3].length) (baseStart_3331087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3331087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3331087 prefixEnd_3331087 := by exact prefixLift 3331087
  have htrace : WordTrace (prefixWord ++ tailWord_3331087) baseStart_3331087 baseEnd_3331087 := by
    simpa [prefixWord, tailWord_3331087, baseEnd_3331087] using wordTrace_append hprefix tailTrace_3331087
  have hstable : (prefixWord ++ tailWord_3331087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331087).length < 2 ^ (prefixWord ++ tailWord_3331087).sum := by decide
  have hdescent : baseEnd_3331087 < baseStart_3331087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331093 : List Nat := [1, 3, 2, 1, 4, 3, 2, 1, 2, 3]
def baseStart_3331093 : Nat := 118140960795 + 3331093 * 2 ^ 59
def prefixEnd_3331093 : Nat := 4983230072969 + 3 ^ 40 * 3331093 * 2
def baseEnd_3331093 : Nat := 1140301209218293878012059

theorem tailTrace_3331093 : CollatzResearch.WordTrace tailWord_3331093 prefixEnd_3331093 1140301209218293878012059 := by
  unfold tailWord_3331093
  simp only [CollatzResearch.WordTrace]
  refine ⟨121494942921026441236637933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80996628614017627491091955 121494942921026441236637933)
  ·
    refine ⟨45560603595384915463739225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121494942921026441236637933 45560603595384915463739225)
    ·
      refine ⟨34170452696538686597804419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45560603595384915463739225 34170452696538686597804419)
      ·
        refine ⟨51255679044808029896706629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34170452696538686597804419 51255679044808029896706629)
        ·
          refine ⟨9610439820901505605632493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51255679044808029896706629 9610439820901505605632493)
          ·
            refine ⟨3603914932838064602112185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9610439820901505605632493 3603914932838064602112185)
            ·
              refine ⟨2702936199628548451584139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3603914932838064602112185 2702936199628548451584139)
              ·
                refine ⟨4054404299442822677376209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2702936199628548451584139 4054404299442822677376209)
                ·
                  refine ⟨3040803224582117008032157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4054404299442822677376209 3040803224582117008032157)
                  ·
                    refine ⟨1140301209218293878012059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3040803224582117008032157 1140301209218293878012059)
                    ·
                      rfl

theorem cell22_3331093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 2, 1, 2, 3].length) (baseStart_3331093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3331093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3331093 prefixEnd_3331093 := by exact prefixLift 3331093
  have htrace : WordTrace (prefixWord ++ tailWord_3331093) baseStart_3331093 baseEnd_3331093 := by
    simpa [prefixWord, tailWord_3331093, baseEnd_3331093] using wordTrace_append hprefix tailTrace_3331093
  have hstable : (prefixWord ++ tailWord_3331093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331093).length < 2 ^ (prefixWord ++ tailWord_3331093).sum := by decide
  have hdescent : baseEnd_3331093 < baseStart_3331093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331121 : List Nat := [1, 2, 2, 3, 1, 2, 2, 5, 1, 3]
def baseStart_3331121 : Nat := 118140960795 + 3331121 * 2 ^ 59
def prefixEnd_3331121 : Nat := 4983230072969 + 3 ^ 40 * 3331121 * 2
def baseEnd_3331121 : Nat := 1140310794190511138311973

theorem tailTrace_3331121 : CollatzResearch.WordTrace tailWord_3331121 prefixEnd_3331121 1140310794190511138311973 := by
  unfold tailWord_3331121
  simp only [CollatzResearch.WordTrace]
  refine ⟨121495964164925002018657217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80997309443283334679104811 121495964164925002018657217)
  ·
    refine ⟨91121973123693751513992913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121495964164925002018657217 91121973123693751513992913)
    ·
      refine ⟨68341479842770313635494685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91121973123693751513992913 68341479842770313635494685)
      ·
        refine ⟨25628054941038867613310507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68341479842770313635494685 25628054941038867613310507)
        ·
          refine ⟨38442082411558301419965761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25628054941038867613310507 38442082411558301419965761)
          ·
            refine ⟨28831561808668726064974321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38442082411558301419965761 28831561808668726064974321)
            ·
              refine ⟨21623671356501544548730741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28831561808668726064974321 21623671356501544548730741)
              ·
                refine ⟨2027219189672019801443507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21623671356501544548730741 2027219189672019801443507)
                ·
                  refine ⟨3040828784508029702165261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2027219189672019801443507 3040828784508029702165261)
                  ·
                    refine ⟨1140310794190511138311973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3040828784508029702165261 1140310794190511138311973)
                    ·
                      rfl

theorem cell22_3331121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 5, 1, 3].length) (baseStart_3331121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3331121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3331121 prefixEnd_3331121 := by exact prefixLift 3331121
  have htrace : WordTrace (prefixWord ++ tailWord_3331121) baseStart_3331121 baseEnd_3331121 := by
    simpa [prefixWord, tailWord_3331121, baseEnd_3331121] using wordTrace_append hprefix tailTrace_3331121
  have hstable : (prefixWord ++ tailWord_3331121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331121).length < 2 ^ (prefixWord ++ tailWord_3331121).sum := by decide
  have hdescent : baseEnd_3331121 < baseStart_3331121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331149 : List Nat := [1, 6, 1, 1, 1, 2, 1, 1, 1, 7]
def baseStart_3331149 : Nat := 118140960795 + 3331149 * 2 ^ 59
def prefixEnd_3331149 : Nat := 4983230072969 + 3 ^ 40 * 3331149 * 2
def baseEnd_3331149 : Nat := 1140320379162728398611887

theorem tailTrace_3331149 : CollatzResearch.WordTrace tailWord_3331149 prefixEnd_3331149 1140320379162728398611887 := by
  unfold tailWord_3331149
  simp only [CollatzResearch.WordTrace]
  refine ⟨121496985408823562800676501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80997990272549041867117667 121496985408823562800676501)
  ·
    refine ⟨5695171191038604506281711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 121496985408823562800676501 5695171191038604506281711)
    ·
      refine ⟨8542756786557906759422567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5695171191038604506281711 8542756786557906759422567)
      ·
        refine ⟨12814135179836860139133851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8542756786557906759422567 12814135179836860139133851)
        ·
          refine ⟨19221202769755290208700777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12814135179836860139133851 19221202769755290208700777)
          ·
            refine ⟨14415902077316467656525583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19221202769755290208700777 14415902077316467656525583)
            ·
              refine ⟨21623853115974701484788375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14415902077316467656525583 21623853115974701484788375)
              ·
                refine ⟨32435779673962052227182563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21623853115974701484788375 32435779673962052227182563)
                ·
                  refine ⟨48653669510943078340773845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32435779673962052227182563 48653669510943078340773845)
                  ·
                    refine ⟨1140320379162728398611887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48653669510943078340773845 1140320379162728398611887)
                    ·
                      rfl

theorem cell22_3331149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_3331149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3331149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3331149 prefixEnd_3331149 := by exact prefixLift 3331149
  have htrace : WordTrace (prefixWord ++ tailWord_3331149) baseStart_3331149 baseEnd_3331149 := by
    simpa [prefixWord, tailWord_3331149, baseEnd_3331149] using wordTrace_append hprefix tailTrace_3331149
  have hstable : (prefixWord ++ tailWord_3331149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331149).length < 2 ^ (prefixWord ++ tailWord_3331149).sum := by decide
  have hdescent : baseEnd_3331149 < baseStart_3331149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331164 : List Nat := [2, 2, 4, 1, 1, 1, 1, 3, 3, 4]
def baseStart_3331164 : Nat := 118140960795 + 3331164 * 2 ^ 59
def prefixEnd_3331164 : Nat := 4983230072969 + 3 ^ 40 * 3331164 * 2
def baseEnd_3331164 : Nat := 1140325513969273359486841

theorem tailTrace_3331164 : CollatzResearch.WordTrace tailWord_3331164 prefixEnd_3331164 1140325513969273359486841 := by
  unfold tailWord_3331164
  simp only [CollatzResearch.WordTrace]
  refine ⟨60748766251884610181236273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80998355002512813574981697 60748766251884610181236273)
  ·
    refine ⟨45561574688913457635927205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60748766251884610181236273 45561574688913457635927205)
    ·
      refine ⟨8542795254171273306736351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45561574688913457635927205 8542795254171273306736351)
      ·
        refine ⟨12814192881256909960104527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8542795254171273306736351 12814192881256909960104527)
        ·
          refine ⟨19221289321885364940156791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12814192881256909960104527 19221289321885364940156791)
          ·
            refine ⟨28831933982828047410235187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19221289321885364940156791 28831933982828047410235187)
            ·
              refine ⟨43247900974242071115352781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28831933982828047410235187 43247900974242071115352781)
              ·
                refine ⟨16217962865340776668257293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43247900974242071115352781 16217962865340776668257293)
                ·
                  refine ⟨6081736074502791250596485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16217962865340776668257293 6081736074502791250596485)
                  ·
                    refine ⟨1140325513969273359486841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6081736074502791250596485 1140325513969273359486841)
                    ·
                      rfl

theorem cell22_3331164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_3331164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3331164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3331164 prefixEnd_3331164 := by exact prefixLift 3331164
  have htrace : WordTrace (prefixWord ++ tailWord_3331164) baseStart_3331164 baseEnd_3331164 := by
    simpa [prefixWord, tailWord_3331164, baseEnd_3331164] using wordTrace_append hprefix tailTrace_3331164
  have hstable : (prefixWord ++ tailWord_3331164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331164).length < 2 ^ (prefixWord ++ tailWord_3331164).sum := by decide
  have hdescent : baseEnd_3331164 < baseStart_3331164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331181 : List Nat := [1, 5, 1, 1, 2, 3, 1, 3, 1, 4]
def baseStart_3331181 : Nat := 118140960795 + 3331181 * 2 ^ 59
def prefixEnd_3331181 : Nat := 4983230072969 + 3 ^ 40 * 3331181 * 2
def baseEnd_3331181 : Nat := 1140331333416690981811789

theorem tailTrace_3331181 : CollatzResearch.WordTrace tailWord_3331181 prefixEnd_3331181 1140331333416690981811789 := by
  unfold tailWord_3331181
  simp only [CollatzResearch.WordTrace]
  refine ⟨121498152544707632265841397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80998768363138421510560931 121498152544707632265841397)
  ·
    refine ⟨11390451801066340524922631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 121498152544707632265841397 11390451801066340524922631)
    ·
      refine ⟨17085677701599510787383947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11390451801066340524922631 17085677701599510787383947)
      ·
        refine ⟨25628516552399266181075921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17085677701599510787383947 25628516552399266181075921)
        ·
          refine ⟨19221387414299449635806941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25628516552399266181075921 19221387414299449635806941)
          ·
            refine ⟨7208020280362293613427603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19221387414299449635806941 7208020280362293613427603)
            ·
              refine ⟨10812030420543440420141405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7208020280362293613427603 10812030420543440420141405)
              ·
                refine ⟨4054511407703790157553027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10812030420543440420141405 4054511407703790157553027)
                ·
                  refine ⟨6081767111555685236329541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4054511407703790157553027 6081767111555685236329541)
                  ·
                    refine ⟨1140331333416690981811789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6081767111555685236329541 1140331333416690981811789)
                    ·
                      rfl

theorem cell22_3331181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_3331181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3331181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3331181 prefixEnd_3331181 := by exact prefixLift 3331181
  have htrace : WordTrace (prefixWord ++ tailWord_3331181) baseStart_3331181 baseEnd_3331181 := by
    simpa [prefixWord, tailWord_3331181, baseEnd_3331181] using wordTrace_append hprefix tailTrace_3331181
  have hstable : (prefixWord ++ tailWord_3331181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331181).length < 2 ^ (prefixWord ++ tailWord_3331181).sum := by decide
  have hdescent : baseEnd_3331181 < baseStart_3331181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331207 : List Nat := [1, 1, 4, 2, 1, 1, 1, 11]
def baseStart_3331207 : Nat := 118140960795 + 3331207 * 2 ^ 59
def prefixEnd_3331207 : Nat := 4983230072969 + 3 ^ 40 * 3331207 * 2
def baseEnd_3331207 : Nat := 126704470416448397851301

theorem tailTrace_3331207 : CollatzResearch.WordTrace tailWord_3331207 prefixEnd_3331207 126704470416448397851301 := by
  unfold tailWord_3331207
  simp only [CollatzResearch.WordTrace]
  refine ⟨121499100842613438706287875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80999400561742292470858583 121499100842613438706287875)
  ·
    refine ⟨182248651263920158059431813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121499100842613438706287875 182248651263920158059431813)
    ·
      refine ⟨34171622111985029636143465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 182248651263920158059431813 34171622111985029636143465)
      ·
        refine ⟨25628716583988772227107599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34171622111985029636143465 25628716583988772227107599)
        ·
          refine ⟨38443074875983158340661399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25628716583988772227107599 38443074875983158340661399)
          ·
            refine ⟨57664612313974737510992099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38443074875983158340661399 57664612313974737510992099)
            ·
              refine ⟨86496918470962106266488149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57664612313974737510992099 86496918470962106266488149)
              ·
                refine ⟨126704470416448397851301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 86496918470962106266488149 126704470416448397851301)
                ·
                  rfl

theorem cell22_3331207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 11].length) (baseStart_3331207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3331207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3331207 prefixEnd_3331207 := by exact prefixLift 3331207
  have htrace : WordTrace (prefixWord ++ tailWord_3331207) baseStart_3331207 baseEnd_3331207 := by
    simpa [prefixWord, tailWord_3331207, baseEnd_3331207] using wordTrace_append hprefix tailTrace_3331207
  have hstable : (prefixWord ++ tailWord_3331207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331207).length < 2 ^ (prefixWord ++ tailWord_3331207).sum := by decide
  have hdescent : baseEnd_3331207 < baseStart_3331207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331224 : List Nat := [2, 1, 2, 4, 2, 2, 1, 8]
def baseStart_3331224 : Nat := 118140960795 + 3331224 * 2 ^ 59
def prefixEnd_3331224 : Nat := 4983230072969 + 3 ^ 40 * 3331224 * 2
def baseEnd_3331224 : Nat := 126705117021717022554073

theorem tailTrace_3331224 : CollatzResearch.WordTrace tailWord_3331224 prefixEnd_3331224 126705117021717022554073 := by
  unfold tailWord_3331224
  simp only [CollatzResearch.WordTrace]
  refine ⟨60749860441775925304828363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80999813922367900406437817 60749860441775925304828363)
  ·
    refine ⟨91124790662663887957242545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60749860441775925304828363 91124790662663887957242545)
    ·
      refine ⟨68343592996997915967931909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91124790662663887957242545 68343592996997915967931909)
      ·
        refine ⟨12814423686937109243987233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68343592996997915967931909 12814423686937109243987233)
        ·
          refine ⟨9610817765202831932990425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12814423686937109243987233 9610817765202831932990425)
          ·
            refine ⟨7208113323902123949742819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9610817765202831932990425 7208113323902123949742819)
            ·
              refine ⟨10812169985853185924614229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7208113323902123949742819 10812169985853185924614229)
              ·
                refine ⟨126705117021717022554073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10812169985853185924614229 126705117021717022554073)
                ·
                  rfl

theorem cell22_3331224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 8].length) (baseStart_3331224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3331224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3331224 prefixEnd_3331224 := by exact prefixLift 3331224
  have htrace : WordTrace (prefixWord ++ tailWord_3331224) baseStart_3331224 baseEnd_3331224 := by
    simpa [prefixWord, tailWord_3331224, baseEnd_3331224] using wordTrace_append hprefix tailTrace_3331224
  have hstable : (prefixWord ++ tailWord_3331224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331224).length < 2 ^ (prefixWord ++ tailWord_3331224).sum := by decide
  have hdescent : baseEnd_3331224 < baseStart_3331224 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331230 : List Nat := [4, 3, 1, 1, 2, 3, 1, 3, 4]
def baseStart_3331230 : Nat := 118140960795 + 3331230 * 2 ^ 59
def prefixEnd_3331230 : Nat := 4983230072969 + 3 ^ 40 * 3331230 * 2
def baseEnd_3331230 : Nat := 380116035706023729112213

theorem tailTrace_3331230 : CollatzResearch.WordTrace tailWord_3331230 prefixEnd_3331230 380116035706023729112213 := by
  unfold tailWord_3331230
  simp only [CollatzResearch.WordTrace]
  refine ⟨15187492465191264204296893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80999959814353409089583429 15187492465191264204296893)
  ·
    refine ⟨5695309674446724076611335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15187492465191264204296893 5695309674446724076611335)
    ·
      refine ⟨8542964511670086114917003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5695309674446724076611335 8542964511670086114917003)
      ·
        refine ⟨12814446767505129172375505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8542964511670086114917003 12814446767505129172375505)
        ·
          refine ⟨9610835075628846879281629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12814446767505129172375505 9610835075628846879281629)
          ·
            refine ⟨3604063153360817579730611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9610835075628846879281629 3604063153360817579730611)
            ·
              refine ⟨5406094730041226369595917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3604063153360817579730611 5406094730041226369595917)
              ·
                refine ⟨2027285523765459888598469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5406094730041226369595917 2027285523765459888598469)
                ·
                  refine ⟨380116035706023729112213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2027285523765459888598469 380116035706023729112213)
                  ·
                    rfl

theorem cell22_3331230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_3331230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3331230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3331230 prefixEnd_3331230 := by exact prefixLift 3331230
  have htrace : WordTrace (prefixWord ++ tailWord_3331230) baseStart_3331230 baseEnd_3331230 := by
    simpa [prefixWord, tailWord_3331230, baseEnd_3331230] using wordTrace_append hprefix tailTrace_3331230
  have hstable : (prefixWord ++ tailWord_3331230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331230).length < 2 ^ (prefixWord ++ tailWord_3331230).sum := by decide
  have hdescent : baseEnd_3331230 < baseStart_3331230 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331303 : List Nat := [1, 1, 5, 3, 2, 1, 2, 2, 5]
def baseStart_3331303 : Nat := 118140960795 + 3331303 * 2 ^ 59
def prefixEnd_3331303 : Nat := 4983230072969 + 3 ^ 40 * 3331303 * 2
def baseEnd_3331303 : Nat := 380124365503307776753805

theorem tailTrace_3331303 : CollatzResearch.WordTrace tailWord_3331303 prefixEnd_3331303 380124365503307776753805 := by
  unfold tailWord_3331303
  simp only [CollatzResearch.WordTrace]
  refine ⟨121502602250265647101782563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81001734833510431401188375 121502602250265647101782563)
  ·
    refine ⟨182253903375398470652673845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121502602250265647101782563 182253903375398470652673845)
    ·
      refine ⟨17086303441443606623688173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 182253903375398470652673845 17086303441443606623688173)
      ·
        refine ⟨6407363790541352483883065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17086303441443606623688173 6407363790541352483883065)
        ·
          refine ⟨4805522842906014362912299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6407363790541352483883065 4805522842906014362912299)
          ·
            refine ⟨7208284264359021544368449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4805522842906014362912299 7208284264359021544368449)
            ·
              refine ⟨5406213198269266158276337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7208284264359021544368449 5406213198269266158276337)
              ·
                refine ⟨4054659898701949618707253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5406213198269266158276337 4054659898701949618707253)
                ·
                  refine ⟨380124365503307776753805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4054659898701949618707253 380124365503307776753805)
                  ·
                    rfl

theorem cell22_3331303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 2, 5].length) (baseStart_3331303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3331303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3331303 prefixEnd_3331303 := by exact prefixLift 3331303
  have htrace : WordTrace (prefixWord ++ tailWord_3331303) baseStart_3331303 baseEnd_3331303 := by
    simpa [prefixWord, tailWord_3331303, baseEnd_3331303] using wordTrace_append hprefix tailTrace_3331303
  have hstable : (prefixWord ++ tailWord_3331303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331303).length < 2 ^ (prefixWord ++ tailWord_3331303).sum := by decide
  have hdescent : baseEnd_3331303 < baseStart_3331303 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331363 : List Nat := [1, 1, 1, 4, 2, 3, 3, 2, 2, 3]
def baseStart_3331363 : Nat := 118140960795 + 3331363 * 2 ^ 59
def prefixEnd_3331363 : Nat := 4983230072969 + 3 ^ 40 * 3331363 * 2
def baseEnd_3331363 : Nat := 1140393635736103173761231

theorem tailTrace_3331363 : CollatzResearch.WordTrace tailWord_3331363 prefixEnd_3331363 1140393635736103173761231 := by
  unfold tailWord_3331363
  simp only [CollatzResearch.WordTrace]
  refine ⟨121504790630048277348966743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81003193753365518232644495 121504790630048277348966743)
  ·
    refine ⟨182257185945072416023450115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121504790630048277348966743 182257185945072416023450115)
    ·
      refine ⟨273385778917608624035175173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182257185945072416023450115 273385778917608624035175173)
      ·
        refine ⟨51259833547051617006595345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 273385778917608624035175173 51259833547051617006595345)
        ·
          refine ⟨38444875160288712754946509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51259833547051617006595345 38444875160288712754946509)
          ·
            refine ⟨14416828185108267283104941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38444875160288712754946509 14416828185108267283104941)
            ·
              refine ⟨5406310569415600231164353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14416828185108267283104941 5406310569415600231164353)
              ·
                refine ⟨4054732927061700173373265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5406310569415600231164353 4054732927061700173373265)
                ·
                  refine ⟨3041049695296275130029949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4054732927061700173373265 3041049695296275130029949)
                  ·
                    refine ⟨1140393635736103173761231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3041049695296275130029949 1140393635736103173761231)
                    ·
                      rfl

theorem cell22_3331363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 2, 2, 3].length) (baseStart_3331363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3331363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3331363 prefixEnd_3331363 := by exact prefixLift 3331363
  have htrace : WordTrace (prefixWord ++ tailWord_3331363) baseStart_3331363 baseEnd_3331363 := by
    simpa [prefixWord, tailWord_3331363, baseEnd_3331363] using wordTrace_append hprefix tailTrace_3331363
  have hstable : (prefixWord ++ tailWord_3331363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331363).length < 2 ^ (prefixWord ++ tailWord_3331363).sum := by decide
  have hdescent : baseEnd_3331363 < baseStart_3331363 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331393 : List Nat := [1, 2, 5, 2, 1, 1, 4, 6]
def baseStart_3331393 : Nat := 118140960795 + 3331393 * 2 ^ 59
def prefixEnd_3331393 : Nat := 4983230072969 + 3 ^ 40 * 3331393 * 2
def baseEnd_3331393 : Nat := 126711545038799232834571

theorem tailTrace_3331393 : CollatzResearch.WordTrace tailWord_3331393 prefixEnd_3331393 126711545038799232834571 := by
  unfold tailWord_3331393
  simp only [CollatzResearch.WordTrace]
  refine ⟨121505884819939592472558833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81003923213293061648372555 121505884819939592472558833)
  ·
    refine ⟨91129413614954694354419125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121505884819939592472558833 91129413614954694354419125)
    ·
      refine ⟨8543382526402002595726793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 91129413614954694354419125 8543382526402002595726793)
      ·
        refine ⟨6407536894801501946795095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8543382526402002595726793 6407536894801501946795095)
        ·
          refine ⟨9611305342202252920192643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6407536894801501946795095 9611305342202252920192643)
          ·
            refine ⟨14416958013303379380288965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9611305342202252920192643 14416958013303379380288965)
            ·
              refine ⟨2703179627494383633804181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14416958013303379380288965 2703179627494383633804181)
              ·
                refine ⟨126711545038799232834571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2703179627494383633804181 126711545038799232834571)
                ·
                  rfl

theorem cell22_3331393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 4, 6].length) (baseStart_3331393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3331393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3331393 prefixEnd_3331393 := by exact prefixLift 3331393
  have htrace : WordTrace (prefixWord ++ tailWord_3331393) baseStart_3331393 baseEnd_3331393 := by
    simpa [prefixWord, tailWord_3331393, baseEnd_3331393] using wordTrace_append hprefix tailTrace_3331393
  have hstable : (prefixWord ++ tailWord_3331393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331393).length < 2 ^ (prefixWord ++ tailWord_3331393).sum := by decide
  have hdescent : baseEnd_3331393 < baseStart_3331393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331451 : List Nat := [1, 1, 1, 1, 1, 6, 3, 1, 3, 4]
def baseStart_3331451 : Nat := 118140960795 + 3331451 * 2 ^ 59
def prefixEnd_3331451 : Nat := 4983230072969 + 3 ^ 40 * 3331451 * 2
def baseEnd_3331451 : Nat := 1140423759934500277560961

theorem tailTrace_3331451 : CollatzResearch.WordTrace tailWord_3331451 prefixEnd_3331451 1140423759934500277560961 := by
  unfold tailWord_3331451
  simp only [CollatzResearch.WordTrace]
  refine ⟨121508000253729468378170207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81005333502486312252113471 121508000253729468378170207)
  ·
    refine ⟨182262000380594202567255311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121508000253729468378170207 182262000380594202567255311)
    ·
      refine ⟨273393000570891303850882967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182262000380594202567255311 273393000570891303850882967)
      ·
        refine ⟨410089500856336955776324451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273393000570891303850882967 410089500856336955776324451)
        ·
          refine ⟨615134251284505433664486677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 410089500856336955776324451 615134251284505433664486677)
          ·
            refine ⟨28834418028961192203022813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 615134251284505433664486677 28834418028961192203022813)
            ·
              refine ⟨10812906760860447076133555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28834418028961192203022813 10812906760860447076133555)
              ·
                refine ⟨16219360141290670614200333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10812906760860447076133555 16219360141290670614200333)
                ·
                  refine ⟨6082260052984001480325125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16219360141290670614200333 6082260052984001480325125)
                  ·
                    refine ⟨1140423759934500277560961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6082260052984001480325125 1140423759934500277560961)
                    ·
                      rfl

theorem cell22_3331451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 1, 3, 4].length) (baseStart_3331451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3331451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3331451 prefixEnd_3331451 := by exact prefixLift 3331451
  have htrace : WordTrace (prefixWord ++ tailWord_3331451) baseStart_3331451 baseEnd_3331451 := by
    simpa [prefixWord, tailWord_3331451, baseEnd_3331451] using wordTrace_append hprefix tailTrace_3331451
  have hstable : (prefixWord ++ tailWord_3331451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331451).length < 2 ^ (prefixWord ++ tailWord_3331451).sum := by decide
  have hdescent : baseEnd_3331451 < baseStart_3331451 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331513 : List Nat := [1, 2, 1, 4, 4, 1, 1, 1, 1, 6]
def baseStart_3331513 : Nat := 118140960795 + 3331513 * 2 ^ 59
def prefixEnd_3331513 : Nat := 4983230072969 + 3 ^ 40 * 3331513 * 2
def baseEnd_3331513 : Nat := 1140444983801552782510771

theorem tailTrace_3331513 : CollatzResearch.WordTrace tailWord_3331513 prefixEnd_3331513 1140444983801552782510771 := by
  unfold tailWord_3331513
  simp only [CollatzResearch.WordTrace]
  refine ⟨121510261579504852966927193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81006841053003235311284795 121510261579504852966927193)
  ·
    refine ⟨91132696184628639725195395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121510261579504852966927193 91132696184628639725195395)
    ·
      refine ⟨136699044276942959587793093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91132696184628639725195395 136699044276942959587793093)
      ·
        refine ⟨25631070801926804922711205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136699044276942959587793093 25631070801926804922711205)
        ·
          refine ⟨4805825775361275923008351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25631070801926804922711205 4805825775361275923008351)
          ·
            refine ⟨7208738663041913884512527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4805825775361275923008351 7208738663041913884512527)
            ·
              refine ⟨10813107994562870826768791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7208738663041913884512527 10813107994562870826768791)
              ·
                refine ⟨16219661991844306240153187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10813107994562870826768791 16219661991844306240153187)
                ·
                  refine ⟨24329492987766459360229781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16219661991844306240153187 24329492987766459360229781)
                  ·
                    refine ⟨1140444983801552782510771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24329492987766459360229781 1140444983801552782510771)
                    ·
                      rfl

theorem cell22_3331513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 1, 1, 6].length) (baseStart_3331513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3331513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3331513 prefixEnd_3331513 := by exact prefixLift 3331513
  have htrace : WordTrace (prefixWord ++ tailWord_3331513) baseStart_3331513 baseEnd_3331513 := by
    simpa [prefixWord, tailWord_3331513, baseEnd_3331513] using wordTrace_append hprefix tailTrace_3331513
  have hstable : (prefixWord ++ tailWord_3331513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331513).length < 2 ^ (prefixWord ++ tailWord_3331513).sum := by decide
  have hdescent : baseEnd_3331513 < baseStart_3331513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331532 : List Nat := [2, 2, 1, 4, 2, 3, 1, 2, 2, 3]
def baseStart_3331532 : Nat := 118140960795 + 3331532 * 2 ^ 59
def prefixEnd_3331532 : Nat := 4983230072969 + 3 ^ 40 * 3331532 * 2
def baseEnd_3331532 : Nat := 1140451487889843066285713

theorem tailTrace_3331532 : CollatzResearch.WordTrace tailWord_3331532 prefixEnd_3331532 1140451487889843066285713 := by
  unfold tailWord_3331532
  simp only [CollatzResearch.WordTrace]
  refine ⟨60755477283218009605934425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81007303044290679474579233 60755477283218009605934425)
  ·
    refine ⟨45566607962413507204450819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60755477283218009605934425 45566607962413507204450819)
    ·
      refine ⟨68349911943620260806676229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45566607962413507204450819 68349911943620260806676229)
      ·
        refine ⟨12815608489428798901251793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68349911943620260806676229 12815608489428798901251793)
        ·
          refine ⟨9611706367071599175938845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12815608489428798901251793 9611706367071599175938845)
          ·
            refine ⟨3604389887651849690977067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9611706367071599175938845 3604389887651849690977067)
            ·
              refine ⟨5406584831477774536465601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3604389887651849690977067 5406584831477774536465601)
              ·
                refine ⟨4054938623608330902349201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5406584831477774536465601 4054938623608330902349201)
                ·
                  refine ⟨3041203967706248176761901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4054938623608330902349201 3041203967706248176761901)
                  ·
                    refine ⟨1140451487889843066285713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3041203967706248176761901 1140451487889843066285713)
                    ·
                      rfl

theorem cell22_3331532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 2, 2, 3].length) (baseStart_3331532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3331532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3331532 prefixEnd_3331532 := by exact prefixLift 3331532
  have htrace : WordTrace (prefixWord ++ tailWord_3331532) baseStart_3331532 baseEnd_3331532 := by
    simpa [prefixWord, tailWord_3331532, baseEnd_3331532] using wordTrace_append hprefix tailTrace_3331532
  have hstable : (prefixWord ++ tailWord_3331532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331532).length < 2 ^ (prefixWord ++ tailWord_3331532).sum := by decide
  have hdescent : baseEnd_3331532 < baseStart_3331532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331562 : List Nat := [3, 1, 3, 1, 5, 1, 2, 6]
def baseStart_3331562 : Nat := 118140960795 + 3331562 * 2 ^ 59
def prefixEnd_3331562 : Nat := 4983230072969 + 3 ^ 40 * 3331562 * 2
def baseEnd_3331562 : Nat := 126717973055881443115069

theorem tailTrace_3331562 : CollatzResearch.WordTrace tailWord_3331562 prefixEnd_3331562 126717973055881443115069 := by
  unfold tailWord_3331562
  simp only [CollatzResearch.WordTrace]
  refine ⟨30378012189081833583865235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81008032504218222890307293 30378012189081833583865235)
  ·
    refine ⟨45567018283622750375797853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30378012189081833583865235 45567018283622750375797853)
    ·
      refine ⟨17087631856358531390924195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45567018283622750375797853 17087631856358531390924195)
      ·
        refine ⟨25631447784537797086386293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17087631856358531390924195 25631447784537797086386293)
        ·
          refine ⟨2402948229800418476848715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25631447784537797086386293 2402948229800418476848715)
          ·
            refine ⟨3604422344700627715273073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2402948229800418476848715 3604422344700627715273073)
            ·
              refine ⟨2703316758525470786454805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3604422344700627715273073 2703316758525470786454805)
              ·
                refine ⟨126717973055881443115069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2703316758525470786454805 126717973055881443115069)
                ·
                  rfl

theorem cell22_3331562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 2, 6].length) (baseStart_3331562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3331562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3331562 prefixEnd_3331562 := by exact prefixLift 3331562
  have htrace : WordTrace (prefixWord ++ tailWord_3331562) baseStart_3331562 baseEnd_3331562 := by
    simpa [prefixWord, tailWord_3331562, baseEnd_3331562] using wordTrace_append hprefix tailTrace_3331562
  have hstable : (prefixWord ++ tailWord_3331562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331562).length < 2 ^ (prefixWord ++ tailWord_3331562).sum := by decide
  have hdescent : baseEnd_3331562 < baseStart_3331562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331571 : List Nat := [1, 1, 1, 2, 2, 2, 2, 2, 4, 5]
def baseStart_3331571 : Nat := 118140960795 + 3331571 * 2 ^ 59
def prefixEnd_3331571 : Nat := 4983230072969 + 3 ^ 40 * 3331571 * 2
def baseEnd_3331571 : Nat := 1140464838386859964560593

theorem tailTrace_3331571 : CollatzResearch.WordTrace tailWord_3331571 prefixEnd_3331571 1140464838386859964560593 := by
  unfold tailWord_3331571
  simp only [CollatzResearch.WordTrace]
  refine ⟨121512377013294728872538567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81008251342196485915025711 121512377013294728872538567)
  ·
    refine ⟨182268565519942093308807851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121512377013294728872538567 182268565519942093308807851)
    ·
      refine ⟨273402848279913139963211777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182268565519942093308807851 273402848279913139963211777)
      ·
        refine ⟨205052136209934854972408833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273402848279913139963211777 205052136209934854972408833)
        ·
          refine ⟨153789102157451141229306625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205052136209934854972408833 153789102157451141229306625)
          ·
            refine ⟨115341826618088355921979969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153789102157451141229306625 115341826618088355921979969)
            ·
              refine ⟨86506369963566266941484977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115341826618088355921979969 86506369963566266941484977)
              ·
                refine ⟨64879777472674700206113733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86506369963566266941484977 64879777472674700206113733)
                ·
                  refine ⟨12164958276126506288646325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64879777472674700206113733 12164958276126506288646325)
                  ·
                    refine ⟨1140464838386859964560593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12164958276126506288646325 1140464838386859964560593)
                    ·
                      rfl

theorem cell22_3331571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4, 5].length) (baseStart_3331571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3331571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3331571 prefixEnd_3331571 := by exact prefixLift 3331571
  have htrace : WordTrace (prefixWord ++ tailWord_3331571) baseStart_3331571 baseEnd_3331571 := by
    simpa [prefixWord, tailWord_3331571, baseEnd_3331571] using wordTrace_append hprefix tailTrace_3331571
  have hstable : (prefixWord ++ tailWord_3331571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331571).length < 2 ^ (prefixWord ++ tailWord_3331571).sum := by decide
  have hdescent : baseEnd_3331571 < baseStart_3331571 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331594 : List Nat := [3, 1, 2, 2, 2, 3, 3, 2, 1, 3]
def baseStart_3331594 : Nat := 118140960795 + 3331594 * 2 ^ 59
def prefixEnd_3331594 : Nat := 4983230072969 + 3 ^ 40 * 3331594 * 2
def baseEnd_3331594 : Nat := 1140472711756895571235523

theorem tailTrace_3331594 : CollatzResearch.WordTrace tailWord_3331594 prefixEnd_3331594 1140472711756895571235523 := by
  unfold tailWord_3331594
  simp only [CollatzResearch.WordTrace]
  refine ⟨30378303973052850950156459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81008810594807602533750557 30378303973052850950156459)
  ·
    refine ⟨45567455959579276425234689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30378303973052850950156459 45567455959579276425234689)
    ·
      refine ⟨34175591969684457318926017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45567455959579276425234689 34175591969684457318926017)
      ·
        refine ⟨25631693977263342989194513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34175591969684457318926017 25631693977263342989194513)
        ·
          refine ⟨19223770482947507241895885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25631693977263342989194513 19223770482947507241895885)
          ·
            refine ⟨7208913931105315215710957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19223770482947507241895885 7208913931105315215710957)
            ·
              refine ⟨2703342724164493205891609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7208913931105315215710957 2703342724164493205891609)
              ·
                refine ⟨2027507043123369904418707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2703342724164493205891609 2027507043123369904418707)
                ·
                  refine ⟨3041260564685054856628061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2027507043123369904418707 3041260564685054856628061)
                  ·
                    refine ⟨1140472711756895571235523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3041260564685054856628061 1140472711756895571235523)
                    ·
                      rfl

theorem cell22_3331594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 3, 2, 1, 3].length) (baseStart_3331594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3331594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3331594 prefixEnd_3331594 := by exact prefixLift 3331594
  have htrace : WordTrace (prefixWord ++ tailWord_3331594) baseStart_3331594 baseEnd_3331594 := by
    simpa [prefixWord, tailWord_3331594, baseEnd_3331594] using wordTrace_append hprefix tailTrace_3331594
  have hstable : (prefixWord ++ tailWord_3331594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331594).length < 2 ^ (prefixWord ++ tailWord_3331594).sum := by decide
  have hdescent : baseEnd_3331594 < baseStart_3331594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331618 : List Nat := [3, 3, 1, 1, 1, 1, 2, 4, 6]
def baseStart_3331618 : Nat := 118140960795 + 3331618 * 2 ^ 59
def prefixEnd_3331618 : Nat := 4983230072969 + 3 ^ 40 * 3331618 * 2
def baseEnd_3331618 : Nat := 380160309149122502878483

theorem tailTrace_3331618 : CollatzResearch.WordTrace tailWord_3331618 prefixEnd_3331618 380160309149122502878483 := by
  unfold tailWord_3331618
  simp only [CollatzResearch.WordTrace]
  refine ⟨30378522811031113974874877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81009394162749637266333005 30378522811031113974874877)
  ·
    refine ⟨11391946054136667740578079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30378522811031113974874877 11391946054136667740578079)
    ·
      refine ⟨17087919081205001610867119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11391946054136667740578079 17087919081205001610867119)
      ·
        refine ⟨25631878621807502416300679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17087919081205001610867119 25631878621807502416300679)
        ·
          refine ⟨38447817932711253624451019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25631878621807502416300679 38447817932711253624451019)
          ·
            refine ⟨57671726899066880436676529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38447817932711253624451019 57671726899066880436676529)
            ·
              refine ⟨43253795174300160327507397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57671726899066880436676529 43253795174300160327507397)
              ·
                refine ⟨8110086595181280061407637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43253795174300160327507397 8110086595181280061407637)
                ·
                  refine ⟨380160309149122502878483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8110086595181280061407637 380160309149122502878483)
                  ·
                    rfl

theorem cell22_3331618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 4, 6].length) (baseStart_3331618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3331618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3331618 prefixEnd_3331618 := by exact prefixLift 3331618
  have htrace : WordTrace (prefixWord ++ tailWord_3331618) baseStart_3331618 baseEnd_3331618 := by
    simpa [prefixWord, tailWord_3331618, baseEnd_3331618] using wordTrace_append hprefix tailTrace_3331618
  have hstable : (prefixWord ++ tailWord_3331618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331618).length < 2 ^ (prefixWord ++ tailWord_3331618).sum := by decide
  have hdescent : baseEnd_3331618 < baseStart_3331618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331637 : List Nat := [1, 3, 3, 1, 1, 4, 3, 1, 1, 4]
def baseStart_3331637 : Nat := 118140960795 + 3331637 * 2 ^ 59
def prefixEnd_3331637 : Nat := 4983230072969 + 3 ^ 40 * 3331637 * 2
def baseEnd_3331637 : Nat := 1140487431535657792410391

theorem tailTrace_3331637 : CollatzResearch.WordTrace tailWord_3331637 prefixEnd_3331637 1140487431535657792410391 := by
  unfold tailWord_3331637
  simp only [CollatzResearch.WordTrace]
  refine ⟨121514784231055622144441165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81009856154037081429627443 121514784231055622144441165)
  ·
    refine ⟨45568044086645858304165437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121514784231055622144441165 45568044086645858304165437)
    ·
      refine ⟨17088016532492196864062039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45568044086645858304165437 17088016532492196864062039)
      ·
        refine ⟨25632024798738295296093059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17088016532492196864062039 25632024798738295296093059)
        ·
          refine ⟨38448037198107442944139589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25632024798738295296093059 38448037198107442944139589)
          ·
            refine ⟨7209006974645145552026173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38448037198107442944139589 7209006974645145552026173)
            ·
              refine ⟨2703377615491929582009815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7209006974645145552026173 2703377615491929582009815)
              ·
                refine ⟨4055066423237894373014723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2703377615491929582009815 4055066423237894373014723)
                ·
                  refine ⟨6082599634856841559522085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4055066423237894373014723 6082599634856841559522085)
                  ·
                    refine ⟨1140487431535657792410391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6082599634856841559522085 1140487431535657792410391)
                    ·
                      rfl

theorem cell22_3331637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 3, 1, 1, 4].length) (baseStart_3331637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3331637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3331637 prefixEnd_3331637 := by exact prefixLift 3331637
  have htrace : WordTrace (prefixWord ++ tailWord_3331637) baseStart_3331637 baseEnd_3331637 := by
    simpa [prefixWord, tailWord_3331637, baseEnd_3331637] using wordTrace_append hprefix tailTrace_3331637
  have hstable : (prefixWord ++ tailWord_3331637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331637).length < 2 ^ (prefixWord ++ tailWord_3331637).sum := by decide
  have hdescent : baseEnd_3331637 < baseStart_3331637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331712 : List Nat := [2, 1, 1, 2, 1, 4, 1, 6, 1, 3]
def baseStart_3331712 : Nat := 118140960795 + 3331712 * 2 ^ 59
def prefixEnd_3331712 : Nat := 4983230072969 + 3 ^ 40 * 3331712 * 2
def baseEnd_3331712 : Nat := 1140513105568382596785161

theorem tailTrace_3331712 : CollatzResearch.WordTrace tailWord_3331712 prefixEnd_3331712 1140513105568382596785161 := by
  unfold tailWord_3331712
  simp only [CollatzResearch.WordTrace]
  refine ⟨60758759852891954976710695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81011679803855939968947593 60758759852891954976710695)
  ·
    refine ⟨91138139779337932465066043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60758759852891954976710695 91138139779337932465066043)
    ·
      refine ⟨136707209669006898697599065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91138139779337932465066043 136707209669006898697599065)
      ·
        refine ⟨102530407251755174023199299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136707209669006898697599065 102530407251755174023199299)
        ·
          refine ⟨153795610877632761034798949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102530407251755174023199299 153795610877632761034798949)
          ·
            refine ⟨28836677039556142694024803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 153795610877632761034798949 28836677039556142694024803)
            ·
              refine ⟨43255015559334214041037205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28836677039556142694024803 43255015559334214041037205)
              ·
                refine ⟨2027578854343791283173619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 43255015559334214041037205 2027578854343791283173619)
                ·
                  refine ⟨3041368281515686924760429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2027578854343791283173619 3041368281515686924760429)
                  ·
                    refine ⟨1140513105568382596785161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3041368281515686924760429 1140513105568382596785161)
                    ·
                      rfl

theorem cell22_3331712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 6, 1, 3].length) (baseStart_3331712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3331712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3331712 prefixEnd_3331712 := by exact prefixLift 3331712
  have htrace : WordTrace (prefixWord ++ tailWord_3331712) baseStart_3331712 baseEnd_3331712 := by
    simpa [prefixWord, tailWord_3331712, baseEnd_3331712] using wordTrace_append hprefix tailTrace_3331712
  have hstable : (prefixWord ++ tailWord_3331712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331712).length < 2 ^ (prefixWord ++ tailWord_3331712).sum := by decide
  have hdescent : baseEnd_3331712 < baseStart_3331712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331723 : List Nat := [1, 1, 1, 1, 4, 1, 3, 3, 2, 5]
def baseStart_3331723 : Nat := 118140960795 + 3331723 * 2 ^ 59
def prefixEnd_3331723 : Nat := 4983230072969 + 3 ^ 40 * 3331723 * 2
def baseEnd_3331723 : Nat := 1140516871093182234760127

theorem tailTrace_3331723 : CollatzResearch.WordTrace tailWord_3331723 prefixEnd_3331723 1140516871093182234760127 := by
  unfold tailWord_3331723
  simp only [CollatzResearch.WordTrace]
  refine ⟨121517920908744058832071823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81011947272496039221381215 121517920908744058832071823)
  ·
    refine ⟨182276881363116088248107735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121517920908744058832071823 182276881363116088248107735)
    ·
      refine ⟨273415322044674132372161603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182276881363116088248107735 273415322044674132372161603)
      ·
        refine ⟨410122983067011198558242405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273415322044674132372161603 410122983067011198558242405)
        ·
          refine ⟨76898059325064599729670451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 410122983067011198558242405 76898059325064599729670451)
          ·
            refine ⟨115347088987596899594505677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76898059325064599729670451 115347088987596899594505677)
            ·
              refine ⟨43255158370348837347939629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115347088987596899594505677 43255158370348837347939629)
              ·
                refine ⟨16220684388880814005477361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43255158370348837347939629 16220684388880814005477361)
                ·
                  refine ⟨12165513291660610504108021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16220684388880814005477361 12165513291660610504108021)
                  ·
                    refine ⟨1140516871093182234760127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12165513291660610504108021 1140516871093182234760127)
                    ·
                      rfl

theorem cell22_3331723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 3, 2, 5].length) (baseStart_3331723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3331723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3331723 prefixEnd_3331723 := by exact prefixLift 3331723
  have htrace : WordTrace (prefixWord ++ tailWord_3331723) baseStart_3331723 baseEnd_3331723 := by
    simpa [prefixWord, tailWord_3331723, baseEnd_3331723] using wordTrace_append hprefix tailTrace_3331723
  have hstable : (prefixWord ++ tailWord_3331723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331723).length < 2 ^ (prefixWord ++ tailWord_3331723).sum := by decide
  have hdescent : baseEnd_3331723 < baseStart_3331723 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331770 : List Nat := [3, 1, 1, 1, 2, 4, 3, 1, 6]
def baseStart_3331770 : Nat := 118140960795 + 3331770 * 2 ^ 59
def prefixEnd_3331770 : Nat := 4983230072969 + 3 ^ 40 * 3331770 * 2
def baseEnd_3331770 : Nat := 380177653384563259611661

theorem tailTrace_3331770 : CollatzResearch.WordTrace tailWord_3331770 prefixEnd_3331770 380177653384563259611661 := by
  unfold tailWord_3331770
  simp only [CollatzResearch.WordTrace]
  refine ⟨30379908784893446464758191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81013090093049190572688509 30379908784893446464758191)
  ·
    refine ⟨45569863177340169697137287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30379908784893446464758191 45569863177340169697137287)
    ·
      refine ⟨68354794766010254545705931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45569863177340169697137287 68354794766010254545705931)
      ·
        refine ⟨102532192149015381818558897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68354794766010254545705931 102532192149015381818558897)
        ·
          refine ⟨76899144111761536363919173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102532192149015381818558897 76899144111761536363919173)
          ·
            refine ⟨14418589520955288068234845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76899144111761536363919173 14418589520955288068234845)
            ·
              refine ⟨5406971070358233025588067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14418589520955288068234845 5406971070358233025588067)
              ·
                refine ⟨8110456605537349538382101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5406971070358233025588067 8110456605537349538382101)
                ·
                  refine ⟨380177653384563259611661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8110456605537349538382101 380177653384563259611661)
                  ·
                    rfl

theorem cell22_3331770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 1, 6].length) (baseStart_3331770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3331770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3331770 prefixEnd_3331770 := by exact prefixLift 3331770
  have htrace : WordTrace (prefixWord ++ tailWord_3331770) baseStart_3331770 baseEnd_3331770 := by
    simpa [prefixWord, tailWord_3331770, baseEnd_3331770] using wordTrace_append hprefix tailTrace_3331770
  have hstable : (prefixWord ++ tailWord_3331770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331770).length < 2 ^ (prefixWord ++ tailWord_3331770).sum := by decide
  have hdescent : baseEnd_3331770 < baseStart_3331770 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331789 : List Nat := [1, 6, 2, 1, 1, 2, 1, 1, 3, 4]
def baseStart_3331789 : Nat := 118140960795 + 3331789 * 2 ^ 59
def prefixEnd_3331789 : Nat := 4983230072969 + 3 ^ 40 * 3331789 * 2
def baseEnd_3331789 : Nat := 1140539464241980062609925

theorem tailTrace_3331789 : CollatzResearch.WordTrace tailWord_3331789 prefixEnd_3331789 1140539464241980062609925 := by
  unfold tailWord_3331789
  simp only [CollatzResearch.WordTrace]
  refine ⟨121520328126504952103974421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81013552084336634735982947 121520328126504952103974421)
  ·
    refine ⟨5696265380929919629873801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 121520328126504952103974421 5696265380929919629873801)
    ·
      refine ⟨4272199035697439722405351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5696265380929919629873801 4272199035697439722405351)
      ·
        refine ⟨6408298553546159583608027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4272199035697439722405351 6408298553546159583608027)
        ·
          refine ⟨9612447830319239375412041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6408298553546159583608027 9612447830319239375412041)
          ·
            refine ⟨7209335872739429531559031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9612447830319239375412041 7209335872739429531559031)
            ·
              refine ⟨10814003809109144297338547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7209335872739429531559031 10814003809109144297338547)
              ·
                refine ⟨16221005713663716446007821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10814003809109144297338547 16221005713663716446007821)
                ·
                  refine ⟨6082877142623893667252933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16221005713663716446007821 6082877142623893667252933)
                  ·
                    refine ⟨1140539464241980062609925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6082877142623893667252933 1140539464241980062609925)
                    ·
                      rfl

theorem cell22_3331789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_3331789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3331789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3331789 prefixEnd_3331789 := by exact prefixLift 3331789
  have htrace : WordTrace (prefixWord ++ tailWord_3331789) baseStart_3331789 baseEnd_3331789 := by
    simpa [prefixWord, tailWord_3331789, baseEnd_3331789] using wordTrace_append hprefix tailTrace_3331789
  have hstable : (prefixWord ++ tailWord_3331789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331789).length < 2 ^ (prefixWord ++ tailWord_3331789).sum := by decide
  have hdescent : baseEnd_3331789 < baseStart_3331789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331815 : List Nat := [1, 1, 5, 4, 11]
def baseStart_3331815 : Nat := 118140960795 + 3331815 * 2 ^ 59
def prefixEnd_3331815 : Nat := 4983230072969 + 3 ^ 40 * 3331815 * 2
def baseEnd_3331815 : Nat := 4693614669026027413415

theorem tailTrace_3331815 : CollatzResearch.WordTrace tailWord_3331815 prefixEnd_3331815 4693614669026027413415 := by
  unfold tailWord_3331815
  simp only [CollatzResearch.WordTrace]
  refine ⟨121521276424410758544420899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81014184282940505696280599 121521276424410758544420899)
  ·
    refine ⟨182281914636616137816631349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121521276424410758544420899 182281914636616137816631349)
    ·
      refine ⟨17088929497182762920309189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 182281914636616137816631349 17088929497182762920309189)
      ·
        refine ⟨3204174280721768047557973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17088929497182762920309189 3204174280721768047557973)
        ·
          refine ⟨4693614669026027413415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 3204174280721768047557973 4693614669026027413415)
          ·
            rfl

theorem cell22_3331815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 11].length) (baseStart_3331815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3331815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3331815 prefixEnd_3331815 := by exact prefixLift 3331815
  have htrace : WordTrace (prefixWord ++ tailWord_3331815) baseStart_3331815 baseEnd_3331815 := by
    simpa [prefixWord, tailWord_3331815, baseEnd_3331815] using wordTrace_append hprefix tailTrace_3331815
  have hstable : (prefixWord ++ tailWord_3331815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331815).length < 2 ^ (prefixWord ++ tailWord_3331815).sum := by decide
  have hdescent : baseEnd_3331815 < baseStart_3331815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331821 : List Nat := [1, 5, 1, 2, 1, 4, 2, 2, 4]
def baseStart_3331821 : Nat := 118140960795 + 3331821 * 2 ^ 59
def prefixEnd_3331821 : Nat := 4983230072969 + 3 ^ 40 * 3331821 * 2
def baseEnd_3331821 : Nat := 380183472831980881936609

theorem tailTrace_3331821 : CollatzResearch.WordTrace tailWord_3331821 prefixEnd_3331821 380183472831980881936609 := by
  unfold tailWord_3331821
  simp only [CollatzResearch.WordTrace]
  refine ⟨121521495262389021569139317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81014330174926014379426211 121521495262389021569139317)
  ·
    refine ⟨11392640180848970772106811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 121521495262389021569139317 11392640180848970772106811)
    ·
      refine ⟨17088960271273456158160217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11392640180848970772106811 17088960271273456158160217)
      ·
        refine ⟨12816720203455092118620163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17088960271273456158160217 12816720203455092118620163)
        ·
          refine ⟨19225080305182638177930245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12816720203455092118620163 19225080305182638177930245)
          ·
            refine ⟨3604702557221744658361921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19225080305182638177930245 3604702557221744658361921)
            ·
              refine ⟨2703526917916308493771441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3604702557221744658361921 2703526917916308493771441)
              ·
                refine ⟨2027645188437231370328581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2703526917916308493771441 2027645188437231370328581)
                ·
                  refine ⟨380183472831980881936609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2027645188437231370328581 380183472831980881936609)
                  ·
                    rfl

theorem cell22_3331821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 2, 2, 4].length) (baseStart_3331821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3331821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3331821 prefixEnd_3331821 := by exact prefixLift 3331821
  have htrace : WordTrace (prefixWord ++ tailWord_3331821) baseStart_3331821 baseEnd_3331821 := by
    simpa [prefixWord, tailWord_3331821, baseEnd_3331821] using wordTrace_append hprefix tailTrace_3331821
  have hstable : (prefixWord ++ tailWord_3331821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331821).length < 2 ^ (prefixWord ++ tailWord_3331821).sum := by decide
  have hdescent : baseEnd_3331821 < baseStart_3331821 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331864 : List Nat := [2, 1, 2, 3, 1, 1, 3, 5, 1, 3]
def baseStart_3331864 : Nat := 118140960795 + 3331864 * 2 ^ 59
def prefixEnd_3331864 : Nat := 4983230072969 + 3 ^ 40 * 3331864 * 2
def baseEnd_3331864 : Nat := 1140565138274704866984695

theorem tailTrace_3331864 : CollatzResearch.WordTrace tailWord_3331864 prefixEnd_3331864 1140565138274704866984695 := by
  unfold tailWord_3331864
  simp only [CollatzResearch.WordTrace]
  refine ⟨60761531800616619956477323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81015375734155493275303097 60761531800616619956477323)
  ·
    refine ⟨91142297700924929934715985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60761531800616619956477323 91142297700924929934715985)
    ·
      refine ⟨68356723275693697451036989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91142297700924929934715985 68356723275693697451036989)
      ·
        refine ⟨25633771228385136544138871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68356723275693697451036989 25633771228385136544138871)
        ·
          refine ⟨38450656842577704816208307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25633771228385136544138871 38450656842577704816208307)
          ·
            refine ⟨57675985263866557224312461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38450656842577704816208307 57675985263866557224312461)
            ·
              refine ⟨21628494473949958959117173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57675985263866557224312461 21628494473949958959117173)
              ·
                refine ⟨2027671356932808652417235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21628494473949958959117173 2027671356932808652417235)
                ·
                  refine ⟨3041507035399212978625853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2027671356932808652417235 3041507035399212978625853)
                  ·
                    refine ⟨1140565138274704866984695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3041507035399212978625853 1140565138274704866984695)
                    ·
                      rfl

theorem cell22_3331864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 5, 1, 3].length) (baseStart_3331864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3331864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3331864 prefixEnd_3331864 := by exact prefixLift 3331864
  have htrace : WordTrace (prefixWord ++ tailWord_3331864) baseStart_3331864 baseEnd_3331864 := by
    simpa [prefixWord, tailWord_3331864, baseEnd_3331864] using wordTrace_append hprefix tailTrace_3331864
  have hstable : (prefixWord ++ tailWord_3331864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331864).length < 2 ^ (prefixWord ++ tailWord_3331864).sum := by decide
  have hdescent : baseEnd_3331864 < baseStart_3331864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331870 : List Nat := [4, 3, 2, 2, 1, 2, 1, 2, 2, 3]
def baseStart_3331870 : Nat := 118140960795 + 3331870 * 2 ^ 59
def prefixEnd_3331870 : Nat := 4983230072969 + 3 ^ 40 * 3331870 * 2
def baseEnd_3331870 : Nat := 1140567192197322851334677

theorem tailTrace_3331870 : CollatzResearch.WordTrace tailWord_3331870 prefixEnd_3331870 1140567192197322851334677 := by
  unfold tailWord_3331870
  simp only [CollatzResearch.WordTrace]
  refine ⟨15190410304901437867209133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81015521626141001958448709 15190410304901437867209133)
  ·
    refine ⟨5696403864338039200203425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15190410304901437867209133 5696403864338039200203425)
    ·
      refine ⟨4272302898253529400152569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5696403864338039200203425 4272302898253529400152569)
      ·
        refine ⟨3204227173690147050114427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4272302898253529400152569 3204227173690147050114427)
        ·
          refine ⟨4806340760535220575171641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3204227173690147050114427 4806340760535220575171641)
          ·
            refine ⟨3604755570401415431378731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4806340760535220575171641 3604755570401415431378731)
            ·
              refine ⟨5407133355602123147068097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3604755570401415431378731 5407133355602123147068097)
              ·
                refine ⟨4055350016701592360301073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5407133355602123147068097 4055350016701592360301073)
                ·
                  refine ⟨3041512512526194270225805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4055350016701592360301073 3041512512526194270225805)
                  ·
                    refine ⟨1140567192197322851334677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3041512512526194270225805 1140567192197322851334677)
                    ·
                      rfl

theorem cell22_3331870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_3331870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3331870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3331870 prefixEnd_3331870 := by exact prefixLift 3331870
  have htrace : WordTrace (prefixWord ++ tailWord_3331870) baseStart_3331870 baseEnd_3331870 := by
    simpa [prefixWord, tailWord_3331870, baseEnd_3331870] using wordTrace_append hprefix tailTrace_3331870
  have hstable : (prefixWord ++ tailWord_3331870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331870).length < 2 ^ (prefixWord ++ tailWord_3331870).sum := by decide
  have hdescent : baseEnd_3331870 < baseStart_3331870 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331875 : List Nat := [1, 1, 1, 4, 2, 1, 3, 2, 2, 5]
def baseStart_3331875 : Nat := 118140960795 + 3331875 * 2 ^ 59
def prefixEnd_3331875 : Nat := 4983230072969 + 3 ^ 40 * 3331875 * 2
def baseEnd_3331875 : Nat := 1140568903799504504959661

theorem tailTrace_3331875 : CollatzResearch.WordTrace tailWord_3331875 prefixEnd_3331875 1140568903799504504959661 := by
  unfold tailWord_3331875
  simp only [CollatzResearch.WordTrace]
  refine ⟨121523464804193388791605079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81015643202795592527736719 121523464804193388791605079)
  ·
    refine ⟨182285197206290083187407619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121523464804193388791605079 182285197206290083187407619)
    ·
      refine ⟨273427795809435124781111429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182285197206290083187407619 273427795809435124781111429)
      ·
        refine ⟨51267711714269085896458393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 273427795809435124781111429 51267711714269085896458393)
        ·
          refine ⟨38450783785701814422343795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51267711714269085896458393 38450783785701814422343795)
          ·
            refine ⟨57676175678552721633515693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38450783785701814422343795 57676175678552721633515693)
            ·
              refine ⟨21628565879457270612568385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57676175678552721633515693 21628565879457270612568385)
              ·
                refine ⟨16221424409592952959426289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21628565879457270612568385 16221424409592952959426289)
                ·
                  refine ⟨12166068307194714719569717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16221424409592952959426289 12166068307194714719569717)
                  ·
                    refine ⟨1140568903799504504959661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12166068307194714719569717 1140568903799504504959661)
                    ·
                      rfl

theorem cell22_3331875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 2, 2, 5].length) (baseStart_3331875 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3331875 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3331875 prefixEnd_3331875 := by exact prefixLift 3331875
  have htrace : WordTrace (prefixWord ++ tailWord_3331875) baseStart_3331875 baseEnd_3331875 := by
    simpa [prefixWord, tailWord_3331875, baseEnd_3331875] using wordTrace_append hprefix tailTrace_3331875
  have hstable : (prefixWord ++ tailWord_3331875).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331875).length < 2 ^ (prefixWord ++ tailWord_3331875).sum := by decide
  have hdescent : baseEnd_3331875 < baseStart_3331875 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331877 : List Nat := [1, 3, 1, 2, 3, 2, 3, 2, 5]
def baseStart_3331877 : Nat := 118140960795 + 3331877 * 2 ^ 59
def prefixEnd_3331877 : Nat := 4983230072969 + 3 ^ 40 * 3331877 * 2
def baseEnd_3331877 : Nat := 380189862813459055469885

theorem tailTrace_3331877 : CollatzResearch.WordTrace tailWord_3331877 prefixEnd_3331877 380189862813459055469885 := by
  unfold tailWord_3331877
  simp only [CollatzResearch.WordTrace]
  refine ⟨121523537750186143133177885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81015691833457428755451923 121523537750186143133177885)
  ·
    refine ⟨45571326656319803674941707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121523537750186143133177885 45571326656319803674941707)
    ·
      refine ⟨68356989984479705512412561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45571326656319803674941707 68356989984479705512412561)
      ·
        refine ⟨51267742488359779134309421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68356989984479705512412561 51267742488359779134309421)
        ·
          refine ⟨19225403433134917175366033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51267742488359779134309421 19225403433134917175366033)
          ·
            refine ⟨14419052574851187881524525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19225403433134917175366033 14419052574851187881524525)
            ·
              refine ⟨5407144715569195455571697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14419052574851187881524525 5407144715569195455571697)
              ·
                refine ⟨4055358536676896591678773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5407144715569195455571697 4055358536676896591678773)
                ·
                  refine ⟨380189862813459055469885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4055358536676896591678773 380189862813459055469885)
                  ·
                    rfl

theorem cell22_3331877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 2, 5].length) (baseStart_3331877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3331877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3331877 prefixEnd_3331877 := by exact prefixLift 3331877
  have htrace : WordTrace (prefixWord ++ tailWord_3331877) baseStart_3331877 baseEnd_3331877 := by
    simpa [prefixWord, tailWord_3331877, baseEnd_3331877] using wordTrace_append hprefix tailTrace_3331877
  have hstable : (prefixWord ++ tailWord_3331877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331877).length < 2 ^ (prefixWord ++ tailWord_3331877).sum := by decide
  have hdescent : baseEnd_3331877 < baseStart_3331877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331907 : List Nat := [1, 1, 1, 3, 1, 5, 1, 4, 1, 4]
def baseStart_3331907 : Nat := 118140960795 + 3331907 * 2 ^ 59
def prefixEnd_3331907 : Nat := 4983230072969 + 3 ^ 40 * 3331907 * 2
def baseEnd_3331907 : Nat := 1140579858053467088159563

theorem tailTrace_3331907 : CollatzResearch.WordTrace tailWord_3331907 prefixEnd_3331907 1140579858053467088159563 := by
  unfold tailWord_3331907
  simp only [CollatzResearch.WordTrace]
  refine ⟨121524631940077458256769975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81016421293384972171179983 121524631940077458256769975)
  ·
    refine ⟨182286947910116187385154963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121524631940077458256769975 182286947910116187385154963)
    ·
      refine ⟨273430421865174281077732445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182286947910116187385154963 273430421865174281077732445)
      ·
        refine ⟨102536408199440355404149667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 273430421865174281077732445 102536408199440355404149667)
        ·
          refine ⟨153804612299160533106224501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102536408199440355404149667 153804612299160533106224501)
          ·
            refine ⟨14419182403046299978708547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 153804612299160533106224501 14419182403046299978708547)
            ·
              refine ⟨21628773604569449968062821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14419182403046299978708547 21628773604569449968062821)
              ·
                refine ⟨4055395050856771869011779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21628773604569449968062821 4055395050856771869011779)
                ·
                  refine ⟨6083092576285157803517669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4055395050856771869011779 6083092576285157803517669)
                  ·
                    refine ⟨1140579858053467088159563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6083092576285157803517669 1140579858053467088159563)
                    ·
                      rfl

theorem cell22_3331907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 4, 1, 4].length) (baseStart_3331907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3331907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3331907 prefixEnd_3331907 := by exact prefixLift 3331907
  have htrace : WordTrace (prefixWord ++ tailWord_3331907) baseStart_3331907 baseEnd_3331907 := by
    simpa [prefixWord, tailWord_3331907, baseEnd_3331907] using wordTrace_append hprefix tailTrace_3331907
  have hstable : (prefixWord ++ tailWord_3331907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331907).length < 2 ^ (prefixWord ++ tailWord_3331907).sum := by decide
  have hdescent : baseEnd_3331907 < baseStart_3331907 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331920 : List Nat := [2, 1, 1, 1, 1, 4, 1, 3, 3, 5]
def baseStart_3331920 : Nat := 118140960795 + 3331920 * 2 ^ 59
def prefixEnd_3331920 : Nat := 4983230072969 + 3 ^ 40 * 3331920 * 2
def baseEnd_3331920 : Nat := 1140584308219139387584523

theorem tailTrace_3331920 : CollatzResearch.WordTrace tailWord_3331920 prefixEnd_3331920 1140584308219139387584523 := by
  unfold tailWord_3331920
  simp only [CollatzResearch.WordTrace]
  refine ⟨60762553044515180738496607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81016737392686907651328809 60762553044515180738496607)
  ·
    refine ⟨91143829566772771107744911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60762553044515180738496607 91143829566772771107744911)
    ·
      refine ⟨136715744350159156661617367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91143829566772771107744911 136715744350159156661617367)
      ·
        refine ⟨205073616525238734992426051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136715744350159156661617367 205073616525238734992426051)
        ·
          refine ⟨307610424787858102488639077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205073616525238734992426051 307610424787858102488639077)
          ·
            refine ⟨57676954647723394216619827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 307610424787858102488639077 57676954647723394216619827)
            ·
              refine ⟨86515431971585091324929741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57676954647723394216619827 86515431971585091324929741)
              ·
                refine ⟨32443286989344409246848653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86515431971585091324929741 32443286989344409246848653)
                ·
                  refine ⟨12166232621004153467568245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32443286989344409246848653 12166232621004153467568245)
                  ·
                    refine ⟨1140584308219139387584523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12166232621004153467568245 1140584308219139387584523)
                    ·
                      rfl

theorem cell22_3331920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 3, 5].length) (baseStart_3331920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3331920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3331920 prefixEnd_3331920 := by exact prefixLift 3331920
  have htrace : WordTrace (prefixWord ++ tailWord_3331920) baseStart_3331920 baseEnd_3331920 := by
    simpa [prefixWord, tailWord_3331920, baseEnd_3331920] using wordTrace_append hprefix tailTrace_3331920
  have hstable : (prefixWord ++ tailWord_3331920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331920).length < 2 ^ (prefixWord ++ tailWord_3331920).sum := by decide
  have hdescent : baseEnd_3331920 < baseStart_3331920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331924 : List Nat := [2, 4, 1, 1, 3, 1, 2, 3, 1, 4]
def baseStart_3331924 : Nat := 118140960795 + 3331924 * 2 ^ 59
def prefixEnd_3331924 : Nat := 4983230072969 + 3 ^ 40 * 3331924 * 2
def baseEnd_3331924 : Nat := 1140585677500884710484511

theorem tailTrace_3331924 : CollatzResearch.WordTrace tailWord_3331924 prefixEnd_3331924 1140585677500884710484511 := by
  unfold tailWord_3331924
  simp only [CollatzResearch.WordTrace]
  refine ⟨60762625990507935080069413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81016834654010580106759217 60762625990507935080069413)
  ·
    refine ⟨11392992373220237827513015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60762625990507935080069413 11392992373220237827513015)
    ·
      refine ⟨17089488559830356741269523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11392992373220237827513015 17089488559830356741269523)
      ·
        refine ⟨25634232839745535111904285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17089488559830356741269523 25634232839745535111904285)
        ·
          refine ⟨9612837314904575666964107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25634232839745535111904285 9612837314904575666964107)
          ·
            refine ⟨14419255972356863500446161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9612837314904575666964107 14419255972356863500446161)
            ·
              refine ⟨10814441979267647625334621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14419255972356863500446161 10814441979267647625334621)
              ·
                refine ⟨4055415742225367859500483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10814441979267647625334621 4055415742225367859500483)
                ·
                  refine ⟨6083123613338051789250725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4055415742225367859500483 6083123613338051789250725)
                  ·
                    refine ⟨1140585677500884710484511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6083123613338051789250725 1140585677500884710484511)
                    ·
                      rfl

theorem cell22_3331924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_3331924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3331924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3331924 prefixEnd_3331924 := by exact prefixLift 3331924
  have htrace : WordTrace (prefixWord ++ tailWord_3331924) baseStart_3331924 baseEnd_3331924 := by
    simpa [prefixWord, tailWord_3331924, baseEnd_3331924] using wordTrace_append hprefix tailTrace_3331924
  have hstable : (prefixWord ++ tailWord_3331924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331924).length < 2 ^ (prefixWord ++ tailWord_3331924).sum := by decide
  have hdescent : baseEnd_3331924 < baseStart_3331924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331937 : List Nat := [1, 2, 3, 1, 1, 1, 3, 3, 4, 3]
def baseStart_3331937 : Nat := 118140960795 + 3331937 * 2 ^ 59
def prefixEnd_3331937 : Nat := 4983230072969 + 3 ^ 40 * 3331937 * 2
def baseEnd_3331937 : Nat := 1140590127666557009909471

theorem tailTrace_3331937 : CollatzResearch.WordTrace tailWord_3331937 prefixEnd_3331937 1140590127666557009909471 := by
  unfold tailWord_3331937
  simp only [CollatzResearch.WordTrace]
  refine ⟨121525726129968773380362065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81017150753312515586908043 121525726129968773380362065)
  ·
    refine ⟨91144294597476580035271549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121525726129968773380362065 91144294597476580035271549)
    ·
      refine ⟨34179110474053717513226831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91144294597476580035271549 34179110474053717513226831)
      ·
        refine ⟨51268665711080576269840247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34179110474053717513226831 51268665711080576269840247)
        ·
          refine ⟨76902998566620864404760371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51268665711080576269840247 76902998566620864404760371)
          ·
            refine ⟨115354497849931296607140557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76902998566620864404760371 115354497849931296607140557)
            ·
              refine ⟨43257936693724236227677709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115354497849931296607140557 43257936693724236227677709)
              ·
                refine ⟨16221726260146588585379141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43257936693724236227677709 16221726260146588585379141)
                ·
                  refine ⟨3041573673777485359758589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16221726260146588585379141 3041573673777485359758589)
                  ·
                    refine ⟨1140590127666557009909471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3041573673777485359758589 1140590127666557009909471)
                    ·
                      rfl

theorem cell22_3331937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 3, 4, 3].length) (baseStart_3331937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3331937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3331937 prefixEnd_3331937 := by exact prefixLift 3331937
  have htrace : WordTrace (prefixWord ++ tailWord_3331937) baseStart_3331937 baseEnd_3331937 := by
    simpa [prefixWord, tailWord_3331937, baseEnd_3331937] using wordTrace_append hprefix tailTrace_3331937
  have hstable : (prefixWord ++ tailWord_3331937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331937).length < 2 ^ (prefixWord ++ tailWord_3331937).sum := by decide
  have hdescent : baseEnd_3331937 < baseStart_3331937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331939 : List Nat := [1, 1, 1, 5, 4, 2, 1, 1, 6]
def baseStart_3331939 : Nat := 118140960795 + 3331939 * 2 ^ 59
def prefixEnd_3331939 : Nat := 4983230072969 + 3 ^ 40 * 3331939 * 2
def baseEnd_3331939 : Nat := 380196937435809890453155

theorem tailTrace_3331939 : CollatzResearch.WordTrace tailWord_3331939 prefixEnd_3331939 380196937435809890453155 := by
  unfold tailWord_3331939
  simp only [CollatzResearch.WordTrace]
  refine ⟨121525799075961527721934871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81017199383974351814623247 121525799075961527721934871)
  ·
    refine ⟨182288698613942291582902307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121525799075961527721934871 182288698613942291582902307)
    ·
      refine ⟨273433047920913437374353461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182288698613942291582902307 273433047920913437374353461)
      ·
        refine ⟨25634348242585634753845637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 273433047920913437374353461 25634348242585634753845637)
        ·
          refine ⟨4806440295484806516346057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25634348242585634753845637 4806440295484806516346057)
          ·
            refine ⟨3604830221613604887259543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4806440295484806516346057 3604830221613604887259543)
            ·
              refine ⟨5407245332420407330889315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3604830221613604887259543 5407245332420407330889315)
              ·
                refine ⟨8110867998630610996333973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5407245332420407330889315 8110867998630610996333973)
                ·
                  refine ⟨380196937435809890453155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8110867998630610996333973 380196937435809890453155)
                  ·
                    rfl

theorem cell22_3331939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 1, 6].length) (baseStart_3331939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3331939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3331939 prefixEnd_3331939 := by exact prefixLift 3331939
  have htrace : WordTrace (prefixWord ++ tailWord_3331939) baseStart_3331939 baseEnd_3331939 := by
    simpa [prefixWord, tailWord_3331939, baseEnd_3331939] using wordTrace_append hprefix tailTrace_3331939
  have hstable : (prefixWord ++ tailWord_3331939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331939).length < 2 ^ (prefixWord ++ tailWord_3331939).sum := by decide
  have hdescent : baseEnd_3331939 < baseStart_3331939 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331958 : List Nat := [5, 1, 1, 3, 2, 2, 1, 2, 1, 4]
def baseStart_3331958 : Nat := 118140960795 + 3331958 * 2 ^ 59
def prefixEnd_3331958 : Nat := 4983230072969 + 3 ^ 40 * 3331958 * 2
def baseEnd_3331958 : Nat := 1140597316395719955134407

theorem tailTrace_3331958 : CollatzResearch.WordTrace tailWord_3331958 prefixEnd_3331958 1140597316395719955134407 := by
  unfold tailWord_3331958
  simp only [CollatzResearch.WordTrace]
  refine ⟨7595405753930793372929783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81017661375261795977917685 7595405753930793372929783)
  ·
    refine ⟨11393108630896190059394675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7595405753930793372929783 11393108630896190059394675)
    ·
      refine ⟨17089662946344285089092013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11393108630896190059394675 17089662946344285089092013)
      ·
        refine ⟨6408623604879106908409505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17089662946344285089092013 6408623604879106908409505)
        ·
          refine ⟨4806467703659330181307129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6408623604879106908409505 4806467703659330181307129)
          ·
            refine ⟨3604850777744497635980347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4806467703659330181307129 3604850777744497635980347)
            ·
              refine ⟨5407276166616746453970521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3604850777744497635980347 5407276166616746453970521)
              ·
                refine ⟨4055457124962559840477891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5407276166616746453970521 4055457124962559840477891)
                ·
                  refine ⟨6083185687443839760716837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4055457124962559840477891 6083185687443839760716837)
                  ·
                    refine ⟨1140597316395719955134407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6083185687443839760716837 1140597316395719955134407)
                    ·
                      rfl

theorem cell22_3331958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 2, 1, 4].length) (baseStart_3331958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3331958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3331958 prefixEnd_3331958 := by exact prefixLift 3331958
  have htrace : WordTrace (prefixWord ++ tailWord_3331958) baseStart_3331958 baseEnd_3331958 := by
    simpa [prefixWord, tailWord_3331958, baseEnd_3331958] using wordTrace_append hprefix tailTrace_3331958
  have hstable : (prefixWord ++ tailWord_3331958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331958).length < 2 ^ (prefixWord ++ tailWord_3331958).sum := by decide
  have hdescent : baseEnd_3331958 < baseStart_3331958 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331990 : List Nat := [5, 3, 1, 1, 2, 1, 1, 4, 4]
def baseStart_3331990 : Nat := 118140960795 + 3331990 * 2 ^ 59
def prefixEnd_3331990 : Nat := 4983230072969 + 3 ^ 40 * 3331990 * 2
def baseEnd_3331990 : Nat := 380202756883227512778103

theorem tailTrace_3331990 : CollatzResearch.WordTrace tailWord_3331990 prefixEnd_3331990 380202756883227512778103 := by
  unfold tailWord_3331990
  simp only [CollatzResearch.WordTrace]
  refine ⟨7595478699923547714502589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81018439465851175621360949 7595478699923547714502589)
  ·
    refine ⟨2848304512471330392938471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7595478699923547714502589 2848304512471330392938471)
    ·
      refine ⟨4272456768706995589407707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2848304512471330392938471 4272456768706995589407707)
      ·
        refine ⟨6408685153060493384111561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4272456768706995589407707 6408685153060493384111561)
        ·
          refine ⟨4806513864795370038083671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6408685153060493384111561 4806513864795370038083671)
          ·
            refine ⟨7209770797193055057125507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4806513864795370038083671 7209770797193055057125507)
            ·
              refine ⟨10814656195789582585688261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7209770797193055057125507 10814656195789582585688261)
              ·
                refine ⟨2027748036710546734816549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10814656195789582585688261 2027748036710546734816549)
                ·
                  refine ⟨380202756883227512778103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2027748036710546734816549 380202756883227512778103)
                  ·
                    rfl

theorem cell22_3331990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_3331990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3331990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3331990 prefixEnd_3331990 := by exact prefixLift 3331990
  have htrace : WordTrace (prefixWord ++ tailWord_3331990) baseStart_3331990 baseEnd_3331990 := by
    simpa [prefixWord, tailWord_3331990, baseEnd_3331990] using wordTrace_append hprefix tailTrace_3331990
  have hstable : (prefixWord ++ tailWord_3331990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331990).length < 2 ^ (prefixWord ++ tailWord_3331990).sum := by decide
  have hdescent : baseEnd_3331990 < baseStart_3331990 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331997 : List Nat := [1, 4, 2, 1, 2, 2, 1, 1, 2, 6]
def baseStart_3331997 : Nat := 118140960795 + 3331997 * 2 ^ 59
def prefixEnd_3331997 : Nat := 4983230072969 + 3 ^ 40 * 3331997 * 2
def baseEnd_3331997 : Nat := 1140610666892736853409287

theorem tailTrace_3331997 : CollatzResearch.WordTrace tailWord_3331997 prefixEnd_3331997 1140610666892736853409287 := by
  unfold tailWord_3331997
  simp only [CollatzResearch.WordTrace]
  refine ⟨121527914509751403627546245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81018609673167602418364163 121527914509751403627546245)
  ·
    refine ⟨22786483970578388180164921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121527914509751403627546245 22786483970578388180164921)
    ·
      refine ⟨17089862977933791135123691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22786483970578388180164921 17089862977933791135123691)
      ·
        refine ⟨25634794466900686702685537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17089862977933791135123691 25634794466900686702685537)
        ·
          refine ⟨19226095850175515027014153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25634794466900686702685537 19226095850175515027014153)
          ·
            refine ⟨14419571887631636270260615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19226095850175515027014153 14419571887631636270260615)
            ·
              refine ⟨21629357831447454405390923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14419571887631636270260615 21629357831447454405390923)
              ·
                refine ⟨32444036747171181608086385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21629357831447454405390923 32444036747171181608086385)
                ·
                  refine ⟨24333027560378386206064789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32444036747171181608086385 24333027560378386206064789)
                  ·
                    refine ⟨1140610666892736853409287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24333027560378386206064789 1140610666892736853409287)
                    ·
                      rfl

theorem cell22_3331997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_3331997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3331997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3331997 prefixEnd_3331997 := by exact prefixLift 3331997
  have htrace : WordTrace (prefixWord ++ tailWord_3331997) baseStart_3331997 baseEnd_3331997 := by
    simpa [prefixWord, tailWord_3331997, baseEnd_3331997] using wordTrace_append hprefix tailTrace_3331997
  have hstable : (prefixWord ++ tailWord_3331997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331997).length < 2 ^ (prefixWord ++ tailWord_3331997).sum := by decide
  have hdescent : baseEnd_3331997 < baseStart_3331997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3332001 : List Nat := [1, 2, 3, 4, 3, 1, 1, 7]
def baseStart_3332001 : Nat := 118140960795 + 3332001 * 2 ^ 59
def prefixEnd_3332001 : Nat := 4983230072969 + 3 ^ 40 * 3332001 * 2
def baseEnd_3332001 : Nat := 126734670686053575145475

theorem tailTrace_3332001 : CollatzResearch.WordTrace tailWord_3332001 prefixEnd_3332001 126734670686053575145475 := by
  unfold tailWord_3332001
  simp only [CollatzResearch.WordTrace]
  refine ⟨121528060401736912310691857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81018706934491274873794571 121528060401736912310691857)
  ·
    refine ⟨91146045301302684233018893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121528060401736912310691857 91146045301302684233018893)
    ·
      refine ⟨34179766987988506587382085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91146045301302684233018893 34179766987988506587382085)
      ·
        refine ⟨6408706310247844985134141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34179766987988506587382085 6408706310247844985134141)
        ·
          refine ⟨2403264866342941869425303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6408706310247844985134141 2403264866342941869425303)
          ·
            refine ⟨3604897299514412804137955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2403264866342941869425303 3604897299514412804137955)
            ·
              refine ⟨5407345949271619206206933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3604897299514412804137955 5407345949271619206206933)
              ·
                refine ⟨126734670686053575145475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5407345949271619206206933 126734670686053575145475)
                ·
                  rfl

theorem cell22_3332001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 7].length) (baseStart_3332001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3332001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3332001 prefixEnd_3332001 := by exact prefixLift 3332001
  have htrace : WordTrace (prefixWord ++ tailWord_3332001) baseStart_3332001 baseEnd_3332001 := by
    simpa [prefixWord, tailWord_3332001, baseEnd_3332001] using wordTrace_append hprefix tailTrace_3332001
  have hstable : (prefixWord ++ tailWord_3332001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3332001).length < 2 ^ (prefixWord ++ tailWord_3332001).sum := by decide
  have hdescent : baseEnd_3332001 < baseStart_3332001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3332001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3332020 : List Nat := [2, 5, 2, 1, 3, 1, 1, 1, 2, 4]
def baseStart_3332020 : Nat := 118140960795 + 3332020 * 2 ^ 59
def prefixEnd_3332020 : Nat := 4983230072969 + 3 ^ 40 * 3332020 * 2
def baseEnd_3332020 : Nat := 1140618540262772460084217

theorem tailTrace_3332020 : CollatzResearch.WordTrace tailWord_3332020 prefixEnd_3332020 1140618540262772460084217 := by
  unfold tailWord_3332020
  simp only [CollatzResearch.WordTrace]
  refine ⟨60764376694334039277816757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81019168925778719037089009 60764376694334039277816757)
  ·
    refine ⟨5696660315093816182295321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60764376694334039277816757 5696660315093816182295321)
    ·
      refine ⟨4272495236320362136721491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5696660315093816182295321 4272495236320362136721491)
      ·
        refine ⟨6408742854480543205082237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4272495236320362136721491 6408742854480543205082237)
        ·
          refine ⟨2403278570430203701905839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6408742854480543205082237 2403278570430203701905839)
          ·
            refine ⟨3604917855645305552858759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2403278570430203701905839 3604917855645305552858759)
            ·
              refine ⟨5407376783467958329288139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3604917855645305552858759 5407376783467958329288139)
              ·
                refine ⟨8111065175201937493932209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5407376783467958329288139 8111065175201937493932209)
                ·
                  refine ⟨6083298881401453120449157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8111065175201937493932209 6083298881401453120449157)
                  ·
                    refine ⟨1140618540262772460084217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6083298881401453120449157 1140618540262772460084217)
                    ·
                      rfl

theorem cell22_3332020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_3332020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3332020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3332020 prefixEnd_3332020 := by exact prefixLift 3332020
  have htrace : WordTrace (prefixWord ++ tailWord_3332020) baseStart_3332020 baseEnd_3332020 := by
    simpa [prefixWord, tailWord_3332020, baseEnd_3332020] using wordTrace_append hprefix tailTrace_3332020
  have hstable : (prefixWord ++ tailWord_3332020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3332020).length < 2 ^ (prefixWord ++ tailWord_3332020).sum := by decide
  have hdescent : baseEnd_3332020 < baseStart_3332020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3332020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3332087 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 8, 4]
def baseStart_3332087 : Nat := 118140960795 + 3332087 * 2 ^ 59
def prefixEnd_3332087 : Nat := 4983230072969 + 3 ^ 40 * 3332087 * 2
def baseEnd_3332087 : Nat := 1140641475732006618659011

theorem tailTrace_3332087 : CollatzResearch.WordTrace tailWord_3332087 prefixEnd_3332087 1140641475732006618659011 := by
  unfold tailWord_3332087
  simp only [CollatzResearch.WordTrace]
  refine ⟨121531197079425348998322515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81020798052950232665548343 121531197079425348998322515)
  ·
    refine ⟨182296795619138023497483773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121531197079425348998322515 182296795619138023497483773)
    ·
      refine ⟨68361298357176758811556415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182296795619138023497483773 68361298357176758811556415)
      ·
        refine ⟨102541947535765138217334623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68361298357176758811556415 102541947535765138217334623)
        ·
          refine ⟨153812921303647707326001935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102541947535765138217334623 153812921303647707326001935)
          ·
            refine ⟨230719381955471560989002903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153812921303647707326001935 230719381955471560989002903)
            ·
              refine ⟨346079072933207341483504355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230719381955471560989002903 346079072933207341483504355)
              ·
                refine ⟨519118609399811012225256533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 346079072933207341483504355 519118609399811012225256533)
                ·
                  refine ⟨6083421203904035299514725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 519118609399811012225256533 6083421203904035299514725)
                  ·
                    refine ⟨1140641475732006618659011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6083421203904035299514725 1140641475732006618659011)
                    ·
                      rfl

theorem cell22_3332087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 8, 4].length) (baseStart_3332087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3332087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3332087 prefixEnd_3332087 := by exact prefixLift 3332087
  have htrace : WordTrace (prefixWord ++ tailWord_3332087) baseStart_3332087 baseEnd_3332087 := by
    simpa [prefixWord, tailWord_3332087, baseEnd_3332087] using wordTrace_append hprefix tailTrace_3332087
  have hstable : (prefixWord ++ tailWord_3332087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3332087).length < 2 ^ (prefixWord ++ tailWord_3332087).sum := by decide
  have hdescent : baseEnd_3332087 < baseStart_3332087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3332087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3332089 : List Nat := [1, 2, 1, 3, 1, 4, 1, 2, 4, 3]
def baseStart_3332089 : Nat := 118140960795 + 3332089 * 2 ^ 59
def prefixEnd_3332089 : Nat := 4983230072969 + 3 ^ 40 * 3332089 * 2
def baseEnd_3332089 : Nat := 1140642160372879280109005

theorem tailTrace_3332089 : CollatzResearch.WordTrace tailWord_3332089 prefixEnd_3332089 1140642160372879280109005 := by
  unfold tailWord_3332089
  simp only [CollatzResearch.WordTrace]
  refine ⟨121531270025418103339895321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81020846683612068893263547 121531270025418103339895321)
  ·
    refine ⟨91148452519063577504921491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121531270025418103339895321 91148452519063577504921491)
    ·
      refine ⟨136722678778595366257382237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91148452519063577504921491 136722678778595366257382237)
      ·
        refine ⟨51271004541973262346518339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136722678778595366257382237 51271004541973262346518339)
        ·
          refine ⟨76906506812959893519777509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51271004541973262346518339 76906506812959893519777509)
          ·
            refine ⟨14419970027429980034958283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76906506812959893519777509 14419970027429980034958283)
            ·
              refine ⟨21629955041144970052437425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14419970027429980034958283 21629955041144970052437425)
              ·
                refine ⟨16222466280858727539328069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21629955041144970052437425 16222466280858727539328069)
                ·
                  refine ⟨3041712427661011413624013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16222466280858727539328069 3041712427661011413624013)
                  ·
                    refine ⟨1140642160372879280109005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3041712427661011413624013 1140642160372879280109005)
                    ·
                      rfl

theorem cell22_3332089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 2, 4, 3].length) (baseStart_3332089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3332089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3332089 prefixEnd_3332089 := by exact prefixLift 3332089
  have htrace : WordTrace (prefixWord ++ tailWord_3332089) baseStart_3332089 baseEnd_3332089 := by
    simpa [prefixWord, tailWord_3332089, baseEnd_3332089] using wordTrace_append hprefix tailTrace_3332089
  have hstable : (prefixWord ++ tailWord_3332089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3332089).length < 2 ^ (prefixWord ++ tailWord_3332089).sum := by decide
  have hdescent : baseEnd_3332089 < baseStart_3332089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3332089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3332104 : List Nat := [2, 1, 3, 2, 1, 2, 3, 2, 2, 4]
def baseStart_3332104 : Nat := 118140960795 + 3332104 * 2 ^ 59
def prefixEnd_3332104 : Nat := 4983230072969 + 3 ^ 40 * 3332104 * 2
def baseEnd_3332104 : Nat := 1140647295179424240983959

theorem tailTrace_3332104 : CollatzResearch.WordTrace tailWord_3332104 prefixEnd_3332104 1140647295179424240983959 := by
  unfold tailWord_3332104
  simp only [CollatzResearch.WordTrace]
  refine ⟨60765908560181880450845683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81021211413575840601127577 60765908560181880450845683)
  ·
    refine ⟨91148862840272820676268525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60765908560181880450845683 91148862840272820676268525)
    ·
      refine ⟨34180823565102307753600697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91148862840272820676268525 34180823565102307753600697)
      ·
        refine ⟨25635617673826730815200523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34180823565102307753600697 25635617673826730815200523)
        ·
          refine ⟨38453426510740096222800785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25635617673826730815200523 38453426510740096222800785)
          ·
            refine ⟨28840069883055072167100589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38453426510740096222800785 28840069883055072167100589)
            ·
              refine ⟨10815026206145652062662721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28840069883055072167100589 10815026206145652062662721)
              ·
                refine ⟨8111269654609239046997041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10815026206145652062662721 8111269654609239046997041)
                ·
                  refine ⟨6083452240956929285247781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8111269654609239046997041 6083452240956929285247781)
                  ·
                    refine ⟨1140647295179424240983959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6083452240956929285247781 1140647295179424240983959)
                    ·
                      rfl

theorem cell22_3332104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 2, 2, 4].length) (baseStart_3332104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3332104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3332104 prefixEnd_3332104 := by exact prefixLift 3332104
  have htrace : WordTrace (prefixWord ++ tailWord_3332104) baseStart_3332104 baseEnd_3332104 := by
    simpa [prefixWord, tailWord_3332104, baseEnd_3332104] using wordTrace_append hprefix tailTrace_3332104
  have hstable : (prefixWord ++ tailWord_3332104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3332104).length < 2 ^ (prefixWord ++ tailWord_3332104).sum := by decide
  have hdescent : baseEnd_3332104 < baseStart_3332104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3332104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3332147 : List Nat := [1, 1, 1, 2, 4, 1, 2, 1, 9]
def baseStart_3332147 : Nat := 118140960795 + 3332147 * 2 ^ 59
def prefixEnd_3332147 : Nat := 4983230072969 + 3 ^ 40 * 3332147 * 2
def baseEnd_3332147 : Nat := 380220671652728820719609

theorem tailTrace_3332147 : CollatzResearch.WordTrace tailWord_3332147 prefixEnd_3332147 380220671652728820719609 := by
  unfold tailWord_3332147
  simp only [CollatzResearch.WordTrace]
  refine ⟨121533385459207979245506695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81022256972805319497004463 121533385459207979245506695)
  ·
    refine ⟨182300078188811968868260043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121533385459207979245506695 182300078188811968868260043)
    ·
      refine ⟨273450117283217953302390065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182300078188811968868260043 273450117283217953302390065)
      ·
        refine ⟨205087587962413464976792549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273450117283217953302390065 205087587962413464976792549)
        ·
          refine ⟨38453922742952524683148603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 205087587962413464976792549 38453922742952524683148603)
          ·
            refine ⟨57680884114428787024722905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38453922742952524683148603 57680884114428787024722905)
            ·
              refine ⟨43260663085821590268542179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57680884114428787024722905 43260663085821590268542179)
              ·
                refine ⟨64890994628732385402813269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43260663085821590268542179 64890994628732385402813269)
                ·
                  refine ⟨380220671652728820719609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 64890994628732385402813269 380220671652728820719609)
                  ·
                    rfl

theorem cell22_3332147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 9].length) (baseStart_3332147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3332147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3332147 prefixEnd_3332147 := by exact prefixLift 3332147
  have htrace : WordTrace (prefixWord ++ tailWord_3332147) baseStart_3332147 baseEnd_3332147 := by
    simpa [prefixWord, tailWord_3332147, baseEnd_3332147] using wordTrace_append hprefix tailTrace_3332147
  have hstable : (prefixWord ++ tailWord_3332147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3332147).length < 2 ^ (prefixWord ++ tailWord_3332147).sum := by decide
  have hdescent : baseEnd_3332147 < baseStart_3332147 := by decide
  rcases family_descends (prefixWord ++ tailWord_3332147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3332166 : List Nat := [6, 1, 1, 1, 1, 1, 1, 1, 1, 8]
def baseStart_3332166 : Nat := 118140960795 + 3332166 * 2 ^ 59
def prefixEnd_3332166 : Nat := 4983230072969 + 3 ^ 40 * 3332166 * 2
def baseEnd_3332166 : Nat := 1140668519046476745933769

theorem tailTrace_3332166 : CollatzResearch.WordTrace tailWord_3332166 prefixEnd_3332166 1140668519046476745933769 := by
  unfold tailWord_3332166
  simp only [CollatzResearch.WordTrace]
  refine ⟨3797939951441848296576511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 81022718964092763660298901 3797939951441848296576511)
  ·
    refine ⟨5696909927162772444864767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3797939951441848296576511 5696909927162772444864767)
    ·
      refine ⟨8545364890744158667297151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5696909927162772444864767 8545364890744158667297151)
      ·
        refine ⟨12818047336116238000945727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8545364890744158667297151 12818047336116238000945727)
        ·
          refine ⟨19227071004174357001418591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12818047336116238000945727 19227071004174357001418591)
          ·
            refine ⟨28840606506261535502127887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19227071004174357001418591 28840606506261535502127887)
            ·
              refine ⟨43260909759392303253191831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28840606506261535502127887 43260909759392303253191831)
              ·
                refine ⟨64891364639088454879787747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43260909759392303253191831 64891364639088454879787747)
                ·
                  refine ⟨97337046958632682319681621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64891364639088454879787747 97337046958632682319681621)
                  ·
                    refine ⟨1140668519046476745933769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 97337046958632682319681621 1140668519046476745933769)
                    ·
                      rfl

theorem cell22_3332166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_3332166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3332166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3332166 prefixEnd_3332166 := by exact prefixLift 3332166
  have htrace : WordTrace (prefixWord ++ tailWord_3332166) baseStart_3332166 baseEnd_3332166 := by
    simpa [prefixWord, tailWord_3332166, baseEnd_3332166] using wordTrace_append hprefix tailTrace_3332166
  have hstable : (prefixWord ++ tailWord_3332166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3332166).length < 2 ^ (prefixWord ++ tailWord_3332166).sum := by decide
  have hdescent : baseEnd_3332166 < baseStart_3332166 := by decide
  rcases family_descends (prefixWord ++ tailWord_3332166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3332258 : List Nat := [3, 3, 1, 3, 1, 1, 1, 2, 4, 3]
def baseStart_3332258 : Nat := 118140960795 + 3332258 * 2 ^ 59
def prefixEnd_3332258 : Nat := 4983230072969 + 3 ^ 40 * 3332258 * 2
def baseEnd_3332258 : Nat := 1140700012526619172633487

theorem tailTrace_3332258 : CollatzResearch.WordTrace tailWord_3332258 prefixEnd_3332258 1140700012526619172633487 := by
  unfold tailWord_3332258
  simp only [CollatzResearch.WordTrace]
  refine ⟨30384358490451461300699357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81024955974537230135198285 30384358490451461300699357)
  ·
    refine ⟨11394134433919297987762259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30384358490451461300699357 11394134433919297987762259)
    ·
      refine ⟨17091201650878946981643389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11394134433919297987762259 17091201650878946981643389)
      ·
        refine ⟨6409200619079605118116271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17091201650878946981643389 6409200619079605118116271)
        ·
          refine ⟨9613800928619407677174407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6409200619079605118116271 9613800928619407677174407)
          ·
            refine ⟨14420701392929111515761611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9613800928619407677174407 14420701392929111515761611)
            ·
              refine ⟨21631052089393667273642417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14420701392929111515761611 21631052089393667273642417)
              ·
                refine ⟨16223289067045250455231813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21631052089393667273642417 16223289067045250455231813)
                ·
                  refine ⟨3041866700070984460355965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16223289067045250455231813 3041866700070984460355965)
                  ·
                    refine ⟨1140700012526619172633487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3041866700070984460355965 1140700012526619172633487)
                    ·
                      rfl

theorem cell22_3332258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 2, 4, 3].length) (baseStart_3332258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3332258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3332258 prefixEnd_3332258 := by exact prefixLift 3332258
  have htrace : WordTrace (prefixWord ++ tailWord_3332258) baseStart_3332258 baseEnd_3332258 := by
    simpa [prefixWord, tailWord_3332258, baseEnd_3332258] using wordTrace_append hprefix tailTrace_3332258
  have hstable : (prefixWord ++ tailWord_3332258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3332258).length < 2 ^ (prefixWord ++ tailWord_3332258).sum := by decide
  have hdescent : baseEnd_3332258 < baseStart_3332258 := by decide
  rcases family_descends (prefixWord ++ tailWord_3332258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3332260 : List Nat := [2, 3, 1, 2, 4, 2, 1, 3, 4]
def baseStart_3332260 : Nat := 118140960795 + 3332260 * 2 ^ 59
def prefixEnd_3332260 : Nat := 4983230072969 + 3 ^ 40 * 3332260 * 2
def baseEnd_3332260 : Nat := 380233565722497278027827

theorem tailTrace_3332260 : CollatzResearch.WordTrace tailWord_3332260 prefixEnd_3332260 380233565722497278027827 := by
  unfold tailWord_3332260
  simp only [CollatzResearch.WordTrace]
  refine ⟨60768753453899299772185117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81025004605199066362913489 60768753453899299772185117)
  ·
    refine ⟨22788282545212237414569419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60768753453899299772185117 22788282545212237414569419)
    ·
      refine ⟨34182423817818356121854129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22788282545212237414569419 34182423817818356121854129)
      ·
        refine ⟨25636817863363767091390597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34182423817818356121854129 25636817863363767091390597)
        ·
          refine ⟨4806903349380706329635737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25636817863363767091390597 4806903349380706329635737)
          ·
            refine ⟨3605177512035529747226803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4806903349380706329635737 3605177512035529747226803)
            ·
              refine ⟨5407766268053294620840205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3605177512035529747226803 5407766268053294620840205)
              ·
                refine ⟨2027912350519985482815077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5407766268053294620840205 2027912350519985482815077)
                ·
                  refine ⟨380233565722497278027827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2027912350519985482815077 380233565722497278027827)
                  ·
                    rfl

theorem cell22_3332260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 3, 4].length) (baseStart_3332260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3332260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3332260 prefixEnd_3332260 := by exact prefixLift 3332260
  have htrace : WordTrace (prefixWord ++ tailWord_3332260) baseStart_3332260 baseEnd_3332260 := by
    simpa [prefixWord, tailWord_3332260, baseEnd_3332260] using wordTrace_append hprefix tailTrace_3332260
  have hstable : (prefixWord ++ tailWord_3332260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3332260).length < 2 ^ (prefixWord ++ tailWord_3332260).sum := by decide
  have hdescent : baseEnd_3332260 < baseStart_3332260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3332260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3332273 : List Nat := [1, 2, 2, 5, 2, 1, 1, 2, 2, 4]
def baseStart_3332273 : Nat := 118140960795 + 3332273 * 2 ^ 59
def prefixEnd_3332273 : Nat := 4983230072969 + 3 ^ 40 * 3332273 * 2
def baseEnd_3332273 : Nat := 1140705147333164133508441

theorem tailTrace_3332273 : CollatzResearch.WordTrace tailWord_3332273 prefixEnd_3332273 1140705147333164133508441 := by
  unfold tailWord_3332273
  simp only [CollatzResearch.WordTrace]
  refine ⟨121537981056751502764593473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81025320704501001843062315 121537981056751502764593473)
  ·
    refine ⟨91153485792563627073445105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121537981056751502764593473 91153485792563627073445105)
    ·
      refine ⟨68365114344422720305083829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91153485792563627073445105 68365114344422720305083829)
      ·
        refine ⟨6409229469789630028601609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68365114344422720305083829 6409229469789630028601609)
        ·
          refine ⟨4806922102342222521451207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6409229469789630028601609 4806922102342222521451207)
          ·
            refine ⟨7210383153513333782176811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4806922102342222521451207 7210383153513333782176811)
            ·
              refine ⟨10815574730270000673265217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7210383153513333782176811 10815574730270000673265217)
              ·
                refine ⟨8111681047702500504948913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10815574730270000673265217 8111681047702500504948913)
                ·
                  refine ⟨6083760785776875378711685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8111681047702500504948913 6083760785776875378711685)
                  ·
                    refine ⟨1140705147333164133508441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6083760785776875378711685 1140705147333164133508441)
                    ·
                      rfl

theorem cell22_3332273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 2, 2, 4].length) (baseStart_3332273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3332273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3332273 prefixEnd_3332273 := by exact prefixLift 3332273
  have htrace : WordTrace (prefixWord ++ tailWord_3332273) baseStart_3332273 baseEnd_3332273 := by
    simpa [prefixWord, tailWord_3332273, baseEnd_3332273] using wordTrace_append hprefix tailTrace_3332273
  have hstable : (prefixWord ++ tailWord_3332273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3332273).length < 2 ^ (prefixWord ++ tailWord_3332273).sum := by decide
  have hdescent : baseEnd_3332273 < baseStart_3332273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3332273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3332277 : List Nat := [1, 3, 3, 4, 1, 1, 3, 2, 4]
def baseStart_3332277 : Nat := 118140960795 + 3332277 * 2 ^ 59
def prefixEnd_3332277 : Nat := 4983230072969 + 3 ^ 40 * 3332277 * 2
def baseEnd_3332277 : Nat := 380235505538303152136143

theorem tailTrace_3332277 : CollatzResearch.WordTrace tailWord_3332277 prefixEnd_3332277 380235505538303152136143 := by
  unfold tailWord_3332277
  simp only [CollatzResearch.WordTrace]
  refine ⟨121538126948737011447739085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81025417965824674298492723 121538126948737011447739085)
  ·
    refine ⟨45576797605776379292902157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121538126948737011447739085 45576797605776379292902157)
    ·
      refine ⟨17091299102166142234838309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45576797605776379292902157 17091299102166142234838309)
      ·
        refine ⟨3204618581656151669032183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17091299102166142234838309 3204618581656151669032183)
        ·
          refine ⟨4806927872484227503548275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3204618581656151669032183 4806927872484227503548275)
          ·
            refine ⟨7210391808726341255322413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4806927872484227503548275 7210391808726341255322413)
            ·
              refine ⟨2703896928272377970745905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7210391808726341255322413 2703896928272377970745905)
              ·
                refine ⟨2027922696204283478059429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2703896928272377970745905 2027922696204283478059429)
                ·
                  refine ⟨380235505538303152136143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2027922696204283478059429 380235505538303152136143)
                  ·
                    rfl

theorem cell22_3332277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 3, 2, 4].length) (baseStart_3332277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3332277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3332277 prefixEnd_3332277 := by exact prefixLift 3332277
  have htrace : WordTrace (prefixWord ++ tailWord_3332277) baseStart_3332277 baseEnd_3332277 := by
    simpa [prefixWord, tailWord_3332277, baseEnd_3332277] using wordTrace_append hprefix tailTrace_3332277
  have hstable : (prefixWord ++ tailWord_3332277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3332277).length < 2 ^ (prefixWord ++ tailWord_3332277).sum := by decide
  have hdescent : baseEnd_3332277 < baseStart_3332277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3332277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3332292 : List Nat := [2, 3, 3, 1, 2, 3, 2, 1, 2, 3]
def baseStart_3332292 : Nat := 118140960795 + 3332292 * 2 ^ 59
def prefixEnd_3332292 : Nat := 4983230072969 + 3 ^ 40 * 3332292 * 2
def baseEnd_3332292 : Nat := 1140711651421454417283383

theorem tailTrace_3332292 : CollatzResearch.WordTrace tailWord_3332292 prefixEnd_3332292 1140711651421454417283383 := by
  unfold tailWord_3332292
  simp only [CollatzResearch.WordTrace]
  refine ⟨60769337021841334504767565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81025782695788446006356753 60769337021841334504767565)
  ·
    refine ⟨22788501383190500439287837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60769337021841334504767565 22788501383190500439287837)
    ·
      refine ⟨8545688018696437664732939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22788501383190500439287837 8545688018696437664732939)
      ·
        refine ⟨12818532028044656497099409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8545688018696437664732939 12818532028044656497099409)
        ·
          refine ⟨9613899021033492372824557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12818532028044656497099409 9613899021033492372824557)
          ·
            refine ⟨3605212132887559639809209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9613899021033492372824557 3605212132887559639809209)
            ·
              refine ⟨2703909099665669729856907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3605212132887559639809209 2703909099665669729856907)
              ·
                refine ⟨4055863649498504594785361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2703909099665669729856907 4055863649498504594785361)
                ·
                  refine ⟨3041897737123878446089021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4055863649498504594785361 3041897737123878446089021)
                  ·
                    refine ⟨1140711651421454417283383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3041897737123878446089021 1140711651421454417283383)
                    ·
                      rfl

theorem cell22_3332292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_3332292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3332292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3332292 prefixEnd_3332292 := by exact prefixLift 3332292
  have htrace : WordTrace (prefixWord ++ tailWord_3332292) baseStart_3332292 baseEnd_3332292 := by
    simpa [prefixWord, tailWord_3332292, baseEnd_3332292] using wordTrace_append hprefix tailTrace_3332292
  have hstable : (prefixWord ++ tailWord_3332292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3332292).length < 2 ^ (prefixWord ++ tailWord_3332292).sum := by decide
  have hdescent : baseEnd_3332292 < baseStart_3332292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3332292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3332344 : List Nat := [2, 1, 2, 1, 1, 2, 1, 2, 10]
def baseStart_3332344 : Nat := 118140960795 + 3332344 * 2 ^ 59
def prefixEnd_3332344 : Nat := 4983230072969 + 3 ^ 40 * 3332344 * 2
def baseEnd_3332344 : Nat := 380243150694714538327741

theorem tailTrace_3332344 : CollatzResearch.WordTrace tailWord_3332344 prefixEnd_3332344 380243150694714538327741 := by
  unfold tailWord_3332344
  simp only [CollatzResearch.WordTrace]
  refine ⟨60770285319747140945214043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81027047092996187926952057 60770285319747140945214043)
  ·
    refine ⟨91155427979620711417821065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60770285319747140945214043 91155427979620711417821065)
    ·
      refine ⟨68366570984715533563365799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91155427979620711417821065 68366570984715533563365799)
      ·
        refine ⟨102549856477073300345048699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68366570984715533563365799 102549856477073300345048699)
        ·
          refine ⟨153824784715609950517573049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102549856477073300345048699 153824784715609950517573049)
          ·
            refine ⟨115368588536707462888179787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153824784715609950517573049 115368588536707462888179787)
            ·
              refine ⟨173052882805061194332269681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115368588536707462888179787 173052882805061194332269681)
              ·
                refine ⟨129789662103795895749202261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 173052882805061194332269681 129789662103795895749202261)
                ·
                  refine ⟨380243150694714538327741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 129789662103795895749202261 380243150694714538327741)
                  ·
                    rfl

theorem cell22_3332344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 10].length) (baseStart_3332344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3332344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3332344 prefixEnd_3332344 := by exact prefixLift 3332344
  have htrace : WordTrace (prefixWord ++ tailWord_3332344) baseStart_3332344 baseEnd_3332344 := by
    simpa [prefixWord, tailWord_3332344, baseEnd_3332344] using wordTrace_append hprefix tailTrace_3332344
  have hstable : (prefixWord ++ tailWord_3332344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3332344).length < 2 ^ (prefixWord ++ tailWord_3332344).sum := by decide
  have hdescent : baseEnd_3332344 < baseStart_3332344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3332344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3332346 : List Nat := [3, 1, 1, 1, 1, 5, 1, 2, 3, 4]
def baseStart_3332346 : Nat := 118140960795 + 3332346 * 2 ^ 59
def prefixEnd_3332346 : Nat := 4983230072969 + 3 ^ 40 * 3332346 * 2
def baseEnd_3332346 : Nat := 1140730136725016276433217

theorem tailTrace_3332346 : CollatzResearch.WordTrace tailWord_3332346 prefixEnd_3332346 1140730136725016276433217 := by
  unfold tailWord_3332346
  simp only [CollatzResearch.WordTrace]
  refine ⟨30385160896371759058000223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81027095723658024154667261 30385160896371759058000223)
  ·
    refine ⟨45577741344557638587000335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30385160896371759058000223 45577741344557638587000335)
    ·
      refine ⟨68366612016836457880500503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45577741344557638587000335 68366612016836457880500503)
      ·
        refine ⟨102549918025254686820750755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68366612016836457880500503 102549918025254686820750755)
        ·
          refine ⟨153824877037882030231126133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102549918025254686820750755 153824877037882030231126133)
          ·
            refine ⟨14421082222301440334168075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 153824877037882030231126133 14421082222301440334168075)
            ·
              refine ⟨21631623333452160501252113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14421082222301440334168075 21631623333452160501252113)
              ·
                refine ⟨16223717500089120375939085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21631623333452160501252113 16223717500089120375939085)
                ·
                  refine ⟨6083894062533420140977157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16223717500089120375939085 6083894062533420140977157)
                  ·
                    refine ⟨1140730136725016276433217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6083894062533420140977157 1140730136725016276433217)
                    ·
                      rfl

theorem cell22_3332346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 2, 3, 4].length) (baseStart_3332346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3332346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3332346 prefixEnd_3332346 := by exact prefixLift 3332346
  have htrace : WordTrace (prefixWord ++ tailWord_3332346) baseStart_3332346 baseEnd_3332346 := by
    simpa [prefixWord, tailWord_3332346, baseEnd_3332346] using wordTrace_append hprefix tailTrace_3332346
  have hstable : (prefixWord ++ tailWord_3332346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3332346).length < 2 ^ (prefixWord ++ tailWord_3332346).sum := by decide
  have hdescent : baseEnd_3332346 < baseStart_3332346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3332346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3332361 : List Nat := [1, 2, 1, 1, 3, 5, 1, 2, 6]
def baseStart_3332361 : Nat := 118140960795 + 3332361 * 2 ^ 59
def prefixEnd_3332361 : Nat := 4983230072969 + 3 ^ 40 * 3332361 * 2
def baseEnd_3332361 : Nat := 380245090510520412436057

theorem tailTrace_3332361 : CollatzResearch.WordTrace tailWord_3332361 prefixEnd_3332361 380245090510520412436057 := by
  unfold tailWord_3332361
  simp only [CollatzResearch.WordTrace]
  refine ⟨121541190680432693793796937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81027460453621795862531291 121541190680432693793796937)
  ·
    refine ⟨91155893010324520345347703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121541190680432693793796937 91155893010324520345347703)
    ·
      refine ⟨136733839515486780518021555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91155893010324520345347703 136733839515486780518021555)
      ·
        refine ⟨205100759273230170777032333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136733839515486780518021555 205100759273230170777032333)
        ·
          refine ⟨76912784727461314041387125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 205100759273230170777032333 76912784727461314041387125)
          ·
            refine ⟨7210573568199498191380043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76912784727461314041387125 7210573568199498191380043)
            ·
              refine ⟨10815860352299247287070065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7210573568199498191380043 10815860352299247287070065)
              ·
                refine ⟨8111895264224435465302549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10815860352299247287070065 8111895264224435465302549)
                ·
                  refine ⟨380245090510520412436057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8111895264224435465302549 380245090510520412436057)
                  ·
                    rfl

theorem cell22_3332361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 2, 6].length) (baseStart_3332361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3332361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3332361 prefixEnd_3332361 := by exact prefixLift 3332361
  have htrace : WordTrace (prefixWord ++ tailWord_3332361) baseStart_3332361 baseEnd_3332361 := by
    simpa [prefixWord, tailWord_3332361, baseEnd_3332361] using wordTrace_append hprefix tailTrace_3332361
  have hstable : (prefixWord ++ tailWord_3332361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3332361).length < 2 ^ (prefixWord ++ tailWord_3332361).sum := by decide
  have hdescent : baseEnd_3332361 < baseStart_3332361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3332361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3332376 : List Nat := [2, 1, 2, 3, 1, 2, 1, 4, 1, 5]
def baseStart_3332376 : Nat := 118140960795 + 3332376 * 2 ^ 59
def prefixEnd_3332376 : Nat := 4983230072969 + 3 ^ 40 * 3332376 * 2
def baseEnd_3332376 : Nat := 1140740406338106198183125

theorem tailTrace_3332376 : CollatzResearch.WordTrace tailWord_3332376 prefixEnd_3332376 1140740406338106198183125 := by
  unfold tailWord_3332376
  simp only [CollatzResearch.WordTrace]
  refine ⟨60770868887689175677796491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81027825183585567570395321 60770868887689175677796491)
  ·
    refine ⟨91156303331533763516694737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60770868887689175677796491 91156303331533763516694737)
    ·
      refine ⟨68367227498650322637521053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91156303331533763516694737 68367227498650322637521053)
      ·
        refine ⟨25637710311993870989070395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68367227498650322637521053 25637710311993870989070395)
        ·
          refine ⟨38456565467990806483605593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25637710311993870989070395 38456565467990806483605593)
          ·
            refine ⟨28842424100993104862704195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38456565467990806483605593 28842424100993104862704195)
            ·
              refine ⟨43263636151489657294056293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28842424100993104862704195 43263636151489657294056293)
              ·
                refine ⟨8111931778404310742635555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43263636151489657294056293 8111931778404310742635555)
                ·
                  refine ⟨12167897667606466113953333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8111931778404310742635555 12167897667606466113953333)
                  ·
                    refine ⟨1140740406338106198183125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12167897667606466113953333 1140740406338106198183125)
                    ·
                      rfl

theorem cell22_3332376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 4, 1, 5].length) (baseStart_3332376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3332376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3332376 prefixEnd_3332376 := by exact prefixLift 3332376
  have htrace : WordTrace (prefixWord ++ tailWord_3332376) baseStart_3332376 baseEnd_3332376 := by
    simpa [prefixWord, tailWord_3332376, baseEnd_3332376] using wordTrace_append hprefix tailTrace_3332376
  have hstable : (prefixWord ++ tailWord_3332376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3332376).length < 2 ^ (prefixWord ++ tailWord_3332376).sum := by decide
  have hdescent : baseEnd_3332376 < baseStart_3332376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3332376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3332446 : List Nat := [4, 4, 2, 1, 1, 2, 1, 1, 6]
def baseStart_3332446 : Nat := 118140960795 + 3332446 * 2 ^ 59
def prefixEnd_3332446 : Nat := 4983230072969 + 3 ^ 40 * 3332446 * 2
def baseEnd_3332446 : Nat := 380254789589549782977637

theorem tailTrace_3332446 : CollatzResearch.WordTrace tailWord_3332446 prefixEnd_3332446 380254789589549782977637 := by
  unfold tailWord_3332446
  simp only [CollatzResearch.WordTrace]
  refine ⟨15193036360640594163830149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81029527256749835540427461 15193036360640594163830149)
  ·
    refine ⟨2848694317620111405718153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15193036360640594163830149 2848694317620111405718153)
    ·
      refine ⟨2136520738215083554288615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2848694317620111405718153 2136520738215083554288615)
      ·
        refine ⟨3204781107322625331432923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2136520738215083554288615 3204781107322625331432923)
        ·
          refine ⟨4807171660983937997149385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3204781107322625331432923 4807171660983937997149385)
          ·
            refine ⟨3605378745737953497862039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4807171660983937997149385 3605378745737953497862039)
            ·
              refine ⟨5408068118606930246793059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3605378745737953497862039 5408068118606930246793059)
              ·
                refine ⟨8112102177910395370189589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5408068118606930246793059 8112102177910395370189589)
                ·
                  refine ⟨380254789589549782977637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8112102177910395370189589 380254789589549782977637)
                  ·
                    rfl

theorem cell22_3332446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_3332446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3332446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3332446 prefixEnd_3332446 := by exact prefixLift 3332446
  have htrace : WordTrace (prefixWord ++ tailWord_3332446) baseStart_3332446 baseEnd_3332446 := by
    simpa [prefixWord, tailWord_3332446, baseEnd_3332446] using wordTrace_append hprefix tailTrace_3332446
  have hstable : (prefixWord ++ tailWord_3332446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3332446).length < 2 ^ (prefixWord ++ tailWord_3332446).sum := by decide
  have hdescent : baseEnd_3332446 < baseStart_3332446 := by decide
  rcases family_descends (prefixWord ++ tailWord_3332446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3332451 : List Nat := [1, 1, 1, 5, 2, 1, 1, 3, 7]
def baseStart_3332451 : Nat := 118140960795 + 3332451 * 2 ^ 59
def prefixEnd_3332451 : Nat := 4983230072969 + 3 ^ 40 * 3332451 * 2
def baseEnd_3332451 : Nat := 380255360123610334185965

theorem tailTrace_3332451 : CollatzResearch.WordTrace tailWord_3332451 prefixEnd_3332451 380255360123610334185965 := by
  unfold tailWord_3332451
  simp only [CollatzResearch.WordTrace]
  refine ⟨121544473250106639164573207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81029648833404426109715471 121544473250106639164573207)
  ·
    refine ⟨182316709875159958746859811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121544473250106639164573207 182316709875159958746859811)
    ·
      refine ⟨273475064812739938120289717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182316709875159958746859811 273475064812739938120289717)
      ·
        refine ⟨25638287326194369198777161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 273475064812739938120289717 25638287326194369198777161)
        ·
          refine ⟨19228715494645776899082871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25638287326194369198777161 19228715494645776899082871)
          ·
            refine ⟨28843073241968665348624307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19228715494645776899082871 28843073241968665348624307)
            ·
              refine ⟨43264609862952998022936461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28843073241968665348624307 43264609862952998022936461)
              ·
                refine ⟨16224228698607374258601173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43264609862952998022936461 16224228698607374258601173)
                ·
                  refine ⟨380255360123610334185965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16224228698607374258601173 380255360123610334185965)
                  ·
                    rfl

theorem cell22_3332451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 3, 7].length) (baseStart_3332451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3332451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3332451 prefixEnd_3332451 := by exact prefixLift 3332451
  have htrace : WordTrace (prefixWord ++ tailWord_3332451) baseStart_3332451 baseEnd_3332451 := by
    simpa [prefixWord, tailWord_3332451, baseEnd_3332451] using wordTrace_append hprefix tailTrace_3332451
  have hstable : (prefixWord ++ tailWord_3332451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3332451).length < 2 ^ (prefixWord ++ tailWord_3332451).sum := by decide
  have hdescent : baseEnd_3332451 < baseStart_3332451 := by decide
  rcases family_descends (prefixWord ++ tailWord_3332451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3332455 : List Nat := [1, 1, 5, 1, 3, 1, 3, 1, 3, 3]
def baseStart_3332455 : Nat := 118140960795 + 3332455 * 2 ^ 59
def prefixEnd_3332455 : Nat := 4983230072969 + 3 ^ 40 * 3332455 * 2
def baseEnd_3332455 : Nat := 1140767449652576325457883

theorem tailTrace_3332455 : CollatzResearch.WordTrace tailWord_3332455 prefixEnd_3332455 1140767449652576325457883 := by
  unfold tailWord_3332455
  simp only [CollatzResearch.WordTrace]
  refine ⟨121544619142092147847718819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81029746094728098565145879 121544619142092147847718819)
  ·
    refine ⟨182316928713138221771578229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121544619142092147847718819 182316928713138221771578229)
    ·
      refine ⟨17092212066856708291085459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 182316928713138221771578229 17092212066856708291085459)
      ·
        refine ⟨25638318100285062436628189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17092212066856708291085459 25638318100285062436628189)
        ·
          refine ⟨9614369287606898413735571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25638318100285062436628189 9614369287606898413735571)
          ·
            refine ⟨14421553931410347620603357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9614369287606898413735571 14421553931410347620603357)
            ·
              refine ⟨5408082724278880357726259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14421553931410347620603357 5408082724278880357726259)
              ·
                refine ⟨8112124086418320536589389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5408082724278880357726259 8112124086418320536589389)
                ·
                  refine ⟨3042046532406870201221021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8112124086418320536589389 3042046532406870201221021)
                  ·
                    refine ⟨1140767449652576325457883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3042046532406870201221021 1140767449652576325457883)
                    ·
                      rfl

theorem cell22_3332455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 1, 3, 3].length) (baseStart_3332455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3332455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3332455 prefixEnd_3332455 := by exact prefixLift 3332455
  have htrace : WordTrace (prefixWord ++ tailWord_3332455) baseStart_3332455 baseEnd_3332455 := by
    simpa [prefixWord, tailWord_3332455, baseEnd_3332455] using wordTrace_append hprefix tailTrace_3332455
  have hstable : (prefixWord ++ tailWord_3332455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3332455).length < 2 ^ (prefixWord ++ tailWord_3332455).sum := by decide
  have hdescent : baseEnd_3332455 < baseStart_3332455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3332455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3332579 : List Nat := [1, 1, 1, 6, 3, 1, 3, 1, 2, 3]
def baseStart_3332579 : Nat := 118140960795 + 3332579 * 2 ^ 59
def prefixEnd_3332579 : Nat := 4983230072969 + 3 ^ 40 * 3332579 * 2
def baseEnd_3332579 : Nat := 1140809897386681335357503

theorem tailTrace_3332579 : CollatzResearch.WordTrace tailWord_3332579 prefixEnd_3332579 1140809897386681335357503 := by
  unfold tailWord_3332579
  simp only [CollatzResearch.WordTrace]
  refine ⟨121549141793642917025232791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81032761195761944683488527 121549141793642917025232791)
  ·
    refine ⟨182323712690464375537849187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121549141793642917025232791 182323712690464375537849187)
    ·
      refine ⟨273485569035696563306773781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182323712690464375537849187 273485569035696563306773781)
      ·
        refine ⟨12819636048548276405005021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 273485569035696563306773781 12819636048548276405005021)
        ·
          refine ⟨4807363518205603651876883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12819636048548276405005021 4807363518205603651876883)
          ·
            refine ⟨7211045277308405477815325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4807363518205603651876883 7211045277308405477815325)
            ·
              refine ⟨2704141978990652054180747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7211045277308405477815325 2704141978990652054180747)
              ·
                refine ⟨4056212968485978081271121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2704141978990652054180747 4056212968485978081271121)
                ·
                  refine ⟨3042159726364483560953341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4056212968485978081271121 3042159726364483560953341)
                  ·
                    refine ⟨1140809897386681335357503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3042159726364483560953341 1140809897386681335357503)
                    ·
                      rfl

theorem cell22_3332579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 3, 1, 2, 3].length) (baseStart_3332579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3332579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3332579 prefixEnd_3332579 := by exact prefixLift 3332579
  have htrace : WordTrace (prefixWord ++ tailWord_3332579) baseStart_3332579 baseEnd_3332579 := by
    simpa [prefixWord, tailWord_3332579, baseEnd_3332579] using wordTrace_append hprefix tailTrace_3332579
  have hstable : (prefixWord ++ tailWord_3332579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3332579).length < 2 ^ (prefixWord ++ tailWord_3332579).sum := by decide
  have hdescent : baseEnd_3332579 < baseStart_3332579 := by decide
  rcases family_descends (prefixWord ++ tailWord_3332579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3332633 : List Nat := [1, 2, 1, 2, 1, 1, 2, 3, 5, 4]
def baseStart_3332633 : Nat := 118140960795 + 3332633 * 2 ^ 59
def prefixEnd_3332633 : Nat := 4983230072969 + 3 ^ 40 * 3332633 * 2
def baseEnd_3332633 : Nat := 1140828382690243194507337

theorem tailTrace_3332633 : CollatzResearch.WordTrace tailWord_3332633 prefixEnd_3332633 1140828382690243194507337 := by
  unfold tailWord_3332633
  simp only [CollatzResearch.WordTrace]
  refine ⟨121551111335447284247698553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81034074223631522831799035 121551111335447284247698553)
  ·
    refine ⟨91163333501585463185773915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121551111335447284247698553 91163333501585463185773915)
    ·
      refine ⟨136745000252378194778660873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91163333501585463185773915 136745000252378194778660873)
      ·
        refine ⟨102558750189283646083995655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136745000252378194778660873 102558750189283646083995655)
        ·
          refine ⟨153838125283925469125993483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102558750189283646083995655 153838125283925469125993483)
          ·
            refine ⟨230757187925888203688990225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153838125283925469125993483 230757187925888203688990225)
            ·
              refine ⟨173067890944416152766742669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 230757187925888203688990225 173067890944416152766742669)
              ·
                refine ⟨64900459104156057287528501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 173067890944416152766742669 64900459104156057287528501)
                ·
                  refine ⟨6084418041014630370705797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64900459104156057287528501 6084418041014630370705797)
                  ·
                    refine ⟨1140828382690243194507337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6084418041014630370705797 1140828382690243194507337)
                    ·
                      rfl

theorem cell22_3332633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 5, 4].length) (baseStart_3332633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3332633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3332633 prefixEnd_3332633 := by exact prefixLift 3332633
  have htrace : WordTrace (prefixWord ++ tailWord_3332633) baseStart_3332633 baseEnd_3332633 := by
    simpa [prefixWord, tailWord_3332633, baseEnd_3332633] using wordTrace_append hprefix tailTrace_3332633
  have hstable : (prefixWord ++ tailWord_3332633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3332633).length < 2 ^ (prefixWord ++ tailWord_3332633).sum := by decide
  have hdescent : baseEnd_3332633 < baseStart_3332633 := by decide
  rcases family_descends (prefixWord ++ tailWord_3332633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3332637 : List Nat := [1, 4, 2, 2, 1, 2, 4, 1, 5]
def baseStart_3332637 : Nat := 118140960795 + 3332637 * 2 ^ 59
def prefixEnd_3332637 : Nat := 4983230072969 + 3 ^ 40 * 3332637 * 2
def baseEnd_3332637 : Nat := 380276583990662839135775

theorem tailTrace_3332637 : CollatzResearch.WordTrace tailWord_3332637 prefixEnd_3332637 380276583990662839135775 := by
  unfold tailWord_3332637
  simp only [CollatzResearch.WordTrace]
  refine ⟨121551257227432792930844165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81034171484955195287229443 121551257227432792930844165)
  ·
    refine ⟨22790860730143648674533281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121551257227432792930844165 22790860730143648674533281)
    ·
      refine ⟨17093145547607736505899961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22790860730143648674533281 17093145547607736505899961)
      ·
        refine ⟨12819859160705802379424971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17093145547607736505899961 12819859160705802379424971)
        ·
          refine ⟨19229788741058703569137457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12819859160705802379424971 19229788741058703569137457)
          ·
            refine ⟨14422341555794027676853093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19229788741058703569137457 14422341555794027676853093)
            ·
              refine ⟨2704189041711380189409955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14422341555794027676853093 2704189041711380189409955)
              ·
                refine ⟨4056283562567070284114933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2704189041711380189409955 4056283562567070284114933)
                ·
                  refine ⟨380276583990662839135775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4056283562567070284114933 380276583990662839135775)
                  ·
                    rfl

theorem cell22_3332637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 4, 1, 5].length) (baseStart_3332637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3332637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3332637 prefixEnd_3332637 := by exact prefixLift 3332637
  have htrace : WordTrace (prefixWord ++ tailWord_3332637) baseStart_3332637 baseEnd_3332637 := by
    simpa [prefixWord, tailWord_3332637, baseEnd_3332637] using wordTrace_append hprefix tailTrace_3332637
  have hstable : (prefixWord ++ tailWord_3332637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3332637).length < 2 ^ (prefixWord ++ tailWord_3332637).sum := by decide
  have hdescent : baseEnd_3332637 < baseStart_3332637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3332637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3332680 : List Nat := [2, 1, 3, 1, 1, 1, 1, 5, 4, 3]
def baseStart_3332680 : Nat := 118140960795 + 3332680 * 2 ^ 59
def prefixEnd_3332680 : Nat := 4983230072969 + 3 ^ 40 * 3332680 * 2
def baseEnd_3332680 : Nat := 1140844471750750738582193

theorem tailTrace_3332680 : CollatzResearch.WordTrace tailWord_3332680 prefixEnd_3332680 1140844471750750738582193 := by
  unfold tailWord_3332680
  simp only [CollatzResearch.WordTrace]
  refine ⟨60776412783138505637329747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81035217044184674183106329 60776412783138505637329747)
  ·
    refine ⟨91164619174707758455994621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60776412783138505637329747 91164619174707758455994621)
    ·
      refine ⟨34186732190515409420997983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91164619174707758455994621 34186732190515409420997983)
      ·
        refine ⟨51280098285773114131496975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34186732190515409420997983 51280098285773114131496975)
        ·
          refine ⟨76920147428659671197245463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51280098285773114131496975 76920147428659671197245463)
          ·
            refine ⟨115380221142989506795868195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76920147428659671197245463 115380221142989506795868195)
            ·
              refine ⟨173070331714484260193802293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115380221142989506795868195 173070331714484260193802293)
              ·
                refine ⟨16225343598232899393168965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 173070331714484260193802293 16225343598232899393168965)
                ·
                  refine ⟨3042251924668668636219181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16225343598232899393168965 3042251924668668636219181)
                  ·
                    refine ⟨1140844471750750738582193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3042251924668668636219181 1140844471750750738582193)
                    ·
                      rfl

theorem cell22_3332680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 5, 4, 3].length) (baseStart_3332680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3332680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3332680 prefixEnd_3332680 := by exact prefixLift 3332680
  have htrace : WordTrace (prefixWord ++ tailWord_3332680) baseStart_3332680 baseEnd_3332680 := by
    simpa [prefixWord, tailWord_3332680, baseEnd_3332680] using wordTrace_append hprefix tailTrace_3332680
  have hstable : (prefixWord ++ tailWord_3332680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3332680).length < 2 ^ (prefixWord ++ tailWord_3332680).sum := by decide
  have hdescent : baseEnd_3332680 < baseStart_3332680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3332680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3332682 : List Nat := [3, 1, 2, 1, 1, 5, 1, 4, 4]
def baseStart_3332682 : Nat := 118140960795 + 3332682 * 2 ^ 59
def prefixEnd_3332682 : Nat := 4983230072969 + 3 ^ 40 * 3332682 * 2
def baseEnd_3332682 : Nat := 380281718797207800010729

theorem tailTrace_3332682 : CollatzResearch.WordTrace tailWord_3332682 prefixEnd_3332682 380281718797207800010729 := by
  unfold tailWord_3332682
  simp only [CollatzResearch.WordTrace]
  refine ⟨30388224628067441404058075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81035265674846510410821533 30388224628067441404058075)
  ·
    refine ⟨45582336942101162106087113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30388224628067441404058075 45582336942101162106087113)
    ·
      refine ⟨34186752706575871579565335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45582336942101162106087113 34186752706575871579565335)
      ·
        refine ⟨51280129059863807369348003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34186752706575871579565335 51280129059863807369348003)
        ·
          refine ⟨76920193589795711054022005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51280129059863807369348003 76920193589795711054022005)
          ·
            refine ⟨7211268149043347911314563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76920193589795711054022005 7211268149043347911314563)
            ·
              refine ⟨10816902223565021866971845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7211268149043347911314563 10816902223565021866971845)
              ·
                refine ⟨2028169166918441600057221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10816902223565021866971845 2028169166918441600057221)
                ·
                  refine ⟨380281718797207800010729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2028169166918441600057221 380281718797207800010729)
                  ·
                    rfl

theorem cell22_3332682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 4, 4].length) (baseStart_3332682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3332682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3332682 prefixEnd_3332682 := by exact prefixLift 3332682
  have htrace : WordTrace (prefixWord ++ tailWord_3332682) baseStart_3332682 baseEnd_3332682 := by
    simpa [prefixWord, tailWord_3332682, baseEnd_3332682] using wordTrace_append hprefix tailTrace_3332682
  have hstable : (prefixWord ++ tailWord_3332682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3332682).length < 2 ^ (prefixWord ++ tailWord_3332682).sum := by decide
  have hdescent : baseEnd_3332682 < baseStart_3332682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3332682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3332712 : List Nat := [2, 1, 4, 3, 2, 1, 1, 1, 1, 6]
def baseStart_3332712 : Nat := 118140960795 + 3332712 * 2 ^ 59
def prefixEnd_3332712 : Nat := 4983230072969 + 3 ^ 40 * 3332712 * 2
def baseEnd_3332712 : Nat := 1140855426004713321782095

theorem tailTrace_3332712 : CollatzResearch.WordTrace tailWord_3332712 prefixEnd_3332712 1140855426004713321782095 := by
  unfold tailWord_3332712
  simp only [CollatzResearch.WordTrace]
  refine ⟨60776996351080540369912195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81035995134774053826549593 60776996351080540369912195)
  ·
    refine ⟨91165494526620810554868293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60776996351080540369912195 91165494526620810554868293)
    ·
      refine ⟨17093530223741401979037805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91165494526620810554868293 17093530223741401979037805)
      ·
        refine ⟨6410073833903025742139177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17093530223741401979037805 6410073833903025742139177)
        ·
          refine ⟨4807555375427269306604383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6410073833903025742139177 4807555375427269306604383)
          ·
            refine ⟨7211333063140903959906575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4807555375427269306604383 7211333063140903959906575)
            ·
              refine ⟨10816999594711355939859863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7211333063140903959906575 10816999594711355939859863)
              ·
                refine ⟨16225499392067033909789795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10816999594711355939859863 16225499392067033909789795)
                ·
                  refine ⟨24338249088100550864684693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16225499392067033909789795 24338249088100550864684693)
                  ·
                    refine ⟨1140855426004713321782095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24338249088100550864684693 1140855426004713321782095)
                    ·
                      rfl

theorem cell22_3332712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_3332712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3332712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3332712 prefixEnd_3332712 := by exact prefixLift 3332712
  have htrace : WordTrace (prefixWord ++ tailWord_3332712) baseStart_3332712 baseEnd_3332712 := by
    simpa [prefixWord, tailWord_3332712, baseEnd_3332712] using wordTrace_append hprefix tailTrace_3332712
  have hstable : (prefixWord ++ tailWord_3332712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3332712).length < 2 ^ (prefixWord ++ tailWord_3332712).sum := by decide
  have hdescent : baseEnd_3332712 < baseStart_3332712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3332712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3332723 : List Nat := [1, 1, 1, 2, 2, 1, 1, 4, 1, 8]
def baseStart_3332723 : Nat := 118140960795 + 3332723 * 2 ^ 59
def prefixEnd_3332723 : Nat := 4983230072969 + 3 ^ 40 * 3332723 * 2
def baseEnd_3332723 : Nat := 1140859191529512959757061

theorem tailTrace_3332723 : CollatzResearch.WordTrace tailWord_3332723 prefixEnd_3332723 1140859191529512959757061 := by
  unfold tailWord_3332723
  simp only [CollatzResearch.WordTrace]
  refine ⟨121554393905121229618474823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81036262603414153078983215 121554393905121229618474823)
  ·
    refine ⟨182331590857681844427712235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121554393905121229618474823 182331590857681844427712235)
    ·
      refine ⟨273497386286522766641568353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182331590857681844427712235 273497386286522766641568353)
      ·
        refine ⟨205123039714892074981176265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273497386286522766641568353 205123039714892074981176265)
        ·
          refine ⟨153842279786169056235882199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205123039714892074981176265 153842279786169056235882199)
          ·
            refine ⟨230763419679253584353823299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153842279786169056235882199 230763419679253584353823299)
            ·
              refine ⟨346145129518880376530734949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230763419679253584353823299 346145129518880376530734949)
              ·
                refine ⟨64902211784790070599512803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 346145129518880376530734949 64902211784790070599512803)
                ·
                  refine ⟨97353317677185105899269205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64902211784790070599512803 97353317677185105899269205)
                  ·
                    refine ⟨1140859191529512959757061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 97353317677185105899269205 1140859191529512959757061)
                    ·
                      rfl

theorem cell22_3332723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 8].length) (baseStart_3332723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3332723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3332723 prefixEnd_3332723 := by exact prefixLift 3332723
  have htrace : WordTrace (prefixWord ++ tailWord_3332723) baseStart_3332723 baseEnd_3332723 := by
    simpa [prefixWord, tailWord_3332723, baseEnd_3332723] using wordTrace_append hprefix tailTrace_3332723
  have hstable : (prefixWord ++ tailWord_3332723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3332723).length < 2 ^ (prefixWord ++ tailWord_3332723).sum := by decide
  have hdescent : baseEnd_3332723 < baseStart_3332723 := by decide
  rcases family_descends (prefixWord ++ tailWord_3332723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3332847 : List Nat := [1, 1, 2, 1, 5, 2, 2, 2, 2, 4]
def baseStart_3332847 : Nat := 118140960795 + 3332847 * 2 ^ 59
def prefixEnd_3332847 : Nat := 4983230072969 + 3 ^ 40 * 3332847 * 2
def baseEnd_3332847 : Nat := 1140901639263617969656681

theorem tailTrace_3332847 : CollatzResearch.WordTrace tailWord_3332847 prefixEnd_3332847 1140901639263617969656681 := by
  unfold tailWord_3332847
  simp only [CollatzResearch.WordTrace]
  refine ⟨121558916556671998795988795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81039277704447999197325863 121558916556671998795988795)
  ·
    refine ⟨182338374835007998193983193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121558916556671998795988795 182338374835007998193983193)
    ·
      refine ⟨136753781126255998645487395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182338374835007998193983193 136753781126255998645487395)
      ·
        refine ⟨205130671689383997968231093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136753781126255998645487395 205130671689383997968231093)
        ·
          refine ⟨19231000470879749809521665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 205130671689383997968231093 19231000470879749809521665)
          ·
            refine ⟨14423250353159812357141249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19231000470879749809521665 14423250353159812357141249)
            ·
              refine ⟨10817437764869859267855937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14423250353159812357141249 10817437764869859267855937)
              ·
                refine ⟨8113078323652394450891953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10817437764869859267855937 8113078323652394450891953)
                ·
                  refine ⟨6084808742739295838168965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8113078323652394450891953 6084808742739295838168965)
                  ·
                    refine ⟨1140901639263617969656681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6084808742739295838168965 1140901639263617969656681)
                    ·
                      rfl

theorem cell22_3332847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 2, 2, 4].length) (baseStart_3332847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3332847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3332847 prefixEnd_3332847 := by exact prefixLift 3332847
  have htrace : WordTrace (prefixWord ++ tailWord_3332847) baseStart_3332847 baseEnd_3332847 := by
    simpa [prefixWord, tailWord_3332847, baseEnd_3332847] using wordTrace_append hprefix tailTrace_3332847
  have hstable : (prefixWord ++ tailWord_3332847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3332847).length < 2 ^ (prefixWord ++ tailWord_3332847).sum := by decide
  have hdescent : baseEnd_3332847 < baseStart_3332847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3332847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3332849 : List Nat := [1, 2, 2, 2, 2, 2, 4, 2, 2, 3]
def baseStart_3332849 : Nat := 118140960795 + 3332849 * 2 ^ 59
def prefixEnd_3332849 : Nat := 4983230072969 + 3 ^ 40 * 3332849 * 2
def baseEnd_3332849 : Nat := 1140902323904490631106675

theorem tailTrace_3332849 : CollatzResearch.WordTrace tailWord_3332849 prefixEnd_3332849 1140902323904490631106675 := by
  unfold tailWord_3332849
  simp only [CollatzResearch.WordTrace]
  refine ⟨121558989502664753137561601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81039326335109835425041067 121558989502664753137561601)
  ·
    refine ⟨91169242126998564853171201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121558989502664753137561601 91169242126998564853171201)
    ·
      refine ⟨68376931595248923639878401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91169242126998564853171201 68376931595248923639878401)
      ·
        refine ⟨51282698696436692729908801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68376931595248923639878401 51282698696436692729908801)
        ·
          refine ⟨38462024022327519547431601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51282698696436692729908801 38462024022327519547431601)
          ·
            refine ⟨28846518016745639660573701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38462024022327519547431601 28846518016745639660573701)
            ·
              refine ⟨5408722128139807436357569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28846518016745639660573701 5408722128139807436357569)
              ·
                refine ⟨4056541596104855577268177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5408722128139807436357569 4056541596104855577268177)
                ·
                  refine ⟨3042406197078641682951133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4056541596104855577268177 3042406197078641682951133)
                  ·
                    refine ⟨1140902323904490631106675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3042406197078641682951133 1140902323904490631106675)
                    ·
                      rfl

theorem cell22_3332849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 2, 2, 3].length) (baseStart_3332849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3332849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3332849 prefixEnd_3332849 := by exact prefixLift 3332849
  have htrace : WordTrace (prefixWord ++ tailWord_3332849) baseStart_3332849 baseEnd_3332849 := by
    simpa [prefixWord, tailWord_3332849, baseEnd_3332849] using wordTrace_append hprefix tailTrace_3332849
  have hstable : (prefixWord ++ tailWord_3332849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3332849).length < 2 ^ (prefixWord ++ tailWord_3332849).sum := by decide
  have hdescent : baseEnd_3332849 < baseStart_3332849 := by decide
  rcases family_descends (prefixWord ++ tailWord_3332849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3332866 : List Nat := [3, 4, 1, 1, 1, 2, 2, 3, 2, 3]
def baseStart_3332866 : Nat := 118140960795 + 3332866 * 2 ^ 59
def prefixEnd_3332866 : Nat := 4983230072969 + 3 ^ 40 * 3332866 * 2
def baseEnd_3332866 : Nat := 1140908143351908253431623

theorem tailTrace_3332866 : CollatzResearch.WordTrace tailWord_3332866 prefixEnd_3332866 1140908143351908253431623 := by
  unfold tailWord_3332866
  simp only [CollatzResearch.WordTrace]
  refine ⟨30389902385900791260232613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81039739695735443360620301 30389902385900791260232613)
  ·
    refine ⟨5698106697356398361293615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30389902385900791260232613 5698106697356398361293615)
    ·
      refine ⟨8547160046034597541940423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5698106697356398361293615 8547160046034597541940423)
      ·
        refine ⟨12820740069051896312910635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8547160046034597541940423 12820740069051896312910635)
        ·
          refine ⟨19231110103577844469365953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12820740069051896312910635 19231110103577844469365953)
          ·
            refine ⟨14423332577683383352024465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19231110103577844469365953 14423332577683383352024465)
            ·
              refine ⟨10817499433262537514018349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14423332577683383352024465 10817499433262537514018349)
              ·
                refine ⟨4056562287473451567756881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10817499433262537514018349 4056562287473451567756881)
                ·
                  refine ⟨3042421715605088675817661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4056562287473451567756881 3042421715605088675817661)
                  ·
                    refine ⟨1140908143351908253431623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3042421715605088675817661 1140908143351908253431623)
                    ·
                      rfl

theorem cell22_3332866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_3332866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3332866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3332866 prefixEnd_3332866 := by exact prefixLift 3332866
  have htrace : WordTrace (prefixWord ++ tailWord_3332866) baseStart_3332866 baseEnd_3332866 := by
    simpa [prefixWord, tailWord_3332866, baseEnd_3332866] using wordTrace_append hprefix tailTrace_3332866
  have hstable : (prefixWord ++ tailWord_3332866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3332866).length < 2 ^ (prefixWord ++ tailWord_3332866).sum := by decide
  have hdescent : baseEnd_3332866 < baseStart_3332866 := by decide
  rcases family_descends (prefixWord ++ tailWord_3332866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3332875 : List Nat := [1, 1, 1, 1, 5, 1, 1, 1, 4, 6]
def baseStart_3332875 : Nat := 118140960795 + 3332875 * 2 ^ 59
def prefixEnd_3332875 : Nat := 4983230072969 + 3 ^ 40 * 3332875 * 2
def baseEnd_3332875 : Nat := 1140911224235835229956595

theorem tailTrace_3332875 : CollatzResearch.WordTrace tailWord_3332875 prefixEnd_3332875 1140911224235835229956595 := by
  unfold tailWord_3332875
  simp only [CollatzResearch.WordTrace]
  refine ⟨121559937800570559578008079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81039958533713706385338719 121559937800570559578008079)
  ·
    refine ⟨182339906700855839367012119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121559937800570559578008079 182339906700855839367012119)
    ·
      refine ⟨273509860051283759050518179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182339906700855839367012119 273509860051283759050518179)
      ·
        refine ⟨410264790076925638575777269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273509860051283759050518179 410264790076925638575777269)
        ·
          refine ⟨38462324069711778616479119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 410264790076925638575777269 38462324069711778616479119)
          ·
            refine ⟨57693486104567667924718679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38462324069711778616479119 57693486104567667924718679)
            ·
              refine ⟨86540229156851501887078019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57693486104567667924718679 86540229156851501887078019)
              ·
                refine ⟨129810343735277252830617029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86540229156851501887078019 129810343735277252830617029)
                ·
                  refine ⟨24339439450364484905740693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 129810343735277252830617029 24339439450364484905740693)
                  ·
                    refine ⟨1140911224235835229956595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24339439450364484905740693 1140911224235835229956595)
                    ·
                      rfl

theorem cell22_3332875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 4, 6].length) (baseStart_3332875 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3332875 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3332875 prefixEnd_3332875 := by exact prefixLift 3332875
  have htrace : WordTrace (prefixWord ++ tailWord_3332875) baseStart_3332875 baseEnd_3332875 := by
    simpa [prefixWord, tailWord_3332875, baseEnd_3332875] using wordTrace_append hprefix tailTrace_3332875
  have hstable : (prefixWord ++ tailWord_3332875).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3332875).length < 2 ^ (prefixWord ++ tailWord_3332875).sum := by decide
  have hdescent : baseEnd_3332875 < baseStart_3332875 := by decide
  rcases family_descends (prefixWord ++ tailWord_3332875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3332905 : List Nat := [1, 2, 1, 1, 1, 1, 1, 4, 3, 7]
def baseStart_3332905 : Nat := 118140960795 + 3332905 * 2 ^ 59
def prefixEnd_3332905 : Nat := 4983230072969 + 3 ^ 40 * 3332905 * 2
def baseEnd_3332905 : Nat := 1140921493848925151706503

theorem tailTrace_3332905 : CollatzResearch.WordTrace tailWord_3332905 prefixEnd_3332905 1140921493848925151706503 := by
  unfold tailWord_3332905
  simp only [CollatzResearch.WordTrace]
  refine ⟨121561031990461874701600169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81040687993641249801066779 121561031990461874701600169)
  ·
    refine ⟨91170773992846406026200127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121561031990461874701600169 91170773992846406026200127)
    ·
      refine ⟨136756160989269609039300191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91170773992846406026200127 136756160989269609039300191)
      ·
        refine ⟨205134241483904413558950287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136756160989269609039300191 205134241483904413558950287)
        ·
          refine ⟨307701362225856620338425431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205134241483904413558950287 307701362225856620338425431)
          ·
            refine ⟨461552043338784930507638147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307701362225856620338425431 461552043338784930507638147)
            ·
              refine ⟨692328065008177395761457221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 461552043338784930507638147 692328065008177395761457221)
              ·
                refine ⟨129811512189033261705273229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 692328065008177395761457221 129811512189033261705273229)
                ·
                  refine ⟨48679317070887473139477461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 129811512189033261705273229 48679317070887473139477461)
                  ·
                    refine ⟨1140921493848925151706503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48679317070887473139477461 1140921493848925151706503)
                    ·
                      rfl

theorem cell22_3332905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 7].length) (baseStart_3332905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3332905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3332905 prefixEnd_3332905 := by exact prefixLift 3332905
  have htrace : WordTrace (prefixWord ++ tailWord_3332905) baseStart_3332905 baseEnd_3332905 := by
    simpa [prefixWord, tailWord_3332905, baseEnd_3332905] using wordTrace_append hprefix tailTrace_3332905
  have hstable : (prefixWord ++ tailWord_3332905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3332905).length < 2 ^ (prefixWord ++ tailWord_3332905).sum := by decide
  have hdescent : baseEnd_3332905 < baseStart_3332905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3332905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3332945 : List Nat := [1, 2, 2, 1, 7, 1, 1, 3, 1, 3]
def baseStart_3332945 : Nat := 118140960795 + 3332945 * 2 ^ 59
def prefixEnd_3332945 : Nat := 4983230072969 + 3 ^ 40 * 3332945 * 2
def baseEnd_3332945 : Nat := 1140935186666378380706381

theorem tailTrace_3332945 : CollatzResearch.WordTrace tailWord_3332945 prefixEnd_3332945 1140935186666378380706381 := by
  unfold tailWord_3332945
  simp only [CollatzResearch.WordTrace]
  refine ⟨121562490910316961533056289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81041660606877974355370859 121562490910316961533056289)
  ·
    refine ⟨91171868182737721149792217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121562490910316961533056289 91171868182737721149792217)
    ·
      refine ⟨68378901137053290862344163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91171868182737721149792217 68378901137053290862344163)
      ·
        refine ⟨102568351705579936293516245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68378901137053290862344163 102568351705579936293516245)
        ·
          refine ⟨2403945743099529756879287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 102568351705579936293516245 2403945743099529756879287)
          ·
            refine ⟨3605918614649294635318931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2403945743099529756879287 3605918614649294635318931)
            ·
              refine ⟨5408877921973941952978397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3605918614649294635318931 5408877921973941952978397)
              ·
                refine ⟨2028329220740228232366899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5408877921973941952978397 2028329220740228232366899)
                ·
                  refine ⟨3042493831110342348550349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2028329220740228232366899 3042493831110342348550349)
                  ·
                    refine ⟨1140935186666378380706381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3042493831110342348550349 1140935186666378380706381)
                    ·
                      rfl

theorem cell22_3332945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 3, 1, 3].length) (baseStart_3332945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3332945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3332945 prefixEnd_3332945 := by exact prefixLift 3332945
  have htrace : WordTrace (prefixWord ++ tailWord_3332945) baseStart_3332945 baseEnd_3332945 := by
    simpa [prefixWord, tailWord_3332945, baseEnd_3332945] using wordTrace_append hprefix tailTrace_3332945
  have hstable : (prefixWord ++ tailWord_3332945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3332945).length < 2 ^ (prefixWord ++ tailWord_3332945).sum := by decide
  have hdescent : baseEnd_3332945 < baseStart_3332945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3332945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3332954 : List Nat := [3, 1, 1, 2, 1, 4, 2, 3, 1, 4]
def baseStart_3332954 : Nat := 118140960795 + 3332954 * 2 ^ 59
def prefixEnd_3332954 : Nat := 4983230072969 + 3 ^ 40 * 3332954 * 2
def baseEnd_3332954 : Nat := 1140938267550305357231353

theorem tailTrace_3332954 : CollatzResearch.WordTrace tailWord_3332954 prefixEnd_3332954 1140938267550305357231353 := by
  unfold tailWord_3332954
  simp only [CollatzResearch.WordTrace]
  refine ⟨30390704791821089017533479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81041879444856237380089277 30390704791821089017533479)
  ·
    refine ⟨45586057187731633526300219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30390704791821089017533479 45586057187731633526300219)
    ·
      refine ⟨68379085781597450289450329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45586057187731633526300219 68379085781597450289450329)
      ·
        refine ⟨51284314336198087717087747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68379085781597450289450329 51284314336198087717087747)
        ·
          refine ⟨76926471504297131575631621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51284314336198087717087747 76926471504297131575631621)
          ·
            refine ⟨14423713407055712170430929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76926471504297131575631621 14423713407055712170430929)
            ·
              refine ⟨10817785055291784127823197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14423713407055712170430929 10817785055291784127823197)
              ·
                refine ⟨4056669395734419047933699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10817785055291784127823197 4056669395734419047933699)
                ·
                  refine ⟨6085004093601628571900549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4056669395734419047933699 6085004093601628571900549)
                  ·
                    refine ⟨1140938267550305357231353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6085004093601628571900549 1140938267550305357231353)
                    ·
                      rfl

theorem cell22_3332954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 3, 1, 4].length) (baseStart_3332954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3332954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3332954 prefixEnd_3332954 := by exact prefixLift 3332954
  have htrace : WordTrace (prefixWord ++ tailWord_3332954) baseStart_3332954 baseEnd_3332954 := by
    simpa [prefixWord, tailWord_3332954, baseEnd_3332954] using wordTrace_append hprefix tailTrace_3332954
  have hstable : (prefixWord ++ tailWord_3332954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3332954).length < 2 ^ (prefixWord ++ tailWord_3332954).sum := by decide
  have hdescent : baseEnd_3332954 < baseStart_3332954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3332954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3332997 : List Nat := [1, 3, 1, 1, 3, 3, 2, 8]
def baseStart_3332997 : Nat := 118140960795 + 3332997 * 2 ^ 59
def prefixEnd_3332997 : Nat := 4983230072969 + 3 ^ 40 * 3332997 * 2
def baseEnd_3332997 : Nat := 126772554147674175378469

theorem tailTrace_3332997 : CollatzResearch.WordTrace tailWord_3332997 prefixEnd_3332997 126772554147674175378469 := by
  unfold tailWord_3332997
  simp only [CollatzResearch.WordTrace]
  refine ⟨121564387506128574413949245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81042925004085716275966163 121564387506128574413949245)
  ·
    refine ⟨45586645314798215405230967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121564387506128574413949245 45586645314798215405230967)
    ·
      refine ⟨68379967972197323107846451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45586645314798215405230967 68379967972197323107846451)
      ·
        refine ⟨102569951958295984661769677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68379967972197323107846451 102569951958295984661769677)
        ·
          refine ⟨38463731984360994248163629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102569951958295984661769677 38463731984360994248163629)
          ·
            refine ⟨14423899494135372843061361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38463731984360994248163629 14423899494135372843061361)
            ·
              refine ⟨10817924620601529632296021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14423899494135372843061361 10817924620601529632296021)
              ·
                refine ⟨126772554147674175378469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10817924620601529632296021 126772554147674175378469)
                ·
                  rfl

theorem cell22_3332997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 8].length) (baseStart_3332997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3332997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3332997 prefixEnd_3332997 := by exact prefixLift 3332997
  have htrace : WordTrace (prefixWord ++ tailWord_3332997) baseStart_3332997 baseEnd_3332997 := by
    simpa [prefixWord, tailWord_3332997, baseEnd_3332997] using wordTrace_append hprefix tailTrace_3332997
  have hstable : (prefixWord ++ tailWord_3332997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3332997).length < 2 ^ (prefixWord ++ tailWord_3332997).sum := by decide
  have hdescent : baseEnd_3332997 < baseStart_3332997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3332997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3332999 : List Nat := [1, 1, 4, 2, 3, 1, 1, 3, 2, 4]
def baseStart_3332999 : Nat := 118140960795 + 3332999 * 2 ^ 59
def prefixEnd_3332999 : Nat := 4983230072969 + 3 ^ 40 * 3332999 * 2
def baseEnd_3332999 : Nat := 1140953671969940239856215

theorem tailTrace_3332999 : CollatzResearch.WordTrace tailWord_3332999 prefixEnd_3332999 1140953671969940239856215 := by
  unfold tailWord_3332999
  simp only [CollatzResearch.WordTrace]
  refine ⟨121564460452121328755522051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81042973634747552503681367 121564460452121328755522051)
  ·
    refine ⟨182346690678181993133283077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121564460452121328755522051 182346690678181993133283077)
    ·
      refine ⟨34190004502159123712490577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 182346690678181993133283077 34190004502159123712490577)
      ·
        refine ⟨25642503376619342784367933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34190004502159123712490577 25642503376619342784367933)
        ·
          refine ⟨9615938766232253544137975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25642503376619342784367933 9615938766232253544137975)
          ·
            refine ⟨14423908149348380316206963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9615938766232253544137975 14423908149348380316206963)
            ·
              refine ⟨21635862224022570474310445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14423908149348380316206963 21635862224022570474310445)
              ·
                refine ⟨8113448334008463927866417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21635862224022570474310445 8113448334008463927866417)
                ·
                  refine ⟨6085086250506347945899813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8113448334008463927866417 6085086250506347945899813)
                  ·
                    refine ⟨1140953671969940239856215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6085086250506347945899813 1140953671969940239856215)
                    ·
                      rfl

theorem cell22_3332999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 3, 2, 4].length) (baseStart_3332999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3332999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3332999 prefixEnd_3332999 := by exact prefixLift 3332999
  have htrace : WordTrace (prefixWord ++ tailWord_3332999) baseStart_3332999 baseEnd_3332999 := by
    simpa [prefixWord, tailWord_3332999, baseEnd_3332999] using wordTrace_append hprefix tailTrace_3332999
  have hstable : (prefixWord ++ tailWord_3332999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3332999).length < 2 ^ (prefixWord ++ tailWord_3332999).sum := by decide
  have hdescent : baseEnd_3332999 < baseStart_3332999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3332999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3333018 : List Nat := [3, 1, 1, 4, 3, 1, 2, 2, 2, 3]
def baseStart_3333018 : Nat := 118140960795 + 3333018 * 2 ^ 59
def prefixEnd_3333018 : Nat := 4983230072969 + 3 ^ 40 * 3333018 * 2
def baseEnd_3333018 : Nat := 1140960176058230523631157

theorem tailTrace_3333018 : CollatzResearch.WordTrace tailWord_3333018 prefixEnd_3333018 1140960176058230523631157 := by
  unfold tailWord_3333018
  simp only [CollatzResearch.WordTrace]
  refine ⟨30391288359763123750115927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81043435626034996666975805 30391288359763123750115927)
  ·
    refine ⟨45586932539644685625173891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30391288359763123750115927 45586932539644685625173891)
    ·
      refine ⟨68380398809467028437760837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45586932539644685625173891 68380398809467028437760837)
      ·
        refine ⟨12821324776775067832080157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68380398809467028437760837 12821324776775067832080157)
        ·
          refine ⟨4807996791290650437030059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12821324776775067832080157 4807996791290650437030059)
          ·
            refine ⟨7211995186935975655545089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4807996791290650437030059 7211995186935975655545089)
            ·
              refine ⟨5408996390201981741658817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7211995186935975655545089 5408996390201981741658817)
              ·
                refine ⟨4056747292651486306244113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5408996390201981741658817 4056747292651486306244113)
                ·
                  refine ⟨3042560469488614729683085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4056747292651486306244113 3042560469488614729683085)
                  ·
                    refine ⟨1140960176058230523631157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3042560469488614729683085 1140960176058230523631157)
                    ·
                      rfl

theorem cell22_3333018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 2, 2, 3].length) (baseStart_3333018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3333018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3333018 prefixEnd_3333018 := by exact prefixLift 3333018
  have htrace : WordTrace (prefixWord ++ tailWord_3333018) baseStart_3333018 baseEnd_3333018 := by
    simpa [prefixWord, tailWord_3333018, baseEnd_3333018] using wordTrace_append hprefix tailTrace_3333018
  have hstable : (prefixWord ++ tailWord_3333018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3333018).length < 2 ^ (prefixWord ++ tailWord_3333018).sum := by decide
  have hdescent : baseEnd_3333018 < baseStart_3333018 := by decide
  rcases family_descends (prefixWord ++ tailWord_3333018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3333020 : List Nat := [2, 2, 3, 3, 2, 2, 2, 2, 4]
def baseStart_3333020 : Nat := 118140960795 + 3333020 * 2 ^ 59
def prefixEnd_3333020 : Nat := 4983230072969 + 3 ^ 40 * 3333020 * 2
def baseEnd_3333020 : Nat := 380320286899701061693717

theorem tailTrace_3333020 : CollatzResearch.WordTrace tailWord_3333020 prefixEnd_3333020 380320286899701061693717 := by
  unfold tailWord_3333020
  simp only [CollatzResearch.WordTrace]
  refine ⟨60782613192522624671018257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81043484256696832894691009 60782613192522624671018257)
  ·
    refine ⟨45586959894391968503263693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60782613192522624671018257 45586959894391968503263693)
    ·
      refine ⟨17095109960396988188723885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45586959894391968503263693 17095109960396988188723885)
      ·
        refine ⟨6410666235148870570771457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17095109960396988188723885 6410666235148870570771457)
        ·
          refine ⟨4807999676361652928078593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6410666235148870570771457 4807999676361652928078593)
          ·
            refine ⟨3605999757271239696058945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4807999676361652928078593 3605999757271239696058945)
            ·
              refine ⟨2704499817953429772044209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3605999757271239696058945 2704499817953429772044209)
              ·
                refine ⟨2028374863465072329033157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2704499817953429772044209 2028374863465072329033157)
                ·
                  refine ⟨380320286899701061693717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2028374863465072329033157 380320286899701061693717)
                  ·
                    rfl

theorem cell22_3333020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 2, 2, 4].length) (baseStart_3333020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3333020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3333020 prefixEnd_3333020 := by exact prefixLift 3333020
  have htrace : WordTrace (prefixWord ++ tailWord_3333020) baseStart_3333020 baseEnd_3333020 := by
    simpa [prefixWord, tailWord_3333020, baseEnd_3333020] using wordTrace_append hprefix tailTrace_3333020
  have hstable : (prefixWord ++ tailWord_3333020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3333020).length < 2 ^ (prefixWord ++ tailWord_3333020).sum := by decide
  have hdescent : baseEnd_3333020 < baseStart_3333020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3333020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3333027 : List Nat := [1, 1, 1, 4, 1, 2, 3, 1, 2, 6]
def baseStart_3333027 : Nat := 118140960795 + 3333027 * 2 ^ 59
def prefixEnd_3333027 : Nat := 4983230072969 + 3 ^ 40 * 3333027 * 2
def baseEnd_3333027 : Nat := 1140963256942157500156129

theorem tailTrace_3333027 : CollatzResearch.WordTrace tailWord_3333027 prefixEnd_3333027 1140963256942157500156129 := by
  unfold tailWord_3333027
  simp only [CollatzResearch.WordTrace]
  refine ⟨121565481696019889537541335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81043654464013259691694223 121565481696019889537541335)
  ·
    refine ⟨182348222544029834306312003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121565481696019889537541335 182348222544029834306312003)
    ·
      refine ⟨273522333816044751459468005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182348222544029834306312003 273522333816044751459468005)
      ·
        refine ⟨51285437590508390898650251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 273522333816044751459468005 51285437590508390898650251)
        ·
          refine ⟨76928156385762586347975377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51285437590508390898650251 76928156385762586347975377)
          ·
            refine ⟨57696117289321939760981533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76928156385762586347975377 57696117289321939760981533)
            ·
              refine ⟨21636043983495727410368075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57696117289321939760981533 21636043983495727410368075)
              ·
                refine ⟨32454065975243591115552113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21636043983495727410368075 32454065975243591115552113)
                ·
                  refine ⟨24340549481432693336664085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32454065975243591115552113 24340549481432693336664085)
                  ·
                    refine ⟨1140963256942157500156129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24340549481432693336664085 1140963256942157500156129)
                    ·
                      rfl

theorem cell22_3333027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 2, 6].length) (baseStart_3333027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3333027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3333027 prefixEnd_3333027 := by exact prefixLift 3333027
  have htrace : WordTrace (prefixWord ++ tailWord_3333027) baseStart_3333027 baseEnd_3333027 := by
    simpa [prefixWord, tailWord_3333027, baseEnd_3333027] using wordTrace_append hprefix tailTrace_3333027
  have hstable : (prefixWord ++ tailWord_3333027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3333027).length < 2 ^ (prefixWord ++ tailWord_3333027).sum := by decide
  have hdescent : baseEnd_3333027 < baseStart_3333027 := by decide
  rcases family_descends (prefixWord ++ tailWord_3333027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3333031 : List Nat := [1, 1, 6, 1, 3, 2, 1, 7]
def baseStart_3333031 : Nat := 118140960795 + 3333031 * 2 ^ 59
def prefixEnd_3333031 : Nat := 4983230072969 + 3 ^ 40 * 3333031 * 2
def baseEnd_3333031 : Nat := 126773847358211424784013

theorem tailTrace_3333031 : CollatzResearch.WordTrace tailWord_3333031 prefixEnd_3333031 126773847358211424784013 := by
  unfold tailWord_3333031
  simp only [CollatzResearch.WordTrace]
  refine ⟨121565627588005398220686947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81043751725336932147124631 121565627588005398220686947)
  ·
    refine ⟨182348441382008097331030421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121565627588005398220686947 182348441382008097331030421)
    ·
      refine ⟨8547583189781629562392051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 182348441382008097331030421 8547583189781629562392051)
      ·
        refine ⟨12821374784672444343588077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8547583189781629562392051 12821374784672444343588077)
        ·
          refine ⟨4808015544252166628845529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12821374784672444343588077 4808015544252166628845529)
          ·
            refine ⟨3606011658189124971634147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4808015544252166628845529 3606011658189124971634147)
            ·
              refine ⟨5409017487283687457451221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3606011658189124971634147 5409017487283687457451221)
              ·
                refine ⟨126773847358211424784013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5409017487283687457451221 126773847358211424784013)
                ·
                  rfl

theorem cell22_3333031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 7].length) (baseStart_3333031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3333031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3333031 prefixEnd_3333031 := by exact prefixLift 3333031
  have htrace : WordTrace (prefixWord ++ tailWord_3333031) baseStart_3333031 baseEnd_3333031 := by
    simpa [prefixWord, tailWord_3333031, baseEnd_3333031] using wordTrace_append hprefix tailTrace_3333031
  have hstable : (prefixWord ++ tailWord_3333031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3333031).length < 2 ^ (prefixWord ++ tailWord_3333031).sum := by decide
  have hdescent : baseEnd_3333031 < baseStart_3333031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3333031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3333042 : List Nat := [3, 2, 1, 1, 1, 1, 1, 1, 11]
def baseStart_3333042 : Nat := 118140960795 + 3333042 * 2 ^ 59
def prefixEnd_3333042 : Nat := 4983230072969 + 3 ^ 40 * 3333042 * 2
def baseEnd_3333042 : Nat := 380322797249567487010361

theorem tailTrace_3333042 : CollatzResearch.WordTrace tailWord_3333042 prefixEnd_3333042 380322797249567487010361 := by
  unfold tailWord_3333042
  simp only [CollatzResearch.WordTrace]
  refine ⟨30391507197741386774834345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81044019193977031399558253 30391507197741386774834345)
  ·
    refine ⟨22793630398306040081125759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30391507197741386774834345 22793630398306040081125759)
    ·
      refine ⟨34190445597459060121688639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22793630398306040081125759 34190445597459060121688639)
      ·
        refine ⟨51285668396188590182532959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34190445597459060121688639 51285668396188590182532959)
        ·
          refine ⟨76928502594282885273799439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51285668396188590182532959 76928502594282885273799439)
          ·
            refine ⟨115392753891424327910699159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76928502594282885273799439 115392753891424327910699159)
            ·
              refine ⟨173089130837136491866048739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115392753891424327910699159 173089130837136491866048739)
              ·
                refine ⟨259633696255704737799073109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173089130837136491866048739 259633696255704737799073109)
                ·
                  refine ⟨380322797249567487010361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 259633696255704737799073109 380322797249567487010361)
                  ·
                    rfl

theorem cell22_3333042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 11].length) (baseStart_3333042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3333042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3333042 prefixEnd_3333042 := by exact prefixLift 3333042
  have htrace : WordTrace (prefixWord ++ tailWord_3333042) baseStart_3333042 baseEnd_3333042 := by
    simpa [prefixWord, tailWord_3333042, baseEnd_3333042] using wordTrace_append hprefix tailTrace_3333042
  have hstable : (prefixWord ++ tailWord_3333042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3333042).length < 2 ^ (prefixWord ++ tailWord_3333042).sum := by decide
  have hdescent : baseEnd_3333042 < baseStart_3333042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3333042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3333069 : List Nat := [1, 6, 3, 1, 1, 2, 1, 2, 2, 3]
def baseStart_3333069 : Nat := 118140960795 + 3333069 * 2 ^ 59
def prefixEnd_3333069 : Nat := 4983230072969 + 3 ^ 40 * 3333069 * 2
def baseEnd_3333069 : Nat := 1140977634400483390606001

theorem tailTrace_3333069 : CollatzResearch.WordTrace tailWord_3333069 prefixEnd_3333069 1140977634400483390606001 := by
  unfold tailWord_3333069
  simp only [CollatzResearch.WordTrace]
  refine ⟨121567013561867730710570261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81044675707911820473713507 121567013561867730710570261)
  ·
    refine ⟨5698453760712549877057981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 121567013561867730710570261 5698453760712549877057981)
    ·
      refine ⟨2136920160267206203896743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5698453760712549877057981 2136920160267206203896743)
      ·
        refine ⟨3205380240400809305845115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2136920160267206203896743 3205380240400809305845115)
        ·
          refine ⟨4808070360601213958767673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3205380240400809305845115 4808070360601213958767673)
          ·
            refine ⟨3606052770450910469075755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4808070360601213958767673 3606052770450910469075755)
            ·
              refine ⟨5409079155676365703613633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3606052770450910469075755 5409079155676365703613633)
              ·
                refine ⟨4056809366757274277710225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5409079155676365703613633 4056809366757274277710225)
                ·
                  refine ⟨3042607025067955708282669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4056809366757274277710225 3042607025067955708282669)
                  ·
                    refine ⟨1140977634400483390606001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3042607025067955708282669 1140977634400483390606001)
                    ·
                      rfl

theorem cell22_3333069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_3333069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3333069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3333069 prefixEnd_3333069 := by exact prefixLift 3333069
  have htrace : WordTrace (prefixWord ++ tailWord_3333069) baseStart_3333069 baseEnd_3333069 := by
    simpa [prefixWord, tailWord_3333069, baseEnd_3333069] using wordTrace_append hprefix tailTrace_3333069
  have hstable : (prefixWord ++ tailWord_3333069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3333069).length < 2 ^ (prefixWord ++ tailWord_3333069).sum := by decide
  have hdescent : baseEnd_3333069 < baseStart_3333069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3333069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3333076 : List Nat := [2, 4, 1, 2, 1, 2, 3, 2, 5]
def baseStart_3333076 : Nat := 118140960795 + 3333076 * 2 ^ 59
def prefixEnd_3333076 : Nat := 4983230072969 + 3 ^ 40 * 3333076 * 2
def baseEnd_3333076 : Nat := 380326676881179235226993

theorem tailTrace_3333076 : CollatzResearch.WordTrace tailWord_3333076 prefixEnd_3333076 380326676881179235226993 := by
  unfold tailWord_3333076
  simp only [CollatzResearch.WordTrace]
  refine ⟨60783634436421185453037541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81044845915228247270716721 60783634436421185453037541)
  ·
    refine ⟨11396931456828972272444539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60783634436421185453037541 11396931456828972272444539)
    ·
      refine ⟨17095397185243458408666809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11396931456828972272444539 17095397185243458408666809)
      ·
        refine ⟨12821547888932593806500107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17095397185243458408666809 12821547888932593806500107)
        ·
          refine ⟨19232321833398890709750161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12821547888932593806500107 19232321833398890709750161)
          ·
            refine ⟨14424241375049168032312621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19232321833398890709750161 14424241375049168032312621)
            ·
              refine ⟨5409090515643438012117233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14424241375049168032312621 5409090515643438012117233)
              ·
                refine ⟨4056817886732578509087925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5409090515643438012117233 4056817886732578509087925)
                ·
                  refine ⟨380326676881179235226993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4056817886732578509087925 380326676881179235226993)
                  ·
                    rfl

theorem cell22_3333076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 2, 5].length) (baseStart_3333076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3333076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3333076 prefixEnd_3333076 := by exact prefixLift 3333076
  have htrace : WordTrace (prefixWord ++ tailWord_3333076) baseStart_3333076 baseEnd_3333076 := by
    simpa [prefixWord, tailWord_3333076, baseEnd_3333076] using wordTrace_append hprefix tailTrace_3333076
  have hstable : (prefixWord ++ tailWord_3333076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3333076).length < 2 ^ (prefixWord ++ tailWord_3333076).sum := by decide
  have hdescent : baseEnd_3333076 < baseStart_3333076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3333076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3333153 : List Nat := [1, 2, 3, 2, 3, 2, 1, 3, 2, 3]
def baseStart_3333153 : Nat := 118140960795 + 3333153 * 2 ^ 59
def prefixEnd_3333153 : Nat := 4983230072969 + 3 ^ 40 * 3333153 * 2
def baseEnd_3333153 : Nat := 1141006389317135171505743

theorem tailTrace_3333153 : CollatzResearch.WordTrace tailWord_3333153 prefixEnd_3333153 1141006389317135171505743 := by
  unfold tailWord_3333153
  simp only [CollatzResearch.WordTrace]
  refine ⟨121570077293563413056628113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81046718195708942037752075 121570077293563413056628113)
  ·
    refine ⟨91177557970172559792471085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121570077293563413056628113 91177557970172559792471085)
    ·
      refine ⟨34191584238814709922176657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91177557970172559792471085 34191584238814709922176657)
      ·
        refine ⟨25643688179111032441632493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34191584238814709922176657 25643688179111032441632493)
        ·
          refine ⟨9616383067166637165612185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25643688179111032441632493 9616383067166637165612185)
          ·
            refine ⟨7212287300374977874209139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9616383067166637165612185 7212287300374977874209139)
            ·
              refine ⟨10818430950562466811313709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7212287300374977874209139 10818430950562466811313709)
              ·
                refine ⟨4056911606460925054242641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10818430950562466811313709 4056911606460925054242641)
                ·
                  refine ⟨3042683704845693790681981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4056911606460925054242641 3042683704845693790681981)
                  ·
                    refine ⟨1141006389317135171505743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3042683704845693790681981 1141006389317135171505743)
                    ·
                      rfl

theorem cell22_3333153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 3, 2, 3].length) (baseStart_3333153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3333153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3333153 prefixEnd_3333153 := by exact prefixLift 3333153
  have htrace : WordTrace (prefixWord ++ tailWord_3333153) baseStart_3333153 baseEnd_3333153 := by
    simpa [prefixWord, tailWord_3333153, baseEnd_3333153] using wordTrace_append hprefix tailTrace_3333153
  have hstable : (prefixWord ++ tailWord_3333153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3333153).length < 2 ^ (prefixWord ++ tailWord_3333153).sum := by decide
  have hdescent : baseEnd_3333153 < baseStart_3333153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3333153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3333194 : List Nat := [3, 1, 2, 1, 1, 2, 2, 3, 7]
def baseStart_3333194 : Nat := 118140960795 + 3333194 * 2 ^ 59
def prefixEnd_3333194 : Nat := 4983230072969 + 3 ^ 40 * 3333194 * 2
def baseEnd_3333194 : Nat := 380340141485008243743539

theorem tailTrace_3333194 : CollatzResearch.WordTrace tailWord_3333194 prefixEnd_3333194 380340141485008243743539 := by
  unfold tailWord_3333194
  simp only [CollatzResearch.WordTrace]
  refine ⟨30392893171603719264717659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81047715124276584705913757 30392893171603719264717659)
  ·
    refine ⟨45589339757405578897076489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30392893171603719264717659 45589339757405578897076489)
    ·
      refine ⟨34192004818054184172807367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45589339757405578897076489 34192004818054184172807367)
      ·
        refine ⟨51288007227081276259211051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34192004818054184172807367 51288007227081276259211051)
        ·
          refine ⟨76932010840621914388816577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51288007227081276259211051 76932010840621914388816577)
          ·
            refine ⟨57699008130466435791612433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76932010840621914388816577 57699008130466435791612433)
            ·
              refine ⟨43274256097849826843709325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57699008130466435791612433 43274256097849826843709325)
              ·
                refine ⟨16227846036693685066390997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43274256097849826843709325 16227846036693685066390997)
                ·
                  refine ⟨380340141485008243743539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16227846036693685066390997 380340141485008243743539)
                  ·
                    rfl

theorem cell22_3333194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 3, 7].length) (baseStart_3333194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3333194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3333194 prefixEnd_3333194 := by exact prefixLift 3333194
  have htrace : WordTrace (prefixWord ++ tailWord_3333194) baseStart_3333194 baseEnd_3333194 := by
    simpa [prefixWord, tailWord_3333194, baseEnd_3333194] using wordTrace_append hprefix tailTrace_3333194
  have hstable : (prefixWord ++ tailWord_3333194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3333194).length < 2 ^ (prefixWord ++ tailWord_3333194).sum := by decide
  have hdescent : baseEnd_3333194 < baseStart_3333194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3333194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3333239 : List Nat := [1, 1, 3, 1, 1, 4, 1, 2, 8]
def baseStart_3333239 : Nat := 118140960795 + 3333239 * 2 ^ 59
def prefixEnd_3333239 : Nat := 4983230072969 + 3 ^ 40 * 3333239 * 2
def baseEnd_3333239 : Nat := 380345276291553204618493

theorem tailTrace_3333239 : CollatzResearch.WordTrace tailWord_3333239 prefixEnd_3333239 380345276291553204618493 := by
  unfold tailWord_3333239
  simp only [CollatzResearch.WordTrace]
  refine ⟨121573213971251849744258771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81048809314167899829505847 121573213971251849744258771)
  ·
    refine ⟨182359820956877774616388157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121573213971251849744258771 182359820956877774616388157)
    ·
      refine ⟨68384932858829165481145559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182359820956877774616388157 68384932858829165481145559)
      ·
        refine ⟨102577399288243748221718339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68384932858829165481145559 102577399288243748221718339)
        ·
          refine ⟨153866098932365622332577509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102577399288243748221718339 153866098932365622332577509)
          ·
            refine ⟨28849893549818554187358283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 153866098932365622332577509 28849893549818554187358283)
            ·
              refine ⟨43274840324727831281037425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28849893549818554187358283 43274840324727831281037425)
              ·
                refine ⟨32456130243545873460778069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43274840324727831281037425 32456130243545873460778069)
                ·
                  refine ⟨380345276291553204618493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32456130243545873460778069 380345276291553204618493)
                  ·
                    rfl

theorem cell22_3333239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 8].length) (baseStart_3333239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3333239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3333239 prefixEnd_3333239 := by exact prefixLift 3333239
  have htrace : WordTrace (prefixWord ++ tailWord_3333239) baseStart_3333239 baseEnd_3333239 := by
    simpa [prefixWord, tailWord_3333239, baseEnd_3333239] using wordTrace_append hprefix tailTrace_3333239
  have hstable : (prefixWord ++ tailWord_3333239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3333239).length < 2 ^ (prefixWord ++ tailWord_3333239).sum := by decide
  have hdescent : baseEnd_3333239 < baseStart_3333239 := by decide
  rcases family_descends (prefixWord ++ tailWord_3333239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3333322 : List Nat := [3, 1, 2, 1, 3, 4, 2, 1, 2, 3]
def baseStart_3333322 : Nat := 118140960795 + 3333322 * 2 ^ 59
def prefixEnd_3333322 : Nat := 4983230072969 + 3 ^ 40 * 3333322 * 2
def baseEnd_3333322 : Nat := 1141064241470875064030225

theorem tailTrace_3333322 : CollatzResearch.WordTrace tailWord_3333322 prefixEnd_3333322 1141064241470875064030225 := by
  unfold tailWord_3333322
  simp only [CollatzResearch.WordTrace]
  refine ⟨30394060307487788729882555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81050827486634103279686813 30394060307487788729882555)
  ·
    refine ⟨45591090461231683094823833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30394060307487788729882555 45591090461231683094823833)
    ·
      refine ⟨34193317845923762321117875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45591090461231683094823833 34193317845923762321117875)
      ·
        refine ⟨51289976768885643481676813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34193317845923762321117875 51289976768885643481676813)
        ·
          refine ⟨19233741288332116305628805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51289976768885643481676813 19233741288332116305628805)
          ·
            refine ⟨3606326491562271807305401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19233741288332116305628805 3606326491562271807305401)
            ·
              refine ⟨2704744868671703855479051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3606326491562271807305401 2704744868671703855479051)
              ·
                refine ⟨4057117303007555783218577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2704744868671703855479051 4057117303007555783218577)
                ·
                  refine ⟨3042837977255666837413933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4057117303007555783218577 3042837977255666837413933)
                  ·
                    refine ⟨1141064241470875064030225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3042837977255666837413933 1141064241470875064030225)
                    ·
                      rfl

theorem cell22_3333322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 2, 1, 2, 3].length) (baseStart_3333322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3333322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3333322 prefixEnd_3333322 := by exact prefixLift 3333322
  have htrace : WordTrace (prefixWord ++ tailWord_3333322) baseStart_3333322 baseEnd_3333322 := by
    simpa [prefixWord, tailWord_3333322, baseEnd_3333322] using wordTrace_append hprefix tailTrace_3333322
  have hstable : (prefixWord ++ tailWord_3333322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3333322).length < 2 ^ (prefixWord ++ tailWord_3333322).sum := by decide
  have hdescent : baseEnd_3333322 < baseStart_3333322 := by decide
  rcases family_descends (prefixWord ++ tailWord_3333322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3333361 : List Nat := [1, 2, 2, 2, 2, 1, 1, 4, 2, 5]
def baseStart_3333361 : Nat := 118140960795 + 3333361 * 2 ^ 59
def prefixEnd_3333361 : Nat := 4983230072969 + 3 ^ 40 * 3333361 * 2
def baseEnd_3333361 : Nat := 1141077591967891962305105

theorem tailTrace_3333361 : CollatzResearch.WordTrace tailWord_3333361 prefixEnd_3333361 1141077591967891962305105 := by
  unfold tailWord_3333361
  simp only [CollatzResearch.WordTrace]
  refine ⟨121577663676809864580199937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81051775784539909720133291 121577663676809864580199937)
  ·
    refine ⟨91183247757607398435149953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121577663676809864580199937 91183247757607398435149953)
    ·
      refine ⟨68387435818205548826362465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91183247757607398435149953 68387435818205548826362465)
      ·
        refine ⟨51290576863654161619771849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68387435818205548826362465 51290576863654161619771849)
        ·
          refine ⟨38467932647740621214828887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51290576863654161619771849 38467932647740621214828887)
          ·
            refine ⟨57701898971610931822243331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38467932647740621214828887 57701898971610931822243331)
            ·
              refine ⟨86552848457416397733364997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57701898971610931822243331 86552848457416397733364997)
              ·
                refine ⟨16228659085765574575005937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86552848457416397733364997 16228659085765574575005937)
                ·
                  refine ⟨12171494314324180931254453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16228659085765574575005937 12171494314324180931254453)
                  ·
                    refine ⟨1141077591967891962305105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12171494314324180931254453 1141077591967891962305105)
                    ·
                      rfl

theorem cell22_3333361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 4, 2, 5].length) (baseStart_3333361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3333361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3333361 prefixEnd_3333361 := by exact prefixLift 3333361
  have htrace : WordTrace (prefixWord ++ tailWord_3333361) baseStart_3333361 baseEnd_3333361 := by
    simpa [prefixWord, tailWord_3333361, baseEnd_3333361] using wordTrace_append hprefix tailTrace_3333361
  have hstable : (prefixWord ++ tailWord_3333361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3333361).length < 2 ^ (prefixWord ++ tailWord_3333361).sum := by decide
  have hdescent : baseEnd_3333361 < baseStart_3333361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3333361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3333363 : List Nat := [1, 1, 1, 2, 2, 6, 2, 2, 5]
def baseStart_3333363 : Nat := 118140960795 + 3333363 * 2 ^ 59
def prefixEnd_3333363 : Nat := 4983230072969 + 3 ^ 40 * 3333363 * 2
def baseEnd_3333363 : Nat := 380359425536254874585033

theorem tailTrace_3333363 : CollatzResearch.WordTrace tailWord_3333363 prefixEnd_3333363 380359425536254874585033 := by
  unfold tailWord_3333363
  simp only [CollatzResearch.WordTrace]
  refine ⟨121577736622802618921772743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81051824415201745947848495 121577736622802618921772743)
  ·
    refine ⟨182366604934203928382659115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121577736622802618921772743 182366604934203928382659115)
    ·
      refine ⟨273549907401305892573988673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182366604934203928382659115 273549907401305892573988673)
      ·
        refine ⟨205162430550979419430491505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273549907401305892573988673 205162430550979419430491505)
        ·
          refine ⟨153871822913234564572868629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205162430550979419430491505 153871822913234564572868629)
          ·
            refine ⟨7212741699057870214353217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 153871822913234564572868629 7212741699057870214353217)
            ·
              refine ⟨5409556274293402660764913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7212741699057870214353217 5409556274293402660764913)
              ·
                refine ⟨4057167205720051995573685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5409556274293402660764913 4057167205720051995573685)
                ·
                  refine ⟨380359425536254874585033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4057167205720051995573685 380359425536254874585033)
                  ·
                    rfl

theorem cell22_3333363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 2, 5].length) (baseStart_3333363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3333363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3333363 prefixEnd_3333363 := by exact prefixLift 3333363
  have htrace : WordTrace (prefixWord ++ tailWord_3333363) baseStart_3333363 baseEnd_3333363 := by
    simpa [prefixWord, tailWord_3333363, baseEnd_3333363] using wordTrace_append hprefix tailTrace_3333363
  have hstable : (prefixWord ++ tailWord_3333363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3333363).length < 2 ^ (prefixWord ++ tailWord_3333363).sum := by decide
  have hdescent : baseEnd_3333363 < baseStart_3333363 := by decide
  rcases family_descends (prefixWord ++ tailWord_3333363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3333393 : List Nat := [1, 2, 2, 1, 1, 4, 2, 4, 1, 4]
def baseStart_3333393 : Nat := 118140960795 + 3333393 * 2 ^ 59
def prefixEnd_3333393 : Nat := 4983230072969 + 3 ^ 40 * 3333393 * 2
def baseEnd_3333393 : Nat := 1141088546221854545505007

theorem tailTrace_3333393 : CollatzResearch.WordTrace tailWord_3333393 prefixEnd_3333393 1141088546221854545505007 := by
  unfold tailWord_3333393
  simp only [CollatzResearch.WordTrace]
  refine ⟨121578830812693934045364833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81052553875129289363576555 121578830812693934045364833)
  ·
    refine ⟨91184123109520450534023625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121578830812693934045364833 91184123109520450534023625)
    ·
      refine ⟨68388092332140337900517719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91184123109520450534023625 68388092332140337900517719)
      ·
        refine ⟨102582138498210506850776579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68388092332140337900517719 102582138498210506850776579)
        ·
          refine ⟨153873207747315760276164869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102582138498210506850776579 153873207747315760276164869)
          ·
            refine ⟨28851226452621705051780913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 153873207747315760276164869 28851226452621705051780913)
            ·
              refine ⟨21638419839466278788835685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28851226452621705051780913 21638419839466278788835685)
              ·
                refine ⟨4057203719899927272906691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21638419839466278788835685 4057203719899927272906691)
                ·
                  refine ⟨6085805579849890909360037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4057203719899927272906691 6085805579849890909360037)
                  ·
                    refine ⟨1141088546221854545505007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6085805579849890909360037 1141088546221854545505007)
                    ·
                      rfl

theorem cell22_3333393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 4].length) (baseStart_3333393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3333393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3333393 prefixEnd_3333393 := by exact prefixLift 3333393
  have htrace : WordTrace (prefixWord ++ tailWord_3333393) baseStart_3333393 baseEnd_3333393 := by
    simpa [prefixWord, tailWord_3333393, baseEnd_3333393] using wordTrace_append hprefix tailTrace_3333393
  have hstable : (prefixWord ++ tailWord_3333393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3333393).length < 2 ^ (prefixWord ++ tailWord_3333393).sum := by decide
  have hdescent : baseEnd_3333393 < baseStart_3333393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3333393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3333425 : List Nat := [1, 2, 2, 3, 3, 1, 2, 4, 4]
def baseStart_3333425 : Nat := 118140960795 + 3333425 * 2 ^ 59
def prefixEnd_3333425 : Nat := 4983230072969 + 3 ^ 40 * 3333425 * 2
def baseEnd_3333425 : Nat := 380366500158605709568303

theorem tailTrace_3333425 : CollatzResearch.WordTrace tailWord_3333425 prefixEnd_3333425 380366500158605709568303 := by
  unfold tailWord_3333425
  simp only [CollatzResearch.WordTrace]
  refine ⟨121579997948578003510529729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81053331965718669007019819 121579997948578003510529729)
  ·
    refine ⟨91184998461433502632897297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121579997948578003510529729 91184998461433502632897297)
    ·
      refine ⟨68388748846075126974672973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91184998461433502632897297 68388748846075126974672973)
      ·
        refine ⟨25645780817278172615502365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68388748846075126974672973 25645780817278172615502365)
        ·
          refine ⟨9617167806479314730813387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25645780817278172615502365 9617167806479314730813387)
          ·
            refine ⟨14425751709718972096220081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9617167806479314730813387 14425751709718972096220081)
            ·
              refine ⟨10819313782289229072165061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14425751709718972096220081 10819313782289229072165061)
              ·
                refine ⟨2028621334179230451030949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10819313782289229072165061 2028621334179230451030949)
                ·
                  refine ⟨380366500158605709568303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2028621334179230451030949 380366500158605709568303)
                  ·
                    rfl

theorem cell22_3333425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 4, 4].length) (baseStart_3333425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3333425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3333425 prefixEnd_3333425 := by exact prefixLift 3333425
  have htrace : WordTrace (prefixWord ++ tailWord_3333425) baseStart_3333425 baseEnd_3333425 := by
    simpa [prefixWord, tailWord_3333425, baseEnd_3333425] using wordTrace_append hprefix tailTrace_3333425
  have hstable : (prefixWord ++ tailWord_3333425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3333425).length < 2 ^ (prefixWord ++ tailWord_3333425).sum := by decide
  have hdescent : baseEnd_3333425 < baseStart_3333425 := by decide
  rcases family_descends (prefixWord ++ tailWord_3333425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3333438 : List Nat := [4, 2, 1, 2, 1, 1, 1, 1, 3, 6]
def baseStart_3333438 : Nat := 118140960795 + 3333438 * 2 ^ 59
def prefixEnd_3333438 : Nat := 4983230072969 + 3 ^ 40 * 3333438 * 2
def baseEnd_3333438 : Nat := 1141103950641489428129869

theorem tailTrace_3333438 : CollatzResearch.WordTrace tailWord_3333438 prefixEnd_3333438 1141103950641489428129869 := by
  unfold tailWord_3333438
  simp only [CollatzResearch.WordTrace]
  refine ⟨15197559012191363341344121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81053648065020604487168645 15197559012191363341344121)
  ·
    refine ⟨11398169259143522506008091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15197559012191363341344121 11398169259143522506008091)
    ·
      refine ⟨17097253888715283759012137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11398169259143522506008091 17097253888715283759012137)
      ·
        refine ⟨12822940416536462819259103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17097253888715283759012137 12822940416536462819259103)
        ·
          refine ⟨19234410624804694228888655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12822940416536462819259103 19234410624804694228888655)
          ·
            refine ⟨28851615937207041343332983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19234410624804694228888655 28851615937207041343332983)
            ·
              refine ⟨43277423905810562014999475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28851615937207041343332983 43277423905810562014999475)
              ·
                refine ⟨64916135858715843022499213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43277423905810562014999475 64916135858715843022499213)
                ·
                  refine ⟨24343550947018441133437205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64916135858715843022499213 24343550947018441133437205)
                  ·
                    refine ⟨1141103950641489428129869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24343550947018441133437205 1141103950641489428129869)
                    ·
                      rfl

theorem cell22_3333438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_3333438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3333438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3333438 prefixEnd_3333438 := by exact prefixLift 3333438
  have htrace : WordTrace (prefixWord ++ tailWord_3333438) baseStart_3333438 baseEnd_3333438 := by
    simpa [prefixWord, tailWord_3333438, baseEnd_3333438] using wordTrace_append hprefix tailTrace_3333438
  have hstable : (prefixWord ++ tailWord_3333438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3333438).length < 2 ^ (prefixWord ++ tailWord_3333438).sum := by decide
  have hdescent : baseEnd_3333438 < baseStart_3333438 := by decide
  rcases family_descends (prefixWord ++ tailWord_3333438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3333498 : List Nat := [3, 1, 1, 1, 1, 1, 2, 7, 5]
def baseStart_3333498 : Nat := 118140960795 + 3333498 * 2 ^ 59
def prefixEnd_3333498 : Nat := 4983230072969 + 3 ^ 40 * 3333498 * 2
def baseEnd_3333498 : Nat := 380374829955889757209895

theorem tailTrace_3333498 : CollatzResearch.WordTrace tailWord_3333498 prefixEnd_3333498 380374829955889757209895 := by
  unfold tailWord_3333498
  simp only [CollatzResearch.WordTrace]
  refine ⟨30395665119328384244484287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81055106984875691318624765 30395665119328384244484287)
  ·
    refine ⟨45593497678992576366726431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30395665119328384244484287 45593497678992576366726431)
    ·
      refine ⟨68390246518488864550089647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45593497678992576366726431 68390246518488864550089647)
      ·
        refine ⟨102585369777733296825134471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68390246518488864550089647 102585369777733296825134471)
        ·
          refine ⟨153878054666599945237701707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102585369777733296825134471 153878054666599945237701707)
          ·
            refine ⟨230817081999899917856552561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153878054666599945237701707 230817081999899917856552561)
            ·
              refine ⟨173112811499924938392414421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 230817081999899917856552561 173112811499924938392414421)
              ·
                refine ⟨4057331519529490743572213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 173112811499924938392414421 4057331519529490743572213)
                ·
                  refine ⟨380374829955889757209895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4057331519529490743572213 380374829955889757209895)
                  ·
                    rfl

theorem cell22_3333498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 7, 5].length) (baseStart_3333498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3333498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3333498 prefixEnd_3333498 := by exact prefixLift 3333498
  have htrace : WordTrace (prefixWord ++ tailWord_3333498) baseStart_3333498 baseEnd_3333498 := by
    simpa [prefixWord, tailWord_3333498, baseEnd_3333498] using wordTrace_append hprefix tailTrace_3333498
  have hstable : (prefixWord ++ tailWord_3333498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3333498).length < 2 ^ (prefixWord ++ tailWord_3333498).sum := by decide
  have hdescent : baseEnd_3333498 < baseStart_3333498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3333498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3333575 : List Nat := [1, 1, 4, 1, 1, 3, 2, 2, 4, 3]
def baseStart_3333575 : Nat := 118140960795 + 3333575 * 2 ^ 59
def prefixEnd_3333575 : Nat := 4983230072969 + 3 ^ 40 * 3333575 * 2
def baseEnd_3333575 : Nat := 1141150848541266737454449

theorem tailTrace_3333575 : CollatzResearch.WordTrace tailWord_3333575 prefixEnd_3333575 1141150848541266737454449 := by
  unfold tailWord_3333575
  simp only [CollatzResearch.WordTrace]
  refine ⟨121585468898034579128490179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81056979265356386085660119 121585468898034579128490179)
  ·
    refine ⟨182378203347051868692735269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121585468898034579128490179 182378203347051868692735269)
    ·
      refine ⟨34195913127572225379887863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 182378203347051868692735269 34195913127572225379887863)
      ·
        refine ⟨51293869691358338069831795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34195913127572225379887863 51293869691358338069831795)
        ·
          refine ⟨76940804537037507104747693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51293869691358338069831795 76940804537037507104747693)
          ·
            refine ⟨28852801701389065164280385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76940804537037507104747693 28852801701389065164280385)
            ·
              refine ⟨21639601276041798873210289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28852801701389065164280385 21639601276041798873210289)
              ·
                refine ⟨16229700957031349154907717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21639601276041798873210289 16229700957031349154907717)
                ·
                  refine ⟨3043068929443377966545197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16229700957031349154907717 3043068929443377966545197)
                  ·
                    refine ⟨1141150848541266737454449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3043068929443377966545197 1141150848541266737454449)
                    ·
                      rfl

theorem cell22_3333575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 2, 4, 3].length) (baseStart_3333575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3333575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3333575 prefixEnd_3333575 := by exact prefixLift 3333575
  have htrace : WordTrace (prefixWord ++ tailWord_3333575) baseStart_3333575 baseEnd_3333575 := by
    simpa [prefixWord, tailWord_3333575, baseEnd_3333575] using wordTrace_append hprefix tailTrace_3333575
  have hstable : (prefixWord ++ tailWord_3333575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3333575).length < 2 ^ (prefixWord ++ tailWord_3333575).sum := by decide
  have hdescent : baseEnd_3333575 < baseStart_3333575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3333575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3333592 : List Nat := [2, 1, 2, 2, 2, 1, 5, 2, 2, 3]
def baseStart_3333592 : Nat := 118140960795 + 3333592 * 2 ^ 59
def prefixEnd_3333592 : Nat := 4983230072969 + 3 ^ 40 * 3333592 * 2
def baseEnd_3333592 : Nat := 1141156667988684359779397

theorem tailTrace_3333592 : CollatzResearch.WordTrace tailWord_3333592 prefixEnd_3333592 1141156667988684359779397 := by
  unfold tailWord_3333592
  simp only [CollatzResearch.WordTrace]
  refine ⟨60793044469486495515929515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81057392625981994021239353 60793044469486495515929515)
  ·
    refine ⟨91189566704229743273894273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60793044469486495515929515 91189566704229743273894273)
    ·
      refine ⟨68392175028172307455420705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91189566704229743273894273 68392175028172307455420705)
      ·
        refine ⟨51294131271129230591565529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68392175028172307455420705 51294131271129230591565529)
        ·
          refine ⟨38470598453346922943674147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51294131271129230591565529 38470598453346922943674147)
          ·
            refine ⟨57705897680020384415511221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38470598453346922943674147 57705897680020384415511221)
            ·
              refine ⟨5409927907501911038954177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57705897680020384415511221 5409927907501911038954177)
              ·
                refine ⟨4057445930626433279215633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5409927907501911038954177 4057445930626433279215633)
                ·
                  refine ⟨3043084447969824959411725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4057445930626433279215633 3043084447969824959411725)
                  ·
                    refine ⟨1141156667988684359779397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3043084447969824959411725 1141156667988684359779397)
                    ·
                      rfl

theorem cell22_3333592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 2, 2, 3].length) (baseStart_3333592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3333592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3333592 prefixEnd_3333592 := by exact prefixLift 3333592
  have htrace : WordTrace (prefixWord ++ tailWord_3333592) baseStart_3333592 baseEnd_3333592 := by
    simpa [prefixWord, tailWord_3333592, baseEnd_3333592] using wordTrace_append hprefix tailTrace_3333592
  have hstable : (prefixWord ++ tailWord_3333592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3333592).length < 2 ^ (prefixWord ++ tailWord_3333592).sum := by decide
  have hdescent : baseEnd_3333592 < baseStart_3333592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3333592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3333622 : List Nat := [5, 1, 1, 1, 2, 2, 4, 6]
def baseStart_3333622 : Nat := 118140960795 + 3333622 * 2 ^ 59
def prefixEnd_3333622 : Nat := 4983230072969 + 3 ^ 40 * 3333622 * 2
def baseEnd_3333622 : Nat := 126796326400197142392145

theorem tailTrace_3333622 : CollatzResearch.WordTrace tailWord_3333622 prefixEnd_3333622 126796326400197142392145 := by
  unfold tailWord_3333622
  simp only [CollatzResearch.WordTrace]
  refine ⟨7599198945554019134715695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81058122085909537436967413 7599198945554019134715695)
  ·
    refine ⟨11398798418331028702073543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7599198945554019134715695 11398798418331028702073543)
    ·
      refine ⟨17098197627496543053110315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11398798418331028702073543 17098197627496543053110315)
      ·
        refine ⟨25647296441244814579665473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17098197627496543053110315 25647296441244814579665473)
        ·
          refine ⟨19235472330933610934749105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25647296441244814579665473 19235472330933610934749105)
          ·
            refine ⟨14426604248200208201061829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19235472330933610934749105 14426604248200208201061829)
            ·
              refine ⟨2704988296537539037699093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14426604248200208201061829 2704988296537539037699093)
              ·
                refine ⟨126796326400197142392145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2704988296537539037699093 126796326400197142392145)
                ·
                  rfl

theorem cell22_3333622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 4, 6].length) (baseStart_3333622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3333622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3333622 prefixEnd_3333622 := by exact prefixLift 3333622
  have htrace : WordTrace (prefixWord ++ tailWord_3333622) baseStart_3333622 baseEnd_3333622 := by
    simpa [prefixWord, tailWord_3333622, baseEnd_3333622] using wordTrace_append hprefix tailTrace_3333622
  have hstable : (prefixWord ++ tailWord_3333622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3333622).length < 2 ^ (prefixWord ++ tailWord_3333622).sum := by decide
  have hdescent : baseEnd_3333622 < baseStart_3333622 := by decide
  rcases family_descends (prefixWord ++ tailWord_3333622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3333667 : List Nat := [1, 1, 1, 4, 5, 1, 1, 3, 5]
def baseStart_3333667 : Nat := 118140960795 + 3333667 * 2 ^ 59
def prefixEnd_3333667 : Nat := 4983230072969 + 3 ^ 40 * 3333667 * 2
def baseEnd_3333667 : Nat := 380394114007136388051389

theorem tailTrace_3333667 : CollatzResearch.WordTrace tailWord_3333667 prefixEnd_3333667 380394114007136388051389 := by
  unfold tailWord_3333667
  simp only [CollatzResearch.WordTrace]
  refine ⟨121588824413701278840839255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81059216275800852560559503 121588824413701278840839255)
  ·
    refine ⟨182383236620551918261258883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121588824413701278840839255 182383236620551918261258883)
    ·
      refine ⟨273574854930827877391888325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182383236620551918261258883 273574854930827877391888325)
      ·
        refine ⟨51295285299530227010979061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 273574854930827877391888325 51295285299530227010979061)
        ·
          refine ⟨4808932996830958782279287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51295285299530227010979061 4808932996830958782279287)
          ·
            refine ⟨7213399495246438173418931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4808932996830958782279287 7213399495246438173418931)
            ·
              refine ⟨10820099242869657260128397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7213399495246438173418931 10820099242869657260128397)
              ·
                refine ⟨4057537216076121472548149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10820099242869657260128397 4057537216076121472548149)
                ·
                  refine ⟨380394114007136388051389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4057537216076121472548149 380394114007136388051389)
                  ·
                    rfl

theorem cell22_3333667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 3, 5].length) (baseStart_3333667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3333667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3333667 prefixEnd_3333667 := by exact prefixLift 3333667
  have htrace : WordTrace (prefixWord ++ tailWord_3333667) baseStart_3333667 baseEnd_3333667 := by
    simpa [prefixWord, tailWord_3333667, baseEnd_3333667] using wordTrace_append hprefix tailTrace_3333667
  have hstable : (prefixWord ++ tailWord_3333667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3333667).length < 2 ^ (prefixWord ++ tailWord_3333667).sum := by decide
  have hdescent : baseEnd_3333667 < baseStart_3333667 := by decide
  rcases family_descends (prefixWord ++ tailWord_3333667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3333710 : List Nat := [4, 1, 1, 1, 1, 2, 1, 1, 5, 5]
def baseStart_3333710 : Nat := 118140960795 + 3333710 * 2 ^ 59
def prefixEnd_3333710 : Nat := 4983230072969 + 3 ^ 40 * 3333710 * 2
def baseEnd_3333710 : Nat := 1141197061800171385329035

theorem tailTrace_3333710 : CollatzResearch.WordTrace tailWord_3333710 prefixEnd_3333710 1141197061800171385329035 := by
  unfold tailWord_3333710
  simp only [CollatzResearch.WordTrace]
  refine ⟨15198799094068187148081823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81060261835030331456436389 15198799094068187148081823)
  ·
    refine ⟨22798198641102280722122735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15198799094068187148081823 22798198641102280722122735)
    ·
      refine ⟨34197297961653421083184103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22798198641102280722122735 34197297961653421083184103)
      ·
        refine ⟨51295946942480131624776155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34197297961653421083184103 51295946942480131624776155)
        ·
          refine ⟨76943920413720197437164233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51295946942480131624776155 76943920413720197437164233)
          ·
            refine ⟨57707940310290148077873175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76943920413720197437164233 57707940310290148077873175)
            ·
              refine ⟨86561910465435222116809763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57707940310290148077873175 86561910465435222116809763)
              ·
                refine ⟨129842865698152833175214645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86561910465435222116809763 129842865698152833175214645)
                ·
                  refine ⟨12172768659201828110176373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 129842865698152833175214645 12172768659201828110176373)
                  ·
                    refine ⟨1141197061800171385329035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12172768659201828110176373 1141197061800171385329035)
                    ·
                      rfl

theorem cell22_3333710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 5, 5].length) (baseStart_3333710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3333710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3333710 prefixEnd_3333710 := by exact prefixLift 3333710
  have htrace : WordTrace (prefixWord ++ tailWord_3333710) baseStart_3333710 baseEnd_3333710 := by
    simpa [prefixWord, tailWord_3333710, baseEnd_3333710] using wordTrace_append hprefix tailTrace_3333710
  have hstable : (prefixWord ++ tailWord_3333710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3333710).length < 2 ^ (prefixWord ++ tailWord_3333710).sum := by decide
  have hdescent : baseEnd_3333710 < baseStart_3333710 := by decide
  rcases family_descends (prefixWord ++ tailWord_3333710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3333712 : List Nat := [2, 1, 1, 1, 1, 3, 5, 4, 4]
def baseStart_3333712 : Nat := 118140960795 + 3333712 * 2 ^ 59
def prefixEnd_3333712 : Nat := 4983230072969 + 3 ^ 40 * 3333712 * 2
def baseEnd_3333712 : Nat := 380399248813681348926343

theorem tailTrace_3333712 : CollatzResearch.WordTrace tailWord_3333712 prefixEnd_3333712 380399248813681348926343 := by
  unfold tailWord_3333712
  simp only [CollatzResearch.WordTrace]
  refine ⟨60795232849269125763113695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81060310465692167684151593 60795232849269125763113695)
  ·
    refine ⟨91192849273903688644670543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60795232849269125763113695 91192849273903688644670543)
    ·
      refine ⟨136789273910855532967005815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91192849273903688644670543 136789273910855532967005815)
      ·
        refine ⟨205183910866283299450508723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136789273910855532967005815 205183910866283299450508723)
        ·
          refine ⟨307775866299424949175763085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205183910866283299450508723 307775866299424949175763085)
          ·
            refine ⟨115415949862284355940911157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 307775866299424949175763085 115415949862284355940911157)
            ·
              refine ⟨10820245299589158369460421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 115415949862284355940911157 10820245299589158369460421)
              ·
                refine ⟨2028795993672967194273829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10820245299589158369460421 2028795993672967194273829)
                ·
                  refine ⟨380399248813681348926343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2028795993672967194273829 380399248813681348926343)
                  ·
                    rfl

theorem cell22_3333712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 4, 4].length) (baseStart_3333712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3333712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3333712 prefixEnd_3333712 := by exact prefixLift 3333712
  have htrace : WordTrace (prefixWord ++ tailWord_3333712) baseStart_3333712 baseEnd_3333712 := by
    simpa [prefixWord, tailWord_3333712, baseEnd_3333712] using wordTrace_append hprefix tailTrace_3333712
  have hstable : (prefixWord ++ tailWord_3333712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3333712).length < 2 ^ (prefixWord ++ tailWord_3333712).sum := by decide
  have hdescent : baseEnd_3333712 < baseStart_3333712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3333712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3333761 : List Nat := [1, 2, 4, 2, 1, 4, 1, 2, 2, 3]
def baseStart_3333761 : Nat := 118140960795 + 3333761 * 2 ^ 59
def prefixEnd_3333761 : Nat := 4983230072969 + 3 ^ 40 * 3333761 * 2
def baseEnd_3333761 : Nat := 1141214520142424252303879

theorem tailTrace_3333761 : CollatzResearch.WordTrace tailWord_3333761 prefixEnd_3333761 1141214520142424252303879 := by
  unfold tailWord_3333761
  simp only [CollatzResearch.WordTrace]
  refine ⟨121592252875360732894761137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81061501916907155263174091 121592252875360732894761137)
  ·
    refine ⟨91194189656520549671070853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121592252875360732894761137 91194189656520549671070853)
    ·
      refine ⟨17098910560597603063325785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91194189656520549671070853 17098910560597603063325785)
      ·
        refine ⟨12824182920448202297494339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17098910560597603063325785 12824182920448202297494339)
        ·
          refine ⟨19236274380672303446241509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12824182920448202297494339 19236274380672303446241509)
          ·
            refine ⟨3606801446376056896170283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19236274380672303446241509 3606801446376056896170283)
            ·
              refine ⟨5410202169564085344255425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3606801446376056896170283 5410202169564085344255425)
              ·
                refine ⟨4057651627173064008191569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5410202169564085344255425 4057651627173064008191569)
                ·
                  refine ⟨3043238720379798006143677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4057651627173064008191569 3043238720379798006143677)
                  ·
                    refine ⟨1141214520142424252303879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3043238720379798006143677 1141214520142424252303879)
                    ·
                      rfl

theorem cell22_3333761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 2, 2, 3].length) (baseStart_3333761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3333761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3333761 prefixEnd_3333761 := by exact prefixLift 3333761
  have htrace : WordTrace (prefixWord ++ tailWord_3333761) baseStart_3333761 baseEnd_3333761 := by
    simpa [prefixWord, tailWord_3333761, baseEnd_3333761] using wordTrace_append hprefix tailTrace_3333761
  have hstable : (prefixWord ++ tailWord_3333761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3333761).length < 2 ^ (prefixWord ++ tailWord_3333761).sum := by decide
  have hdescent : baseEnd_3333761 < baseStart_3333761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3333761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3333778 : List Nat := [3, 2, 3, 1, 3, 1, 3, 1, 2, 3]
def baseStart_3333778 : Nat := 118140960795 + 3333778 * 2 ^ 59
def prefixEnd_3333778 : Nat := 4983230072969 + 3 ^ 40 * 3333778 * 2
def baseEnd_3333778 : Nat := 1141220339589841874628827

theorem tailTrace_3333778 : CollatzResearch.WordTrace tailWord_3333778 prefixEnd_3333778 1141220339589841874628827 := by
  unfold tailWord_3333778
  simp only [CollatzResearch.WordTrace]
  refine ⟨30398218229074786199532497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81061915277532763198753325 30398218229074786199532497)
  ·
    refine ⟨22798663671806089649649373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30398218229074786199532497 22798663671806089649649373)
    ·
      refine ⟨8549498876927283618618515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22798663671806089649649373 8549498876927283618618515)
      ·
        refine ⟨12824248315390925427927773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8549498876927283618618515 12824248315390925427927773)
        ·
          refine ⟨4809093118271597035472915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12824248315390925427927773 4809093118271597035472915)
          ·
            refine ⟨7213639677407395553209373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4809093118271597035472915 7213639677407395553209373)
            ·
              refine ⟨2705114879027773332453515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7213639677407395553209373 2705114879027773332453515)
              ·
                refine ⟨4057672318541659998680273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2705114879027773332453515 4057672318541659998680273)
                ·
                  refine ⟨3043254238906244999010205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4057672318541659998680273 3043254238906244999010205)
                  ·
                    refine ⟨1141220339589841874628827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3043254238906244999010205 1141220339589841874628827)
                    ·
                      rfl

theorem cell22_3333778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_3333778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3333778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3333778 prefixEnd_3333778 := by exact prefixLift 3333778
  have htrace : WordTrace (prefixWord ++ tailWord_3333778) baseStart_3333778 baseEnd_3333778 := by
    simpa [prefixWord, tailWord_3333778, baseEnd_3333778] using wordTrace_append hprefix tailTrace_3333778
  have hstable : (prefixWord ++ tailWord_3333778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3333778).length < 2 ^ (prefixWord ++ tailWord_3333778).sum := by decide
  have hdescent : baseEnd_3333778 < baseStart_3333778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3333778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3333791 : List Nat := [1, 1, 2, 7, 1, 2, 2, 6]
def baseStart_3333791 : Nat := 118140960795 + 3333791 * 2 ^ 59
def prefixEnd_3333791 : Nat := 4983230072969 + 3 ^ 40 * 3333791 * 2
def baseEnd_3333791 : Nat := 126802754417279352672643

theorem tailTrace_3333791 : CollatzResearch.WordTrace tailWord_3333791 prefixEnd_3333791 126802754417279352672643 := by
  unfold tailWord_3333791
  simp only [CollatzResearch.WordTrace]
  refine ⟨121593347065252048018353227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81062231376834698678902151 121593347065252048018353227)
  ·
    refine ⟨182390020597878072027529841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121593347065252048018353227 182390020597878072027529841)
    ·
      refine ⟨136792515448408554020647381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182390020597878072027529841 136792515448408554020647381)
      ·
        refine ⟨3206074580822075484858923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 136792515448408554020647381 3206074580822075484858923)
        ·
          refine ⟨4809111871233113227288385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3206074580822075484858923 4809111871233113227288385)
          ·
            refine ⟨3606833903424834920466289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4809111871233113227288385 3606833903424834920466289)
            ·
              refine ⟨2705125427568626190349717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3606833903424834920466289 2705125427568626190349717)
              ·
                refine ⟨126802754417279352672643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2705125427568626190349717 126802754417279352672643)
                ·
                  rfl

theorem cell22_3333791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 2, 6].length) (baseStart_3333791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3333791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3333791 prefixEnd_3333791 := by exact prefixLift 3333791
  have htrace : WordTrace (prefixWord ++ tailWord_3333791) baseStart_3333791 baseEnd_3333791 := by
    simpa [prefixWord, tailWord_3333791, baseEnd_3333791] using wordTrace_append hprefix tailTrace_3333791
  have hstable : (prefixWord ++ tailWord_3333791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3333791).length < 2 ^ (prefixWord ++ tailWord_3333791).sum := by decide
  have hdescent : baseEnd_3333791 < baseStart_3333791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3333791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3333832 : List Nat := [2, 1, 3, 1, 2, 2, 2, 2, 3, 4]
def baseStart_3333832 : Nat := 118140960795 + 3333832 * 2 ^ 59
def prefixEnd_3333832 : Nat := 4983230072969 + 3 ^ 40 * 3333832 * 2
def baseEnd_3333832 : Nat := 1141238824893403733778661

theorem tailTrace_3333832 : CollatzResearch.WordTrace tailWord_3333832 prefixEnd_3333832 1141238824893403733778661 := by
  unfold tailWord_3333832
  simp only [CollatzResearch.WordTrace]
  refine ⟨60797421229051756010297875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81063228305402341347063833 60797421229051756010297875)
  ·
    refine ⟨91196131843577634015446813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60797421229051756010297875 91196131843577634015446813)
    ·
      refine ⟨34198549441341612755792555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91196131843577634015446813 34198549441341612755792555)
      ·
        refine ⟨51297824162012419133688833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34198549441341612755792555 51297824162012419133688833)
        ·
          refine ⟨38473368121509314350266625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51297824162012419133688833 38473368121509314350266625)
          ·
            refine ⟨28855026091131985762699969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38473368121509314350266625 28855026091131985762699969)
            ·
              refine ⟨21641269568348989322024977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28855026091131985762699969 21641269568348989322024977)
              ·
                refine ⟨16230952176261741991518733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21641269568348989322024977 16230952176261741991518733)
                ·
                  refine ⟨6086607066098153246819525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16230952176261741991518733 6086607066098153246819525)
                  ·
                    refine ⟨1141238824893403733778661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6086607066098153246819525 1141238824893403733778661)
                    ·
                      rfl

theorem cell22_3333832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 2, 3, 4].length) (baseStart_3333832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3333832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3333832 prefixEnd_3333832 := by exact prefixLift 3333832
  have htrace : WordTrace (prefixWord ++ tailWord_3333832) baseStart_3333832 baseEnd_3333832 := by
    simpa [prefixWord, tailWord_3333832, baseEnd_3333832] using wordTrace_append hprefix tailTrace_3333832
  have hstable : (prefixWord ++ tailWord_3333832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3333832).length < 2 ^ (prefixWord ++ tailWord_3333832).sum := by decide
  have hdescent : baseEnd_3333832 < baseStart_3333832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3333832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3333849 : List Nat := [1, 2, 1, 2, 3, 3, 3, 2, 1, 4]
def baseStart_3333849 : Nat := 118140960795 + 3333849 * 2 ^ 59
def prefixEnd_3333849 : Nat := 4983230072969 + 3 ^ 40 * 3333849 * 2
def baseEnd_3333849 : Nat := 1141244644340821356103609

theorem tailTrace_3333849 : CollatzResearch.WordTrace tailWord_3333849 prefixEnd_3333849 1141244644340821356103609 := by
  unfold tailWord_3333849
  simp only [CollatzResearch.WordTrace]
  refine ⟨121595462499041923923964601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81063641666027949282643067 121595462499041923923964601)
  ·
    refine ⟨91196596874281442942973451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121595462499041923923964601 91196596874281442942973451)
    ·
      refine ⟨136794895311422164414460177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91196596874281442942973451 136794895311422164414460177)
      ·
        refine ⟨102596171483566623310845133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136794895311422164414460177 102596171483566623310845133)
        ·
          refine ⟨38473564306337483741566925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102596171483566623310845133 38473564306337483741566925)
          ·
            refine ⟨14427586614876556403087597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38473564306337483741566925 14427586614876556403087597)
            ·
              refine ⟨5410344980578708651157849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14427586614876556403087597 5410344980578708651157849)
              ·
                refine ⟨4057758735434031488368387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5410344980578708651157849 4057758735434031488368387)
                ·
                  refine ⟨6086638103151047232552581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4057758735434031488368387 6086638103151047232552581)
                  ·
                    refine ⟨1141244644340821356103609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6086638103151047232552581 1141244644340821356103609)
                    ·
                      rfl

theorem cell22_3333849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 2, 1, 4].length) (baseStart_3333849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3333849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3333849 prefixEnd_3333849 := by exact prefixLift 3333849
  have htrace : WordTrace (prefixWord ++ tailWord_3333849) baseStart_3333849 baseEnd_3333849 := by
    simpa [prefixWord, tailWord_3333849, baseEnd_3333849] using wordTrace_append hprefix tailTrace_3333849
  have hstable : (prefixWord ++ tailWord_3333849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3333849).length < 2 ^ (prefixWord ++ tailWord_3333849).sum := by decide
  have hdescent : baseEnd_3333849 < baseStart_3333849 := by decide
  rcases family_descends (prefixWord ++ tailWord_3333849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3333879 : List Nat := [1, 1, 3, 1, 1, 1, 5, 4, 2, 3]
def baseStart_3333879 : Nat := 118140960795 + 3333879 * 2 ^ 59
def prefixEnd_3333879 : Nat := 4983230072969 + 3 ^ 40 * 3333879 * 2
def baseEnd_3333879 : Nat := 1141254913953911277853517

theorem tailTrace_3333879 : CollatzResearch.WordTrace tailWord_3333879 prefixEnd_3333879 1141254913953911277853517 := by
  unfold tailWord_3333879
  simp only [CollatzResearch.WordTrace]
  refine ⟨121596556688933239047556691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81064371125955492698371127 121596556688933239047556691)
  ·
    refine ⟨182394835033399858571335037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121596556688933239047556691 182394835033399858571335037)
    ·
      refine ⟨68398063137524946964250639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182394835033399858571335037 68398063137524946964250639)
      ·
        refine ⟨102597094706287420446375959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68398063137524946964250639 102597094706287420446375959)
        ·
          refine ⟨153895642059431130669563939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102597094706287420446375959 153895642059431130669563939)
          ·
            refine ⟨230843463089146696004345909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153895642059431130669563939 230843463089146696004345909)
            ·
              refine ⟨21641574664607502750407429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 230843463089146696004345909 21641574664607502750407429)
              ·
                refine ⟨4057795249613906765701393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21641574664607502750407429 4057795249613906765701393)
                ·
                  refine ⟨3043346437210430074276045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4057795249613906765701393 3043346437210430074276045)
                  ·
                    refine ⟨1141254913953911277853517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3043346437210430074276045 1141254913953911277853517)
                    ·
                      rfl

theorem cell22_3333879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 4, 2, 3].length) (baseStart_3333879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3333879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3333879 prefixEnd_3333879 := by exact prefixLift 3333879
  have htrace : WordTrace (prefixWord ++ tailWord_3333879) baseStart_3333879 baseEnd_3333879 := by
    simpa [prefixWord, tailWord_3333879, baseEnd_3333879] using wordTrace_append hprefix tailTrace_3333879
  have hstable : (prefixWord ++ tailWord_3333879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3333879).length < 2 ^ (prefixWord ++ tailWord_3333879).sum := by decide
  have hdescent : baseEnd_3333879 < baseStart_3333879 := by decide
  rcases family_descends (prefixWord ++ tailWord_3333879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3333909 : List Nat := [1, 3, 2, 1, 2, 4, 3, 6]
def baseStart_3333909 : Nat := 118140960795 + 3333909 * 2 ^ 59
def prefixEnd_3333909 : Nat := 4983230072969 + 3 ^ 40 * 3333909 * 2
def baseEnd_3333909 : Nat := 126807242618555688844825

theorem tailTrace_3333909 : CollatzResearch.WordTrace tailWord_3333909 prefixEnd_3333909 126807242618555688844825 := by
  unfold tailWord_3333909
  simp only [CollatzResearch.WordTrace]
  refine ⟨121597650878824554171148781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81065100585883036114099187 121597650878824554171148781)
  ·
    refine ⟨45599119079559207814180793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121597650878824554171148781 45599119079559207814180793)
    ·
      refine ⟨34199339309669405860635595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45599119079559207814180793 34199339309669405860635595)
      ·
        refine ⟨51299008964504108790953393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34199339309669405860635595 51299008964504108790953393)
        ·
          refine ⟨38474256723378081593215045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51299008964504108790953393 38474256723378081593215045)
          ·
            refine ⟨7213923135633390298727821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38474256723378081593215045 7213923135633390298727821)
            ·
              refine ⟨2705221175862521362022933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7213923135633390298727821 2705221175862521362022933)
              ·
                refine ⟨126807242618555688844825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2705221175862521362022933 126807242618555688844825)
                ·
                  rfl

theorem cell22_3333909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 3, 6].length) (baseStart_3333909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3333909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3333909 prefixEnd_3333909 := by exact prefixLift 3333909
  have htrace : WordTrace (prefixWord ++ tailWord_3333909) baseStart_3333909 baseEnd_3333909 := by
    simpa [prefixWord, tailWord_3333909, baseEnd_3333909] using wordTrace_append hprefix tailTrace_3333909
  have hstable : (prefixWord ++ tailWord_3333909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3333909).length < 2 ^ (prefixWord ++ tailWord_3333909).sum := by decide
  have hdescent : baseEnd_3333909 < baseStart_3333909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3333909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3333911 : List Nat := [1, 1, 3, 4, 2, 3, 1, 1, 2, 4]
def baseStart_3333911 : Nat := 118140960795 + 3333911 * 2 ^ 59
def prefixEnd_3333911 : Nat := 4983230072969 + 3 ^ 40 * 3333911 * 2
def baseEnd_3333911 : Nat := 1141265868207873861053419

theorem tailTrace_3333911 : CollatzResearch.WordTrace tailWord_3333911 prefixEnd_3333911 1141265868207873861053419 := by
  unfold tailWord_3333911
  simp only [CollatzResearch.WordTrace]
  refine ⟨121597723824817308512721587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81065149216544872341814391 121597723824817308512721587)
  ·
    refine ⟨182396585737225962769082381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121597723824817308512721587 182396585737225962769082381)
    ·
      refine ⟨68398719651459736038405893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182396585737225962769082381 68398719651459736038405893)
      ·
        refine ⟨12824759934648700507201105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68398719651459736038405893 12824759934648700507201105)
        ·
          refine ⟨9618569950986525380400829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12824759934648700507201105 9618569950986525380400829)
          ·
            refine ⟨3606963731619947017650311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9618569950986525380400829 3606963731619947017650311)
            ·
              refine ⟨5410445597429920526475467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3606963731619947017650311 5410445597429920526475467)
              ·
                refine ⟨8115668396144880789713201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5410445597429920526475467 8115668396144880789713201)
                ·
                  refine ⟨6086751297108660592284901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8115668396144880789713201 6086751297108660592284901)
                  ·
                    refine ⟨1141265868207873861053419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6086751297108660592284901 1141265868207873861053419)
                    ·
                      rfl

theorem cell22_3333911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 1, 2, 4].length) (baseStart_3333911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3333911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3333911 prefixEnd_3333911 := by exact prefixLift 3333911
  have htrace : WordTrace (prefixWord ++ tailWord_3333911) baseStart_3333911 baseEnd_3333911 := by
    simpa [prefixWord, tailWord_3333911, baseEnd_3333911] using wordTrace_append hprefix tailTrace_3333911
  have hstable : (prefixWord ++ tailWord_3333911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3333911).length < 2 ^ (prefixWord ++ tailWord_3333911).sum := by decide
  have hdescent : baseEnd_3333911 < baseStart_3333911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3333911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3333975 : List Nat := [1, 1, 3, 2, 5, 2, 1, 3, 1, 3]
def baseStart_3333975 : Nat := 118140960795 + 3333975 * 2 ^ 59
def prefixEnd_3333975 : Nat := 4983230072969 + 3 ^ 40 * 3333975 * 2
def baseEnd_3333975 : Nat := 1141287776715799027453223

theorem tailTrace_3333975 : CollatzResearch.WordTrace tailWord_3333975 prefixEnd_3333975 1141287776715799027453223 := by
  unfold tailWord_3333975
  simp only [CollatzResearch.WordTrace]
  refine ⟨121600058096585447443051379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81066705397723631628700919 121600058096585447443051379)
  ·
    refine ⟨182400087144878171164577069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121600058096585447443051379 182400087144878171164577069)
    ·
      refine ⟨68400032679329314186716401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182400087144878171164577069 68400032679329314186716401)
      ·
        refine ⟨51300024509496985640037301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68400032679329314186716401 51300024509496985640037301)
        ·
          refine ⟨4809377297765342403753497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51300024509496985640037301 4809377297765342403753497)
          ·
            refine ⟨3607032973324006802815123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4809377297765342403753497 3607032973324006802815123)
            ·
              refine ⟨5410549459986010204222685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3607032973324006802815123 5410549459986010204222685)
              ·
                refine ⟨2028956047494753826583507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5410549459986010204222685 2028956047494753826583507)
                ·
                  refine ⟨3043434071242130739875261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2028956047494753826583507 3043434071242130739875261)
                  ·
                    refine ⟨1141287776715799027453223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3043434071242130739875261 1141287776715799027453223)
                    ·
                      rfl

theorem cell22_3333975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 3, 1, 3].length) (baseStart_3333975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3333975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3333975 prefixEnd_3333975 := by exact prefixLift 3333975
  have htrace : WordTrace (prefixWord ++ tailWord_3333975) baseStart_3333975 baseEnd_3333975 := by
    simpa [prefixWord, tailWord_3333975, baseEnd_3333975] using wordTrace_append hprefix tailTrace_3333975
  have hstable : (prefixWord ++ tailWord_3333975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3333975).length < 2 ^ (prefixWord ++ tailWord_3333975).sum := by decide
  have hdescent : baseEnd_3333975 < baseStart_3333975 := by decide
  rcases family_descends (prefixWord ++ tailWord_3333975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3334044 : List Nat := [2, 2, 3, 3, 1, 11]
def baseStart_3334044 : Nat := 118140960795 + 3334044 * 2 ^ 59
def prefixEnd_3334044 : Nat := 4983230072969 + 3 ^ 40 * 3334044 * 2
def baseEnd_3334044 : Nat := 14090264158344516635531

theorem tailTrace_3334044 : CollatzResearch.WordTrace tailWord_3334044 prefixEnd_3334044 14090264158344516635531 := by
  unfold tailWord_3334044
  simp only [CollatzResearch.WordTrace]
  refine ⟨60801287366667736113656593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81068383155556981484875457 60801287366667736113656593)
  ·
    refine ⟨45600965525000802085242445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60801287366667736113656593 45600965525000802085242445)
    ·
      refine ⟨17100362071875300781965917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45600965525000802085242445 17100362071875300781965917)
      ·
        refine ⟨6412635776953237793237219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17100362071875300781965917 6412635776953237793237219)
        ·
          refine ⟨9618953665429856689855829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6412635776953237793237219 9618953665429856689855829)
          ·
            refine ⟨14090264158344516635531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 9618953665429856689855829 14090264158344516635531)
            ·
              rfl

theorem cell22_3334044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 11].length) (baseStart_3334044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3334044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3334044 prefixEnd_3334044 := by exact prefixLift 3334044
  have htrace : WordTrace (prefixWord ++ tailWord_3334044) baseStart_3334044 baseEnd_3334044 := by
    simpa [prefixWord, tailWord_3334044, baseEnd_3334044] using wordTrace_append hprefix tailTrace_3334044
  have hstable : (prefixWord ++ tailWord_3334044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334044).length < 2 ^ (prefixWord ++ tailWord_3334044).sum := by decide
  have hdescent : baseEnd_3334044 < baseStart_3334044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3334104 : List Nat := [2, 1, 2, 2, 2, 2, 1, 1, 4, 5]
def baseStart_3334104 : Nat := 118140960795 + 3334104 * 2 ^ 59
def prefixEnd_3334104 : Nat := 4983230072969 + 3 ^ 40 * 3334104 * 2
def baseEnd_3334104 : Nat := 1141331936052085690977827

theorem tailTrace_3334104 : CollatzResearch.WordTrace tailWord_3334104 prefixEnd_3334104 1141331936052085690977827 := by
  unfold tailWord_3334104
  simp only [CollatzResearch.WordTrace]
  refine ⟨60802381556559051237248683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81069842075412068316331577 60802381556559051237248683)
  ·
    refine ⟨91203572334838576855873025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60802381556559051237248683 91203572334838576855873025)
    ·
      refine ⟨68402679251128932641904769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91203572334838576855873025 68402679251128932641904769)
      ·
        refine ⟨51302009438346699481428577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68402679251128932641904769 51302009438346699481428577)
        ·
          refine ⟨38476507078760024611071433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51302009438346699481428577 38476507078760024611071433)
          ·
            refine ⟨28857380309070018458303575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38476507078760024611071433 28857380309070018458303575)
            ·
              refine ⟨43286070463605027687455363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28857380309070018458303575 43286070463605027687455363)
              ·
                refine ⟨64929105695407541531183045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43286070463605027687455363 64929105695407541531183045)
                ·
                  refine ⟨12174207317888914037096821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64929105695407541531183045 12174207317888914037096821)
                  ·
                    refine ⟨1141331936052085690977827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12174207317888914037096821 1141331936052085690977827)
                    ·
                      rfl

theorem cell22_3334104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 4, 5].length) (baseStart_3334104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3334104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3334104 prefixEnd_3334104 := by exact prefixLift 3334104
  have htrace : WordTrace (prefixWord ++ tailWord_3334104) baseStart_3334104 baseEnd_3334104 := by
    simpa [prefixWord, tailWord_3334104, baseEnd_3334104] using wordTrace_append hprefix tailTrace_3334104
  have hstable : (prefixWord ++ tailWord_3334104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334104).length < 2 ^ (prefixWord ++ tailWord_3334104).sum := by decide
  have hdescent : baseEnd_3334104 < baseStart_3334104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
