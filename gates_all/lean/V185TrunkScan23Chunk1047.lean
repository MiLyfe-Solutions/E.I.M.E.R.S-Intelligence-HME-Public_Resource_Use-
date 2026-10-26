import V185TrunkScan23Chunk1046

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6198624 : List Nat := [2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 4]
def baseStart_6198624 : Nat := 118140960795 + 6198624 * 2 ^ 59
def prefixEnd_6198624 : Nat := 4983230072969 + 3 ^ 40 * 6198624 * 2
def baseEnd_6198624 : Nat := 3182873508495261088793053

theorem tailTrace_6198624 : CollatzResearch.WordTrace tailWord_6198624 prefixEnd_6198624 3182873508495261088793053 := by
  unfold tailWord_6198624
  simp only [CollatzResearch.WordTrace]
  refine ⟨113041195347725681770809463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150721593796967575694412617 113041195347725681770809463)
  ·
    refine ⟨169561793021588522656214195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113041195347725681770809463 169561793021588522656214195)
    ·
      refine ⟨254342689532382783984321293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169561793021588522656214195 254342689532382783984321293)
      ·
        refine ⟨95378508574643543994120485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 254342689532382783984321293 95378508574643543994120485)
        ·
          refine ⟨17883470357745664498897591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95378508574643543994120485 17883470357745664498897591)
          ·
            refine ⟨26825205536618496748346387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17883470357745664498897591 26825205536618496748346387)
            ·
              refine ⟨40237808304927745122519581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26825205536618496748346387 40237808304927745122519581)
              ·
                refine ⟨15089178114347904420944843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40237808304927745122519581 15089178114347904420944843)
                ·
                  refine ⟨22633767171521856631417265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15089178114347904420944843 22633767171521856631417265)
                  ·
                    refine ⟨16975325378641392473562949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22633767171521856631417265 16975325378641392473562949)
                    ·
                      refine ⟨3182873508495261088793053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16975325378641392473562949 3182873508495261088793053)
                      ·
                        rfl

theorem cell23_6198624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 4].length) (baseStart_6198624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6198624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6198624 prefixEnd_6198624 := by exact prefixLift 6198624
  have htrace : WordTrace (prefixWord ++ tailWord_6198624) baseStart_6198624 baseEnd_6198624 := by
    simpa [prefixWord, tailWord_6198624, baseEnd_6198624] using wordTrace_append hprefix tailTrace_6198624
  have hstable : (prefixWord ++ tailWord_6198624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6198624).length < 2 ^ (prefixWord ++ tailWord_6198624).sum := by decide
  have hdescent : baseEnd_6198624 < baseStart_6198624 := by decide
  rcases family_descends (prefixWord ++ tailWord_6198624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6198628 : List Nat := [2, 3, 1, 1, 3, 3, 1, 2, 3, 2, 2]
def baseStart_6198628 : Nat := 118140960795 + 6198628 * 2 ^ 59
def prefixEnd_6198628 : Nat := 4983230072969 + 3 ^ 40 * 6198628 * 2
def baseEnd_6198628 : Nat := 3182875562417879073143035

theorem tailTrace_6198628 : CollatzResearch.WordTrace tailWord_6198628 prefixEnd_6198628 3182875562417879073143035 := by
  unfold tailWord_6198628
  simp only [CollatzResearch.WordTrace]
  refine ⟨113041268293718436112382269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150721691058291248149843025 113041268293718436112382269)
  ·
    refine ⟨42390475610144413542143351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113041268293718436112382269 42390475610144413542143351)
    ·
      refine ⟨63585713415216620313215027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42390475610144413542143351 63585713415216620313215027)
      ·
        refine ⟨95378570122824930469822541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63585713415216620313215027 95378570122824930469822541)
        ·
          refine ⟨35766963796059348926183453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95378570122824930469822541 35766963796059348926183453)
          ·
            refine ⟨13412611423522255847318795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35766963796059348926183453 13412611423522255847318795)
            ·
              refine ⟨20118917135283383770978193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13412611423522255847318795 20118917135283383770978193)
              ·
                refine ⟨15089187851462537828233645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20118917135283383770978193 15089187851462537828233645)
                ·
                  refine ⟨5658445444298451685587617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15089187851462537828233645 5658445444298451685587617)
                  ·
                    refine ⟨4243834083223838764190713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5658445444298451685587617 4243834083223838764190713)
                    ·
                      refine ⟨3182875562417879073143035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4243834083223838764190713 3182875562417879073143035)
                      ·
                        rfl

theorem cell23_6198628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 2, 3, 2, 2].length) (baseStart_6198628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6198628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6198628 prefixEnd_6198628 := by exact prefixLift 6198628
  have htrace : WordTrace (prefixWord ++ tailWord_6198628) baseStart_6198628 baseEnd_6198628 := by
    simpa [prefixWord, tailWord_6198628, baseEnd_6198628] using wordTrace_append hprefix tailTrace_6198628
  have hstable : (prefixWord ++ tailWord_6198628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6198628).length < 2 ^ (prefixWord ++ tailWord_6198628).sum := by decide
  have hdescent : baseEnd_6198628 < baseStart_6198628 := by decide
  rcases family_descends (prefixWord ++ tailWord_6198628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6198645 : List Nat := [1, 3, 4, 1, 3, 2, 2, 1, 1, 1, 4]
def baseStart_6198645 : Nat := 118140960795 + 6198645 * 2 ^ 59
def prefixEnd_6198645 : Nat := 4983230072969 + 3 ^ 40 * 6198645 * 2
def baseEnd_6198645 : Nat := 3182884291589005506630457

theorem tailTrace_6198645 : CollatzResearch.WordTrace tailWord_6198645 prefixEnd_6198645 3182884291589005506630457 := by
  unfold tailWord_6198645
  simp only [CollatzResearch.WordTrace]
  refine ⟨226083156628375284128133389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150722104418916856085422259 226083156628375284128133389)
  ·
    refine ⟨84781183735640731548050021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226083156628375284128133389 84781183735640731548050021)
    ·
      refine ⟨15896471950432637165259379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84781183735640731548050021 15896471950432637165259379)
      ·
        refine ⟨23844707925648955747889069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15896471950432637165259379 23844707925648955747889069)
        ·
          refine ⟨8941765472118358405458401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23844707925648955747889069 8941765472118358405458401)
          ·
            refine ⟨6706324104088768804093801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8941765472118358405458401 6706324104088768804093801)
            ·
              refine ⟨5029743078066576603070351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6706324104088768804093801 5029743078066576603070351)
              ·
                refine ⟨7544614617099864904605527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5029743078066576603070351 7544614617099864904605527)
                ·
                  refine ⟨11316921925649797356908291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7544614617099864904605527 11316921925649797356908291)
                  ·
                    refine ⟨16975382888474696035362437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11316921925649797356908291 16975382888474696035362437)
                    ·
                      refine ⟨3182884291589005506630457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16975382888474696035362437 3182884291589005506630457)
                      ·
                        rfl

theorem cell23_6198645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 2, 1, 1, 1, 4].length) (baseStart_6198645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6198645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6198645 prefixEnd_6198645 := by exact prefixLift 6198645
  have htrace : WordTrace (prefixWord ++ tailWord_6198645) baseStart_6198645 baseEnd_6198645 := by
    simpa [prefixWord, tailWord_6198645, baseEnd_6198645] using wordTrace_append hprefix tailTrace_6198645
  have hstable : (prefixWord ++ tailWord_6198645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6198645).length < 2 ^ (prefixWord ++ tailWord_6198645).sum := by decide
  have hdescent : baseEnd_6198645 < baseStart_6198645 := by decide
  rcases family_descends (prefixWord ++ tailWord_6198645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6198688 : List Nat := [2, 1, 1, 4, 1, 2, 4, 2, 1, 3, 2]
def baseStart_6198688 : Nat := 118140960795 + 6198688 * 2 ^ 59
def prefixEnd_6198688 : Nat := 4983230072969 + 3 ^ 40 * 6198688 * 2
def baseEnd_6198688 : Nat := 3182906371257148838392759

theorem tailTrace_6198688 : CollatzResearch.WordTrace tailWord_6198688 prefixEnd_6198688 3182906371257148838392759 := by
  unfold tailWord_6198688
  simp only [CollatzResearch.WordTrace]
  refine ⟨113042362483609751235974359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150723149978146334981299145 113042362483609751235974359)
  ·
    refine ⟨169563543725414626853961539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113042362483609751235974359 169563543725414626853961539)
    ·
      refine ⟨254345315588121940280942309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169563543725414626853961539 254345315588121940280942309)
      ·
        refine ⟨47689746672772863802676683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 254345315588121940280942309 47689746672772863802676683)
        ·
          refine ⟨71534620009159295704015025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47689746672772863802676683 71534620009159295704015025)
          ·
            refine ⟨53650965006869471778011269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71534620009159295704015025 53650965006869471778011269)
            ·
              refine ⟨10059555938788025958377113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53650965006869471778011269 10059555938788025958377113)
              ·
                refine ⟨7544666954091019468782835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10059555938788025958377113 7544666954091019468782835)
                ·
                  refine ⟨11317000431136529203174253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7544666954091019468782835 11317000431136529203174253)
                  ·
                    refine ⟨4243875161676198451190345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11317000431136529203174253 4243875161676198451190345)
                    ·
                      refine ⟨3182906371257148838392759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4243875161676198451190345 3182906371257148838392759)
                      ·
                        rfl

theorem cell23_6198688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 2, 1, 3, 2].length) (baseStart_6198688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6198688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6198688 prefixEnd_6198688 := by exact prefixLift 6198688
  have htrace : WordTrace (prefixWord ++ tailWord_6198688) baseStart_6198688 baseEnd_6198688 := by
    simpa [prefixWord, tailWord_6198688, baseEnd_6198688] using wordTrace_append hprefix tailTrace_6198688
  have hstable : (prefixWord ++ tailWord_6198688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6198688).length < 2 ^ (prefixWord ++ tailWord_6198688).sum := by decide
  have hdescent : baseEnd_6198688 < baseStart_6198688 := by decide
  rcases family_descends (prefixWord ++ tailWord_6198688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6198696 : List Nat := [2, 1, 6, 1, 3, 1, 1, 3, 1, 2, 2]
def baseStart_6198696 : Nat := 118140960795 + 6198696 * 2 ^ 59
def prefixEnd_6198696 : Nat := 4983230072969 + 3 ^ 40 * 6198696 * 2
def baseEnd_6198696 : Nat := 3182910479102384807092723

theorem tailTrace_6198696 : CollatzResearch.WordTrace tailWord_6198696 prefixEnd_6198696 3182910479102384807092723 := by
  unfold tailWord_6198696
  simp only [CollatzResearch.WordTrace]
  refine ⟨113042508375595259919119971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150723344500793679892159961 113042508375595259919119971)
  ·
    refine ⟨169563762563392889878679957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113042508375595259919119971 169563762563392889878679957)
    ·
      refine ⟨7948301370159041713063123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 169563762563392889878679957 7948301370159041713063123)
      ·
        refine ⟨11922452055238562569594685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7948301370159041713063123 11922452055238562569594685)
        ·
          refine ⟨4470919520714460963598007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11922452055238562569594685 4470919520714460963598007)
          ·
            refine ⟨6706379281071691445397011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4470919520714460963598007 6706379281071691445397011)
            ·
              refine ⟨10059568921607537168095517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6706379281071691445397011 10059568921607537168095517)
              ·
                refine ⟨3772338345602826438035819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10059568921607537168095517 3772338345602826438035819)
                ·
                  refine ⟨5658507518404239657053729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3772338345602826438035819 5658507518404239657053729)
                  ·
                    refine ⟨4243880638803179742790297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5658507518404239657053729 4243880638803179742790297)
                    ·
                      refine ⟨3182910479102384807092723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4243880638803179742790297 3182910479102384807092723)
                      ·
                        rfl

theorem cell23_6198696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_6198696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6198696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6198696 prefixEnd_6198696 := by exact prefixLift 6198696
  have htrace : WordTrace (prefixWord ++ tailWord_6198696) baseStart_6198696 baseEnd_6198696 := by
    simpa [prefixWord, tailWord_6198696, baseEnd_6198696] using wordTrace_append hprefix tailTrace_6198696
  have hstable : (prefixWord ++ tailWord_6198696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6198696).length < 2 ^ (prefixWord ++ tailWord_6198696).sum := by decide
  have hdescent : baseEnd_6198696 < baseStart_6198696 := by decide
  rcases family_descends (prefixWord ++ tailWord_6198696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6198707 : List Nat := [1, 1, 1, 2, 3, 1, 1, 4, 9]
def baseStart_6198707 : Nat := 118140960795 + 6198707 * 2 ^ 59
def prefixEnd_6198707 : Nat := 4983230072969 + 3 ^ 40 * 6198707 * 2
def baseEnd_6198707 : Nat := 353657347487731584895019

theorem tailTrace_6198707 : CollatzResearch.WordTrace tailWord_6198707 prefixEnd_6198707 353657347487731584895019 := by
  unfold tailWord_6198707
  simp only [CollatzResearch.WordTrace]
  refine ⟨226085417954150668716890375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150723611969433779144593583 226085417954150668716890375)
  ·
    refine ⟨339128126931226003075335563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226085417954150668716890375 339128126931226003075335563)
    ·
      refine ⟨508692190396839004613003345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339128126931226003075335563 508692190396839004613003345)
      ·
        refine ⟨381519142797629253459752509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 508692190396839004613003345 381519142797629253459752509)
        ·
          refine ⟨143069678549110970047407191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 381519142797629253459752509 143069678549110970047407191)
          ·
            refine ⟨214604517823666455071110787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143069678549110970047407191 214604517823666455071110787)
            ·
              refine ⟨321906776735499682606666181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214604517823666455071110787 321906776735499682606666181)
              ·
                refine ⟨60357520637906190488749909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 321906776735499682606666181 60357520637906190488749909)
                ·
                  refine ⟨353657347487731584895019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 60357520637906190488749909 353657347487731584895019)
                  ·
                    rfl

theorem cell23_6198707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 9].length) (baseStart_6198707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6198707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6198707 prefixEnd_6198707 := by exact prefixLift 6198707
  have htrace : WordTrace (prefixWord ++ tailWord_6198707) baseStart_6198707 baseEnd_6198707 := by
    simpa [prefixWord, tailWord_6198707, baseEnd_6198707] using wordTrace_append hprefix tailTrace_6198707
  have hstable : (prefixWord ++ tailWord_6198707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6198707).length < 2 ^ (prefixWord ++ tailWord_6198707).sum := by decide
  have hdescent : baseEnd_6198707 < baseStart_6198707 := by decide
  rcases family_descends (prefixWord ++ tailWord_6198707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6198735 : List Nat := [1, 1, 2, 1, 1, 4, 6, 1, 2, 2, 2]
def baseStart_6198735 : Nat := 118140960795 + 6198735 * 2 ^ 59
def prefixEnd_6198735 : Nat := 4983230072969 + 3 ^ 40 * 6198735 * 2
def baseEnd_6198735 : Nat := 3182930504847910154505043

theorem tailTrace_6198735 : CollatzResearch.WordTrace tailWord_6198735 prefixEnd_6198735 3182930504847910154505043 := by
  unfold tailWord_6198735
  simp only [CollatzResearch.WordTrace]
  refine ⟨226086439198049229498909659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150724292798699486332606439 226086439198049229498909659)
  ·
    refine ⟨339129658797073844248364489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226086439198049229498909659 339129658797073844248364489)
    ·
      refine ⟨254347244097805383186273367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 339129658797073844248364489 254347244097805383186273367)
      ·
        refine ⟨381520866146708074779410051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254347244097805383186273367 381520866146708074779410051)
        ·
          refine ⟨572281299220062112169115077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 381520866146708074779410051 572281299220062112169115077)
          ·
            refine ⟨107302743603761646031709077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 572281299220062112169115077 107302743603761646031709077)
            ·
              refine ⟨5029816106426327157736363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 107302743603761646031709077 5029816106426327157736363)
              ·
                refine ⟨7544724159639490736604545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5029816106426327157736363 7544724159639490736604545)
                ·
                  refine ⟨5658543119729618052453409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7544724159639490736604545 5658543119729618052453409)
                  ·
                    refine ⟨4243907339797213539340057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5658543119729618052453409 4243907339797213539340057)
                    ·
                      refine ⟨3182930504847910154505043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4243907339797213539340057 3182930504847910154505043)
                      ·
                        rfl

theorem cell23_6198735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 6, 1, 2, 2, 2].length) (baseStart_6198735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6198735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6198735 prefixEnd_6198735 := by exact prefixLift 6198735
  have htrace : WordTrace (prefixWord ++ tailWord_6198735) baseStart_6198735 baseEnd_6198735 := by
    simpa [prefixWord, tailWord_6198735, baseEnd_6198735] using wordTrace_append hprefix tailTrace_6198735
  have hstable : (prefixWord ++ tailWord_6198735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6198735).length < 2 ^ (prefixWord ++ tailWord_6198735).sum := by decide
  have hdescent : baseEnd_6198735 < baseStart_6198735 := by decide
  rcases family_descends (prefixWord ++ tailWord_6198735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6198801 : List Nat := [1, 2, 2, 1, 1, 2, 5, 2, 3, 4]
def baseStart_6198801 : Nat := 118140960795 + 6198801 * 2 ^ 59
def prefixEnd_6198801 : Nat := 4983230072969 + 3 ^ 40 * 6198801 * 2
def baseEnd_6198801 : Nat := 1060988131523702298759913

theorem tailTrace_6198801 : CollatzResearch.WordTrace tailWord_6198801 prefixEnd_6198801 1060988131523702298759913 := by
  unfold tailWord_6198801
  simp only [CollatzResearch.WordTrace]
  refine ⟨226088846415810122770812257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150725897610540081847208171 226088846415810122770812257)
  ·
    refine ⟨169566634811857592078109193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226088846415810122770812257 169566634811857592078109193)
    ·
      refine ⟨127174976108893194058581895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169566634811857592078109193 127174976108893194058581895)
      ·
        refine ⟨190762464163339791087872843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127174976108893194058581895 190762464163339791087872843)
        ·
          refine ⟨286143696245009686631809265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190762464163339791087872843 286143696245009686631809265)
          ·
            refine ⟨214607772183757264973856949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 286143696245009686631809265 214607772183757264973856949)
            ·
              refine ⟨20119478642227243591299089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 214607772183757264973856949 20119478642227243591299089)
              ·
                refine ⟨15089608981670432693474317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20119478642227243591299089 15089608981670432693474317)
                ·
                  refine ⟨5658603368126412260052869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15089608981670432693474317 5658603368126412260052869)
                  ·
                    refine ⟨1060988131523702298759913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5658603368126412260052869 1060988131523702298759913)
                    ·
                      rfl

theorem cell23_6198801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 2, 3, 4].length) (baseStart_6198801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6198801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6198801 prefixEnd_6198801 := by exact prefixLift 6198801
  have htrace : WordTrace (prefixWord ++ tailWord_6198801) baseStart_6198801 baseEnd_6198801 := by
    simpa [prefixWord, tailWord_6198801, baseEnd_6198801] using wordTrace_append hprefix tailTrace_6198801
  have hstable : (prefixWord ++ tailWord_6198801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6198801).length < 2 ^ (prefixWord ++ tailWord_6198801).sum := by decide
  have hdescent : baseEnd_6198801 < baseStart_6198801 := by decide
  rcases family_descends (prefixWord ++ tailWord_6198801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6198858 : List Nat := [3, 1, 2, 1, 1, 3, 1, 4, 3, 1, 3]
def baseStart_6198858 : Nat := 118140960795 + 6198858 * 2 ^ 59
def prefixEnd_6198858 : Nat := 4983230072969 + 3 ^ 40 * 6198858 * 2
def baseEnd_6198858 : Nat := 3182993662968413173266977

theorem tailTrace_6198858 : CollatzResearch.WordTrace tailWord_6198858 prefixEnd_6198858 3182993662968413173266977 := by
  unfold tailWord_6198858
  simp only [CollatzResearch.WordTrace]
  refine ⟨56522731344150905376409307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150727283584402414337091485 56522731344150905376409307)
  ·
    refine ⟨84784097016226358064613961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56522731344150905376409307 84784097016226358064613961)
    ·
      refine ⟨63588072762169768548460471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84784097016226358064613961 63588072762169768548460471)
      ·
        refine ⟨95382109143254652822690707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63588072762169768548460471 95382109143254652822690707)
        ·
          refine ⟨143073163714881979234036061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95382109143254652822690707 143073163714881979234036061)
          ·
            refine ⟨53652436393080742212763523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143073163714881979234036061 53652436393080742212763523)
            ·
              refine ⟨80478654589621113319145285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53652436393080742212763523 80478654589621113319145285)
              ·
                refine ⟨15089747735553958747339741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80478654589621113319145285 15089747735553958747339741)
                ·
                  refine ⟨5658655400832734530252403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15089747735553958747339741 5658655400832734530252403)
                  ·
                    refine ⟨8487983101249101795378605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5658655400832734530252403 8487983101249101795378605)
                    ·
                      refine ⟨3182993662968413173266977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8487983101249101795378605 3182993662968413173266977)
                      ·
                        rfl

theorem cell23_6198858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 4, 3, 1, 3].length) (baseStart_6198858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6198858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6198858 prefixEnd_6198858 := by exact prefixLift 6198858
  have htrace : WordTrace (prefixWord ++ tailWord_6198858) baseStart_6198858 baseEnd_6198858 := by
    simpa [prefixWord, tailWord_6198858, baseEnd_6198858] using wordTrace_append hprefix tailTrace_6198858
  have hstable : (prefixWord ++ tailWord_6198858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6198858).length < 2 ^ (prefixWord ++ tailWord_6198858).sum := by decide
  have hdescent : baseEnd_6198858 < baseStart_6198858 := by decide
  rcases family_descends (prefixWord ++ tailWord_6198858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6198868 : List Nat := [2, 4, 1, 1, 1, 2, 1, 3, 1, 5, 2]
def baseStart_6198868 : Nat := 118140960795 + 6198868 * 2 ^ 59
def prefixEnd_6198868 : Nat := 4983230072969 + 3 ^ 40 * 6198868 * 2
def baseEnd_6198868 : Nat := 3182998797774958134141931

theorem tailTrace_6198868 : CollatzResearch.WordTrace tailWord_6198868 prefixEnd_6198868 3182998797774958134141931 := by
  unfold tailWord_6198868
  simp only [CollatzResearch.WordTrace]
  refine ⟨113045645053283696606750629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150727526737711595475667505 113045645053283696606750629)
  ·
    refine ⟨21196058447490693113765743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113045645053283696606750629 21196058447490693113765743)
    ·
      refine ⟨31794087671236039670648615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21196058447490693113765743 31794087671236039670648615)
      ·
        refine ⟨47691131506854059505972923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31794087671236039670648615 47691131506854059505972923)
        ·
          refine ⟨71536697260281089258959385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47691131506854059505972923 71536697260281089258959385)
          ·
            refine ⟨53652522945210816944219539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71536697260281089258959385 53652522945210816944219539)
            ·
              refine ⟨80478784417816225416329309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53652522945210816944219539 80478784417816225416329309)
              ·
                refine ⟨30179544156681084531123491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80478784417816225416329309 30179544156681084531123491)
                ·
                  refine ⟨45269316235021626796685237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30179544156681084531123491 45269316235021626796685237)
                  ·
                    refine ⟨4243998397033277512189241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45269316235021626796685237 4243998397033277512189241)
                    ·
                      refine ⟨3182998797774958134141931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4243998397033277512189241 3182998797774958134141931)
                      ·
                        rfl

theorem cell23_6198868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 3, 1, 5, 2].length) (baseStart_6198868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6198868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6198868 prefixEnd_6198868 := by exact prefixLift 6198868
  have htrace : WordTrace (prefixWord ++ tailWord_6198868) baseStart_6198868 baseEnd_6198868 := by
    simpa [prefixWord, tailWord_6198868, baseEnd_6198868] using wordTrace_append hprefix tailTrace_6198868
  have hstable : (prefixWord ++ tailWord_6198868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6198868).length < 2 ^ (prefixWord ++ tailWord_6198868).sum := by decide
  have hdescent : baseEnd_6198868 < baseStart_6198868 := by decide
  rcases family_descends (prefixWord ++ tailWord_6198868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6198885 : List Nat := [1, 3, 1, 3, 3, 2, 1, 2, 2, 3, 2]
def baseStart_6198885 : Nat := 118140960795 + 6198885 * 2 ^ 59
def prefixEnd_6198885 : Nat := 4983230072969 + 3 ^ 40 * 6198885 * 2
def baseEnd_6198885 : Nat := 3183007526946084567629353

theorem tailTrace_6198885 : CollatzResearch.WordTrace tailWord_6198885 prefixEnd_6198885 3183007526946084567629353 := by
  unfold tailWord_6198885
  simp only [CollatzResearch.WordTrace]
  refine ⟨226091910147505805116870109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150727940098337203411246739 226091910147505805116870109)
  ·
    refine ⟨84784466305314676918826291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226091910147505805116870109 84784466305314676918826291)
    ·
      refine ⟨127176699457972015378239437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84784466305314676918826291 127176699457972015378239437)
      ·
        refine ⟨47691262296739505766839789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127176699457972015378239437 47691262296739505766839789)
        ·
          refine ⟨17884223361277314662564921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47691262296739505766839789 17884223361277314662564921)
          ·
            refine ⟨13413167520957985996923691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17884223361277314662564921 13413167520957985996923691)
            ·
              refine ⟨20119751281436978995385537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13413167520957985996923691 20119751281436978995385537)
              ·
                refine ⟨15089813461077734246539153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20119751281436978995385537 15089813461077734246539153)
                ·
                  refine ⟨11317360095808300684904365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15089813461077734246539153 11317360095808300684904365)
                  ·
                    refine ⟨4244010035928112756839137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11317360095808300684904365 4244010035928112756839137)
                    ·
                      refine ⟨3183007526946084567629353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4244010035928112756839137 3183007526946084567629353)
                      ·
                        rfl

theorem cell23_6198885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 2, 2, 3, 2].length) (baseStart_6198885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6198885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6198885 prefixEnd_6198885 := by exact prefixLift 6198885
  have htrace : WordTrace (prefixWord ++ tailWord_6198885) baseStart_6198885 baseEnd_6198885 := by
    simpa [prefixWord, tailWord_6198885, baseEnd_6198885] using wordTrace_append hprefix tailTrace_6198885
  have hstable : (prefixWord ++ tailWord_6198885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6198885).length < 2 ^ (prefixWord ++ tailWord_6198885).sum := by decide
  have hdescent : baseEnd_6198885 < baseStart_6198885 := by decide
  rcases family_descends (prefixWord ++ tailWord_6198885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6198942 : List Nat := [4, 3, 1, 1, 1, 3, 2, 2, 2, 4]
def baseStart_6198942 : Nat := 118140960795 + 6198942 * 2 ^ 59
def prefixEnd_6198942 : Nat := 4983230072969 + 3 ^ 40 * 6198942 * 2
def baseEnd_6198942 : Nat := 1061012265114463614872197

theorem tailTrace_6198942 : CollatzResearch.WordTrace tailWord_6198942 prefixEnd_6198942 1061012265114463614872197 := by
  unfold tailWord_6198942
  simp only [CollatzResearch.WordTrace]
  refine ⟨28261748638537412981461885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150729326072199535901130053 28261748638537412981461885)
  ·
    refine ⟨10598155739451529868048207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28261748638537412981461885 10598155739451529868048207)
    ·
      refine ⟨15897233609177294802072311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10598155739451529868048207 15897233609177294802072311)
      ·
        refine ⟨23845850413765942203108467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15897233609177294802072311 23845850413765942203108467)
        ·
          refine ⟨35768775620648913304662701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23845850413765942203108467 35768775620648913304662701)
          ·
            refine ⟨13413290857743342489248513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35768775620648913304662701 13413290857743342489248513)
            ·
              refine ⟨10059968143307506866936385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13413290857743342489248513 10059968143307506866936385)
              ·
                refine ⟨7544976107480630150202289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10059968143307506866936385 7544976107480630150202289)
                ·
                  refine ⟨5658732080610472612651717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7544976107480630150202289 5658732080610472612651717)
                  ·
                    refine ⟨1061012265114463614872197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5658732080610472612651717 1061012265114463614872197)
                    ·
                      rfl

theorem cell23_6198942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_6198942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6198942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6198942 prefixEnd_6198942 := by exact prefixLift 6198942
  have htrace : WordTrace (prefixWord ++ tailWord_6198942) baseStart_6198942 baseEnd_6198942 := by
    simpa [prefixWord, tailWord_6198942, baseEnd_6198942] using wordTrace_append hprefix tailTrace_6198942
  have hstable : (prefixWord ++ tailWord_6198942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6198942).length < 2 ^ (prefixWord ++ tailWord_6198942).sum := by decide
  have hdescent : baseEnd_6198942 < baseStart_6198942 := by decide
  rcases family_descends (prefixWord ++ tailWord_6198942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6198943 : List Nat := [1, 1, 2, 7, 2, 1, 2, 2, 1, 1, 3]
def baseStart_6198943 : Nat := 118140960795 + 6198943 * 2 ^ 59
def prefixEnd_6198943 : Nat := 4983230072969 + 3 ^ 40 * 6198943 * 2
def baseEnd_6198943 : Nat := 3183037308824045340704087

theorem tailTrace_6198943 : CollatzResearch.WordTrace tailWord_6198943 prefixEnd_6198943 3183037308824045340704087 := by
  unfold tailWord_6198943
  simp only [CollatzResearch.WordTrace]
  refine ⟨226094025581295681022481483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150729350387530454014987655 226094025581295681022481483)
  ·
    refine ⟨339141038371943521533722225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226094025581295681022481483 339141038371943521533722225)
    ·
      refine ⟨254355778778957641150291669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 339141038371943521533722225 254355778778957641150291669)
      ·
        refine ⟨5961463565131819714459961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 254355778778957641150291669 5961463565131819714459961)
        ·
          refine ⟨4471097673848864785844971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5961463565131819714459961 4471097673848864785844971)
          ·
            refine ⟨6706646510773297178767457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4471097673848864785844971 6706646510773297178767457)
            ·
              refine ⟨5029984883079972884075593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6706646510773297178767457 5029984883079972884075593)
              ·
                refine ⟨3772488662309979663056695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5029984883079972884075593 3772488662309979663056695)
                ·
                  refine ⟨5658732993464969494585043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3772488662309979663056695 5658732993464969494585043)
                  ·
                    refine ⟨8488099490197454241877565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5658732993464969494585043 8488099490197454241877565)
                    ·
                      refine ⟨3183037308824045340704087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8488099490197454241877565 3183037308824045340704087)
                      ·
                        rfl

theorem cell23_6198943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_6198943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6198943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6198943 prefixEnd_6198943 := by exact prefixLift 6198943
  have htrace : WordTrace (prefixWord ++ tailWord_6198943) baseStart_6198943 baseEnd_6198943 := by
    simpa [prefixWord, tailWord_6198943, baseEnd_6198943] using wordTrace_append hprefix tailTrace_6198943
  have hstable : (prefixWord ++ tailWord_6198943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6198943).length < 2 ^ (prefixWord ++ tailWord_6198943).sum := by decide
  have hdescent : baseEnd_6198943 < baseStart_6198943 := by decide
  rcases family_descends (prefixWord ++ tailWord_6198943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6198949 : List Nat := [1, 3, 1, 2, 1, 2, 6, 2, 1, 2, 2]
def baseStart_6198949 : Nat := 118140960795 + 6198949 * 2 ^ 59
def prefixEnd_6198949 : Nat := 4983230072969 + 3 ^ 40 * 6198949 * 2
def baseEnd_6198949 : Nat := 3183040389707972317229059

theorem tailTrace_6198949 : CollatzResearch.WordTrace tailWord_6198949 prefixEnd_6198949 3183040389707972317229059 := by
  unfold tailWord_6198949
  simp only [CollatzResearch.WordTrace]
  refine ⟨226094244419273944047199901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150729496279515962698133267 226094244419273944047199901)
  ·
    refine ⟨84785341657227729017699963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226094244419273944047199901 84785341657227729017699963)
    ·
      refine ⟨127178012485841593526549945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84785341657227729017699963 127178012485841593526549945)
      ·
        refine ⟨95383509364381195144912459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127178012485841593526549945 95383509364381195144912459)
        ·
          refine ⟨143075264046571792717368689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95383509364381195144912459 143075264046571792717368689)
          ·
            refine ⟨107306448034928844538026517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143075264046571792717368689 107306448034928844538026517)
            ·
              refine ⟨5029989751637289587719993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 107306448034928844538026517 5029989751637289587719993)
              ·
                refine ⟨3772492313727967190789995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5029989751637289587719993 3772492313727967190789995)
                ·
                  refine ⟨5658738470591950786184993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3772492313727967190789995 5658738470591950786184993)
                  ·
                    refine ⟨4244053852943963089638745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5658738470591950786184993 4244053852943963089638745)
                    ·
                      refine ⟨3183040389707972317229059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4244053852943963089638745 3183040389707972317229059)
                      ·
                        rfl

theorem cell23_6198949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 6, 2, 1, 2, 2].length) (baseStart_6198949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6198949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6198949 prefixEnd_6198949 := by exact prefixLift 6198949
  have htrace : WordTrace (prefixWord ++ tailWord_6198949) baseStart_6198949 baseEnd_6198949 := by
    simpa [prefixWord, tailWord_6198949, baseEnd_6198949] using wordTrace_append hprefix tailTrace_6198949
  have hstable : (prefixWord ++ tailWord_6198949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6198949).length < 2 ^ (prefixWord ++ tailWord_6198949).sum := by decide
  have hdescent : baseEnd_6198949 < baseStart_6198949 := by decide
  rcases family_descends (prefixWord ++ tailWord_6198949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6198975 : List Nat := [1, 1, 2, 2, 2, 3, 2, 4, 1, 3, 2]
def baseStart_6198975 : Nat := 118140960795 + 6198975 * 2 ^ 59
def prefixEnd_6198975 : Nat := 4983230072969 + 3 ^ 40 * 6198975 * 2
def baseEnd_6198975 : Nat := 3183053740204989215503939

theorem tailTrace_6198975 : CollatzResearch.WordTrace tailWord_6198975 prefixEnd_6198975 3183053740204989215503939 := by
  unfold tailWord_6198975
  simp only [CollatzResearch.WordTrace]
  refine ⟨226095192717179750487646379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150730128478119833658430919 226095192717179750487646379)
  ·
    refine ⟨339142789075769625731469569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226095192717179750487646379 339142789075769625731469569)
    ·
      refine ⟨254357091806827219298602177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 339142789075769625731469569 254357091806827219298602177)
      ·
        refine ⟨190767818855120414473951633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 254357091806827219298602177 190767818855120414473951633)
        ·
          refine ⟨143075864141340310855463725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190767818855120414473951633 143075864141340310855463725)
          ·
            refine ⟨53653449053002616570798897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143075864141340310855463725 53653449053002616570798897)
            ·
              refine ⟨40240086789751962428099173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53653449053002616570798897 40240086789751962428099173)
              ·
                refine ⟨7545016273078492955268595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40240086789751962428099173 7545016273078492955268595)
                ·
                  refine ⟨11317524409617739432902893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7545016273078492955268595 11317524409617739432902893)
                  ·
                    refine ⟨4244071653606652287338585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11317524409617739432902893 4244071653606652287338585)
                    ·
                      refine ⟨3183053740204989215503939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4244071653606652287338585 3183053740204989215503939)
                      ·
                        rfl

theorem cell23_6198975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 4, 1, 3, 2].length) (baseStart_6198975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6198975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6198975 prefixEnd_6198975 := by exact prefixLift 6198975
  have htrace : WordTrace (prefixWord ++ tailWord_6198975) baseStart_6198975 baseEnd_6198975 := by
    simpa [prefixWord, tailWord_6198975, baseEnd_6198975] using wordTrace_append hprefix tailTrace_6198975
  have hstable : (prefixWord ++ tailWord_6198975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6198975).length < 2 ^ (prefixWord ++ tailWord_6198975).sum := by decide
  have hdescent : baseEnd_6198975 < baseStart_6198975 := by decide
  rcases family_descends (prefixWord ++ tailWord_6198975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6198991 : List Nat := [1, 1, 2, 1, 1, 3, 1, 5, 2, 1, 5]
def baseStart_6198991 : Nat := 118140960795 + 6198991 * 2 ^ 59
def prefixEnd_6198991 : Nat := 4983230072969 + 3 ^ 40 * 6198991 * 2
def baseEnd_6198991 : Nat := 3183061955895461152903865

theorem tailTrace_6198991 : CollatzResearch.WordTrace tailWord_6198991 prefixEnd_6198991 3183061955895461152903865 := by
  unfold tailWord_6198991
  simp only [CollatzResearch.WordTrace]
  refine ⟨226095776285121785220228827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150730517523414523480152551 226095776285121785220228827)
  ·
    refine ⟨339143664427682677830343241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226095776285121785220228827 339143664427682677830343241)
    ·
      refine ⟨254357748320762008372757431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 339143664427682677830343241 254357748320762008372757431)
      ·
        refine ⟨381536622481143012559136147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254357748320762008372757431 381536622481143012559136147)
        ·
          refine ⟨572304933721714518838704221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 381536622481143012559136147 572304933721714518838704221)
          ·
            refine ⟨214614350145642944564514083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 572304933721714518838704221 214614350145642944564514083)
            ·
              refine ⟨321921525218464416846771125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214614350145642944564514083 321921525218464416846771125)
              ·
                refine ⟨30180142989231039079384793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 321921525218464416846771125 30180142989231039079384793)
                ·
                  refine ⟨22635107241923279309538595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30180142989231039079384793 22635107241923279309538595)
                  ·
                    refine ⟨33952660862884918964307893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22635107241923279309538595 33952660862884918964307893)
                    ·
                      refine ⟨3183061955895461152903865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33952660862884918964307893 3183061955895461152903865)
                      ·
                        rfl

theorem cell23_6198991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 5, 2, 1, 5].length) (baseStart_6198991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6198991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6198991 prefixEnd_6198991 := by exact prefixLift 6198991
  have htrace : WordTrace (prefixWord ++ tailWord_6198991) baseStart_6198991 baseEnd_6198991 := by
    simpa [prefixWord, tailWord_6198991, baseEnd_6198991] using wordTrace_append hprefix tailTrace_6198991
  have hstable : (prefixWord ++ tailWord_6198991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6198991).length < 2 ^ (prefixWord ++ tailWord_6198991).sum := by decide
  have hdescent : baseEnd_6198991 < baseStart_6198991 := by decide
  rcases family_descends (prefixWord ++ tailWord_6198991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6199018 : List Nat := [3, 1, 3, 1, 1, 1, 4, 1, 2, 2, 4]
def baseStart_6199018 : Nat := 118140960795 + 6199018 * 2 ^ 59
def prefixEnd_6199018 : Nat := 4983230072969 + 3 ^ 40 * 6199018 * 2
def baseEnd_6199018 : Nat := 3183075819873132547266241

theorem tailTrace_6199018 : CollatzResearch.WordTrace tailWord_6199018 prefixEnd_6199018 3183075819873132547266241 := by
  unfold tailWord_6199018
  simp only [CollatzResearch.WordTrace]
  refine ⟨56524190264005992207865427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150731174037349312554307805 56524190264005992207865427)
  ·
    refine ⟨84786285396008988311798141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56524190264005992207865427 84786285396008988311798141)
    ·
      refine ⟨31794857023503370616924303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84786285396008988311798141 31794857023503370616924303)
      ·
        refine ⟨47692285535255055925386455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31794857023503370616924303 47692285535255055925386455)
        ·
          refine ⟨71538428302882583888079683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47692285535255055925386455 71538428302882583888079683)
          ·
            refine ⟨107307642454323875832119525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71538428302882583888079683 107307642454323875832119525)
            ·
              refine ⟨20120182960185726718522411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 107307642454323875832119525 20120182960185726718522411)
              ·
                refine ⟨30180274440278590077783617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20120182960185726718522411 30180274440278590077783617)
                ·
                  refine ⟨22635205830208942558337713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30180274440278590077783617 22635205830208942558337713)
                  ·
                    refine ⟨16976404372656706918753285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22635205830208942558337713 16976404372656706918753285)
                    ·
                      refine ⟨3183075819873132547266241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16976404372656706918753285 3183075819873132547266241)
                      ·
                        rfl

theorem cell23_6199018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_6199018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6199018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6199018 prefixEnd_6199018 := by exact prefixLift 6199018
  have htrace : WordTrace (prefixWord ++ tailWord_6199018) baseStart_6199018 baseEnd_6199018 := by
    simpa [prefixWord, tailWord_6199018, baseEnd_6199018] using wordTrace_append hprefix tailTrace_6199018
  have hstable : (prefixWord ++ tailWord_6199018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6199018).length < 2 ^ (prefixWord ++ tailWord_6199018).sum := by decide
  have hdescent : baseEnd_6199018 < baseStart_6199018 := by decide
  rcases family_descends (prefixWord ++ tailWord_6199018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6199068 : List Nat := [2, 2, 3, 1, 1, 2, 3, 1, 1, 2, 5]
def baseStart_6199068 : Nat := 118140960795 + 6199068 * 2 ^ 59
def prefixEnd_6199068 : Nat := 4983230072969 + 3 ^ 40 * 6199068 * 2
def baseEnd_6199068 : Nat := 3183101493905857351641011

theorem tailTrace_6199068 : CollatzResearch.WordTrace tailWord_6199068 prefixEnd_6199068 3183101493905857351641011 := by
  unfold tailWord_6199068
  simp only [CollatzResearch.WordTrace]
  refine ⟨113049292352921413685390929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150732389803895218247187905 113049292352921413685390929)
  ·
    refine ⟨84786969264691060264043197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113049292352921413685390929 84786969264691060264043197)
    ·
      refine ⟨31795113474259147599016199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84786969264691060264043197 31795113474259147599016199)
      ·
        refine ⟨47692670211388721398524299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31795113474259147599016199 47692670211388721398524299)
        ·
          refine ⟨71539005317083082097786449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47692670211388721398524299 71539005317083082097786449)
          ·
            refine ⟨53654253987812311573339837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71539005317083082097786449 53654253987812311573339837)
            ·
              refine ⟨20120345245429616840002439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53654253987812311573339837 20120345245429616840002439)
              ·
                refine ⟨30180517868144425260003659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20120345245429616840002439 30180517868144425260003659)
                ·
                  refine ⟨45270776802216637890005489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30180517868144425260003659 45270776802216637890005489)
                  ·
                    refine ⟨33953082601662478417504117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45270776802216637890005489 33953082601662478417504117)
                    ·
                      refine ⟨3183101493905857351641011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33953082601662478417504117 3183101493905857351641011)
                      ·
                        rfl

theorem cell23_6199068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_6199068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6199068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6199068 prefixEnd_6199068 := by exact prefixLift 6199068
  have htrace : WordTrace (prefixWord ++ tailWord_6199068) baseStart_6199068 baseEnd_6199068 := by
    simpa [prefixWord, tailWord_6199068, baseEnd_6199068] using wordTrace_append hprefix tailTrace_6199068
  have hstable : (prefixWord ++ tailWord_6199068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6199068).length < 2 ^ (prefixWord ++ tailWord_6199068).sum := by decide
  have hdescent : baseEnd_6199068 < baseStart_6199068 := by decide
  rcases family_descends (prefixWord ++ tailWord_6199068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6199092 : List Nat := [2, 5, 1, 1, 2, 2, 2, 1, 2, 5]
def baseStart_6199092 : Nat := 118140960795 + 6199092 * 2 ^ 59
def prefixEnd_6199092 : Nat := 4983230072969 + 3 ^ 40 * 6199092 * 2
def baseEnd_6199092 : Nat := 1061037939147188419246967

theorem tailTrace_6199092 : CollatzResearch.WordTrace tailWord_6199092 prefixEnd_6199092 1061037939147188419246967 := by
  unfold tailWord_6199092
  simp only [CollatzResearch.WordTrace]
  refine ⟨113049730028877939734827765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150732973371837252979770353 113049730028877939734827765)
  ·
    refine ⟨10598412190207306850140103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 113049730028877939734827765 10598412190207306850140103)
    ·
      refine ⟨15897618285310960275210155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10598412190207306850140103 15897618285310960275210155)
      ·
        refine ⟨23846427427966440412815233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15897618285310960275210155 23846427427966440412815233)
        ·
          refine ⟨17884820570974830309611425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23846427427966440412815233 17884820570974830309611425)
          ·
            refine ⟨13413615428231122732208569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17884820570974830309611425 13413615428231122732208569)
            ·
              refine ⟨10060211571173342049156427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13413615428231122732208569 10060211571173342049156427)
              ·
                refine ⟨15090317356760013073734641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10060211571173342049156427 15090317356760013073734641)
                ·
                  refine ⟨11317738017570009805300981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15090317356760013073734641 11317738017570009805300981)
                  ·
                    refine ⟨1061037939147188419246967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11317738017570009805300981 1061037939147188419246967)
                    ·
                      rfl

theorem cell23_6199092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_6199092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6199092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6199092 prefixEnd_6199092 := by exact prefixLift 6199092
  have htrace : WordTrace (prefixWord ++ tailWord_6199092) baseStart_6199092 baseEnd_6199092 := by
    simpa [prefixWord, tailWord_6199092, baseEnd_6199092] using wordTrace_append hprefix tailTrace_6199092
  have hstable : (prefixWord ++ tailWord_6199092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6199092).length < 2 ^ (prefixWord ++ tailWord_6199092).sum := by decide
  have hdescent : baseEnd_6199092 < baseStart_6199092 := by decide
  rcases family_descends (prefixWord ++ tailWord_6199092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6199128 : List Nat := [2, 1, 2, 2, 1, 1, 1, 1, 4, 5, 3]
def baseStart_6199128 : Nat := 118140960795 + 6199128 * 2 ^ 59
def prefixEnd_6199128 : Nat := 4983230072969 + 3 ^ 40 * 6199128 * 2
def baseEnd_6199128 : Nat := 3183132302745127116890735

theorem tailTrace_6199128 : CollatzResearch.WordTrace tailWord_6199128 prefixEnd_6199128 3183132302745127116890735 := by
  unfold tailWord_6199128
  simp only [CollatzResearch.WordTrace]
  refine ⟨113050386542812728808983019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150733848723750305078644025 113050386542812728808983019)
  ·
    refine ⟨169575579814219093213474529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113050386542812728808983019 169575579814219093213474529)
    ·
      refine ⟨127181684860664319910105897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169575579814219093213474529 127181684860664319910105897)
      ·
        refine ⟨95386263645498239932579423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127181684860664319910105897 95386263645498239932579423)
        ·
          refine ⟨143079395468247359898869135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95386263645498239932579423 143079395468247359898869135)
          ·
            refine ⟨214619093202371039848303703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143079395468247359898869135 214619093202371039848303703)
            ·
              refine ⟨321928639803556559772455555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214619093202371039848303703 321928639803556559772455555)
              ·
                refine ⟨482892959705334839658683333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 321928639803556559772455555 482892959705334839658683333)
                ·
                  refine ⟨90542429944750282436003125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 482892959705334839658683333 90542429944750282436003125)
                  ·
                    refine ⟨8488352807320338978375293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 90542429944750282436003125 8488352807320338978375293)
                    ·
                      refine ⟨3183132302745127116890735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8488352807320338978375293 3183132302745127116890735)
                      ·
                        rfl

theorem cell23_6199128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 4, 5, 3].length) (baseStart_6199128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6199128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6199128 prefixEnd_6199128 := by exact prefixLift 6199128
  have htrace : WordTrace (prefixWord ++ tailWord_6199128) baseStart_6199128 baseEnd_6199128 := by
    simpa [prefixWord, tailWord_6199128, baseEnd_6199128] using wordTrace_append hprefix tailTrace_6199128
  have hstable : (prefixWord ++ tailWord_6199128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6199128).length < 2 ^ (prefixWord ++ tailWord_6199128).sum := by decide
  have hdescent : baseEnd_6199128 < baseStart_6199128 := by decide
  rcases family_descends (prefixWord ++ tailWord_6199128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6199146 : List Nat := [3, 1, 3, 4, 2, 1, 1, 1, 2, 1, 4]
def baseStart_6199146 : Nat := 118140960795 + 6199146 * 2 ^ 59
def prefixEnd_6199146 : Nat := 4983230072969 + 3 ^ 40 * 6199146 * 2
def baseEnd_6199146 : Nat := 3183141545396908046465653

theorem tailTrace_6199146 : CollatzResearch.WordTrace tailWord_6199146 prefixEnd_6199146 3183141545396908046465653 := by
  unfold tailWord_6199146
  simp only [CollatzResearch.WordTrace]
  refine ⟨56525357399890061673030323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150734286399706831128080861 56525357399890061673030323)
  ·
    refine ⟨84788036099835092509545485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56525357399890061673030323 84788036099835092509545485)
    ·
      refine ⟨31795513537438159691079557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84788036099835092509545485 31795513537438159691079557)
      ·
        refine ⟨5961658788269654942077417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31795513537438159691079557 5961658788269654942077417)
        ·
          refine ⟨4471244091202241206558063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5961658788269654942077417 4471244091202241206558063)
          ·
            refine ⟨6706866136803361809837095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4471244091202241206558063 6706866136803361809837095)
            ·
              refine ⟨10060299205205042714755643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6706866136803361809837095 10060299205205042714755643)
              ·
                refine ⟨15090448807807564072133465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10060299205205042714755643 15090448807807564072133465)
                ·
                  refine ⟨11317836605855673054100099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15090448807807564072133465 11317836605855673054100099)
                  ·
                    refine ⟨16976754908783509581150149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11317836605855673054100099 16976754908783509581150149)
                    ·
                      refine ⟨3183141545396908046465653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16976754908783509581150149 3183141545396908046465653)
                      ·
                        rfl

theorem cell23_6199146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_6199146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6199146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6199146 prefixEnd_6199146 := by exact prefixLift 6199146
  have htrace : WordTrace (prefixWord ++ tailWord_6199146) baseStart_6199146 baseEnd_6199146 := by
    simpa [prefixWord, tailWord_6199146, baseEnd_6199146] using wordTrace_append hprefix tailTrace_6199146
  have hstable : (prefixWord ++ tailWord_6199146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6199146).length < 2 ^ (prefixWord ++ tailWord_6199146).sum := by decide
  have hdescent : baseEnd_6199146 < baseStart_6199146 := by decide
  rcases family_descends (prefixWord ++ tailWord_6199146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6199169 : List Nat := [1, 2, 4, 4, 1, 2, 1, 2, 6]
def baseStart_6199169 : Nat := 118140960795 + 6199169 * 2 ^ 59
def prefixEnd_6199169 : Nat := 4983230072969 + 3 ^ 40 * 6199169 * 2
def baseEnd_6199169 : Nat := 353683706161329050719783

theorem tailTrace_6199169 : CollatzResearch.WordTrace tailWord_6199169 prefixEnd_6199169 353683706161329050719783 := by
  unfold tailWord_6199169
  simp only [CollatzResearch.WordTrace]
  refine ⟨226102268478476921620208561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150734845652317947746805707 226102268478476921620208561)
  ·
    refine ⟨169576701358857691215156421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226102268478476921620208561 169576701358857691215156421)
    ·
      refine ⟨31795631504785817102841829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 169576701358857691215156421 31795631504785817102841829)
      ·
        refine ⟨5961680907147340706782843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31795631504785817102841829 5961680907147340706782843)
        ·
          refine ⟨8942521360721011060174265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5961680907147340706782843 8942521360721011060174265)
          ·
            refine ⟨6706891020540758295130699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8942521360721011060174265 6706891020540758295130699)
            ·
              refine ⟨10060336530811137442696049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6706891020540758295130699 10060336530811137442696049)
              ·
                refine ⟨7545252398108353082022037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10060336530811137442696049 7545252398108353082022037)
                ·
                  refine ⟨353683706161329050719783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7545252398108353082022037 353683706161329050719783)
                  ·
                    rfl

theorem cell23_6199169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 2, 6].length) (baseStart_6199169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6199169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6199169 prefixEnd_6199169 := by exact prefixLift 6199169
  have htrace : WordTrace (prefixWord ++ tailWord_6199169) baseStart_6199169 baseEnd_6199169 := by
    simpa [prefixWord, tailWord_6199169, baseEnd_6199169] using wordTrace_append hprefix tailTrace_6199169
  have hstable : (prefixWord ++ tailWord_6199169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6199169).length < 2 ^ (prefixWord ++ tailWord_6199169).sum := by decide
  have hdescent : baseEnd_6199169 < baseStart_6199169 := by decide
  rcases family_descends (prefixWord ++ tailWord_6199169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6199172 : List Nat := [2, 3, 2, 1, 1, 1, 2, 4, 2, 3, 2]
def baseStart_6199172 : Nat := 118140960795 + 6199172 * 2 ^ 59
def prefixEnd_6199172 : Nat := 4983230072969 + 3 ^ 40 * 6199172 * 2
def baseEnd_6199172 : Nat := 3183154895893924944740533

theorem tailTrace_6199172 : CollatzResearch.WordTrace tailWord_6199172 prefixEnd_6199172 3183154895893924944740533 := by
  unfold tailWord_6199172
  simp only [CollatzResearch.WordTrace]
  refine ⟨113051188948733026566283885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150734918598310702088378513 113051188948733026566283885)
  ·
    refine ⟨42394195855774884962356457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113051188948733026566283885 42394195855774884962356457)
    ·
      refine ⟨31795646891831163721767343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42394195855774884962356457 31795646891831163721767343)
      ·
        refine ⟨47693470337746745582651015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31795646891831163721767343 47693470337746745582651015)
        ·
          refine ⟨71540205506620118373976523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47693470337746745582651015 71540205506620118373976523)
          ·
            refine ⟨107310308259930177560964785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71540205506620118373976523 107310308259930177560964785)
            ·
              refine ⟨80482731194947633170723589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107310308259930177560964785 80482731194947633170723589)
              ·
                refine ⟨15090512099052681219510673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80482731194947633170723589 15090512099052681219510673)
                ·
                  refine ⟨11317884074289510914633005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15090512099052681219510673 11317884074289510914633005)
                  ·
                    refine ⟨4244206527858566592987377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11317884074289510914633005 4244206527858566592987377)
                    ·
                      refine ⟨3183154895893924944740533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4244206527858566592987377 3183154895893924944740533)
                      ·
                        rfl

theorem cell23_6199172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 4, 2, 3, 2].length) (baseStart_6199172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6199172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6199172 prefixEnd_6199172 := by exact prefixLift 6199172
  have htrace : WordTrace (prefixWord ++ tailWord_6199172) baseStart_6199172 baseEnd_6199172 := by
    simpa [prefixWord, tailWord_6199172, baseEnd_6199172] using wordTrace_append hprefix tailTrace_6199172
  have hstable : (prefixWord ++ tailWord_6199172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6199172).length < 2 ^ (prefixWord ++ tailWord_6199172).sum := by decide
  have hdescent : baseEnd_6199172 < baseStart_6199172 := by decide
  rcases family_descends (prefixWord ++ tailWord_6199172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6199205 : List Nat := [1, 3, 1, 2, 1, 1, 1, 5, 3, 2, 3]
def baseStart_6199205 : Nat := 118140960795 + 6199205 * 2 ^ 59
def prefixEnd_6199205 : Nat := 4983230072969 + 3 ^ 40 * 6199205 * 2
def baseEnd_6199205 : Nat := 3183171840755523315627881

theorem tailTrace_6199205 : CollatzResearch.WordTrace tailWord_6199205 prefixEnd_6199205 3183171840755523315627881 := by
  unfold tailWord_6199205
  simp only [CollatzResearch.WordTrace]
  refine ⟨226103581506346499768519069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150735721004230999845679379 226103581506346499768519069)
  ·
    refine ⟨84788843064879937413194651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226103581506346499768519069 84788843064879937413194651)
    ·
      refine ⟨127183264597319906119791977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84788843064879937413194651 127183264597319906119791977)
      ·
        refine ⟨95387448447989929589843983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127183264597319906119791977 95387448447989929589843983)
        ·
          refine ⟨143081172671984894384765975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95387448447989929589843983 143081172671984894384765975)
          ·
            refine ⟨214621759007977341577148963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143081172671984894384765975 214621759007977341577148963)
            ·
              refine ⟨321932638511966012365723445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214621759007977341577148963 321932638511966012365723445)
              ·
                refine ⟨30181184860496813659286573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 321932638511966012365723445 30181184860496813659286573)
                ·
                  refine ⟨11317944322686305122232465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30181184860496813659286573 11317944322686305122232465)
                  ·
                    refine ⟨8488458242014728841674349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11317944322686305122232465 8488458242014728841674349)
                    ·
                      refine ⟨3183171840755523315627881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8488458242014728841674349 3183171840755523315627881)
                      ·
                        rfl

theorem cell23_6199205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 5, 3, 2, 3].length) (baseStart_6199205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6199205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6199205 prefixEnd_6199205 := by exact prefixLift 6199205
  have htrace : WordTrace (prefixWord ++ tailWord_6199205) baseStart_6199205 baseEnd_6199205 := by
    simpa [prefixWord, tailWord_6199205, baseEnd_6199205] using wordTrace_append hprefix tailTrace_6199205
  have hstable : (prefixWord ++ tailWord_6199205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6199205).length < 2 ^ (prefixWord ++ tailWord_6199205).sum := by decide
  have hdescent : baseEnd_6199205 < baseStart_6199205 := by decide
  rcases family_descends (prefixWord ++ tailWord_6199205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6199252 : List Nat := [2, 4, 1, 2, 1, 1, 2, 3, 1, 3, 3]
def baseStart_6199252 : Nat := 118140960795 + 6199252 * 2 ^ 59
def prefixEnd_6199252 : Nat := 4983230072969 + 3 ^ 40 * 6199252 * 2
def baseEnd_6199252 : Nat := 3183195974346284631740165

theorem tailTrace_6199252 : CollatzResearch.WordTrace tailWord_6199252 prefixEnd_6199252 3183195974346284631740165 := by
  unfold tailWord_6199252
  simp only [CollatzResearch.WordTrace]
  refine ⟨113052647868588113397740005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150736863824784151196986673 113052647868588113397740005)
  ·
    refine ⟨21197371475360271262076251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113052647868588113397740005 21197371475360271262076251)
    ·
      refine ⟨31796057213040406893114377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21197371475360271262076251 31796057213040406893114377)
      ·
        refine ⟨23847042909780305169835783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31796057213040406893114377 23847042909780305169835783)
        ·
          refine ⟨35770564364670457754753675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23847042909780305169835783 35770564364670457754753675)
          ·
            refine ⟨53655846547005686632130513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35770564364670457754753675 53655846547005686632130513)
            ·
              refine ⟨40241884910254264974097885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53655846547005686632130513 40241884910254264974097885)
              ·
                refine ⟨15090706841345349365286707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40241884910254264974097885 15090706841345349365286707)
                ·
                  refine ⟨22636060262018024047930061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15090706841345349365286707 22636060262018024047930061)
                  ·
                    refine ⟨8488522598256759017973773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22636060262018024047930061 8488522598256759017973773)
                    ·
                      refine ⟨3183195974346284631740165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8488522598256759017973773 3183195974346284631740165)
                      ·
                        rfl

theorem cell23_6199252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_6199252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6199252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6199252 prefixEnd_6199252 := by exact prefixLift 6199252
  have htrace : WordTrace (prefixWord ++ tailWord_6199252) baseStart_6199252 baseEnd_6199252 := by
    simpa [prefixWord, tailWord_6199252, baseEnd_6199252] using wordTrace_append hprefix tailTrace_6199252
  have hstable : (prefixWord ++ tailWord_6199252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6199252).length < 2 ^ (prefixWord ++ tailWord_6199252).sum := by decide
  have hdescent : baseEnd_6199252 < baseStart_6199252 := by decide
  rcases family_descends (prefixWord ++ tailWord_6199252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6199292 : List Nat := [2, 2, 2, 1, 2, 2, 1, 2, 3, 4, 2]
def baseStart_6199292 : Nat := 118140960795 + 6199292 * 2 ^ 59
def prefixEnd_6199292 : Nat := 4983230072969 + 3 ^ 40 * 6199292 * 2
def baseEnd_6199292 : Nat := 3183216513572464475239981

theorem tailTrace_6199292 : CollatzResearch.WordTrace tailWord_6199292 prefixEnd_6199292 3183216513572464475239981 := by
  unfold tailWord_6199292
  simp only [CollatzResearch.WordTrace]
  refine ⟨113053377328515656813468065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150737836438020875751290753 113053377328515656813468065)
  ·
    refine ⟨84790032996386742610101049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113053377328515656813468065 84790032996386742610101049)
    ·
      refine ⟨63592524747290056957575787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84790032996386742610101049 63592524747290056957575787)
      ·
        refine ⟨95388787120935085436363681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63592524747290056957575787 95388787120935085436363681)
        ·
          refine ⟨71541590340701314077272761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95388787120935085436363681 71541590340701314077272761)
          ·
            refine ⟨53656192755525985557954571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71541590340701314077272761 53656192755525985557954571)
            ·
              refine ⟨80484289133288978336931857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53656192755525985557954571 80484289133288978336931857)
              ·
                refine ⟨60363216849966733752698893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80484289133288978336931857 60363216849966733752698893)
                ·
                  refine ⟨22636206318737525157262085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60363216849966733752698893 22636206318737525157262085)
                  ·
                    refine ⟨4244288684763285966986641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22636206318737525157262085 4244288684763285966986641)
                    ·
                      refine ⟨3183216513572464475239981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4244288684763285966986641 3183216513572464475239981)
                      ·
                        rfl

theorem cell23_6199292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 3, 4, 2].length) (baseStart_6199292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6199292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6199292 prefixEnd_6199292 := by exact prefixLift 6199292
  have htrace : WordTrace (prefixWord ++ tailWord_6199292) baseStart_6199292 baseEnd_6199292 := by
    simpa [prefixWord, tailWord_6199292, baseEnd_6199292] using wordTrace_append hprefix tailTrace_6199292
  have hstable : (prefixWord ++ tailWord_6199292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6199292).length < 2 ^ (prefixWord ++ tailWord_6199292).sum := by decide
  have hdescent : baseEnd_6199292 < baseStart_6199292 := by decide
  rcases family_descends (prefixWord ++ tailWord_6199292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6199395 : List Nat := [1, 1, 1, 5, 1, 1, 2, 1, 1, 3, 6]
def baseStart_6199395 : Nat := 118140960795 + 6199395 * 2 ^ 59
def prefixEnd_6199395 : Nat := 4983230072969 + 3 ^ 40 * 6199395 * 2
def baseEnd_6199395 : Nat := 3183269402079877572252007

theorem tailTrace_6199395 : CollatzResearch.WordTrace tailWord_6199395 prefixEnd_6199395 3183269402079877572252007 := by
  unfold tailWord_6199395
  simp only [CollatzResearch.WordTrace]
  refine ⟨226110511375658162217935639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150740340917105441478623759 226110511375658162217935639)
  ·
    refine ⟨339165767063487243326903459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226110511375658162217935639 339165767063487243326903459)
    ·
      refine ⟨508748650595230864990355189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339165767063487243326903459 508748650595230864990355189)
      ·
        refine ⟨47695185993302893592845799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 508748650595230864990355189 47695185993302893592845799)
        ·
          refine ⟨71542778989954340389268699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47695185993302893592845799 71542778989954340389268699)
          ·
            refine ⟨107314168484931510583903049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71542778989954340389268699 107314168484931510583903049)
            ·
              refine ⟨80485626363698632937927287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107314168484931510583903049 80485626363698632937927287)
              ·
                refine ⟨120728439545547949406890931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80485626363698632937927287 120728439545547949406890931)
                ·
                  refine ⟨181092659318321924110336397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 120728439545547949406890931 181092659318321924110336397)
                  ·
                    refine ⟨67909747244370721541376149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 181092659318321924110336397 67909747244370721541376149)
                    ·
                      refine ⟨3183269402079877572252007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67909747244370721541376149 3183269402079877572252007)
                      ·
                        rfl

theorem cell23_6199395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_6199395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6199395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6199395 prefixEnd_6199395 := by exact prefixLift 6199395
  have htrace : WordTrace (prefixWord ++ tailWord_6199395) baseStart_6199395 baseEnd_6199395 := by
    simpa [prefixWord, tailWord_6199395, baseEnd_6199395] using wordTrace_append hprefix tailTrace_6199395
  have hstable : (prefixWord ++ tailWord_6199395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6199395).length < 2 ^ (prefixWord ++ tailWord_6199395).sum := by decide
  have hdescent : baseEnd_6199395 < baseStart_6199395 := by decide
  rcases family_descends (prefixWord ++ tailWord_6199395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6199460 : List Nat := [2, 3, 1, 2, 4, 2, 2, 2, 1, 4]
def baseStart_6199460 : Nat := 118140960795 + 6199460 * 2 ^ 59
def prefixEnd_6199460 : Nat := 4983230072969 + 3 ^ 40 * 6199460 * 2
def baseEnd_6199460 : Nat := 1061100926107473272646403

theorem tailTrace_6199460 : CollatzResearch.WordTrace tailWord_6199460 prefixEnd_6199460 1061100926107473272646403 := by
  unfold tailWord_6199460
  simp only [CollatzResearch.WordTrace]
  refine ⟨113056441060211339159525917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150741921413615118879367889 113056441060211339159525917)
  ·
    refine ⟨42396165397579252184822219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113056441060211339159525917 42396165397579252184822219)
    ·
      refine ⟨63594248096368878277233329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42396165397579252184822219 63594248096368878277233329)
      ·
        refine ⟨47695686072276658707924997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63594248096368878277233329 47695686072276658707924997)
        ·
          refine ⟨8942941138551873507735937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47695686072276658707924997 8942941138551873507735937)
          ·
            refine ⟨6707205853913905130801953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8942941138551873507735937 6707205853913905130801953)
            ·
              refine ⟨5030404390435428848101465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6707205853913905130801953 5030404390435428848101465)
              ·
                refine ⟨3772803292826571636076099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5030404390435428848101465 3772803292826571636076099)
                ·
                  refine ⟨5659204939239857454114149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3772803292826571636076099 5659204939239857454114149)
                  ·
                    refine ⟨1061100926107473272646403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5659204939239857454114149 1061100926107473272646403)
                    ·
                      rfl

theorem cell23_6199460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 2, 2, 1, 4].length) (baseStart_6199460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6199460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6199460 prefixEnd_6199460 := by exact prefixLift 6199460
  have htrace : WordTrace (prefixWord ++ tailWord_6199460) baseStart_6199460 baseEnd_6199460 := by
    simpa [prefixWord, tailWord_6199460, baseEnd_6199460] using wordTrace_append hprefix tailTrace_6199460
  have hstable : (prefixWord ++ tailWord_6199460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6199460).length < 2 ^ (prefixWord ++ tailWord_6199460).sum := by decide
  have hdescent : baseEnd_6199460 < baseStart_6199460 := by decide
  rcases family_descends (prefixWord ++ tailWord_6199460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6199465 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 1, 12]
def baseStart_6199465 : Nat := 118140960795 + 6199465 * 2 ^ 59
def prefixEnd_6199465 : Nat := 4983230072969 + 3 ^ 40 * 6199465 * 2
def baseEnd_6199465 : Nat := 1061101781908564099458895

theorem tailTrace_6199465 : CollatzResearch.WordTrace tailWord_6199465 prefixEnd_6199465 1061101781908564099458895 := by
  unfold tailWord_6199465
  simp only [CollatzResearch.WordTrace]
  refine ⟨226113064485404564172983849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150742042990269709448655899 226113064485404564172983849)
  ·
    refine ⟨169584798364053423129737887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226113064485404564172983849 169584798364053423129737887)
    ·
      refine ⟨254377197546080134694606831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169584798364053423129737887 254377197546080134694606831)
      ·
        refine ⟨381565796319120202041910247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254377197546080134694606831 381565796319120202041910247)
        ·
          refine ⟨572348694478680303062865371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 381565796319120202041910247 572348694478680303062865371)
          ·
            refine ⟨858523041718020454594298057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 572348694478680303062865371 858523041718020454594298057)
            ·
              refine ⟨643892281288515340945723543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 858523041718020454594298057 643892281288515340945723543)
              ·
                refine ⟨965838421932773011418585315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 643892281288515340945723543 965838421932773011418585315)
                ·
                  refine ⟨1448757632899159517127877973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 965838421932773011418585315 1448757632899159517127877973)
                  ·
                    refine ⟨1061101781908564099458895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 12 1448757632899159517127877973 1061101781908564099458895)
                    ·
                      rfl

theorem cell23_6199465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 12].length) (baseStart_6199465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6199465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6199465 prefixEnd_6199465 := by exact prefixLift 6199465
  have htrace : WordTrace (prefixWord ++ tailWord_6199465) baseStart_6199465 baseEnd_6199465 := by
    simpa [prefixWord, tailWord_6199465, baseEnd_6199465] using wordTrace_append hprefix tailTrace_6199465
  have hstable : (prefixWord ++ tailWord_6199465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6199465).length < 2 ^ (prefixWord ++ tailWord_6199465).sum := by decide
  have hdescent : baseEnd_6199465 < baseStart_6199465 := by decide
  rcases family_descends (prefixWord ++ tailWord_6199465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6199469 : List Nat := [1, 5, 2, 1, 2, 1, 1, 2, 3, 5]
def baseStart_6199469 : Nat := 118140960795 + 6199469 * 2 ^ 59
def prefixEnd_6199469 : Nat := 4983230072969 + 3 ^ 40 * 6199469 * 2
def baseEnd_6199469 : Nat := 1061102466549436760908889

theorem tailTrace_6199469 : CollatzResearch.WordTrace tailWord_6199469 prefixEnd_6199469 1061102466549436760908889 := by
  unfold tailWord_6199469
  simp only [CollatzResearch.WordTrace]
  refine ⟨226113210377390072856129461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150742140251593381904086307 226113210377390072856129461)
  ·
    refine ⟨21198113472880319330262137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 226113210377390072856129461 21198113472880319330262137)
    ·
      refine ⟨15898585104660239497696603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21198113472880319330262137 15898585104660239497696603)
      ·
        refine ⟨23847877656990359246544905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15898585104660239497696603 23847877656990359246544905)
        ·
          refine ⟨17885908242742769434908679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23847877656990359246544905 17885908242742769434908679)
          ·
            refine ⟨26828862364114154152363019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17885908242742769434908679 26828862364114154152363019)
            ·
              refine ⟨40243293546171231228544529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26828862364114154152363019 40243293546171231228544529)
              ·
                refine ⟨30182470159628423421408397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40243293546171231228544529 30182470159628423421408397)
                ·
                  refine ⟨11318426309860658783028149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30182470159628423421408397 11318426309860658783028149)
                  ·
                    refine ⟨1061102466549436760908889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11318426309860658783028149 1061102466549436760908889)
                    ·
                      rfl

theorem cell23_6199469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_6199469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6199469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6199469 prefixEnd_6199469 := by exact prefixLift 6199469
  have htrace : WordTrace (prefixWord ++ tailWord_6199469) baseStart_6199469 baseEnd_6199469 := by
    simpa [prefixWord, tailWord_6199469, baseEnd_6199469] using wordTrace_append hprefix tailTrace_6199469
  have hstable : (prefixWord ++ tailWord_6199469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6199469).length < 2 ^ (prefixWord ++ tailWord_6199469).sum := by decide
  have hdescent : baseEnd_6199469 < baseStart_6199469 := by decide
  rcases family_descends (prefixWord ++ tailWord_6199469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6199482 : List Nat := [3, 1, 1, 1, 2, 2, 3, 3, 1, 6]
def baseStart_6199482 : Nat := 118140960795 + 6199482 * 2 ^ 59
def prefixEnd_6199482 : Nat := 4983230072969 + 3 ^ 40 * 6199482 * 2
def baseEnd_6199482 : Nat := 1061104691632272910621369

theorem tailTrace_6199482 : CollatzResearch.WordTrace tailWord_6199482 prefixEnd_6199482 1061104691632272910621369 := by
  unfold tailWord_6199482
  simp only [CollatzResearch.WordTrace]
  refine ⟨56528421131585744019088175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150742456350895317384235133 56528421131585744019088175)
  ·
    refine ⟨84792631697378616028632263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56528421131585744019088175 84792631697378616028632263)
    ·
      refine ⟨127188947546067924042948395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84792631697378616028632263 127188947546067924042948395)
      ·
        refine ⟨190783421319101886064422593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127188947546067924042948395 190783421319101886064422593)
        ·
          refine ⟨143087565989326414548316945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190783421319101886064422593 143087565989326414548316945)
          ·
            refine ⟨107315674491994810911237709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143087565989326414548316945 107315674491994810911237709)
            ·
              refine ⟨40243377934498054091714141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107315674491994810911237709 40243377934498054091714141)
              ·
                refine ⟨15091266725436770284392803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40243377934498054091714141 15091266725436770284392803)
                ·
                  refine ⟨22636900088155155426589205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15091266725436770284392803 22636900088155155426589205)
                  ·
                    refine ⟨1061104691632272910621369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22636900088155155426589205 1061104691632272910621369)
                    ·
                      rfl

theorem cell23_6199482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 3, 1, 6].length) (baseStart_6199482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6199482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6199482 prefixEnd_6199482 := by exact prefixLift 6199482
  have htrace : WordTrace (prefixWord ++ tailWord_6199482) baseStart_6199482 baseEnd_6199482 := by
    simpa [prefixWord, tailWord_6199482, baseEnd_6199482] using wordTrace_append hprefix tailTrace_6199482
  have hstable : (prefixWord ++ tailWord_6199482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6199482).length < 2 ^ (prefixWord ++ tailWord_6199482).sum := by decide
  have hdescent : baseEnd_6199482 < baseStart_6199482 := by decide
  rcases family_descends (prefixWord ++ tailWord_6199482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6199506 : List Nat := [3, 2, 2, 2, 1, 3, 1, 3, 1, 1, 4]
def baseStart_6199506 : Nat := 118140960795 + 6199506 * 2 ^ 59
def prefixEnd_6199506 : Nat := 4983230072969 + 3 ^ 40 * 6199506 * 2
def baseEnd_6199506 : Nat := 3183326398432526637963997

theorem tailTrace_6199506 : CollatzResearch.WordTrace tailWord_6199506 prefixEnd_6199506 3183326398432526637963997 := by
  unfold tailWord_6199506
  simp only [CollatzResearch.WordTrace]
  refine ⟨56528639969564007043806593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150743039918837352116817581 56528639969564007043806593)
  ·
    refine ⟨42396479977173005282854945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56528639969564007043806593 42396479977173005282854945)
    ·
      refine ⟨31797359982879753962141209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42396479977173005282854945 31797359982879753962141209)
      ·
        refine ⟨23848019987159815471605907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31797359982879753962141209 23848019987159815471605907)
        ·
          refine ⟨35772029980739723207408861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23848019987159815471605907 35772029980739723207408861)
          ·
            refine ⟨13414511242777396202778323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35772029980739723207408861 13414511242777396202778323)
            ·
              refine ⟨20121766864166094304167485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13414511242777396202778323 20121766864166094304167485)
              ·
                refine ⟨7545662574062285364062807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20121766864166094304167485 7545662574062285364062807)
                ·
                  refine ⟨11318493861093428046094211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7545662574062285364062807 11318493861093428046094211)
                  ·
                    refine ⟨16977740791640142069141317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11318493861093428046094211 16977740791640142069141317)
                    ·
                      refine ⟨3183326398432526637963997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16977740791640142069141317 3183326398432526637963997)
                      ·
                        rfl

theorem cell23_6199506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_6199506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6199506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6199506 prefixEnd_6199506 := by exact prefixLift 6199506
  have htrace : WordTrace (prefixWord ++ tailWord_6199506) baseStart_6199506 baseEnd_6199506 := by
    simpa [prefixWord, tailWord_6199506, baseEnd_6199506] using wordTrace_append hprefix tailTrace_6199506
  have hstable : (prefixWord ++ tailWord_6199506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6199506).length < 2 ^ (prefixWord ++ tailWord_6199506).sum := by decide
  have hdescent : baseEnd_6199506 < baseStart_6199506 := by decide
  rcases family_descends (prefixWord ++ tailWord_6199506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6199512 : List Nat := [2, 1, 2, 2, 4, 2, 10]
def baseStart_6199512 : Nat := 118140960795 + 6199512 * 2 ^ 59
def prefixEnd_6199512 : Nat := 4983230072969 + 3 ^ 40 * 6199512 * 2
def baseEnd_6199512 : Nat := 39300363942178439685049

theorem tailTrace_6199512 : CollatzResearch.WordTrace tailWord_6199512 prefixEnd_6199512 39300363942178439685049 := by
  unfold tailWord_6199512
  simp only [CollatzResearch.WordTrace]
  refine ⟨113057389358117145599972395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150743185810822860799963193 113057389358117145599972395)
  ·
    refine ⟨169586084037175718399958593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113057389358117145599972395 169586084037175718399958593)
    ·
      refine ⟨127189563027881788799968945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169586084037175718399958593 127189563027881788799968945)
      ·
        refine ⟨95392172270911341599976709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127189563027881788799968945 95392172270911341599976709)
        ·
          refine ⟨17886032300795876549995633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95392172270911341599976709 17886032300795876549995633)
          ·
            refine ⟨13414524225596907412496725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17886032300795876549995633 13414524225596907412496725)
            ·
              refine ⟨39300363942178439685049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13414524225596907412496725 39300363942178439685049)
              ·
                rfl

theorem cell23_6199512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 10].length) (baseStart_6199512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6199512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6199512 prefixEnd_6199512 := by exact prefixLift 6199512
  have htrace : WordTrace (prefixWord ++ tailWord_6199512) baseStart_6199512 baseEnd_6199512 := by
    simpa [prefixWord, tailWord_6199512, baseEnd_6199512] using wordTrace_append hprefix tailTrace_6199512
  have hstable : (prefixWord ++ tailWord_6199512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6199512).length < 2 ^ (prefixWord ++ tailWord_6199512).sum := by decide
  have hdescent : baseEnd_6199512 < baseStart_6199512 := by decide
  rcases family_descends (prefixWord ++ tailWord_6199512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6199533 : List Nat := [1, 5, 1, 2, 4, 1, 1, 1, 1, 6]
def baseStart_6199533 : Nat := 118140960795 + 6199533 * 2 ^ 59
def prefixEnd_6199533 : Nat := 4983230072969 + 3 ^ 40 * 6199533 * 2
def baseEnd_6199533 : Nat := 1061113420803399344108791

theorem tailTrace_6199533 : CollatzResearch.WordTrace tailWord_6199533 prefixEnd_6199533 1061113420803399344108791 := by
  unfold tailWord_6199533
  simp only [CollatzResearch.WordTrace]
  refine ⟨226115544649158211786459253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150743696432772141190972835 226115544649158211786459253)
  ·
    refine ⟨21198332310858582354980555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 226115544649158211786459253 21198332310858582354980555)
    ·
      refine ⟨31797498466287873532470833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21198332310858582354980555 31797498466287873532470833)
      ·
        refine ⟨23848123849715905149353125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31797498466287873532470833 23848123849715905149353125)
        ·
          refine ⟨4471523221821732215503711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23848123849715905149353125 4471523221821732215503711)
          ·
            refine ⟨6707284832732598323255567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4471523221821732215503711 6707284832732598323255567)
            ·
              refine ⟨10060927249098897484883351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6707284832732598323255567 10060927249098897484883351)
              ·
                refine ⟨15091390873648346227325027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10060927249098897484883351 15091390873648346227325027)
                ·
                  refine ⟨22637086310472519340987541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15091390873648346227325027 22637086310472519340987541)
                  ·
                    refine ⟨1061113420803399344108791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22637086310472519340987541 1061113420803399344108791)
                    ·
                      rfl

theorem cell23_6199533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 1, 1, 6].length) (baseStart_6199533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6199533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6199533 prefixEnd_6199533 := by exact prefixLift 6199533
  have htrace : WordTrace (prefixWord ++ tailWord_6199533) baseStart_6199533 baseEnd_6199533 := by
    simpa [prefixWord, tailWord_6199533, baseEnd_6199533] using wordTrace_append hprefix tailTrace_6199533
  have hstable : (prefixWord ++ tailWord_6199533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6199533).length < 2 ^ (prefixWord ++ tailWord_6199533).sum := by decide
  have hdescent : baseEnd_6199533 < baseStart_6199533 := by decide
  rcases family_descends (prefixWord ++ tailWord_6199533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6199549 : List Nat := [1, 4, 1, 1, 1, 1, 1, 2, 2, 7, 2]
def baseStart_6199549 : Nat := 118140960795 + 6199549 * 2 ^ 59
def prefixEnd_6199549 : Nat := 4983230072969 + 3 ^ 40 * 6199549 * 2
def baseEnd_6199549 : Nat := 3183348478100669969726299

theorem tailTrace_6199549 : CollatzResearch.WordTrace tailWord_6199549 prefixEnd_6199549 3183348478100669969726299 := by
  unfold tailWord_6199549
  simp only [CollatzResearch.WordTrace]
  refine ⟨226116128217100246519041701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150744085478066831012694467 226116128217100246519041701)
  ·
    refine ⟨42396774040706296222320319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 226116128217100246519041701 42396774040706296222320319)
    ·
      refine ⟨63595161061059444333480479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42396774040706296222320319 63595161061059444333480479)
      ·
        refine ⟨95392741591589166500220719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63595161061059444333480479 95392741591589166500220719)
        ·
          refine ⟨143089112387383749750331079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95392741591589166500220719 143089112387383749750331079)
          ·
            refine ⟨214633668581075624625496619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143089112387383749750331079 214633668581075624625496619)
            ·
              refine ⟨321950502871613436938244929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214633668581075624625496619 321950502871613436938244929)
              ·
                refine ⟨241462877153710077703683697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 321950502871613436938244929 241462877153710077703683697)
                ·
                  refine ⟨181097157865282558277762773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 241462877153710077703683697 181097157865282558277762773)
                  ·
                    refine ⟨4244464637467559959635065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 181097157865282558277762773 4244464637467559959635065)
                    ·
                      refine ⟨3183348478100669969726299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4244464637467559959635065 3183348478100669969726299)
                      ·
                        rfl

theorem cell23_6199549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 7, 2].length) (baseStart_6199549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6199549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6199549 prefixEnd_6199549 := by exact prefixLift 6199549
  have htrace : WordTrace (prefixWord ++ tailWord_6199549) baseStart_6199549 baseEnd_6199549 := by
    simpa [prefixWord, tailWord_6199549, baseEnd_6199549] using wordTrace_append hprefix tailTrace_6199549
  have hstable : (prefixWord ++ tailWord_6199549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6199549).length < 2 ^ (prefixWord ++ tailWord_6199549).sum := by decide
  have hdescent : baseEnd_6199549 < baseStart_6199549 := by decide
  rcases family_descends (prefixWord ++ tailWord_6199549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6199552 : List Nat := [2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 5]
def baseStart_6199552 : Nat := 118140960795 + 6199552 * 2 ^ 59
def prefixEnd_6199552 : Nat := 4983230072969 + 3 ^ 40 * 6199552 * 2
def baseEnd_6199552 : Nat := 3183350018542633457988785

theorem tailTrace_6199552 : CollatzResearch.WordTrace tailWord_6199552 prefixEnd_6199552 3183350018542633457988785 := by
  unfold tailWord_6199552
  simp only [CollatzResearch.WordTrace]
  refine ⟨113058118818044689015700455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150744158424059585354267273 113058118818044689015700455)
  ·
    refine ⟨169587178227067033523550683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113058118818044689015700455 169587178227067033523550683)
    ·
      refine ⟨254380767340600550285326025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169587178227067033523550683 254380767340600550285326025)
      ·
        refine ⟨190785575505450412713994519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 254380767340600550285326025 190785575505450412713994519)
        ·
          refine ⟨286178363258175619070991779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190785575505450412713994519 286178363258175619070991779)
          ·
            refine ⟨429267544887263428606487669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286178363258175619070991779 429267544887263428606487669)
            ·
              refine ⟨40243832333180946431858219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 429267544887263428606487669 40243832333180946431858219)
              ·
                refine ⟨60365748499771419647787329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40243832333180946431858219 60365748499771419647787329)
                ·
                  refine ⟨45274311374828564735840497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60365748499771419647787329 45274311374828564735840497)
                  ·
                    refine ⟨33955733531121423551880373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45274311374828564735840497 33955733531121423551880373)
                    ·
                      refine ⟨3183350018542633457988785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33955733531121423551880373 3183350018542633457988785)
                      ·
                        rfl

theorem cell23_6199552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 5].length) (baseStart_6199552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6199552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6199552 prefixEnd_6199552 := by exact prefixLift 6199552
  have htrace : WordTrace (prefixWord ++ tailWord_6199552) baseStart_6199552 baseEnd_6199552 := by
    simpa [prefixWord, tailWord_6199552, baseEnd_6199552] using wordTrace_append hprefix tailTrace_6199552
  have hstable : (prefixWord ++ tailWord_6199552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6199552).length < 2 ^ (prefixWord ++ tailWord_6199552).sum := by decide
  have hdescent : baseEnd_6199552 < baseStart_6199552 := by decide
  rcases family_descends (prefixWord ++ tailWord_6199552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6199617 : List Nat := [1, 2, 5, 2, 2, 1, 3, 1, 1, 3, 2]
def baseStart_6199617 : Nat := 118140960795 + 6199617 * 2 ^ 59
def prefixEnd_6199617 : Nat := 4983230072969 + 3 ^ 40 * 6199617 * 2
def baseEnd_6199617 : Nat := 3183383394785175703675987

theorem tailTrace_6199617 : CollatzResearch.WordTrace tailWord_6199617 prefixEnd_6199617 3183383394785175703675987 := by
  unfold tailWord_6199617
  simp only [CollatzResearch.WordTrace]
  refine ⟨226118608380853894132517105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150745738920569262755011403 226118608380853894132517105)
  ·
    refine ⟨169588956285640420599387829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226118608380853894132517105 169588956285640420599387829)
    ·
      refine ⟨15898964651778789431192609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 169588956285640420599387829 15898964651778789431192609)
      ·
        refine ⟨11924223488834092073394457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15898964651778789431192609 11924223488834092073394457)
        ·
          refine ⟨8943167616625569055045843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11924223488834092073394457 8943167616625569055045843)
          ·
            refine ⟨13414751424938353582568765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8943167616625569055045843 13414751424938353582568765)
            ·
              refine ⟨5030531784351882593463287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13414751424938353582568765 5030531784351882593463287)
              ·
                refine ⟨7545797676527823890194931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5030531784351882593463287 7545797676527823890194931)
                ·
                  refine ⟨11318696514791735835292397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7545797676527823890194931 11318696514791735835292397)
                  ·
                    refine ⟨4244511193046900938234649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11318696514791735835292397 4244511193046900938234649)
                    ·
                      refine ⟨3183383394785175703675987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4244511193046900938234649 3183383394785175703675987)
                      ·
                        rfl

theorem cell23_6199617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_6199617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6199617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6199617 prefixEnd_6199617 := by exact prefixLift 6199617
  have htrace : WordTrace (prefixWord ++ tailWord_6199617) baseStart_6199617 baseEnd_6199617 := by
    simpa [prefixWord, tailWord_6199617, baseEnd_6199617] using wordTrace_append hprefix tailTrace_6199617
  have hstable : (prefixWord ++ tailWord_6199617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6199617).length < 2 ^ (prefixWord ++ tailWord_6199617).sum := by decide
  have hdescent : baseEnd_6199617 < baseStart_6199617 := by decide
  rcases family_descends (prefixWord ++ tailWord_6199617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6199666 : List Nat := [3, 2, 1, 2, 1, 3, 3, 1, 2, 5]
def baseStart_6199666 : Nat := 118140960795 + 6199666 * 2 ^ 59
def prefixEnd_6199666 : Nat := 4983230072969 + 3 ^ 40 * 6199666 * 2
def baseEnd_6199666 : Nat := 1061136185112415337321087

theorem tailTrace_6199666 : CollatzResearch.WordTrace tailWord_6199666 prefixEnd_6199666 1061136185112415337321087 := by
  unfold tailWord_6199666
  simp only [CollatzResearch.WordTrace]
  refine ⟨56530098889419093875262713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150746930371784250334033901 56530098889419093875262713)
  ·
    refine ⟨42397574167064320406447035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56530098889419093875262713 42397574167064320406447035)
    ·
      refine ⟨63596361250596480609670553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42397574167064320406447035 63596361250596480609670553)
      ·
        refine ⟨47697270937947360457252915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63596361250596480609670553 47697270937947360457252915)
        ·
          refine ⟨71545906406921040685879373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47697270937947360457252915 71545906406921040685879373)
          ·
            refine ⟨26829714902595390257204765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71545906406921040685879373 26829714902595390257204765)
            ·
              refine ⟨10061143088473271346451787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26829714902595390257204765 10061143088473271346451787)
              ·
                refine ⟨15091714632709907019677681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10061143088473271346451787 15091714632709907019677681)
                ·
                  refine ⟨11318785974532430264758261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15091714632709907019677681 11318785974532430264758261)
                  ·
                    refine ⟨1061136185112415337321087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11318785974532430264758261 1061136185112415337321087)
                    ·
                      rfl

theorem cell23_6199666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 1, 2, 5].length) (baseStart_6199666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6199666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6199666 prefixEnd_6199666 := by exact prefixLift 6199666
  have htrace : WordTrace (prefixWord ++ tailWord_6199666) baseStart_6199666 baseEnd_6199666 := by
    simpa [prefixWord, tailWord_6199666, baseEnd_6199666] using wordTrace_append hprefix tailTrace_6199666
  have hstable : (prefixWord ++ tailWord_6199666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6199666).length < 2 ^ (prefixWord ++ tailWord_6199666).sum := by decide
  have hdescent : baseEnd_6199666 < baseStart_6199666 := by decide
  rcases family_descends (prefixWord ++ tailWord_6199666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6199706 : List Nat := [3, 1, 1, 4, 1, 2, 1, 2, 1, 4, 3]
def baseStart_6199706 : Nat := 118140960795 + 6199706 * 2 ^ 59
def prefixEnd_6199706 : Nat := 4983230072969 + 3 ^ 40 * 6199706 * 2
def baseEnd_6199706 : Nat := 3183429094563425855463077

theorem tailTrace_6199706 : CollatzResearch.WordTrace tailWord_6199706 prefixEnd_6199706 3183429094563425855463077 := by
  unfold tailWord_6199706
  simp only [CollatzResearch.WordTrace]
  refine ⟨56530463619382865583126743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150747902985020974888337981 56530463619382865583126743)
  ·
    refine ⟨84795695429074298374690115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56530463619382865583126743 84795695429074298374690115)
    ·
      refine ⟨127193543143611447562035173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84795695429074298374690115 127193543143611447562035173)
      ·
        refine ⟨23848789339427146417881595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127193543143611447562035173 23848789339427146417881595)
        ·
          refine ⟨35773184009140719626822393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23848789339427146417881595 35773184009140719626822393)
          ·
            refine ⟨26829888006855539720116795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35773184009140719626822393 26829888006855539720116795)
            ·
              refine ⟨40244832010283309580175193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26829888006855539720116795 40244832010283309580175193)
              ·
                refine ⟨30183624007712482185131395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40244832010283309580175193 30183624007712482185131395)
                ·
                  refine ⟨45275436011568723277697093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30183624007712482185131395 45275436011568723277697093)
                  ·
                    refine ⟨8489144252169135614568205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45275436011568723277697093 8489144252169135614568205)
                    ·
                      refine ⟨3183429094563425855463077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8489144252169135614568205 3183429094563425855463077)
                      ·
                        rfl

theorem cell23_6199706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_6199706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6199706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6199706 prefixEnd_6199706 := by exact prefixLift 6199706
  have htrace : WordTrace (prefixWord ++ tailWord_6199706) baseStart_6199706 baseEnd_6199706 := by
    simpa [prefixWord, tailWord_6199706, baseEnd_6199706] using wordTrace_append hprefix tailTrace_6199706
  have hstable : (prefixWord ++ tailWord_6199706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6199706).length < 2 ^ (prefixWord ++ tailWord_6199706).sum := by decide
  have hdescent : baseEnd_6199706 < baseStart_6199706 := by decide
  rcases family_descends (prefixWord ++ tailWord_6199706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6199753 : List Nat := [1, 2, 1, 1, 2, 1, 7, 1, 3, 1, 3]
def baseStart_6199753 : Nat := 118140960795 + 6199753 * 2 ^ 59
def prefixEnd_6199753 : Nat := 4983230072969 + 3 ^ 40 * 6199753 * 2
def baseEnd_6199753 : Nat := 3183453228154187171575361

theorem tailTrace_6199753 : CollatzResearch.WordTrace tailWord_6199753 prefixEnd_6199753 3183453228154187171575361 := by
  unfold tailWord_6199753
  simp only [CollatzResearch.WordTrace]
  refine ⟨226123568708361189359467913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150749045805574126239645275 226123568708361189359467913)
  ·
    refine ⟨169592676531270892019600935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226123568708361189359467913 169592676531270892019600935)
    ·
      refine ⟨254389014796906338029401403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169592676531270892019600935 254389014796906338029401403)
      ·
        refine ⟨381583522195359507044102105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254389014796906338029401403 381583522195359507044102105)
        ·
          refine ⟨286187641646519630283076579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 381583522195359507044102105 286187641646519630283076579)
          ·
            refine ⟨429281462469779445424614869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286187641646519630283076579 429281462469779445424614869)
            ·
              refine ⟨10061284276635455752139411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 429281462469779445424614869 10061284276635455752139411)
              ·
                refine ⟨15091926414953183628209117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10061284276635455752139411 15091926414953183628209117)
                ·
                  refine ⟨5659472405607443860578419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15091926414953183628209117 5659472405607443860578419)
                  ·
                    refine ⟨8489208608411165790867629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5659472405607443860578419 8489208608411165790867629)
                    ·
                      refine ⟨3183453228154187171575361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8489208608411165790867629 3183453228154187171575361)
                      ·
                        rfl

theorem cell23_6199753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 1, 3, 1, 3].length) (baseStart_6199753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6199753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6199753 prefixEnd_6199753 := by exact prefixLift 6199753
  have htrace : WordTrace (prefixWord ++ tailWord_6199753) baseStart_6199753 baseEnd_6199753 := by
    simpa [prefixWord, tailWord_6199753, baseEnd_6199753] using wordTrace_append hprefix tailTrace_6199753
  have hstable : (prefixWord ++ tailWord_6199753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6199753).length < 2 ^ (prefixWord ++ tailWord_6199753).sum := by decide
  have hdescent : baseEnd_6199753 < baseStart_6199753 := by decide
  rcases family_descends (prefixWord ++ tailWord_6199753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6199759 : List Nat := [1, 1, 2, 1, 1, 4, 1, 1, 2, 5, 4]
def baseStart_6199759 : Nat := 118140960795 + 6199759 * 2 ^ 59
def prefixEnd_6199759 : Nat := 4983230072969 + 3 ^ 40 * 6199759 * 2
def baseEnd_6199759 : Nat := 3183456309038114148100333

theorem tailTrace_6199759 : CollatzResearch.WordTrace tailWord_6199759 prefixEnd_6199759 3183456309038114148100333 := by
  unfold tailWord_6199759
  simp only [CollatzResearch.WordTrace]
  refine ⟨226123787546339452384186331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150749191697559634922790887 226123787546339452384186331)
  ·
    refine ⟨339185681319509178576279497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226123787546339452384186331 339185681319509178576279497)
    ·
      refine ⟨254389260989631883932209623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 339185681319509178576279497 254389260989631883932209623)
      ·
        refine ⟨381583891484447825898314435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254389260989631883932209623 381583891484447825898314435)
        ·
          refine ⟨572375837226671738847471653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 381583891484447825898314435 572375837226671738847471653)
          ·
            refine ⟨107320469480000951033900935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 572375837226671738847471653 107320469480000951033900935)
            ·
              refine ⟨160980704220001426550851403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107320469480000951033900935 160980704220001426550851403)
              ·
                refine ⟨241471056330002139826277105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160980704220001426550851403 241471056330002139826277105)
                ·
                  refine ⟨181103292247501604869707829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 241471056330002139826277105 181103292247501604869707829)
                  ·
                    refine ⟨16978433648203275456535109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 181103292247501604869707829 16978433648203275456535109)
                    ·
                      refine ⟨3183456309038114148100333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16978433648203275456535109 3183456309038114148100333)
                      ·
                        rfl

theorem cell23_6199759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 5, 4].length) (baseStart_6199759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6199759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6199759 prefixEnd_6199759 := by exact prefixLift 6199759
  have htrace : WordTrace (prefixWord ++ tailWord_6199759) baseStart_6199759 baseEnd_6199759 := by
    simpa [prefixWord, tailWord_6199759, baseEnd_6199759] using wordTrace_append hprefix tailTrace_6199759
  have hstable : (prefixWord ++ tailWord_6199759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6199759).length < 2 ^ (prefixWord ++ tailWord_6199759).sum := by decide
  have hdescent : baseEnd_6199759 < baseStart_6199759 := by decide
  rcases family_descends (prefixWord ++ tailWord_6199759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6199776 : List Nat := [2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 4]
def baseStart_6199776 : Nat := 118140960795 + 6199776 * 2 ^ 59
def prefixEnd_6199776 : Nat := 4983230072969 + 3 ^ 40 * 6199776 * 2
def baseEnd_6199776 : Nat := 3183465038209240581587755

theorem tailTrace_6199776 : CollatzResearch.WordTrace tailWord_6199776 prefixEnd_6199776 3183465038209240581587755 := by
  unfold tailWord_6199776
  simp only [CollatzResearch.WordTrace]
  refine ⟨113062203793638932143777591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150749605058185242858370121 113062203793638932143777591)
  ·
    refine ⟨169593305690458398215666387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113062203793638932143777591 169593305690458398215666387)
    ·
      refine ⟨254389958535687597323499581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169593305690458398215666387 254389958535687597323499581)
      ·
        refine ⟨95396234450882848996312343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 254389958535687597323499581 95396234450882848996312343)
        ·
          refine ⟨143094351676324273494468515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95396234450882848996312343 143094351676324273494468515)
          ·
            refine ⟨214641527514486410241702773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143094351676324273494468515 214641527514486410241702773)
            ·
              refine ⟨20122643204483100960159635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 214641527514486410241702773 20122643204483100960159635)
              ·
                refine ⟨30183964806724651440239453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20122643204483100960159635 30183964806724651440239453)
                ·
                  refine ⟨11318986802521744290089795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30183964806724651440239453 11318986802521744290089795)
                  ·
                    refine ⟨16978480203782616435134693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11318986802521744290089795 16978480203782616435134693)
                    ·
                      refine ⟨3183465038209240581587755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16978480203782616435134693 3183465038209240581587755)
                      ·
                        rfl

theorem cell23_6199776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 4].length) (baseStart_6199776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6199776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6199776 prefixEnd_6199776 := by exact prefixLift 6199776
  have htrace : WordTrace (prefixWord ++ tailWord_6199776) baseStart_6199776 baseEnd_6199776 := by
    simpa [prefixWord, tailWord_6199776, baseEnd_6199776] using wordTrace_append hprefix tailTrace_6199776
  have hstable : (prefixWord ++ tailWord_6199776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6199776).length < 2 ^ (prefixWord ++ tailWord_6199776).sum := by decide
  have hdescent : baseEnd_6199776 < baseStart_6199776 := by decide
  rcases family_descends (prefixWord ++ tailWord_6199776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6199786 : List Nat := [3, 1, 3, 1, 3, 1, 1, 1, 3, 6]
def baseStart_6199786 : Nat := 118140960795 + 6199786 * 2 ^ 59
def prefixEnd_6199786 : Nat := 4983230072969 + 3 ^ 40 * 6199786 * 2
def baseEnd_6199786 : Nat := 1061156724338595180820903

theorem tailTrace_6199786 : CollatzResearch.WordTrace tailWord_6199786 prefixEnd_6199786 1061156724338595180820903 := by
  unfold tailWord_6199786
  simp only [CollatzResearch.WordTrace]
  refine ⟨56531193079310408998854803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150749848211494423996946141 56531193079310408998854803)
  ·
    refine ⟨84796789618965613498282205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56531193079310408998854803 84796789618965613498282205)
    ·
      refine ⟨31798796107112105061855827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84796789618965613498282205 31798796107112105061855827)
      ·
        refine ⟨47698194160668157592783741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31798796107112105061855827 47698194160668157592783741)
        ·
          refine ⟨17886822810250559097293903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47698194160668157592783741 17886822810250559097293903)
          ·
            refine ⟨26830234215375838645940855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17886822810250559097293903 26830234215375838645940855)
            ·
              refine ⟨40245351323063757968911283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26830234215375838645940855 40245351323063757968911283)
              ·
                refine ⟨60368026984595636953366925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40245351323063757968911283 60368026984595636953366925)
                ·
                  refine ⟨22638010119223363857512597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60368026984595636953366925 22638010119223363857512597)
                  ·
                    refine ⟨1061156724338595180820903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22638010119223363857512597 1061156724338595180820903)
                    ·
                      rfl

theorem cell23_6199786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 3, 6].length) (baseStart_6199786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6199786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6199786 prefixEnd_6199786 := by exact prefixLift 6199786
  have htrace : WordTrace (prefixWord ++ tailWord_6199786) baseStart_6199786 baseEnd_6199786 := by
    simpa [prefixWord, tailWord_6199786, baseEnd_6199786] using wordTrace_append hprefix tailTrace_6199786
  have hstable : (prefixWord ++ tailWord_6199786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6199786).length < 2 ^ (prefixWord ++ tailWord_6199786).sum := by decide
  have hdescent : baseEnd_6199786 < baseStart_6199786 := by decide
  rcases family_descends (prefixWord ++ tailWord_6199786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6199790 : List Nat := [4, 1, 2, 1, 2, 3, 3, 1, 1, 5]
def baseStart_6199790 : Nat := 118140960795 + 6199790 * 2 ^ 59
def prefixEnd_6199790 : Nat := 4983230072969 + 3 ^ 40 * 6199790 * 2
def baseEnd_6199790 : Nat := 1061157408979467842270897

theorem tailTrace_6199790 : CollatzResearch.WordTrace tailWord_6199790 prefixEnd_6199790 1061157408979467842270897 := by
  unfold tailWord_6199790
  simp only [CollatzResearch.WordTrace]
  refine ⟨28265614776153393084820603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150749945472818096452376549 28265614776153393084820603)
  ·
    refine ⟨42398422164230089627230905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28265614776153393084820603 42398422164230089627230905)
    ·
      refine ⟨31798816623172567220423179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42398422164230089627230905 31798816623172567220423179)
      ·
        refine ⟨47698224934758850830634769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31798816623172567220423179 47698224934758850830634769)
        ·
          refine ⟨35773668701069138122976077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47698224934758850830634769 35773668701069138122976077)
          ·
            refine ⟨13415125762900926796116029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35773668701069138122976077 13415125762900926796116029)
            ·
              refine ⟨5030672161087847548543511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13415125762900926796116029 5030672161087847548543511)
              ·
                refine ⟨7546008241631771322815267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5030672161087847548543511 7546008241631771322815267)
                ·
                  refine ⟨11319012362447656984222901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7546008241631771322815267 11319012362447656984222901)
                  ·
                    refine ⟨1061157408979467842270897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11319012362447656984222901 1061157408979467842270897)
                    ·
                      rfl

theorem cell23_6199790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 3, 1, 1, 5].length) (baseStart_6199790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6199790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6199790 prefixEnd_6199790 := by exact prefixLift 6199790
  have htrace : WordTrace (prefixWord ++ tailWord_6199790) baseStart_6199790 baseEnd_6199790 := by
    simpa [prefixWord, tailWord_6199790, baseEnd_6199790] using wordTrace_append hprefix tailTrace_6199790
  have hstable : (prefixWord ++ tailWord_6199790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6199790).length < 2 ^ (prefixWord ++ tailWord_6199790).sum := by decide
  have hdescent : baseEnd_6199790 < baseStart_6199790 := by decide
  rcases family_descends (prefixWord ++ tailWord_6199790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6199843 : List Nat := [1, 1, 1, 4, 4, 1, 2, 2, 1, 3, 3]
def baseStart_6199843 : Nat := 118140960795 + 6199843 * 2 ^ 59
def prefixEnd_6199843 : Nat := 4983230072969 + 3 ^ 40 * 6199843 * 2
def baseEnd_6199843 : Nat := 3183499441413091819449947

theorem tailTrace_6199843 : CollatzResearch.WordTrace tailWord_6199843 prefixEnd_6199843 3183499441413091819449947 := by
  unfold tailWord_6199843
  simp only [CollatzResearch.WordTrace]
  refine ⟨226126851278035134730244183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150751234185356756486829455 226126851278035134730244183)
  ·
    refine ⟨339190276917052702095366275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226126851278035134730244183 339190276917052702095366275)
    ·
      refine ⟨508785415375579053143049413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339190276917052702095366275 508785415375579053143049413)
      ·
        refine ⟨95397265382921072464321765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 508785415375579053143049413 95397265382921072464321765)
        ·
          refine ⟨17886987259297701087060331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95397265382921072464321765 17886987259297701087060331)
          ·
            refine ⟨26830480888946551630590497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17886987259297701087060331 26830480888946551630590497)
            ·
              refine ⟨20122860666709913722942873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26830480888946551630590497 20122860666709913722942873)
              ·
                refine ⟨15092145500032435292207155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20122860666709913722942873 15092145500032435292207155)
                ·
                  refine ⟨22638218250048652938310733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15092145500032435292207155 22638218250048652938310733)
                  ·
                    refine ⟨8489331843768244851866525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22638218250048652938310733 8489331843768244851866525)
                    ·
                      refine ⟨3183499441413091819449947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8489331843768244851866525 3183499441413091819449947)
                      ·
                        rfl

theorem cell23_6199843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 2, 1, 3, 3].length) (baseStart_6199843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6199843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6199843 prefixEnd_6199843 := by exact prefixLift 6199843
  have htrace : WordTrace (prefixWord ++ tailWord_6199843) baseStart_6199843 baseEnd_6199843 := by
    simpa [prefixWord, tailWord_6199843, baseEnd_6199843] using wordTrace_append hprefix tailTrace_6199843
  have hstable : (prefixWord ++ tailWord_6199843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6199843).length < 2 ^ (prefixWord ++ tailWord_6199843).sum := by decide
  have hdescent : baseEnd_6199843 < baseStart_6199843 := by decide
  rcases family_descends (prefixWord ++ tailWord_6199843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6199844 : List Nat := [2, 3, 1, 5, 1, 2, 2, 1, 1, 1, 4]
def baseStart_6199844 : Nat := 118140960795 + 6199844 * 2 ^ 59
def prefixEnd_6199844 : Nat := 4983230072969 + 3 ^ 40 * 6199844 * 2
def baseEnd_6199844 : Nat := 3183499954893746315537443

theorem tailTrace_6199844 : CollatzResearch.WordTrace tailWord_6199844 prefixEnd_6199844 3183499954893746315537443 := by
  unfold tailWord_6199844
  simp only [CollatzResearch.WordTrace]
  refine ⟨113063443875515755950515293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150751258500687674600687057 113063443875515755950515293)
  ·
    refine ⟨42398791453318408481443235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113063443875515755950515293 42398791453318408481443235)
    ·
      refine ⟨63598187179977612722164853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42398791453318408481443235 63598187179977612722164853)
      ·
        refine ⟨5962330048122901192702955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63598187179977612722164853 5962330048122901192702955)
        ·
          refine ⟨8943495072184351789054433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5962330048122901192702955 8943495072184351789054433)
          ·
            refine ⟨6707621304138263841790825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8943495072184351789054433 6707621304138263841790825)
            ·
              refine ⟨5030715978103697881343119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6707621304138263841790825 5030715978103697881343119)
              ·
                refine ⟨7546073967155546822014679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5030715978103697881343119 7546073967155546822014679)
                ·
                  refine ⟨11319110950733320233022019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7546073967155546822014679 11319110950733320233022019)
                  ·
                    refine ⟨16978666426099980349533029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11319110950733320233022019 16978666426099980349533029)
                    ·
                      refine ⟨3183499954893746315537443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16978666426099980349533029 3183499954893746315537443)
                      ·
                        rfl

theorem cell23_6199844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_6199844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6199844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6199844 prefixEnd_6199844 := by exact prefixLift 6199844
  have htrace : WordTrace (prefixWord ++ tailWord_6199844) baseStart_6199844 baseEnd_6199844 := by
    simpa [prefixWord, tailWord_6199844, baseEnd_6199844] using wordTrace_append hprefix tailTrace_6199844
  have hstable : (prefixWord ++ tailWord_6199844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6199844).length < 2 ^ (prefixWord ++ tailWord_6199844).sum := by decide
  have hdescent : baseEnd_6199844 < baseStart_6199844 := by decide
  rcases family_descends (prefixWord ++ tailWord_6199844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6199854 : List Nat := [4, 1, 3, 1, 4, 1, 1, 2, 2, 4]
def baseStart_6199854 : Nat := 118140960795 + 6199854 * 2 ^ 59
def prefixEnd_6199854 : Nat := 4983230072969 + 3 ^ 40 * 6199854 * 2
def baseEnd_6199854 : Nat := 1061168363233430425470799

theorem tailTrace_6199854 : CollatzResearch.WordTrace tailWord_6199854 prefixEnd_6199854 1061168363233430425470799 := by
  unfold tailWord_6199854
  simp only [CollatzResearch.WordTrace]
  refine ⟨28265906560124410451111827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150751501653996855739263077 28265906560124410451111827)
  ·
    refine ⟨42398859840186615676667741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28265906560124410451111827 42398859840186615676667741)
    ·
      refine ⟨15899572440069980878750403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42398859840186615676667741 15899572440069980878750403)
      ·
        refine ⟨23849358660104971318125605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15899572440069980878750403 23849358660104971318125605)
        ·
          refine ⟨4471754748769682122148551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23849358660104971318125605 4471754748769682122148551)
          ·
            refine ⟨6707632123154523183222827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4471754748769682122148551 6707632123154523183222827)
            ·
              refine ⟨10061448184731784774834241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6707632123154523183222827 10061448184731784774834241)
              ·
                refine ⟨7546086138548838581125681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10061448184731784774834241 7546086138548838581125681)
                ·
                  refine ⟨5659564603911628935844261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7546086138548838581125681 5659564603911628935844261)
                  ·
                    refine ⟨1061168363233430425470799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5659564603911628935844261 1061168363233430425470799)
                    ·
                      rfl

theorem cell23_6199854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_6199854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6199854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6199854 prefixEnd_6199854 := by exact prefixLift 6199854
  have htrace : WordTrace (prefixWord ++ tailWord_6199854) baseStart_6199854 baseEnd_6199854 := by
    simpa [prefixWord, tailWord_6199854, baseEnd_6199854] using wordTrace_append hprefix tailTrace_6199854
  have hstable : (prefixWord ++ tailWord_6199854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6199854).length < 2 ^ (prefixWord ++ tailWord_6199854).sum := by decide
  have hdescent : baseEnd_6199854 < baseStart_6199854 := by decide
  rcases family_descends (prefixWord ++ tailWord_6199854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6199877 : List Nat := [1, 3, 1, 1, 1, 6, 3, 1, 2, 1, 3]
def baseStart_6199877 : Nat := 118140960795 + 6199877 * 2 ^ 59
def prefixEnd_6199877 : Nat := 4983230072969 + 3 ^ 40 * 6199877 * 2
def baseEnd_6199877 : Nat := 3183516899755344686424791

theorem tailTrace_6199877 : CollatzResearch.WordTrace tailWord_6199877 prefixEnd_6199877 3183516899755344686424791 := by
  unfold tailWord_6199877
  simp only [CollatzResearch.WordTrace]
  refine ⟨226128091359911958536981885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150752060906607972357987923 226128091359911958536981885)
  ·
    refine ⟨84798034259966984451368207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226128091359911958536981885 84798034259966984451368207)
    ·
      refine ⟨127197051389950476677052311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84798034259966984451368207 127197051389950476677052311)
      ·
        refine ⟨190795577084925715015578467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127197051389950476677052311 190795577084925715015578467)
        ·
          refine ⟨286193365627388572523367701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190795577084925715015578467 286193365627388572523367701)
          ·
            refine ⟨13415314013783839337032861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 286193365627388572523367701 13415314013783839337032861)
            ·
              refine ⟨5030742755168939751387323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13415314013783839337032861 5030742755168939751387323)
              ·
                refine ⟨7546114132753409627080985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5030742755168939751387323 7546114132753409627080985)
                ·
                  refine ⟨5659585599565057220310739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7546114132753409627080985 5659585599565057220310739)
                  ·
                    refine ⟨8489378399347585830466109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5659585599565057220310739 8489378399347585830466109)
                    ·
                      refine ⟨3183516899755344686424791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8489378399347585830466109 3183516899755344686424791)
                      ·
                        rfl

theorem cell23_6199877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 3, 1, 2, 1, 3].length) (baseStart_6199877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6199877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6199877 prefixEnd_6199877 := by exact prefixLift 6199877
  have htrace : WordTrace (prefixWord ++ tailWord_6199877) baseStart_6199877 baseEnd_6199877 := by
    simpa [prefixWord, tailWord_6199877, baseEnd_6199877] using wordTrace_append hprefix tailTrace_6199877
  have hstable : (prefixWord ++ tailWord_6199877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6199877).length < 2 ^ (prefixWord ++ tailWord_6199877).sum := by decide
  have hdescent : baseEnd_6199877 < baseStart_6199877 := by decide
  rcases family_descends (prefixWord ++ tailWord_6199877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6199896 : List Nat := [2, 1, 2, 2, 1, 2, 2, 2, 1, 4, 4]
def baseStart_6199896 : Nat := 118140960795 + 6199896 * 2 ^ 59
def prefixEnd_6199896 : Nat := 4983230072969 + 3 ^ 40 * 6199896 * 2
def baseEnd_6199896 : Nat := 3183526655887780112087203

theorem tailTrace_6199896 : CollatzResearch.WordTrace tailWord_6199896 prefixEnd_6199896 3183526655887780112087203 := by
  unfold tailWord_6199896
  simp only [CollatzResearch.WordTrace]
  refine ⟨113064392173421562390961771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150752522897895416521282361 113064392173421562390961771)
  ·
    refine ⟨169596588260132343586442657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113064392173421562390961771 169596588260132343586442657)
    ·
      refine ⟨127197441195099257689831993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169596588260132343586442657 127197441195099257689831993)
      ·
        refine ⟨95398080896324443267373995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127197441195099257689831993 95398080896324443267373995)
        ·
          refine ⟨143097121344486664901060993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95398080896324443267373995 143097121344486664901060993)
          ·
            refine ⟨107322841008364998675795745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143097121344486664901060993 107322841008364998675795745)
            ·
              refine ⟨80492130756273749006846809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107322841008364998675795745 80492130756273749006846809)
              ·
                refine ⟨60369098067205311755135107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80492130756273749006846809 60369098067205311755135107)
                ·
                  refine ⟨90553647100807967632702661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60369098067205311755135107 90553647100807967632702661)
                  ·
                    refine ⟨16978808831401493931131749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 90553647100807967632702661 16978808831401493931131749)
                    ·
                      refine ⟨3183526655887780112087203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16978808831401493931131749 3183526655887780112087203)
                      ·
                        rfl

theorem cell23_6199896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 1, 4, 4].length) (baseStart_6199896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6199896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6199896 prefixEnd_6199896 := by exact prefixLift 6199896
  have htrace : WordTrace (prefixWord ++ tailWord_6199896) baseStart_6199896 baseEnd_6199896 := by
    simpa [prefixWord, tailWord_6199896, baseEnd_6199896] using wordTrace_append hprefix tailTrace_6199896
  have hstable : (prefixWord ++ tailWord_6199896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6199896).length < 2 ^ (prefixWord ++ tailWord_6199896).sum := by decide
  have hdescent : baseEnd_6199896 < baseStart_6199896 := by decide
  rcases family_descends (prefixWord ++ tailWord_6199896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6199917 : List Nat := [1, 5, 1, 1, 3, 1, 2, 1, 4, 2, 2]
def baseStart_6199917 : Nat := 118140960795 + 6199917 * 2 ^ 59
def prefixEnd_6199917 : Nat := 4983230072969 + 3 ^ 40 * 6199917 * 2
def baseEnd_6199917 : Nat := 3183537438981524529924607

theorem tailTrace_6199917 : CollatzResearch.WordTrace tailWord_6199917 prefixEnd_6199917 3183537438981524529924607 := by
  unfold tailWord_6199917
  simp only [CollatzResearch.WordTrace]
  refine ⟨226129550279767045368438005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150753033519844696912292003 226129550279767045368438005)
  ·
    refine ⟨21199645338728160503291063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 226129550279767045368438005 21199645338728160503291063)
    ·
      refine ⟨31799468008092240754936595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21199645338728160503291063 31799468008092240754936595)
      ·
        refine ⟨47699202012138361132404893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31799468008092240754936595 47699202012138361132404893)
        ·
          refine ⟨17887200754551885424651835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47699202012138361132404893 17887200754551885424651835)
          ·
            refine ⟨26830801131827828136977753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17887200754551885424651835 26830801131827828136977753)
            ·
              refine ⟨20123100848870871102733315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26830801131827828136977753 20123100848870871102733315)
              ·
                refine ⟨30184651273306306654099973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20123100848870871102733315 30184651273306306654099973)
                ·
                  refine ⟨5659622113744932497643745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30184651273306306654099973 5659622113744932497643745)
                  ·
                    refine ⟨4244716585308699373232809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5659622113744932497643745 4244716585308699373232809)
                    ·
                      refine ⟨3183537438981524529924607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4244716585308699373232809 3183537438981524529924607)
                      ·
                        rfl

theorem cell23_6199917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 1, 4, 2, 2].length) (baseStart_6199917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6199917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6199917 prefixEnd_6199917 := by exact prefixLift 6199917
  have htrace : WordTrace (prefixWord ++ tailWord_6199917) baseStart_6199917 baseEnd_6199917 := by
    simpa [prefixWord, tailWord_6199917, baseEnd_6199917] using wordTrace_append hprefix tailTrace_6199917
  have hstable : (prefixWord ++ tailWord_6199917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6199917).length < 2 ^ (prefixWord ++ tailWord_6199917).sum := by decide
  have hdescent : baseEnd_6199917 < baseStart_6199917 := by decide
  rcases family_descends (prefixWord ++ tailWord_6199917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6199993 : List Nat := [1, 2, 1, 4, 1, 1, 1, 4, 1, 4, 3]
def baseStart_6199993 : Nat := 118140960795 + 6199993 * 2 ^ 59
def prefixEnd_6199993 : Nat := 4983230072969 + 3 ^ 40 * 6199993 * 2
def baseEnd_6199993 : Nat := 3183576463511266232574257

theorem tailTrace_6199993 : CollatzResearch.WordTrace tailWord_6199993 prefixEnd_6199993 3183576463511266232574257 := by
  unfold tailWord_6199993
  simp only [CollatzResearch.WordTrace]
  refine ⟨226132322227491710348204633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150754881484994473565469755 226132322227491710348204633)
  ·
    refine ⟨169599241670618782761153475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226132322227491710348204633 169599241670618782761153475)
    ·
      refine ⟨254398862505928174141730213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169599241670618782761153475 254398862505928174141730213)
      ·
        refine ⟨47699786719861532651574415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 254398862505928174141730213 47699786719861532651574415)
        ·
          refine ⟨71549680079792298977361623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47699786719861532651574415 71549680079792298977361623)
          ·
            refine ⟨107324520119688448466042435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71549680079792298977361623 107324520119688448466042435)
            ·
              refine ⟨160986780179532672699063653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107324520119688448466042435 160986780179532672699063653)
              ·
                refine ⟨30185021283662376131074435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 160986780179532672699063653 30185021283662376131074435)
                ·
                  refine ⟨45277531925493564196611653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30185021283662376131074435 45277531925493564196611653)
                  ·
                    refine ⟨8489537236030043286864685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45277531925493564196611653 8489537236030043286864685)
                    ·
                      refine ⟨3183576463511266232574257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8489537236030043286864685 3183576463511266232574257)
                      ·
                        rfl

theorem cell23_6199993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 4, 1, 4, 3].length) (baseStart_6199993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6199993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6199993 prefixEnd_6199993 := by exact prefixLift 6199993
  have htrace : WordTrace (prefixWord ++ tailWord_6199993) baseStart_6199993 baseEnd_6199993 := by
    simpa [prefixWord, tailWord_6199993, baseEnd_6199993] using wordTrace_append hprefix tailTrace_6199993
  have hstable : (prefixWord ++ tailWord_6199993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6199993).length < 2 ^ (prefixWord ++ tailWord_6199993).sum := by decide
  have hdescent : baseEnd_6199993 < baseStart_6199993 := by decide
  rcases family_descends (prefixWord ++ tailWord_6199993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6200000 : List Nat := [2, 1, 1, 2, 4, 3, 1, 2, 3, 4]
def baseStart_6200000 : Nat := 118140960795 + 6200000 * 2 ^ 59
def prefixEnd_6200000 : Nat := 4983230072969 + 3 ^ 40 * 6200000 * 2
def baseEnd_6200000 : Nat := 1061193352625282568395575

theorem tailTrace_6200000 : CollatzResearch.WordTrace tailWord_6200000 prefixEnd_6200000 1061193352625282568395575 := by
  unfold tailWord_6200000
  simp only [CollatzResearch.WordTrace]
  refine ⟨113066288769233175271854727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150755051692310900362472969 113066288769233175271854727)
  ·
    refine ⟨169599433153849762907782091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113066288769233175271854727 169599433153849762907782091)
    ·
      refine ⟨254399149730774644361673137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169599433153849762907782091 254399149730774644361673137)
      ·
        refine ⟨190799362298080983271254853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 254399149730774644361673137 190799362298080983271254853)
        ·
          refine ⟨35774880430890184363360285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 190799362298080983271254853 35774880430890184363360285)
          ·
            refine ⟨13415580161583819136260107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35774880430890184363360285 13415580161583819136260107)
            ·
              refine ⟨20123370242375728704390161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13415580161583819136260107 20123370242375728704390161)
              ·
                refine ⟨15092527681781796528292621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20123370242375728704390161 15092527681781796528292621)
                ·
                  refine ⟨5659697880668173698109733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15092527681781796528292621 5659697880668173698109733)
                  ·
                    refine ⟨1061193352625282568395575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5659697880668173698109733 1061193352625282568395575)
                    ·
                      rfl

theorem cell23_6200000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 2, 3, 4].length) (baseStart_6200000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6200000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6200000 prefixEnd_6200000 := by exact prefixLift 6200000
  have htrace : WordTrace (prefixWord ++ tailWord_6200000) baseStart_6200000 baseEnd_6200000 := by
    simpa [prefixWord, tailWord_6200000, baseEnd_6200000] using wordTrace_append hprefix tailTrace_6200000
  have hstable : (prefixWord ++ tailWord_6200000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6200000).length < 2 ^ (prefixWord ++ tailWord_6200000).sum := by decide
  have hdescent : baseEnd_6200000 < baseStart_6200000 := by decide
  rcases family_descends (prefixWord ++ tailWord_6200000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6200010 : List Nat := [3, 1, 2, 1, 4, 2, 1, 1, 1, 4, 3]
def baseStart_6200010 : Nat := 118140960795 + 6200010 * 2 ^ 59
def prefixEnd_6200010 : Nat := 4983230072969 + 3 ^ 40 * 6200010 * 2
def baseEnd_6200010 : Nat := 3183585192682392666061679

theorem tailTrace_6200010 : CollatzResearch.WordTrace tailWord_6200010 prefixEnd_6200010 3183585192682392666061679 := by
  unfold tailWord_6200010
  simp only [CollatzResearch.WordTrace]
  refine ⟨56533235567107530562893371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150755294845620081501048989 56533235567107530562893371)
  ·
    refine ⟨84799853350661295844340057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56533235567107530562893371 84799853350661295844340057)
    ·
      refine ⟨63599890012995971883255043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84799853350661295844340057 63599890012995971883255043)
      ·
        refine ⟨95399835019493957824882565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63599890012995971883255043 95399835019493957824882565)
        ·
          refine ⟨17887469066155117092165481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95399835019493957824882565 17887469066155117092165481)
          ·
            refine ⟨13415601799616337819124111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17887469066155117092165481 13415601799616337819124111)
            ·
              refine ⟨20123402699424506728686167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13415601799616337819124111 20123402699424506728686167)
              ·
                refine ⟨30185104049136760093029251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20123402699424506728686167 30185104049136760093029251)
                ·
                  refine ⟨45277656073705140139543877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30185104049136760093029251 45277656073705140139543877)
                  ·
                    refine ⟨8489560513819713776164477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45277656073705140139543877 8489560513819713776164477)
                    ·
                      refine ⟨3183585192682392666061679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8489560513819713776164477 3183585192682392666061679)
                      ·
                        rfl

theorem cell23_6200010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 1, 1, 4, 3].length) (baseStart_6200010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6200010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6200010 prefixEnd_6200010 := by exact prefixLift 6200010
  have htrace : WordTrace (prefixWord ++ tailWord_6200010) baseStart_6200010 baseEnd_6200010 := by
    simpa [prefixWord, tailWord_6200010, baseEnd_6200010] using wordTrace_append hprefix tailTrace_6200010
  have hstable : (prefixWord ++ tailWord_6200010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6200010).length < 2 ^ (prefixWord ++ tailWord_6200010).sum := by decide
  have hdescent : baseEnd_6200010 < baseStart_6200010 := by decide
  rcases family_descends (prefixWord ++ tailWord_6200010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6200017 : List Nat := [1, 2, 2, 1, 2, 3, 4, 3, 1, 4]
def baseStart_6200017 : Nat := 118140960795 + 6200017 * 2 ^ 59
def prefixEnd_6200017 : Nat := 4983230072969 + 3 ^ 40 * 6200017 * 2
def baseEnd_6200017 : Nat := 1061196262348991379558049

theorem tailTrace_6200017 : CollatzResearch.WordTrace tailWord_6200017 prefixEnd_6200017 1061196262348991379558049 := by
  unfold tailWord_6200017
  simp only [CollatzResearch.WordTrace]
  refine ⟨226133197579404762447078305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150755465052936508298052203 226133197579404762447078305)
  ·
    refine ⟨169599898184553571835308729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226133197579404762447078305 169599898184553571835308729)
    ·
      refine ⟨127199923638415178876481547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169599898184553571835308729 127199923638415178876481547)
      ·
        refine ⟨190799885457622768314722321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127199923638415178876481547 190799885457622768314722321)
        ·
          refine ⟨143099914093217076236041741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190799885457622768314722321 143099914093217076236041741)
          ·
            refine ⟨53662467784956403588515653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143099914093217076236041741 53662467784956403588515653)
            ·
              refine ⟨10061712709679325672846685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53662467784956403588515653 10061712709679325672846685)
              ·
                refine ⟨3773142266129747127317507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10061712709679325672846685 3773142266129747127317507)
                ·
                  refine ⟨5659713399194620690976261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3773142266129747127317507 5659713399194620690976261)
                  ·
                    refine ⟨1061196262348991379558049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5659713399194620690976261 1061196262348991379558049)
                    ·
                      rfl

theorem cell23_6200017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 3, 1, 4].length) (baseStart_6200017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6200017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6200017 prefixEnd_6200017 := by exact prefixLift 6200017
  have htrace : WordTrace (prefixWord ++ tailWord_6200017) baseStart_6200017 baseEnd_6200017 := by
    simpa [prefixWord, tailWord_6200017, baseEnd_6200017] using wordTrace_append hprefix tailTrace_6200017
  have hstable : (prefixWord ++ tailWord_6200017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6200017).length < 2 ^ (prefixWord ++ tailWord_6200017).sum := by decide
  have hdescent : baseEnd_6200017 < baseStart_6200017 := by decide
  rcases family_descends (prefixWord ++ tailWord_6200017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6200033 : List Nat := [1, 2, 3, 1, 4, 1, 1, 1, 1, 2, 6]
def baseStart_6200033 : Nat := 118140960795 + 6200033 * 2 ^ 59
def prefixEnd_6200033 : Nat := 4983230072969 + 3 ^ 40 * 6200033 * 2
def baseEnd_6200033 : Nat := 3183597002737446076074073

theorem tailTrace_6200033 : CollatzResearch.WordTrace tailWord_6200033 prefixEnd_6200033 3183597002737446076074073 := by
  unfold tailWord_6200033
  simp only [CollatzResearch.WordTrace]
  refine ⟨226133781147346797179660753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150755854098231198119773835 226133781147346797179660753)
  ·
    refine ⟨169600335860510097884745565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226133781147346797179660753 169600335860510097884745565)
    ·
      refine ⟨63600125947691286706779587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169600335860510097884745565 63600125947691286706779587)
      ·
        refine ⟨95400188921536930060169381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63600125947691286706779587 95400188921536930060169381)
        ·
          refine ⟨17887535422788174386281759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95400188921536930060169381 17887535422788174386281759)
          ·
            refine ⟨26831303134182261579422639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17887535422788174386281759 26831303134182261579422639)
            ·
              refine ⟨40246954701273392369133959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26831303134182261579422639 40246954701273392369133959)
              ·
                refine ⟨60370432051910088553700939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40246954701273392369133959 60370432051910088553700939)
                ·
                  refine ⟨90555648077865132830551409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60370432051910088553700939 90555648077865132830551409)
                  ·
                    refine ⟨67916736058398849622913557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 90555648077865132830551409 67916736058398849622913557)
                    ·
                      refine ⟨3183597002737446076074073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67916736058398849622913557 3183597002737446076074073)
                      ·
                        rfl

theorem cell23_6200033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 2, 6].length) (baseStart_6200033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6200033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6200033 prefixEnd_6200033 := by exact prefixLift 6200033
  have htrace : WordTrace (prefixWord ++ tailWord_6200033) baseStart_6200033 baseEnd_6200033 := by
    simpa [prefixWord, tailWord_6200033, baseEnd_6200033] using wordTrace_append hprefix tailTrace_6200033
  have hstable : (prefixWord ++ tailWord_6200033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6200033).length < 2 ^ (prefixWord ++ tailWord_6200033).sum := by decide
  have hdescent : baseEnd_6200033 < baseStart_6200033 := by decide
  rcases family_descends (prefixWord ++ tailWord_6200033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6200060 : List Nat := [2, 2, 2, 1, 3, 2, 1, 4, 1, 5]
def baseStart_6200060 : Nat := 118140960795 + 6200060 * 2 ^ 59
def prefixEnd_6200060 : Nat := 4983230072969 + 3 ^ 40 * 6200060 * 2
def baseEnd_6200060 : Nat := 1061203622238372490145483

theorem tailTrace_6200060 : CollatzResearch.WordTrace tailWord_6200060 prefixEnd_6200060 1061203622238372490145483 := by
  unfold tailWord_6200060
  simp only [CollatzResearch.WordTrace]
  refine ⟨113067382959124490395446817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150756510612165987193929089 113067382959124490395446817)
  ·
    refine ⟨84800537219343367796585113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113067382959124490395446817 84800537219343367796585113)
    ·
      refine ⟨63600402914507525847438835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84800537219343367796585113 63600402914507525847438835)
      ·
        refine ⟨95400604371761288771158253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63600402914507525847438835 95400604371761288771158253)
        ·
          refine ⟨35775226639410483289184345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95400604371761288771158253 35775226639410483289184345)
          ·
            refine ⟨26831419979557862466888259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35775226639410483289184345 26831419979557862466888259)
            ·
              refine ⟨40247129969336793700332389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26831419979557862466888259 40247129969336793700332389)
              ·
                refine ⟨7546336869250648818812323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40247129969336793700332389 7546336869250648818812323)
                ·
                  refine ⟨11319505303875973228218485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7546336869250648818812323 11319505303875973228218485)
                  ·
                    refine ⟨1061203622238372490145483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11319505303875973228218485 1061203622238372490145483)
                    ·
                      rfl

theorem cell23_6200060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 4, 1, 5].length) (baseStart_6200060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6200060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6200060 prefixEnd_6200060 := by exact prefixLift 6200060
  have htrace : WordTrace (prefixWord ++ tailWord_6200060) baseStart_6200060 baseEnd_6200060 := by
    simpa [prefixWord, tailWord_6200060, baseEnd_6200060] using wordTrace_append hprefix tailTrace_6200060
  have hstable : (prefixWord ++ tailWord_6200060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6200060).length < 2 ^ (prefixWord ++ tailWord_6200060).sum := by decide
  have hdescent : baseEnd_6200060 < baseStart_6200060 := by decide
  rcases family_descends (prefixWord ++ tailWord_6200060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6200073 : List Nat := [1, 2, 1, 1, 3, 2, 2, 4, 1, 6]
def baseStart_6200073 : Nat := 118140960795 + 6200073 * 2 ^ 59
def prefixEnd_6200073 : Nat := 4983230072969 + 3 ^ 40 * 6200073 * 2
def baseEnd_6200073 : Nat := 1061205847321208639857963

theorem tailTrace_6200073 : CollatzResearch.WordTrace tailWord_6200073 prefixEnd_6200073 1061205847321208639857963 := by
  unfold tailWord_6200073
  simp only [CollatzResearch.WordTrace]
  refine ⟨226135240067201884011116873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150756826711467922674077915 226135240067201884011116873)
  ·
    refine ⟨169601430050401413008337655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226135240067201884011116873 169601430050401413008337655)
    ·
      refine ⟨254402145075602119512506483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169601430050401413008337655 254402145075602119512506483)
      ·
        refine ⟨381603217613403179268759725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254402145075602119512506483 381603217613403179268759725)
        ·
          refine ⟨143101206605026192225784897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 381603217613403179268759725 143101206605026192225784897)
          ·
            refine ⟨107325904953769644169338673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143101206605026192225784897 107325904953769644169338673)
            ·
              refine ⟨80494428715327233127004005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107325904953769644169338673 80494428715327233127004005)
              ·
                refine ⟨15092705384123856211313251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80494428715327233127004005 15092705384123856211313251)
                ·
                  refine ⟨22639058076185784316969877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15092705384123856211313251 22639058076185784316969877)
                  ·
                    refine ⟨1061205847321208639857963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22639058076185784316969877 1061205847321208639857963)
                    ·
                      rfl

theorem cell23_6200073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 4, 1, 6].length) (baseStart_6200073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6200073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6200073 prefixEnd_6200073 := by exact prefixLift 6200073
  have htrace : WordTrace (prefixWord ++ tailWord_6200073) baseStart_6200073 baseEnd_6200073 := by
    simpa [prefixWord, tailWord_6200073, baseEnd_6200073] using wordTrace_append hprefix tailTrace_6200073
  have hstable : (prefixWord ++ tailWord_6200073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6200073).length < 2 ^ (prefixWord ++ tailWord_6200073).sum := by decide
  have hdescent : baseEnd_6200073 < baseStart_6200073 := by decide
  rcases family_descends (prefixWord ++ tailWord_6200073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6200090 : List Nat := [3, 1, 1, 3, 2, 1, 1, 3, 4, 4]
def baseStart_6200090 : Nat := 118140960795 + 6200090 * 2 ^ 59
def prefixEnd_6200090 : Nat := 4983230072969 + 3 ^ 40 * 6200090 * 2
def baseEnd_6200090 : Nat := 1061208757044917451020437

theorem tailTrace_6200090 : CollatzResearch.WordTrace tailWord_6200090 prefixEnd_6200090 1061208757044917451020437 := by
  unfold tailWord_6200090
  simp only [CollatzResearch.WordTrace]
  refine ⟨56533965027035073978621431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150757240072093530609657149 56533965027035073978621431)
  ·
    refine ⟨84800947540552610967932147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56533965027035073978621431 84800947540552610967932147)
    ·
      refine ⟨127201421310828916451898221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84800947540552610967932147 127201421310828916451898221)
      ·
        refine ⟨47700532991560843669461833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127201421310828916451898221 47700532991560843669461833)
        ·
          refine ⟨35775399743670632752096375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47700532991560843669461833 35775399743670632752096375)
          ·
            refine ⟨53663099615505949128144563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35775399743670632752096375 53663099615505949128144563)
            ·
              refine ⟨80494649423258923692216845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53663099615505949128144563 80494649423258923692216845)
              ·
                refine ⟨30185493533722096384581317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80494649423258923692216845 30185493533722096384581317)
                ·
                  refine ⟨5659780037572893072108997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30185493533722096384581317 5659780037572893072108997)
                  ·
                    refine ⟨1061208757044917451020437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5659780037572893072108997 1061208757044917451020437)
                    ·
                      rfl

theorem cell23_6200090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 3, 4, 4].length) (baseStart_6200090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6200090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6200090 prefixEnd_6200090 := by exact prefixLift 6200090
  have htrace : WordTrace (prefixWord ++ tailWord_6200090) baseStart_6200090 baseEnd_6200090 := by
    simpa [prefixWord, tailWord_6200090, baseEnd_6200090] using wordTrace_append hprefix tailTrace_6200090
  have hstable : (prefixWord ++ tailWord_6200090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6200090).length < 2 ^ (prefixWord ++ tailWord_6200090).sum := by decide
  have hdescent : baseEnd_6200090 < baseStart_6200090 := by decide
  rcases family_descends (prefixWord ++ tailWord_6200090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6200117 : List Nat := [1, 3, 3, 1, 3, 2, 1, 1, 3, 2, 3]
def baseStart_6200117 : Nat := 118140960795 + 6200117 * 2 ^ 59
def prefixEnd_6200117 : Nat := 4983230072969 + 3 ^ 40 * 6200117 * 2
def baseEnd_6200117 : Nat := 3183640135112423747423687

theorem tailTrace_6200117 : CollatzResearch.WordTrace tailWord_6200117 prefixEnd_6200117 3183640135112423747423687 := by
  unfold tailWord_6200117
  simp only [CollatzResearch.WordTrace]
  refine ⟨226136844879042479525718605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150757896586028319683812403 226136844879042479525718605)
  ·
    refine ⟨84801316829640929822144477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226136844879042479525718605 84801316829640929822144477)
    ·
      refine ⟨31800493811115348683304179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84801316829640929822144477 31800493811115348683304179)
      ·
        refine ⟨47700740716673023024956269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31800493811115348683304179 47700740716673023024956269)
        ·
          refine ⟨17887777768752383634358601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47700740716673023024956269 17887777768752383634358601)
          ·
            refine ⟨13415833326564287725768951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17887777768752383634358601 13415833326564287725768951)
            ·
              refine ⟨20123749989846431588653427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13415833326564287725768951 20123749989846431588653427)
              ·
                refine ⟨30185624984769647382980141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20123749989846431588653427 30185624984769647382980141)
                ·
                  refine ⟨11319609369288617768617553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30185624984769647382980141 11319609369288617768617553)
                  ·
                    refine ⟨8489707026966463326463165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11319609369288617768617553 8489707026966463326463165)
                    ·
                      refine ⟨3183640135112423747423687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8489707026966463326463165 3183640135112423747423687)
                      ·
                        rfl

theorem cell23_6200117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 1, 3, 2, 3].length) (baseStart_6200117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6200117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6200117 prefixEnd_6200117 := by exact prefixLift 6200117
  have htrace : WordTrace (prefixWord ++ tailWord_6200117) baseStart_6200117 baseEnd_6200117 := by
    simpa [prefixWord, tailWord_6200117, baseEnd_6200117] using wordTrace_append hprefix tailTrace_6200117
  have hstable : (prefixWord ++ tailWord_6200117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6200117).length < 2 ^ (prefixWord ++ tailWord_6200117).sum := by decide
  have hdescent : baseEnd_6200117 < baseStart_6200117 := by decide
  rcases family_descends (prefixWord ++ tailWord_6200117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6200141 : List Nat := [1, 6, 1, 2, 2, 1, 2, 2, 2, 4]
def baseStart_6200141 : Nat := 118140960795 + 6200141 * 2 ^ 59
def prefixEnd_6200141 : Nat := 4983230072969 + 3 ^ 40 * 6200141 * 2
def baseEnd_6200141 : Nat := 1061217486216043884507859

theorem tailTrace_6200141 : CollatzResearch.WordTrace tailWord_6200141 prefixEnd_6200141 1061217486216043884507859 := by
  unfold tailWord_6200141
  simp only [CollatzResearch.WordTrace]
  refine ⟨226137720230955531624592277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150758480153970354416394851 226137720230955531624592277)
  ·
    refine ⟨10600205635826040544902763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 226137720230955531624592277 10600205635826040544902763)
    ·
      refine ⟨15900308453739060817354145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10600205635826040544902763 15900308453739060817354145)
      ·
        refine ⟨11925231340304295613015609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15900308453739060817354145 11925231340304295613015609)
        ·
          refine ⟨8943923505228221709761707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11925231340304295613015609 8943923505228221709761707)
          ·
            refine ⟨13415885257842332564642561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8943923505228221709761707 13415885257842332564642561)
            ·
              refine ⟨10061913943381749423481921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13415885257842332564642561 10061913943381749423481921)
              ·
                refine ⟨7546435457536312067611441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10061913943381749423481921 7546435457536312067611441)
                ·
                  refine ⟨5659826593152234050708581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7546435457536312067611441 5659826593152234050708581)
                  ·
                    refine ⟨1061217486216043884507859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5659826593152234050708581 1061217486216043884507859)
                    ·
                      rfl

theorem cell23_6200141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_6200141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6200141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6200141 prefixEnd_6200141 := by exact prefixLift 6200141
  have htrace : WordTrace (prefixWord ++ tailWord_6200141) baseStart_6200141 baseEnd_6200141 := by
    simpa [prefixWord, tailWord_6200141, baseEnd_6200141] using wordTrace_append hprefix tailTrace_6200141
  have hstable : (prefixWord ++ tailWord_6200141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6200141).length < 2 ^ (prefixWord ++ tailWord_6200141).sum := by decide
  have hdescent : baseEnd_6200141 < baseStart_6200141 := by decide
  rcases family_descends (prefixWord ++ tailWord_6200141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6200148 : List Nat := [2, 4, 1, 1, 4, 1, 1, 4, 1, 2, 2]
def baseStart_6200148 : Nat := 118140960795 + 6200148 * 2 ^ 59
def prefixEnd_6200148 : Nat := 4983230072969 + 3 ^ 40 * 6200148 * 2
def baseEnd_6200148 : Nat := 3183656053012713126136045

theorem tailTrace_6200148 : CollatzResearch.WordTrace tailWord_6200148 prefixEnd_6200148 3183656053012713126136045 := by
  unfold tailWord_6200148
  simp only [CollatzResearch.WordTrace]
  refine ⟨113068987770965085910048549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150758650361286781213398065 113068987770965085910048549)
  ·
    refine ⟨21200435207055953608134103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113068987770965085910048549 21200435207055953608134103)
    ·
      refine ⟨31800652810583930412201155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21200435207055953608134103 31800652810583930412201155)
      ·
        refine ⟨47700979215875895618301733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31800652810583930412201155 47700979215875895618301733)
        ·
          refine ⟨8943933602976730428431575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47700979215875895618301733 8943933602976730428431575)
          ·
            refine ⟨13415900404465095642647363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8943933602976730428431575 13415900404465095642647363)
            ·
              refine ⟨20123850606697643463971045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13415900404465095642647363 20123850606697643463971045)
              ·
                refine ⟨3773221988755808149494571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20123850606697643463971045 3773221988755808149494571)
                ·
                  refine ⟨5659832983133712224241857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3773221988755808149494571 5659832983133712224241857)
                  ·
                    refine ⟨4244874737350284168181393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5659832983133712224241857 4244874737350284168181393)
                    ·
                      refine ⟨3183656053012713126136045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4244874737350284168181393 3183656053012713126136045)
                      ·
                        rfl

theorem cell23_6200148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 4, 1, 2, 2].length) (baseStart_6200148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6200148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6200148 prefixEnd_6200148 := by exact prefixLift 6200148
  have htrace : WordTrace (prefixWord ++ tailWord_6200148) baseStart_6200148 baseEnd_6200148 := by
    simpa [prefixWord, tailWord_6200148, baseEnd_6200148] using wordTrace_append hprefix tailTrace_6200148
  have hstable : (prefixWord ++ tailWord_6200148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6200148).length < 2 ^ (prefixWord ++ tailWord_6200148).sum := by decide
  have hdescent : baseEnd_6200148 < baseStart_6200148 := by decide
  rcases family_descends (prefixWord ++ tailWord_6200148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6200164 : List Nat := [2, 3, 1, 1, 4, 1, 2, 3, 2, 1, 3]
def baseStart_6200164 : Nat := 118140960795 + 6200164 * 2 ^ 59
def prefixEnd_6200164 : Nat := 4983230072969 + 3 ^ 40 * 6200164 * 2
def baseEnd_6200164 : Nat := 3183664268703185063535971

theorem tailTrace_6200164 : CollatzResearch.WordTrace tailWord_6200164 prefixEnd_6200164 3183664268703185063535971 := by
  unfold tailWord_6200164
  simp only [CollatzResearch.WordTrace]
  refine ⟨113069279554936103276339773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150759039406581471035119697 113069279554936103276339773)
  ·
    refine ⟨42400979833101038728627415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113069279554936103276339773 42400979833101038728627415)
    ·
      refine ⟨63601469749651558092941123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42400979833101038728627415 63601469749651558092941123)
      ·
        refine ⟨95402204624477337139411685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63601469749651558092941123 95402204624477337139411685)
        ·
          refine ⟨17887913367089500713639691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95402204624477337139411685 17887913367089500713639691)
          ·
            refine ⟨26831870050634251070459537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17887913367089500713639691 26831870050634251070459537)
            ·
              refine ⟨20123902537975688302844653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26831870050634251070459537 20123902537975688302844653)
              ·
                refine ⟨7546463451740883113566745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20123902537975688302844653 7546463451740883113566745)
                ·
                  refine ⟨5659847588805662335175059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7546463451740883113566745 5659847588805662335175059)
                  ·
                    refine ⟨8489771383208493502762589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5659847588805662335175059 8489771383208493502762589)
                    ·
                      refine ⟨3183664268703185063535971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8489771383208493502762589 3183664268703185063535971)
                      ·
                        rfl

theorem cell23_6200164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 3, 2, 1, 3].length) (baseStart_6200164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6200164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6200164 prefixEnd_6200164 := by exact prefixLift 6200164
  have htrace : WordTrace (prefixWord ++ tailWord_6200164) baseStart_6200164 baseEnd_6200164 := by
    simpa [prefixWord, tailWord_6200164, baseEnd_6200164] using wordTrace_append hprefix tailTrace_6200164
  have hstable : (prefixWord ++ tailWord_6200164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6200164).length < 2 ^ (prefixWord ++ tailWord_6200164).sum := by decide
  have hdescent : baseEnd_6200164 < baseStart_6200164 := by decide
  rcases family_descends (prefixWord ++ tailWord_6200164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6200187 : List Nat := [1, 1, 1, 1, 1, 5, 4, 2, 1, 4, 2]
def baseStart_6200187 : Nat := 118140960795 + 6200187 * 2 ^ 59
def prefixEnd_6200187 : Nat := 4983230072969 + 3 ^ 40 * 6200187 * 2
def baseEnd_6200187 : Nat := 3183676078758238473548365

theorem tailTrace_6200187 : CollatzResearch.WordTrace tailWord_6200187 prefixEnd_6200187 3183676078758238473548365 := by
  unfold tailWord_6200187
  simp only [CollatzResearch.WordTrace]
  refine ⟨226139397988788881480766815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150759598659192587653844543 226139397988788881480766815)
  ·
    refine ⟨339209096983183322221150223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226139397988788881480766815 339209096983183322221150223)
    ·
      refine ⟨508813645474774983331725335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339209096983183322221150223 508813645474774983331725335)
      ·
        refine ⟨763220468212162474997588003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 508813645474774983331725335 763220468212162474997588003)
        ·
          refine ⟨1144830702318243712496382005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 763220468212162474997588003 1144830702318243712496382005)
          ·
            refine ⟨107327878342335348046535813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1144830702318243712496382005 107327878342335348046535813)
            ·
              refine ⟨20123977189187877758725465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 107327878342335348046535813 20123977189187877758725465)
              ·
                refine ⟨15092982891890908319044099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20123977189187877758725465 15092982891890908319044099)
                ·
                  refine ⟨22639474337836362478566149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15092982891890908319044099 22639474337836362478566149)
                  ·
                    refine ⟨4244901438344317964731153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22639474337836362478566149 4244901438344317964731153)
                    ·
                      refine ⟨3183676078758238473548365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4244901438344317964731153 3183676078758238473548365)
                      ·
                        rfl

theorem cell23_6200187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 2, 1, 4, 2].length) (baseStart_6200187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6200187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6200187 prefixEnd_6200187 := by exact prefixLift 6200187
  have htrace : WordTrace (prefixWord ++ tailWord_6200187) baseStart_6200187 baseEnd_6200187 := by
    simpa [prefixWord, tailWord_6200187, baseEnd_6200187] using wordTrace_append hprefix tailTrace_6200187
  have hstable : (prefixWord ++ tailWord_6200187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6200187).length < 2 ^ (prefixWord ++ tailWord_6200187).sum := by decide
  have hdescent : baseEnd_6200187 < baseStart_6200187 := by decide
  rcases family_descends (prefixWord ++ tailWord_6200187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6200250 : List Nat := [3, 1, 1, 1, 2, 1, 4, 2, 1, 2, 5]
def baseStart_6200250 : Nat := 118140960795 + 6200250 * 2 ^ 59
def prefixEnd_6200250 : Nat := 4983230072969 + 3 ^ 40 * 6200250 * 2
def baseEnd_6200250 : Nat := 3183708428039471727060575

theorem tailTrace_6200250 : CollatzResearch.WordTrace tailWord_6200250 prefixEnd_6200250 3183708428039471727060575 := by
  unfold tailWord_6200250
  simp only [CollatzResearch.WordTrace]
  refine ⟨56535423946890160810077551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150761130525040428826873469 56535423946890160810077551)
  ·
    refine ⟨84803135920335241215116327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56535423946890160810077551 84803135920335241215116327)
    ·
      refine ⟨127204703880502861822674491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84803135920335241215116327 127204703880502861822674491)
      ·
        refine ⟨190807055820754292734011737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127204703880502861822674491 190807055820754292734011737)
        ·
          refine ⟨143105291865565719550508803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190807055820754292734011737 143105291865565719550508803)
          ·
            refine ⟨214657937798348579325763205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143105291865565719550508803 214657937798348579325763205)
            ·
              refine ⟨40248363337190358623580601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 214657937798348579325763205 40248363337190358623580601)
              ·
                refine ⟨30186272502892768967685451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40248363337190358623580601 30186272502892768967685451)
                ·
                  refine ⟨45279408754339153451528177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30186272502892768967685451 45279408754339153451528177)
                  ·
                    refine ⟨33959556565754365088646133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45279408754339153451528177 33959556565754365088646133)
                    ·
                      refine ⟨3183708428039471727060575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33959556565754365088646133 3183708428039471727060575)
                      ·
                        rfl

theorem cell23_6200250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 2, 1, 2, 5].length) (baseStart_6200250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6200250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6200250 prefixEnd_6200250 := by exact prefixLift 6200250
  have htrace : WordTrace (prefixWord ++ tailWord_6200250) baseStart_6200250 baseEnd_6200250 := by
    simpa [prefixWord, tailWord_6200250, baseEnd_6200250] using wordTrace_append hprefix tailTrace_6200250
  have hstable : (prefixWord ++ tailWord_6200250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6200250).length < 2 ^ (prefixWord ++ tailWord_6200250).sum := by decide
  have hdescent : baseEnd_6200250 < baseStart_6200250 := by decide
  rcases family_descends (prefixWord ++ tailWord_6200250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6200304 : List Nat := [2, 1, 1, 1, 3, 2, 1, 7, 1, 4]
def baseStart_6200304 : Nat := 118140960795 + 6200304 * 2 ^ 59
def prefixEnd_6200304 : Nat := 4983230072969 + 3 ^ 40 * 6200304 * 2
def baseEnd_6200304 : Nat := 1061245385331604838595109

theorem tailTrace_6200304 : CollatzResearch.WordTrace tailWord_6200304 prefixEnd_6200304 1061245385331604838595109 := by
  unfold tailWord_6200304
  simp only [CollatzResearch.WordTrace]
  refine ⟨113071832664682505231387983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150762443552910006975183977 113071832664682505231387983)
  ·
    refine ⟨169607748997023757847081975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113071832664682505231387983 169607748997023757847081975)
    ·
      refine ⟨254411623495535636770622963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169607748997023757847081975 254411623495535636770622963)
      ·
        refine ⟨381617435243303455155934445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254411623495535636770622963 381617435243303455155934445)
        ·
          refine ⟨143106538216238795683475417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 381617435243303455155934445 143106538216238795683475417)
          ·
            refine ⟨107329903662179096762606563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143106538216238795683475417 107329903662179096762606563)
            ·
              refine ⟨160994855493268645143909845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107329903662179096762606563 160994855493268645143909845)
              ·
                refine ⟨3773316925623483870560387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 160994855493268645143909845 3773316925623483870560387)
                ·
                  refine ⟨5659975388435225805840581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3773316925623483870560387 5659975388435225805840581)
                  ·
                    refine ⟨1061245385331604838595109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5659975388435225805840581 1061245385331604838595109)
                    ·
                      rfl

theorem cell23_6200304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 7, 1, 4].length) (baseStart_6200304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6200304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6200304 prefixEnd_6200304 := by exact prefixLift 6200304
  have htrace : WordTrace (prefixWord ++ tailWord_6200304) baseStart_6200304 baseEnd_6200304 := by
    simpa [prefixWord, tailWord_6200304, baseEnd_6200304] using wordTrace_append hprefix tailTrace_6200304
  have hstable : (prefixWord ++ tailWord_6200304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6200304).length < 2 ^ (prefixWord ++ tailWord_6200304).sum := by decide
  have hdescent : baseEnd_6200304 < baseStart_6200304 := by decide
  rcases family_descends (prefixWord ++ tailWord_6200304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6200321 : List Nat := [1, 2, 4, 1, 2, 3, 1, 4, 1, 4]
def baseStart_6200321 : Nat := 118140960795 + 6200321 * 2 ^ 59
def prefixEnd_6200321 : Nat := 4983230072969 + 3 ^ 40 * 6200321 * 2
def baseEnd_6200321 : Nat := 1061248295055313649757583

theorem tailTrace_6200321 : CollatzResearch.WordTrace tailWord_6200321 prefixEnd_6200321 1061248295055313649757583 := by
  unfold tailWord_6200321
  simp only [CollatzResearch.WordTrace]
  refine ⟨226144285370303422366144817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150762856913535614910763211 226144285370303422366144817)
  ·
    refine ⟨169608214027727566774608613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226144285370303422366144817 169608214027727566774608613)
    ·
      refine ⟨31801540130198918770239115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 169608214027727566774608613 31801540130198918770239115)
      ·
        refine ⟨47702310195298378155358673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31801540130198918770239115 47702310195298378155358673)
        ·
          refine ⟨35776732646473783616519005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47702310195298378155358673 35776732646473783616519005)
          ·
            refine ⟨13416274742427668856194627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35776732646473783616519005 13416274742427668856194627)
            ·
              refine ⟨20124412113641503284291941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13416274742427668856194627 20124412113641503284291941)
              ·
                refine ⟨3773327271307781865804739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20124412113641503284291941 3773327271307781865804739)
                ·
                  refine ⟨5659990906961672798707109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3773327271307781865804739 5659990906961672798707109)
                  ·
                    refine ⟨1061248295055313649757583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5659990906961672798707109 1061248295055313649757583)
                    ·
                      rfl

theorem cell23_6200321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 4, 1, 4].length) (baseStart_6200321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6200321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6200321 prefixEnd_6200321 := by exact prefixLift 6200321
  have htrace : WordTrace (prefixWord ++ tailWord_6200321) baseStart_6200321 baseEnd_6200321 := by
    simpa [prefixWord, tailWord_6200321, baseEnd_6200321] using wordTrace_append hprefix tailTrace_6200321
  have hstable : (prefixWord ++ tailWord_6200321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6200321).length < 2 ^ (prefixWord ++ tailWord_6200321).sum := by decide
  have hdescent : baseEnd_6200321 < baseStart_6200321 := by decide
  rcases family_descends (prefixWord ++ tailWord_6200321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6200344 : List Nat := [2, 1, 2, 3, 2, 2, 1, 1, 5, 1, 3]
def baseStart_6200344 : Nat := 118140960795 + 6200344 * 2 ^ 59
def prefixEnd_6200344 : Nat := 4983230072969 + 3 ^ 40 * 6200344 * 2
def baseEnd_6200344 : Nat := 3183756695220994359285143

theorem tailTrace_6200344 : CollatzResearch.WordTrace tailWord_6200344 prefixEnd_6200344 3183756695220994359285143 := by
  unfold tailWord_6200344
  simp only [CollatzResearch.WordTrace]
  refine ⟨113072562124610048647116043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150763416166146731529488057 113072562124610048647116043)
  ·
    refine ⟨169608843186915072970674065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113072562124610048647116043 169608843186915072970674065)
    ·
      refine ⟨127206632390186304728005549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169608843186915072970674065 127206632390186304728005549)
      ·
        refine ⟨47702487146319864273002081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127206632390186304728005549 47702487146319864273002081)
        ·
          refine ⟨35776865359739898204751561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47702487146319864273002081 35776865359739898204751561)
          ·
            refine ⟨26832649019804923653563671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35776865359739898204751561 26832649019804923653563671)
            ·
              refine ⟨40248973529707385480345507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26832649019804923653563671 40248973529707385480345507)
              ·
                refine ⟨60373460294561078220518261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40248973529707385480345507 60373460294561078220518261)
                ·
                  refine ⟨5660011902615101083173587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60373460294561078220518261 5660011902615101083173587)
                  ·
                    refine ⟨8490017853922651624760381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5660011902615101083173587 8490017853922651624760381)
                    ·
                      refine ⟨3183756695220994359285143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8490017853922651624760381 3183756695220994359285143)
                      ·
                        rfl

theorem cell23_6200344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 5, 1, 3].length) (baseStart_6200344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6200344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6200344 prefixEnd_6200344 := by exact prefixLift 6200344
  have htrace : WordTrace (prefixWord ++ tailWord_6200344) baseStart_6200344 baseEnd_6200344 := by
    simpa [prefixWord, tailWord_6200344, baseEnd_6200344] using wordTrace_append hprefix tailTrace_6200344
  have hstable : (prefixWord ++ tailWord_6200344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6200344).length < 2 ^ (prefixWord ++ tailWord_6200344).sum := by decide
  have hdescent : baseEnd_6200344 < baseStart_6200344 := by decide
  rcases family_descends (prefixWord ++ tailWord_6200344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6200348 : List Nat := [2, 2, 3, 1, 5, 1, 1, 1, 2, 2, 3]
def baseStart_6200348 : Nat := 118140960795 + 6200348 * 2 ^ 59
def prefixEnd_6200348 : Nat := 4983230072969 + 3 ^ 40 * 6200348 * 2
def baseEnd_6200348 : Nat := 3183758749143612343635125

theorem tailTrace_6200348 : CollatzResearch.WordTrace tailWord_6200348 prefixEnd_6200348 3183758749143612343635125 := by
  unfold tailWord_6200348
  simp only [CollatzResearch.WordTrace]
  refine ⟨113072635070602802988688849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150763513427470403984918465 113072635070602802988688849)
  ·
    refine ⟨84804476302952102241516637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113072635070602802988688849 84804476302952102241516637)
    ·
      refine ⟨31801678613607038340568739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84804476302952102241516637 31801678613607038340568739)
      ·
        refine ⟨47702517920410557510853109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31801678613607038340568739 47702517920410557510853109)
        ·
          refine ⟨4472111055038489766642479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47702517920410557510853109 4472111055038489766642479)
          ·
            refine ⟨6708166582557734649963719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4472111055038489766642479 6708166582557734649963719)
            ·
              refine ⟨10062249873836601974945579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6708166582557734649963719 10062249873836601974945579)
              ·
                refine ⟨15093374810754902962418369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10062249873836601974945579 15093374810754902962418369)
                ·
                  refine ⟨11320031108066177221813777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15093374810754902962418369 11320031108066177221813777)
                  ·
                    refine ⟨8490023331049632916360333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11320031108066177221813777 8490023331049632916360333)
                    ·
                      refine ⟨3183758749143612343635125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8490023331049632916360333 3183758749143612343635125)
                      ·
                        rfl

theorem cell23_6200348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 1, 2, 2, 3].length) (baseStart_6200348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6200348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6200348 prefixEnd_6200348 := by exact prefixLift 6200348
  have htrace : WordTrace (prefixWord ++ tailWord_6200348) baseStart_6200348 baseEnd_6200348 := by
    simpa [prefixWord, tailWord_6200348, baseEnd_6200348] using wordTrace_append hprefix tailTrace_6200348
  have hstable : (prefixWord ++ tailWord_6200348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6200348).length < 2 ^ (prefixWord ++ tailWord_6200348).sum := by decide
  have hdescent : baseEnd_6200348 < baseStart_6200348 := by decide
  rcases family_descends (prefixWord ++ tailWord_6200348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6200387 : List Nat := [1, 1, 1, 3, 1, 2, 5, 2, 1, 1, 5]
def baseStart_6200387 : Nat := 118140960795 + 6200387 * 2 ^ 59
def prefixEnd_6200387 : Nat := 4983230072969 + 3 ^ 40 * 6200387 * 2
def baseEnd_6200387 : Nat := 3183778774889137691047445

theorem tailTrace_6200387 : CollatzResearch.WordTrace tailWord_6200387 prefixEnd_6200387 3183778774889137691047445 := by
  unfold tailWord_6200387
  simp only [CollatzResearch.WordTrace]
  refine ⟨226146692588064315638047415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150764461725376210425364943 226146692588064315638047415)
  ·
    refine ⟨339220038882096473457071123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226146692588064315638047415 339220038882096473457071123)
    ·
      refine ⟨508830058323144710185606685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339220038882096473457071123 508830058323144710185606685)
      ·
        refine ⟨190811271871179266319602507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 508830058323144710185606685 190811271871179266319602507)
        ·
          refine ⟨286216907806768899479403761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190811271871179266319602507 286216907806768899479403761)
          ·
            refine ⟨214662680855076674609552821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 286216907806768899479403761 214662680855076674609552821)
            ·
              refine ⟨20124626330163438244645577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 214662680855076674609552821 20124626330163438244645577)
              ·
                refine ⟨15093469747622578683484183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20124626330163438244645577 15093469747622578683484183)
                ·
                  refine ⟨22640204621433868025226275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15093469747622578683484183 22640204621433868025226275)
                  ·
                    refine ⟨33960306932150802037839413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22640204621433868025226275 33960306932150802037839413)
                    ·
                      refine ⟨3183778774889137691047445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33960306932150802037839413 3183778774889137691047445)
                      ·
                        rfl

theorem cell23_6200387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 2, 1, 1, 5].length) (baseStart_6200387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6200387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6200387 prefixEnd_6200387 := by exact prefixLift 6200387
  have htrace : WordTrace (prefixWord ++ tailWord_6200387) baseStart_6200387 baseEnd_6200387 := by
    simpa [prefixWord, tailWord_6200387, baseEnd_6200387] using wordTrace_append hprefix tailTrace_6200387
  have hstable : (prefixWord ++ tailWord_6200387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6200387).length < 2 ^ (prefixWord ++ tailWord_6200387).sum := by decide
  have hdescent : baseEnd_6200387 < baseStart_6200387 := by decide
  rcases family_descends (prefixWord ++ tailWord_6200387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6200394 : List Nat := [3, 1, 2, 1, 1, 2, 2, 5, 2, 4]
def baseStart_6200394 : Nat := 118140960795 + 6200394 * 2 ^ 59
def prefixEnd_6200394 : Nat := 4983230072969 + 3 ^ 40 * 6200394 * 2
def baseEnd_6200394 : Nat := 1061260789751239721219971

theorem tailTrace_6200394 : CollatzResearch.WordTrace tailWord_6200394 prefixEnd_6200394 1061260789751239721219971 := by
  unfold tailWord_6200394
  simp only [CollatzResearch.WordTrace]
  refine ⟨56536736974759738958388059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150764631932692637222368157 56536736974759738958388059)
  ·
    refine ⟨84805105462139608437582089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56536736974759738958388059 84805105462139608437582089)
    ·
      refine ⟨63603829096604706328186567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84805105462139608437582089 63603829096604706328186567)
      ·
        refine ⟨95405743644907059492279851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63603829096604706328186567 95405743644907059492279851)
        ·
          refine ⟨143108615467360589238419777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95405743644907059492279851 143108615467360589238419777)
          ·
            refine ⟨107331461600520441928814833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143108615467360589238419777 107331461600520441928814833)
            ·
              refine ⟨80498596200390331446611125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107331461600520441928814833 80498596200390331446611125)
              ·
                refine ⟨7546743393786593573119793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 80498596200390331446611125 7546743393786593573119793)
                ·
                  refine ⟨5660057545339945179839845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7546743393786593573119793 5660057545339945179839845)
                  ·
                    refine ⟨1061260789751239721219971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5660057545339945179839845 1061260789751239721219971)
                    ·
                      rfl

theorem cell23_6200394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 5, 2, 4].length) (baseStart_6200394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6200394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6200394 prefixEnd_6200394 := by exact prefixLift 6200394
  have htrace : WordTrace (prefixWord ++ tailWord_6200394) baseStart_6200394 baseEnd_6200394 := by
    simpa [prefixWord, tailWord_6200394, baseEnd_6200394] using wordTrace_append hprefix tailTrace_6200394
  have hstable : (prefixWord ++ tailWord_6200394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6200394).length < 2 ^ (prefixWord ++ tailWord_6200394).sum := by decide
  have hdescent : baseEnd_6200394 < baseStart_6200394 := by decide
  rcases family_descends (prefixWord ++ tailWord_6200394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6200401 : List Nat := [1, 2, 2, 1, 3, 1, 4, 2, 3, 2, 2]
def baseStart_6200401 : Nat := 118140960795 + 6200401 * 2 ^ 59
def prefixEnd_6200401 : Nat := 4983230072969 + 3 ^ 40 * 6200401 * 2
def baseEnd_6200401 : Nat := 3183785963618300636272381

theorem tailTrace_6200401 : CollatzResearch.WordTrace tailWord_6200401 prefixEnd_6200401 3183785963618300636272381 := by
  unfold tailWord_6200401
  simp only [CollatzResearch.WordTrace]
  refine ⟨226147203210013596029057057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150764802140009064019371371 226147203210013596029057057)
  ·
    refine ⟨169610402407510197021792793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226147203210013596029057057 169610402407510197021792793)
    ·
      refine ⟨127207801805632647766344595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169610402407510197021792793 127207801805632647766344595)
      ·
        refine ⟨190811702708448971649516893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127207801805632647766344595 190811702708448971649516893)
        ·
          refine ⟨71554388515668364368568835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 190811702708448971649516893 71554388515668364368568835)
          ·
            refine ⟨107331582773502546552853253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71554388515668364368568835 107331582773502546552853253)
            ·
              refine ⟨20124671770031727478659985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 107331582773502546552853253 20124671770031727478659985)
              ·
                refine ⟨15093503827523795608994989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20124671770031727478659985 15093503827523795608994989)
                ·
                  refine ⟨5660063935321423353373121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15093503827523795608994989 5660063935321423353373121)
                  ·
                    refine ⟨4245047951491067515029841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5660063935321423353373121 4245047951491067515029841)
                    ·
                      refine ⟨3183785963618300636272381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4245047951491067515029841 3183785963618300636272381)
                      ·
                        rfl

theorem cell23_6200401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 2, 3, 2, 2].length) (baseStart_6200401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6200401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6200401 prefixEnd_6200401 := by exact prefixLift 6200401
  have htrace : WordTrace (prefixWord ++ tailWord_6200401) baseStart_6200401 baseEnd_6200401 := by
    simpa [prefixWord, tailWord_6200401, baseEnd_6200401] using wordTrace_append hprefix tailTrace_6200401
  have hstable : (prefixWord ++ tailWord_6200401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6200401).length < 2 ^ (prefixWord ++ tailWord_6200401).sum := by decide
  have hdescent : baseEnd_6200401 < baseStart_6200401 := by decide
  rcases family_descends (prefixWord ++ tailWord_6200401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6200404 : List Nat := [2, 4, 1, 1, 1, 1, 2, 3, 3, 2, 3]
def baseStart_6200404 : Nat := 118140960795 + 6200404 * 2 ^ 59
def prefixEnd_6200404 : Nat := 4983230072969 + 3 ^ 40 * 6200404 * 2
def baseEnd_6200404 : Nat := 3183787504060264124534867

theorem tailTrace_6200404 : CollatzResearch.WordTrace tailWord_6200404 prefixEnd_6200404 3183787504060264124534867 := by
  unfold tailWord_6200404
  simp only [CollatzResearch.WordTrace]
  refine ⟨113073656314501363770708133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150764875086001818360944177 113073656314501363770708133)
  ·
    refine ⟨21201310558969005707007775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113073656314501363770708133 21201310558969005707007775)
    ·
      refine ⟨31801965838453508560511663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21201310558969005707007775 31801965838453508560511663)
      ·
        refine ⟨47702948757680262840767495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31801965838453508560511663 47702948757680262840767495)
        ·
          refine ⟨71554423136520394261151243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47702948757680262840767495 71554423136520394261151243)
          ·
            refine ⟨107331634704780591391726865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71554423136520394261151243 107331634704780591391726865)
            ·
              refine ⟨80498726028585443543795149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107331634704780591391726865 80498726028585443543795149)
              ·
                refine ⟨30187022260719541328923181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80498726028585443543795149 30187022260719541328923181)
                ·
                  refine ⟨11320133347769827998346193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30187022260719541328923181 11320133347769827998346193)
                  ·
                    refine ⟨8490100010827370998759645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11320133347769827998346193 8490100010827370998759645)
                    ·
                      refine ⟨3183787504060264124534867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8490100010827370998759645 3183787504060264124534867)
                      ·
                        rfl

theorem cell23_6200404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 3, 3, 2, 3].length) (baseStart_6200404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6200404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6200404 prefixEnd_6200404 := by exact prefixLift 6200404
  have htrace : WordTrace (prefixWord ++ tailWord_6200404) baseStart_6200404 baseEnd_6200404 := by
    simpa [prefixWord, tailWord_6200404, baseEnd_6200404] using wordTrace_append hprefix tailTrace_6200404
  have hstable : (prefixWord ++ tailWord_6200404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6200404).length < 2 ^ (prefixWord ++ tailWord_6200404).sum := by decide
  have hdescent : baseEnd_6200404 < baseStart_6200404 := by decide
  rcases family_descends (prefixWord ++ tailWord_6200404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6200451 : List Nat := [1, 1, 1, 3, 3, 2, 3, 3, 2, 1, 3]
def baseStart_6200451 : Nat := 118140960795 + 6200451 * 2 ^ 59
def prefixEnd_6200451 : Nat := 4983230072969 + 3 ^ 40 * 6200451 * 2
def baseEnd_6200451 : Nat := 3183811637651025440647151

theorem tailTrace_6200451 : CollatzResearch.WordTrace tailWord_6200451 prefixEnd_6200451 3183811637651025440647151 := by
  unfold tailWord_6200451
  simp only [CollatzResearch.WordTrace]
  refine ⟨226149026859832454568377207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150766017906554969712251471 226149026859832454568377207)
  ·
    refine ⟨339223540289748681852565811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226149026859832454568377207 339223540289748681852565811)
    ·
      refine ⟨508835310434623022778848717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339223540289748681852565811 508835310434623022778848717)
      ·
        refine ⟨190813241412983633542068269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 508835310434623022778848717 190813241412983633542068269)
        ·
          refine ⟨71554965529868862578275601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 190813241412983633542068269 71554965529868862578275601)
          ·
            refine ⟨53666224147401646933706701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71554965529868862578275601 53666224147401646933706701)
            ·
              refine ⟨20124834055275617600140013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53666224147401646933706701 20124834055275617600140013)
              ·
                refine ⟨7546812770728356600052505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20124834055275617600140013 7546812770728356600052505)
                ·
                  refine ⟨5660109578046267450039379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7546812770728356600052505 5660109578046267450039379)
                  ·
                    refine ⟨8490164367069401175059069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5660109578046267450039379 8490164367069401175059069)
                    ·
                      refine ⟨3183811637651025440647151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8490164367069401175059069 3183811637651025440647151)
                      ·
                        rfl

theorem cell23_6200451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 3, 2, 1, 3].length) (baseStart_6200451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6200451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6200451 prefixEnd_6200451 := by exact prefixLift 6200451
  have htrace : WordTrace (prefixWord ++ tailWord_6200451) baseStart_6200451 baseEnd_6200451 := by
    simpa [prefixWord, tailWord_6200451, baseEnd_6200451] using wordTrace_append hprefix tailTrace_6200451
  have hstable : (prefixWord ++ tailWord_6200451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6200451).length < 2 ^ (prefixWord ++ tailWord_6200451).sum := by decide
  have hdescent : baseEnd_6200451 < baseStart_6200451 := by decide
  rcases family_descends (prefixWord ++ tailWord_6200451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6200508 : List Nat := [2, 2, 2, 3, 2, 2, 2, 1, 1, 4, 2]
def baseStart_6200508 : Nat := 118140960795 + 6200508 * 2 ^ 59
def prefixEnd_6200508 : Nat := 4983230072969 + 3 ^ 40 * 6200508 * 2
def baseEnd_6200508 : Nat := 3183840906048331717634389

theorem tailTrace_6200508 : CollatzResearch.WordTrace tailWord_6200508 prefixEnd_6200508 3183840906048331717634389 := by
  unfold tailWord_6200508
  simp only [CollatzResearch.WordTrace]
  refine ⟨113075552910312976651601089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150767403880417302202134785 113075552910312976651601089)
  ·
    refine ⟨84806664682734732488700817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113075552910312976651601089 84806664682734732488700817)
    ·
      refine ⟨63604998512051049366525613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84806664682734732488700817 63604998512051049366525613)
      ·
        refine ⟨23851874442019143512447105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63604998512051049366525613 23851874442019143512447105)
        ·
          refine ⟨17888905831514357634335329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23851874442019143512447105 17888905831514357634335329)
          ·
            refine ⟨13416679373635768225751497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17888905831514357634335329 13416679373635768225751497)
            ·
              refine ⟨10062509530226826169313623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13416679373635768225751497 10062509530226826169313623)
              ·
                refine ⟨15093764295340239253970435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10062509530226826169313623 15093764295340239253970435)
                ·
                  refine ⟨22640646443010358880955653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15093764295340239253970435 22640646443010358880955653)
                  ·
                    refine ⟨4245121208064442290179185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22640646443010358880955653 4245121208064442290179185)
                    ·
                      refine ⟨3183840906048331717634389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4245121208064442290179185 3183840906048331717634389)
                      ·
                        rfl

theorem cell23_6200508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 1, 1, 4, 2].length) (baseStart_6200508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6200508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6200508 prefixEnd_6200508 := by exact prefixLift 6200508
  have htrace : WordTrace (prefixWord ++ tailWord_6200508) baseStart_6200508 baseEnd_6200508 := by
    simpa [prefixWord, tailWord_6200508, baseEnd_6200508] using wordTrace_append hprefix tailTrace_6200508
  have hstable : (prefixWord ++ tailWord_6200508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6200508).length < 2 ^ (prefixWord ++ tailWord_6200508).sum := by decide
  have hdescent : baseEnd_6200508 < baseStart_6200508 := by decide
  rcases family_descends (prefixWord ++ tailWord_6200508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6200604 : List Nat := [2, 2, 3, 1, 1, 1, 4, 1, 8]
def baseStart_6200604 : Nat := 118140960795 + 6200604 * 2 ^ 59
def prefixEnd_6200604 : Nat := 4983230072969 + 3 ^ 40 * 6200604 * 2
def baseEnd_6200604 : Nat := 353765577799018149114883

theorem tailTrace_6200604 : CollatzResearch.WordTrace tailWord_6200604 prefixEnd_6200604 353765577799018149114883 := by
  unfold tailWord_6200604
  simp only [CollatzResearch.WordTrace]
  refine ⟨113077303614139080849348433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150769738152185441132464577 113077303614139080849348433)
  ·
    refine ⟨84807977710604310637011325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113077303614139080849348433 84807977710604310637011325)
    ·
      refine ⟨31802991641476616488879247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84807977710604310637011325 31802991641476616488879247)
      ·
        refine ⟨47704487462214924733318871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31802991641476616488879247 47704487462214924733318871)
        ·
          refine ⟨71556731193322387099978307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47704487462214924733318871 71556731193322387099978307)
          ·
            refine ⟨107335096789983580649967461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71556731193322387099978307 107335096789983580649967461)
            ·
              refine ⟨20125330648121921371868899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 107335096789983580649967461 20125330648121921371868899)
              ·
                refine ⟨30187995972182882057803349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20125330648121921371868899 30187995972182882057803349)
                ·
                  refine ⟨353765577799018149114883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30187995972182882057803349 353765577799018149114883)
                  ·
                    rfl

theorem cell23_6200604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 1, 8].length) (baseStart_6200604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6200604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6200604 prefixEnd_6200604 := by exact prefixLift 6200604
  have htrace : WordTrace (prefixWord ++ tailWord_6200604) baseStart_6200604 baseEnd_6200604 := by
    simpa [prefixWord, tailWord_6200604, baseEnd_6200604] using wordTrace_append hprefix tailTrace_6200604
  have hstable : (prefixWord ++ tailWord_6200604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6200604).length < 2 ^ (prefixWord ++ tailWord_6200604).sum := by decide
  have hdescent : baseEnd_6200604 < baseStart_6200604 := by decide
  rcases family_descends (prefixWord ++ tailWord_6200604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6200664 : List Nat := [2, 1, 2, 2, 1, 1, 3, 2, 3, 6]
def baseStart_6200664 : Nat := 118140960795 + 6200664 * 2 ^ 59
def prefixEnd_6200664 : Nat := 4983230072969 + 3 ^ 40 * 6200664 * 2
def baseEnd_6200664 : Nat := 1061307003010144369094557

theorem tailTrace_6200664 : CollatzResearch.WordTrace tailWord_6200664 prefixEnd_6200664 1061307003010144369094557 := by
  unfold tailWord_6200664
  simp only [CollatzResearch.WordTrace]
  refine ⟨113078397804030395972940523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150771197072040527963920697 113078397804030395972940523)
  ·
    refine ⟨169617596706045593959410785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113078397804030395972940523 169617596706045593959410785)
    ·
      refine ⟨127213197529534195469558089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169617596706045593959410785 127213197529534195469558089)
      ·
        refine ⟨95409898147150646602168567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127213197529534195469558089 95409898147150646602168567)
        ·
          refine ⟨143114847220725969903252851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95409898147150646602168567 143114847220725969903252851)
          ·
            refine ⟨214672270831088954854879277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143114847220725969903252851 214672270831088954854879277)
            ·
              refine ⟨80502101561658358070579729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 214672270831088954854879277 80502101561658358070579729)
              ·
                refine ⟨60376576171243768552934797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80502101561658358070579729 60376576171243768552934797)
                ·
                  refine ⟨22641216064216413207350549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60376576171243768552934797 22641216064216413207350549)
                  ·
                    refine ⟨1061307003010144369094557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22641216064216413207350549 1061307003010144369094557)
                    ·
                      rfl

theorem cell23_6200664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 3, 6].length) (baseStart_6200664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6200664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6200664 prefixEnd_6200664 := by exact prefixLift 6200664
  have htrace : WordTrace (prefixWord ++ tailWord_6200664) baseStart_6200664 baseEnd_6200664 := by
    simpa [prefixWord, tailWord_6200664, baseEnd_6200664] using wordTrace_append hprefix tailTrace_6200664
  have hstable : (prefixWord ++ tailWord_6200664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6200664).length < 2 ^ (prefixWord ++ tailWord_6200664).sum := by decide
  have hdescent : baseEnd_6200664 < baseStart_6200664 := by decide
  rcases family_descends (prefixWord ++ tailWord_6200664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6200671 : List Nat := [1, 1, 2, 3, 1, 2, 1, 2, 2, 6, 2]
def baseStart_6200671 : Nat := 118140960795 + 6200671 * 2 ^ 59
def prefixEnd_6200671 : Nat := 4983230072969 + 3 ^ 40 * 6200671 * 2
def baseEnd_6200671 : Nat := 3183924603395014579896139

theorem tailTrace_6200671 : CollatzResearch.WordTrace tailWord_6200671 prefixEnd_6200671 3183924603395014579896139 := by
  unfold tailWord_6200671
  simp only [CollatzResearch.WordTrace]
  refine ⟨226157050919035432141385867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150771367279356954760923911 226157050919035432141385867)
  ·
    refine ⟨339235576378553148212078801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226157050919035432141385867 339235576378553148212078801)
    ·
      refine ⟨254426682283914861159059101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 339235576378553148212078801 254426682283914861159059101)
      ·
        refine ⟨95410005856468072934647163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 254426682283914861159059101 95410005856468072934647163)
        ·
          refine ⟨143115008784702109401970745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95410005856468072934647163 143115008784702109401970745)
          ·
            refine ⟨107336256588526582051478059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143115008784702109401970745 107336256588526582051478059)
            ·
              refine ⟨161004384882789873077217089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107336256588526582051478059 161004384882789873077217089)
              ·
                refine ⟨120753288662092404807912817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161004384882789873077217089 120753288662092404807912817)
                ·
                  refine ⟨90564966496569303605934613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 120753288662092404807912817 90564966496569303605934613)
                  ·
                    refine ⟨4245232804526686106528185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 90564966496569303605934613 4245232804526686106528185)
                    ·
                      refine ⟨3183924603395014579896139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4245232804526686106528185 3183924603395014579896139)
                      ·
                        rfl

theorem cell23_6200671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 6, 2].length) (baseStart_6200671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6200671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6200671 prefixEnd_6200671 := by exact prefixLift 6200671
  have htrace : WordTrace (prefixWord ++ tailWord_6200671) baseStart_6200671 baseEnd_6200671 := by
    simpa [prefixWord, tailWord_6200671, baseEnd_6200671] using wordTrace_append hprefix tailTrace_6200671
  have hstable : (prefixWord ++ tailWord_6200671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6200671).length < 2 ^ (prefixWord ++ tailWord_6200671).sum := by decide
  have hdescent : baseEnd_6200671 < baseStart_6200671 := by decide
  rcases family_descends (prefixWord ++ tailWord_6200671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6200701 : List Nat := [1, 4, 1, 1, 2, 2, 1, 4, 1, 2, 4]
def baseStart_6200701 : Nat := 118140960795 + 6200701 * 2 ^ 59
def prefixEnd_6200701 : Nat := 4983230072969 + 3 ^ 40 * 6200701 * 2
def baseEnd_6200701 : Nat := 3183940007814649462521001

theorem tailTrace_6200701 : CollatzResearch.WordTrace tailWord_6200701 prefixEnd_6200701 3183940007814649462521001 := by
  unfold tailWord_6200701
  simp only [CollatzResearch.WordTrace]
  refine ⟨226158145108926747264977957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150772096739284498176651971 226158145108926747264977957)
  ·
    refine ⟨42404652207923765112183367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 226158145108926747264977957 42404652207923765112183367)
    ·
      refine ⟨63606978311885647668275051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42404652207923765112183367 63606978311885647668275051)
      ·
        refine ⟨95410467467828471502412577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63606978311885647668275051 95410467467828471502412577)
        ·
          refine ⟨71557850600871353626809433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95410467467828471502412577 71557850600871353626809433)
          ·
            refine ⟨53668387950653515220107075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71557850600871353626809433 53668387950653515220107075)
            ·
              refine ⟨80502581925980272830160613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53668387950653515220107075 80502581925980272830160613)
              ·
                refine ⟨15094234111121301155655115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80502581925980272830160613 15094234111121301155655115)
                ·
                  refine ⟨22641351166681951733482673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15094234111121301155655115 22641351166681951733482673)
                  ·
                    refine ⟨16981013375011463800112005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22641351166681951733482673 16981013375011463800112005)
                    ·
                      refine ⟨3183940007814649462521001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16981013375011463800112005 3183940007814649462521001)
                      ·
                        rfl

theorem cell23_6200701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 4, 1, 2, 4].length) (baseStart_6200701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6200701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6200701 prefixEnd_6200701 := by exact prefixLift 6200701
  have htrace : WordTrace (prefixWord ++ tailWord_6200701) baseStart_6200701 baseEnd_6200701 := by
    simpa [prefixWord, tailWord_6200701, baseEnd_6200701] using wordTrace_append hprefix tailTrace_6200701
  have hstable : (prefixWord ++ tailWord_6200701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6200701).length < 2 ^ (prefixWord ++ tailWord_6200701).sum := by decide
  have hdescent : baseEnd_6200701 < baseStart_6200701 := by decide
  rcases family_descends (prefixWord ++ tailWord_6200701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6200702 : List Nat := [4, 2, 3, 2, 1, 1, 1, 3, 1, 5]
def baseStart_6200702 : Nat := 118140960795 + 6200702 * 2 ^ 59
def prefixEnd_6200702 : Nat := 4983230072969 + 3 ^ 40 * 6200702 * 2
def baseEnd_6200702 : Nat := 1061313507098434652869499

theorem tailTrace_6200702 : CollatzResearch.WordTrace tailWord_6200702 prefixEnd_6200702 1061313507098434652869499 := by
  unfold tailWord_6200702
  simp only [CollatzResearch.WordTrace]
  refine ⟨28269772697740390554470545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150772121054615416290509573 28269772697740390554470545)
  ·
    refine ⟨21202329523305292915852909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28269772697740390554470545 21202329523305292915852909)
    ·
      refine ⟨7950873571239484843444841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21202329523305292915852909 7950873571239484843444841)
      ·
        refine ⟨5963155178429613632583631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7950873571239484843444841 5963155178429613632583631)
        ·
          refine ⟨8944732767644420448875447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5963155178429613632583631 8944732767644420448875447)
          ·
            refine ⟨13417099151466630673313171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8944732767644420448875447 13417099151466630673313171)
            ·
              refine ⟨20125648727199946009969757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13417099151466630673313171 20125648727199946009969757)
              ·
                refine ⟨7547118272699979753738659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20125648727199946009969757 7547118272699979753738659)
                ·
                  refine ⟨11320677409049969630607989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7547118272699979753738659 11320677409049969630607989)
                  ·
                    refine ⟨1061313507098434652869499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11320677409049969630607989 1061313507098434652869499)
                    ·
                      rfl

theorem cell23_6200702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_6200702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6200702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6200702 prefixEnd_6200702 := by exact prefixLift 6200702
  have htrace : WordTrace (prefixWord ++ tailWord_6200702) baseStart_6200702 baseEnd_6200702 := by
    simpa [prefixWord, tailWord_6200702, baseEnd_6200702] using wordTrace_append hprefix tailTrace_6200702
  have hstable : (prefixWord ++ tailWord_6200702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6200702).length < 2 ^ (prefixWord ++ tailWord_6200702).sum := by decide
  have hdescent : baseEnd_6200702 < baseStart_6200702 := by decide
  rcases family_descends (prefixWord ++ tailWord_6200702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6200705 : List Nat := [1, 2, 4, 3, 2, 1, 1, 3, 1, 1, 4]
def baseStart_6200705 : Nat := 118140960795 + 6200705 * 2 ^ 59
def prefixEnd_6200705 : Nat := 4983230072969 + 3 ^ 40 * 6200705 * 2
def baseEnd_6200705 : Nat := 3183942061737267446870983

theorem tailTrace_6200705 : CollatzResearch.WordTrace tailWord_6200705 prefixEnd_6200705 3183942061737267446870983 := by
  unfold tailWord_6200705
  simp only [CollatzResearch.WordTrace]
  refine ⟨226158291000912255948123569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150772194000608170632082379 226158291000912255948123569)
  ·
    refine ⟨169618718250684191961092677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226158291000912255948123569 169618718250684191961092677)
    ·
      refine ⟨31803509672003285992704877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 169618718250684191961092677 31803509672003285992704877)
      ·
        refine ⟨11926316127001232247264329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31803509672003285992704877 11926316127001232247264329)
        ·
          refine ⟨8944737095250924185448247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11926316127001232247264329 8944737095250924185448247)
          ·
            refine ⟨13417105642876386278172371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8944737095250924185448247 13417105642876386278172371)
            ·
              refine ⟨20125658464314579417258557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13417105642876386278172371 20125658464314579417258557)
              ·
                refine ⟨7547121924117967281471959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20125658464314579417258557 7547121924117967281471959)
                ·
                  refine ⟨11320682886176950922207939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7547121924117967281471959 11320682886176950922207939)
                  ·
                    refine ⟨16981024329265426383311909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11320682886176950922207939 16981024329265426383311909)
                    ·
                      refine ⟨3183942061737267446870983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16981024329265426383311909 3183942061737267446870983)
                      ·
                        rfl

theorem cell23_6200705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_6200705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6200705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6200705 prefixEnd_6200705 := by exact prefixLift 6200705
  have htrace : WordTrace (prefixWord ++ tailWord_6200705) baseStart_6200705 baseEnd_6200705 := by
    simpa [prefixWord, tailWord_6200705, baseEnd_6200705] using wordTrace_append hprefix tailTrace_6200705
  have hstable : (prefixWord ++ tailWord_6200705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6200705).length < 2 ^ (prefixWord ++ tailWord_6200705).sum := by decide
  have hdescent : baseEnd_6200705 < baseStart_6200705 := by decide
  rcases family_descends (prefixWord ++ tailWord_6200705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6200732 : List Nat := [2, 2, 3, 4, 2, 1, 1, 1, 1, 6]
def baseStart_6200732 : Nat := 118140960795 + 6200732 * 2 ^ 59
def prefixEnd_6200732 : Nat := 4983230072969 + 3 ^ 40 * 6200732 * 2
def baseEnd_6200732 : Nat := 1061318641904979613744453

theorem tailTrace_6200732 : CollatzResearch.WordTrace tailWord_6200732 prefixEnd_6200732 1061318641904979613744453 := by
  unfold tailWord_6200732
  simp only [CollatzResearch.WordTrace]
  refine ⟨113079637885907219779678225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150772850514542959706237633 113079637885907219779678225)
  ·
    refine ⟨84809728414430414834758669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113079637885907219779678225 84809728414430414834758669)
    ·
      refine ⟨31803648155411405563034501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84809728414430414834758669 31803648155411405563034501)
      ·
        refine ⟨5963184029139638543068969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31803648155411405563034501 5963184029139638543068969)
        ·
          refine ⟨4472388021854728907301727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5963184029139638543068969 4472388021854728907301727)
          ·
            refine ⟨6708582032782093360952591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4472388021854728907301727 6708582032782093360952591)
            ·
              refine ⟨10062873049173140041428887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6708582032782093360952591 10062873049173140041428887)
              ·
                refine ⟨15094309573759710062143331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10062873049173140041428887 15094309573759710062143331)
                ·
                  refine ⟨22641464360639565093214997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15094309573759710062143331 22641464360639565093214997)
                  ·
                    refine ⟨1061318641904979613744453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22641464360639565093214997 1061318641904979613744453)
                    ·
                      rfl

theorem cell23_6200732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 1, 1, 6].length) (baseStart_6200732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6200732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6200732 prefixEnd_6200732 := by exact prefixLift 6200732
  have htrace : WordTrace (prefixWord ++ tailWord_6200732) baseStart_6200732 baseEnd_6200732 := by
    simpa [prefixWord, tailWord_6200732, baseEnd_6200732] using wordTrace_append hprefix tailTrace_6200732
  have hstable : (prefixWord ++ tailWord_6200732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6200732).length < 2 ^ (prefixWord ++ tailWord_6200732).sum := by decide
  have hdescent : baseEnd_6200732 < baseStart_6200732 := by decide
  rcases family_descends (prefixWord ++ tailWord_6200732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6200748 : List Nat := [2, 2, 1, 1, 1, 1, 4, 3, 3, 3, 2]
def baseStart_6200748 : Nat := 118140960795 + 6200748 * 2 ^ 59
def prefixEnd_6200748 : Nat := 4983230072969 + 3 ^ 40 * 6200748 * 2
def baseEnd_6200748 : Nat := 3183964141405410778633285

theorem tailTrace_6200748 : CollatzResearch.WordTrace tailWord_6200748 prefixEnd_6200748 3183964141405410778633285 := by
  unfold tailWord_6200748
  simp only [CollatzResearch.WordTrace]
  refine ⟨113079929669878237145969449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150773239559837649527959265 113079929669878237145969449)
  ·
    refine ⟨84809947252408677859477087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113079929669878237145969449 84809947252408677859477087)
    ·
      refine ⟨127214920878613016789215631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84809947252408677859477087 127214920878613016789215631)
      ·
        refine ⟨190822381317919525183823447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127214920878613016789215631 190822381317919525183823447)
        ·
          refine ⟨286233571976879287775735171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190822381317919525183823447 286233571976879287775735171)
          ·
            refine ⟨429350357965318931663602757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286233571976879287775735171 429350357965318931663602757)
            ·
              refine ⟨80503192118497299686925517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 429350357965318931663602757 80503192118497299686925517)
              ·
                refine ⟨30188697044436487382597069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80503192118497299686925517 30188697044436487382597069)
                ·
                  refine ⟨11320761391663682768473901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30188697044436487382597069 11320761391663682768473901)
                  ·
                    refine ⟨4245285521873881038177713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11320761391663682768473901 4245285521873881038177713)
                    ·
                      refine ⟨3183964141405410778633285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4245285521873881038177713 3183964141405410778633285)
                      ·
                        rfl

theorem cell23_6200748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 3, 2].length) (baseStart_6200748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6200748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6200748 prefixEnd_6200748 := by exact prefixLift 6200748
  have htrace : WordTrace (prefixWord ++ tailWord_6200748) baseStart_6200748 baseEnd_6200748 := by
    simpa [prefixWord, tailWord_6200748, baseEnd_6200748] using wordTrace_append hprefix tailTrace_6200748
  have hstable : (prefixWord ++ tailWord_6200748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6200748).length < 2 ^ (prefixWord ++ tailWord_6200748).sum := by decide
  have hdescent : baseEnd_6200748 < baseStart_6200748 := by decide
  rcases family_descends (prefixWord ++ tailWord_6200748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6200765 : List Nat := [1, 4, 1, 2, 2, 1, 1, 5, 1, 3, 2]
def baseStart_6200765 : Nat := 118140960795 + 6200765 * 2 ^ 59
def prefixEnd_6200765 : Nat := 4983230072969 + 3 ^ 40 * 6200765 * 2
def baseEnd_6200765 : Nat := 3183972870576537212120707

theorem tailTrace_6200765 : CollatzResearch.WordTrace tailWord_6200765 prefixEnd_6200765 3183972870576537212120707 := by
  unfold tailWord_6200765
  simp only [CollatzResearch.WordTrace]
  refine ⟨226160479380694886195307749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150773652920463257463538499 226160479380694886195307749)
  ·
    refine ⟨42405089883880291161620203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 226160479380694886195307749 42405089883880291161620203)
    ·
      refine ⟨63607634825820436742430305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42405089883880291161620203 63607634825820436742430305)
      ·
        refine ⟨47705726119365327556822729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63607634825820436742430305 47705726119365327556822729)
        ·
          refine ⟨35779294589523995667617047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47705726119365327556822729 35779294589523995667617047)
          ·
            refine ⟨53668941884285993501425571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35779294589523995667617047 53668941884285993501425571)
            ·
              refine ⟨80503412826428990252138357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53668941884285993501425571 80503412826428990252138357)
              ·
                refine ⟨7547194952477717836137971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 80503412826428990252138357 7547194952477717836137971)
                ·
                  refine ⟨11320792428716576754206957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7547194952477717836137971 11320792428716576754206957)
                  ·
                    refine ⟨4245297160768716282827609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11320792428716576754206957 4245297160768716282827609)
                    ·
                      refine ⟨3183972870576537212120707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4245297160768716282827609 3183972870576537212120707)
                      ·
                        rfl

theorem cell23_6200765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 5, 1, 3, 2].length) (baseStart_6200765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6200765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6200765 prefixEnd_6200765 := by exact prefixLift 6200765
  have htrace : WordTrace (prefixWord ++ tailWord_6200765) baseStart_6200765 baseEnd_6200765 := by
    simpa [prefixWord, tailWord_6200765, baseEnd_6200765] using wordTrace_append hprefix tailTrace_6200765
  have hstable : (prefixWord ++ tailWord_6200765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6200765).length < 2 ^ (prefixWord ++ tailWord_6200765).sum := by decide
  have hdescent : baseEnd_6200765 < baseStart_6200765 := by decide
  rcases family_descends (prefixWord ++ tailWord_6200765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6200791 : List Nat := [1, 1, 3, 2, 1, 1, 1, 5, 2, 2, 4]
def baseStart_6200791 : Nat := 118140960795 + 6200791 * 2 ^ 59
def prefixEnd_6200791 : Nat := 4983230072969 + 3 ^ 40 * 6200791 * 2
def baseEnd_6200791 : Nat := 3183986221073554110395587

theorem tailTrace_6200791 : CollatzResearch.WordTrace tailWord_6200791 prefixEnd_6200791 3183986221073554110395587 := by
  unfold tailWord_6200791
  simp only [CollatzResearch.WordTrace]
  refine ⟨226161427678600692635754227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150774285119067128423836151 226161427678600692635754227)
  ·
    refine ⟨339242141517901038953631341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226161427678600692635754227 339242141517901038953631341)
    ·
      refine ⟨127215803069212889607611753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 339242141517901038953631341 127215803069212889607611753)
      ·
        refine ⟨95411852301909667205708815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127215803069212889607611753 95411852301909667205708815)
        ·
          refine ⟨143117778452864500808563223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95411852301909667205708815 143117778452864500808563223)
          ·
            refine ⟨214676667679296751212844835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143117778452864500808563223 214676667679296751212844835)
            ·
              refine ⟨322015001518945126819267253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214676667679296751212844835 322015001518945126819267253)
              ·
                refine ⟨30188906392401105639306305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 322015001518945126819267253 30188906392401105639306305)
                ·
                  refine ⟨22641679794300829229479729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30188906392401105639306305 22641679794300829229479729)
                  ·
                    refine ⟨16981259845725621922109797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22641679794300829229479729 16981259845725621922109797)
                    ·
                      refine ⟨3183986221073554110395587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16981259845725621922109797 3183986221073554110395587)
                      ·
                        rfl

theorem cell23_6200791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 5, 2, 2, 4].length) (baseStart_6200791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6200791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6200791 prefixEnd_6200791 := by exact prefixLift 6200791
  have htrace : WordTrace (prefixWord ++ tailWord_6200791) baseStart_6200791 baseEnd_6200791 := by
    simpa [prefixWord, tailWord_6200791, baseEnd_6200791] using wordTrace_append hprefix tailTrace_6200791
  have hstable : (prefixWord ++ tailWord_6200791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6200791).length < 2 ^ (prefixWord ++ tailWord_6200791).sum := by decide
  have hdescent : baseEnd_6200791 < baseStart_6200791 := by decide
  rcases family_descends (prefixWord ++ tailWord_6200791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6200811 : List Nat := [1, 1, 1, 1, 2, 3, 2, 1, 3, 5, 3]
def baseStart_6200811 : Nat := 118140960795 + 6200811 * 2 ^ 59
def prefixEnd_6200811 : Nat := 4983230072969 + 3 ^ 40 * 6200811 * 2
def baseEnd_6200811 : Nat := 3183996490686644032145495

theorem tailTrace_6200811 : CollatzResearch.WordTrace tailWord_6200811 prefixEnd_6200811 3183996490686644032145495 := by
  unfold tailWord_6200811
  simp only [CollatzResearch.WordTrace]
  refine ⟨226162157138528236051482287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150774771425685490700988191 226162157138528236051482287)
  ·
    refine ⟨339243235707792354077223431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226162157138528236051482287 339243235707792354077223431)
    ·
      refine ⟨508864853561688531115835147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339243235707792354077223431 508864853561688531115835147)
      ·
        refine ⟨763297280342532796673752721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 508864853561688531115835147 763297280342532796673752721)
        ·
          refine ⟨572472960256899597505314541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 763297280342532796673752721 572472960256899597505314541)
          ·
            refine ⟨214677360096337349064492953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 572472960256899597505314541 214677360096337349064492953)
            ·
              refine ⟨161008020072253011798369715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 214677360096337349064492953 161008020072253011798369715)
              ·
                refine ⟨241512030108379517697554573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 161008020072253011798369715 241512030108379517697554573)
                ·
                  refine ⟨90567011290642319136582965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 241512030108379517697554573 90567011290642319136582965)
                  ·
                    refine ⟨8490657308497717419054653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 90567011290642319136582965 8490657308497717419054653)
                    ·
                      refine ⟨3183996490686644032145495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8490657308497717419054653 3183996490686644032145495)
                      ·
                        rfl

theorem cell23_6200811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 5, 3].length) (baseStart_6200811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6200811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6200811 prefixEnd_6200811 := by exact prefixLift 6200811
  have htrace : WordTrace (prefixWord ++ tailWord_6200811) baseStart_6200811 baseEnd_6200811 := by
    simpa [prefixWord, tailWord_6200811, baseEnd_6200811] using wordTrace_append hprefix tailTrace_6200811
  have hstable : (prefixWord ++ tailWord_6200811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6200811).length < 2 ^ (prefixWord ++ tailWord_6200811).sum := by decide
  have hdescent : baseEnd_6200811 < baseStart_6200811 := by decide
  rcases family_descends (prefixWord ++ tailWord_6200811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6200831 : List Nat := [1, 1, 2, 2, 1, 2, 2, 3, 4, 5]
def baseStart_6200831 : Nat := 118140960795 + 6200831 * 2 ^ 59
def prefixEnd_6200831 : Nat := 4983230072969 + 3 ^ 40 * 6200831 * 2
def baseEnd_6200831 : Nat := 1061335586766577984631801

theorem tailTrace_6200831 : CollatzResearch.WordTrace tailWord_6200831 prefixEnd_6200831 1061335586766577984631801 := by
  unfold tailWord_6200831
  simp only [CollatzResearch.WordTrace]
  refine ⟨226162886598455779467210347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150775257732303852978140231 226162886598455779467210347)
  ·
    refine ⟨339244329897683669200815521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226162886598455779467210347 339244329897683669200815521)
    ·
      refine ⟨254433247423262751900611641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 339244329897683669200815521 254433247423262751900611641)
      ·
        refine ⟨190824935567447063925458731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 254433247423262751900611641 190824935567447063925458731)
        ·
          refine ⟨286237403351170595888188097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190824935567447063925458731 286237403351170595888188097)
          ·
            refine ⟨214678052513377946916141073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 286237403351170595888188097 214678052513377946916141073)
            ·
              refine ⟨161008539385033460187105805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 214678052513377946916141073 161008539385033460187105805)
              ·
                refine ⟨60378202269387547570164677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 161008539385033460187105805 60378202269387547570164677)
                ·
                  refine ⟨11320912925510165169405877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60378202269387547570164677 11320912925510165169405877)
                  ·
                    refine ⟨1061335586766577984631801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11320912925510165169405877 1061335586766577984631801)
                    ·
                      rfl

theorem cell23_6200831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 4, 5].length) (baseStart_6200831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6200831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6200831 prefixEnd_6200831 := by exact prefixLift 6200831
  have htrace : WordTrace (prefixWord ++ tailWord_6200831) baseStart_6200831 baseEnd_6200831 := by
    simpa [prefixWord, tailWord_6200831, baseEnd_6200831] using wordTrace_append hprefix tailTrace_6200831
  have hstable : (prefixWord ++ tailWord_6200831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6200831).length < 2 ^ (prefixWord ++ tailWord_6200831).sum := by decide
  have hdescent : baseEnd_6200831 < baseStart_6200831 := by decide
  rcases family_descends (prefixWord ++ tailWord_6200831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6200841 : List Nat := [1, 2, 1, 1, 3, 1, 3, 3, 1, 2, 5]
def baseStart_6200841 : Nat := 118140960795 + 6200841 * 2 ^ 59
def prefixEnd_6200841 : Nat := 4983230072969 + 3 ^ 40 * 6200841 * 2
def baseEnd_6200841 : Nat := 3184011895106278914770357

theorem tailTrace_6200841 : CollatzResearch.WordTrace tailWord_6200841 prefixEnd_6200841 3184011895106278914770357 := by
  unfold tailWord_6200841
  simp only [CollatzResearch.WordTrace]
  refine ⟨226163251328419551175074377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150775500885613034116716251 226163251328419551175074377)
  ·
    refine ⟨169622438496314663381305783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226163251328419551175074377 169622438496314663381305783)
    ·
      refine ⟨254433657744471995071958675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169622438496314663381305783 254433657744471995071958675)
      ·
        refine ⟨381650486616707992607938013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254433657744471995071958675 381650486616707992607938013)
        ·
          refine ⟨143118932481265497227976755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 381650486616707992607938013 143118932481265497227976755)
          ·
            refine ⟨214678398721898245841965133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143118932481265497227976755 214678398721898245841965133)
            ·
              refine ⟨80504399520711842190736925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 214678398721898245841965133 80504399520711842190736925)
              ·
                refine ⟨30189149820266940821526347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80504399520711842190736925 30189149820266940821526347)
                ·
                  refine ⟨45283724730400411232289521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30189149820266940821526347 45283724730400411232289521)
                  ·
                    refine ⟨33962793547800308424217141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45283724730400411232289521 33962793547800308424217141)
                    ·
                      refine ⟨3184011895106278914770357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33962793547800308424217141 3184011895106278914770357)
                      ·
                        rfl

theorem cell23_6200841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 3, 1, 2, 5].length) (baseStart_6200841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6200841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6200841 prefixEnd_6200841 := by exact prefixLift 6200841
  have htrace : WordTrace (prefixWord ++ tailWord_6200841) baseStart_6200841 baseEnd_6200841 := by
    simpa [prefixWord, tailWord_6200841, baseEnd_6200841] using wordTrace_append hprefix tailTrace_6200841
  have hstable : (prefixWord ++ tailWord_6200841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6200841).length < 2 ^ (prefixWord ++ tailWord_6200841).sum := by decide
  have hdescent : baseEnd_6200841 < baseStart_6200841 := by decide
  rcases family_descends (prefixWord ++ tailWord_6200841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6200865 : List Nat := [1, 2, 3, 2, 2, 4, 1, 1, 2, 5]
def baseStart_6200865 : Nat := 118140960795 + 6200865 * 2 ^ 59
def prefixEnd_6200865 : Nat := 4983230072969 + 3 ^ 40 * 6200865 * 2
def baseEnd_6200865 : Nat := 1061341406213995606956749

theorem tailTrace_6200865 : CollatzResearch.WordTrace tailWord_6200865 prefixEnd_6200865 1061341406213995606956749 := by
  unfold tailWord_6200865
  simp only [CollatzResearch.WordTrace]
  refine ⟨226164126680332603273948049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150776084453555068849298699 226164126680332603273948049)
  ·
    refine ⟨169623095010249452455461037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226164126680332603273948049 169623095010249452455461037)
    ·
      refine ⟨63608660628843544670797889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169623095010249452455461037 63608660628843544670797889)
      ·
        refine ⟨47706495471632658503098417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63608660628843544670797889 47706495471632658503098417)
        ·
          refine ⟨35779871603724493877323813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47706495471632658503098417 35779871603724493877323813)
          ·
            refine ⟨6708725925698342601998215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35779871603724493877323813 6708725925698342601998215)
            ·
              refine ⟨10063088888547513902997323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6708725925698342601998215 10063088888547513902997323)
              ·
                refine ⟨15094633332821270854495985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10063088888547513902997323 15094633332821270854495985)
                ·
                  refine ⟨11320974999615953140871989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15094633332821270854495985 11320974999615953140871989)
                  ·
                    refine ⟨1061341406213995606956749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11320974999615953140871989 1061341406213995606956749)
                    ·
                      rfl

theorem cell23_6200865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 1, 2, 5].length) (baseStart_6200865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6200865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6200865 prefixEnd_6200865 := by exact prefixLift 6200865
  have htrace : WordTrace (prefixWord ++ tailWord_6200865) baseStart_6200865 baseEnd_6200865 := by
    simpa [prefixWord, tailWord_6200865, baseEnd_6200865] using wordTrace_append hprefix tailTrace_6200865
  have hstable : (prefixWord ++ tailWord_6200865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6200865).length < 2 ^ (prefixWord ++ tailWord_6200865).sum := by decide
  have hdescent : baseEnd_6200865 < baseStart_6200865 := by decide
  rcases family_descends (prefixWord ++ tailWord_6200865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6200885 : List Nat := [1, 3, 3, 1, 1, 3, 1, 2, 2, 4, 2]
def baseStart_6200885 : Nat := 118140960795 + 6200885 * 2 ^ 59
def prefixEnd_6200885 : Nat := 4983230072969 + 3 ^ 40 * 6200885 * 2
def baseEnd_6200885 : Nat := 3184034488255076742620155

theorem tailTrace_6200885 : CollatzResearch.WordTrace tailWord_6200885 prefixEnd_6200885 3184034488255076742620155 := by
  unfold tailWord_6200885
  simp only [CollatzResearch.WordTrace]
  refine ⟨226164856140260146689676109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150776570760173431126450739 226164856140260146689676109)
  ·
    refine ⟨84811821052597555008628541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226164856140260146689676109 84811821052597555008628541)
    ·
      refine ⟨31804432894724083128235703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84811821052597555008628541 31804432894724083128235703)
      ·
        refine ⟨47706649342086124692353555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31804432894724083128235703 47706649342086124692353555)
        ·
          refine ⟨71559974013129187038530333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47706649342086124692353555 71559974013129187038530333)
          ·
            refine ⟨26834990254923445139448875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71559974013129187038530333 26834990254923445139448875)
            ·
              refine ⟨40252485382385167709173313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26834990254923445139448875 40252485382385167709173313)
              ·
                refine ⟨30189364036788875781879985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40252485382385167709173313 30189364036788875781879985)
                ·
                  refine ⟨22642023027591656836409989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30189364036788875781879985 22642023027591656836409989)
                  ·
                    refine ⟨4245379317673435656826873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22642023027591656836409989 4245379317673435656826873)
                    ·
                      refine ⟨3184034488255076742620155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4245379317673435656826873 3184034488255076742620155)
                      ·
                        rfl

theorem cell23_6200885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 2, 2, 4, 2].length) (baseStart_6200885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6200885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6200885 prefixEnd_6200885 := by exact prefixLift 6200885
  have htrace : WordTrace (prefixWord ++ tailWord_6200885) baseStart_6200885 baseEnd_6200885 := by
    simpa [prefixWord, tailWord_6200885, baseEnd_6200885] using wordTrace_append hprefix tailTrace_6200885
  have hstable : (prefixWord ++ tailWord_6200885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6200885).length < 2 ^ (prefixWord ++ tailWord_6200885).sum := by decide
  have hdescent : baseEnd_6200885 < baseStart_6200885 := by decide
  rcases family_descends (prefixWord ++ tailWord_6200885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6200895 : List Nat := [1, 1, 2, 2, 3, 4, 2, 1, 3, 4]
def baseStart_6200895 : Nat := 118140960795 + 6200895 * 2 ^ 59
def prefixEnd_6200895 : Nat := 4983230072969 + 3 ^ 40 * 6200895 * 2
def baseEnd_6200895 : Nat := 1061346541020540567831703

theorem tailTrace_6200895 : CollatzResearch.WordTrace tailWord_6200895 prefixEnd_6200895 1061346541020540567831703 := by
  unfold tailWord_6200895
  simp only [CollatzResearch.WordTrace]
  refine ⟨226165220870223918397540139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150776813913482612265026759 226165220870223918397540139)
  ·
    refine ⟨339247831305335877596310209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226165220870223918397540139 339247831305335877596310209)
    ·
      refine ⟨254435873479001908197232657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 339247831305335877596310209 254435873479001908197232657)
      ·
        refine ⟨190826905109251431147924493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 254435873479001908197232657 190826905109251431147924493)
        ·
          refine ⟨71560089415969286680471685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 190826905109251431147924493 71560089415969286680471685)
          ·
            refine ⟨13417516765494241252588441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71560089415969286680471685 13417516765494241252588441)
            ·
              refine ⟨10063137574120680939441331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13417516765494241252588441 10063137574120680939441331)
              ·
                refine ⟨15094706361181021409161997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10063137574120680939441331 15094706361181021409161997)
                ·
                  refine ⟨5660514885442883028435749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15094706361181021409161997 5660514885442883028435749)
                  ·
                    refine ⟨1061346541020540567831703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5660514885442883028435749 1061346541020540567831703)
                    ·
                      rfl

theorem cell23_6200895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 1, 3, 4].length) (baseStart_6200895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6200895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6200895 prefixEnd_6200895 := by exact prefixLift 6200895
  have htrace : WordTrace (prefixWord ++ tailWord_6200895) baseStart_6200895 baseEnd_6200895 := by
    simpa [prefixWord, tailWord_6200895, baseEnd_6200895] using wordTrace_append hprefix tailTrace_6200895
  have hstable : (prefixWord ++ tailWord_6200895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6200895).length < 2 ^ (prefixWord ++ tailWord_6200895).sum := by decide
  have hdescent : baseEnd_6200895 < baseStart_6200895 := by decide
  rcases family_descends (prefixWord ++ tailWord_6200895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6200911 : List Nat := [1, 1, 2, 1, 1, 2, 3, 1, 3, 2, 6]
def baseStart_6200911 : Nat := 118140960795 + 6200911 * 2 ^ 59
def prefixEnd_6200911 : Nat := 4983230072969 + 3 ^ 40 * 6200911 * 2
def baseEnd_6200911 : Nat := 3184047838752093640895035

theorem tailTrace_6200911 : CollatzResearch.WordTrace tailWord_6200911 prefixEnd_6200911 3184047838752093640895035 := by
  unfold tailWord_6200911
  simp only [CollatzResearch.WordTrace]
  refine ⟨226165804438165953130122587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150777202958777302086748391 226165804438165953130122587)
  ·
    refine ⟨339248706657248929695183881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226165804438165953130122587 339248706657248929695183881)
    ·
      refine ⟨254436529992936697271387911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 339248706657248929695183881 254436529992936697271387911)
      ·
        refine ⟨381654794989405045907081867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254436529992936697271387911 381654794989405045907081867)
        ·
          refine ⟨572482192484107568860622801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 381654794989405045907081867 572482192484107568860622801)
          ·
            refine ⟨429361644363080676645467101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 572482192484107568860622801 429361644363080676645467101)
            ·
              refine ⟨161010616636155253742050163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 429361644363080676645467101 161010616636155253742050163)
              ·
                refine ⟨241515924954232880613075245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 161010616636155253742050163 241515924954232880613075245)
                ·
                  refine ⟨90568471857837330229903217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 241515924954232880613075245 90568471857837330229903217)
                  ·
                    refine ⟨67926353893377997672427413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 90568471857837330229903217 67926353893377997672427413)
                    ·
                      refine ⟨3184047838752093640895035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67926353893377997672427413 3184047838752093640895035)
                      ·
                        rfl

theorem cell23_6200911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 2, 6].length) (baseStart_6200911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6200911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6200911 prefixEnd_6200911 := by exact prefixLift 6200911
  have htrace : WordTrace (prefixWord ++ tailWord_6200911) baseStart_6200911 baseEnd_6200911 := by
    simpa [prefixWord, tailWord_6200911, baseEnd_6200911] using wordTrace_append hprefix tailTrace_6200911
  have hstable : (prefixWord ++ tailWord_6200911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6200911).length < 2 ^ (prefixWord ++ tailWord_6200911).sum := by decide
  have hdescent : baseEnd_6200911 < baseStart_6200911 := by decide
  rcases family_descends (prefixWord ++ tailWord_6200911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6200921 : List Nat := [1, 2, 1, 2, 2, 1, 1, 2, 2, 9]
def baseStart_6200921 : Nat := 118140960795 + 6200921 * 2 ^ 59
def prefixEnd_6200921 : Nat := 4983230072969 + 3 ^ 40 * 6200921 * 2
def baseEnd_6200921 : Nat := 1061350991186212867256663

theorem tailTrace_6200921 : CollatzResearch.WordTrace tailWord_6200921 prefixEnd_6200921 1061350991186212867256663 := by
  unfold tailWord_6200921
  simp only [CollatzResearch.WordTrace]
  refine ⟨226166169168129724837986617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150777446112086483225324411 226166169168129724837986617)
  ·
    refine ⟨169624626876097293628489963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226166169168129724837986617 169624626876097293628489963)
    ·
      refine ⟨254436940314145940442734945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169624626876097293628489963 254436940314145940442734945)
      ·
        refine ⟨190827705235609455332051209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 254436940314145940442734945 190827705235609455332051209)
        ·
          refine ⟨143120778926707091499038407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190827705235609455332051209 143120778926707091499038407)
          ·
            refine ⟨214681168390060637248557611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143120778926707091499038407 214681168390060637248557611)
            ·
              refine ⟨322021752585090955872836417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214681168390060637248557611 322021752585090955872836417)
              ·
                refine ⟨241516314438818216904627313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 322021752585090955872836417 241516314438818216904627313)
                ·
                  refine ⟨181137235829113662678470485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 241516314438818216904627313 181137235829113662678470485)
                  ·
                    refine ⟨1061350991186212867256663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 181137235829113662678470485 1061350991186212867256663)
                    ·
                      rfl

theorem cell23_6200921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 9].length) (baseStart_6200921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6200921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6200921 prefixEnd_6200921 := by exact prefixLift 6200921
  have htrace : WordTrace (prefixWord ++ tailWord_6200921) baseStart_6200921 baseEnd_6200921 := by
    simpa [prefixWord, tailWord_6200921, baseEnd_6200921] using wordTrace_append hprefix tailTrace_6200921
  have hstable : (prefixWord ++ tailWord_6200921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6200921).length < 2 ^ (prefixWord ++ tailWord_6200921).sum := by decide
  have hdescent : baseEnd_6200921 < baseStart_6200921 := by decide
  rcases family_descends (prefixWord ++ tailWord_6200921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6200935 : List Nat := [1, 1, 5, 1, 1, 1, 2, 2, 5, 1, 3]
def baseStart_6200935 : Nat := 118140960795 + 6200935 * 2 ^ 59
def prefixEnd_6200935 : Nat := 4983230072969 + 3 ^ 40 * 6200935 * 2
def baseEnd_6200935 : Nat := 3184060162287801546994925

theorem tailTrace_6200935 : CollatzResearch.WordTrace tailWord_6200935 prefixEnd_6200935 3184060162287801546994925 := by
  unfold tailWord_6200935
  simp only [CollatzResearch.WordTrace]
  refine ⟨226166679790079005228996259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150777786526719336819330839 226166679790079005228996259)
  ·
    refine ⟨339250019685118507843494389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226166679790079005228996259 339250019685118507843494389)
    ·
      refine ⟨31804689345479860110327599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 339250019685118507843494389 31804689345479860110327599)
      ·
        refine ⟨47707034018219790165491399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31804689345479860110327599 47707034018219790165491399)
        ·
          refine ⟨71560551027329685248237099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47707034018219790165491399 71560551027329685248237099)
          ·
            refine ⟨107340826540994527872355649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71560551027329685248237099 107340826540994527872355649)
            ·
              refine ⟨80505619905745895904266737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107340826540994527872355649 80505619905745895904266737)
              ·
                refine ⟨60379214929309421928200053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80505619905745895904266737 60379214929309421928200053)
                ·
                  refine ⟨5660551399622758305768755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60379214929309421928200053 5660551399622758305768755)
                  ·
                    refine ⟨8490827099434137458653133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5660551399622758305768755 8490827099434137458653133)
                    ·
                      refine ⟨3184060162287801546994925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8490827099434137458653133 3184060162287801546994925)
                      ·
                        rfl

theorem cell23_6200935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 5, 1, 3].length) (baseStart_6200935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6200935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6200935 prefixEnd_6200935 := by exact prefixLift 6200935
  have htrace : WordTrace (prefixWord ++ tailWord_6200935) baseStart_6200935 baseEnd_6200935 := by
    simpa [prefixWord, tailWord_6200935, baseEnd_6200935] using wordTrace_append hprefix tailTrace_6200935
  have hstable : (prefixWord ++ tailWord_6200935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6200935).length < 2 ^ (prefixWord ++ tailWord_6200935).sum := by decide
  have hdescent : baseEnd_6200935 < baseStart_6200935 := by decide
  rcases family_descends (prefixWord ++ tailWord_6200935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6201005 : List Nat := [1, 5, 2, 1, 1, 1, 1, 2, 3, 2, 4]
def baseStart_6201005 : Nat := 118140960795 + 6201005 * 2 ^ 59
def prefixEnd_6201005 : Nat := 4983230072969 + 3 ^ 40 * 6201005 * 2
def baseEnd_6201005 : Nat := 3184096105933616273119603

theorem tailTrace_6201005 : CollatzResearch.WordTrace tailWord_6201005 prefixEnd_6201005 3184096105933616273119603 := by
  unfold tailWord_6201005
  simp only [CollatzResearch.WordTrace]
  refine ⟨226169232899825407184044469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150779488599883604789362979 226169232899825407184044469)
  ·
    refine ⟨21203365584358631923504169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 226169232899825407184044469 21203365584358631923504169)
    ·
      refine ⟨15902524188268973942628127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21203365584358631923504169 15902524188268973942628127)
      ·
        refine ⟨23853786282403460913942191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15902524188268973942628127 23853786282403460913942191)
        ·
          refine ⟨35780679423605191370913287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23853786282403460913942191 35780679423605191370913287)
          ·
            refine ⟨53671019135407787056369931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35780679423605191370913287 53671019135407787056369931)
            ·
              refine ⟨80506528703111680584554897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53671019135407787056369931 80506528703111680584554897)
              ·
                refine ⟨60379896527333760438416173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80506528703111680584554897 60379896527333760438416173)
                ·
                  refine ⟨22642461197750160164406065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60379896527333760438416173 22642461197750160164406065)
                  ·
                    refine ⟨16981845898312620123304549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22642461197750160164406065 16981845898312620123304549)
                    ·
                      refine ⟨3184096105933616273119603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16981845898312620123304549 3184096105933616273119603)
                      ·
                        rfl

theorem cell23_6201005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_6201005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6201005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6201005 prefixEnd_6201005 := by exact prefixLift 6201005
  have htrace : WordTrace (prefixWord ++ tailWord_6201005) baseStart_6201005 baseEnd_6201005 := by
    simpa [prefixWord, tailWord_6201005, baseEnd_6201005] using wordTrace_append hprefix tailTrace_6201005
  have hstable : (prefixWord ++ tailWord_6201005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6201005).length < 2 ^ (prefixWord ++ tailWord_6201005).sum := by decide
  have hdescent : baseEnd_6201005 < baseStart_6201005 := by decide
  rcases family_descends (prefixWord ++ tailWord_6201005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6201015 : List Nat := [1, 1, 3, 1, 5, 3, 1, 8]
def baseStart_6201015 : Nat := 118140960795 + 6201015 * 2 ^ 59
def prefixEnd_6201015 : Nat := 4983230072969 + 3 ^ 40 * 6201015 * 2
def baseEnd_6201015 : Nat := 117929675582968934592391

theorem tailTrace_6201015 : CollatzResearch.WordTrace tailWord_6201015 prefixEnd_6201015 117929675582968934592391 := by
  unfold tailWord_6201015
  simp only [CollatzResearch.WordTrace]
  refine ⟨226169597629789178891908499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150779731753192785927938999 226169597629789178891908499)
  ·
    refine ⟨339254396444683768337862749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226169597629789178891908499 339254396444683768337862749)
    ·
      refine ⟨127220398666756413126698531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 339254396444683768337862749 127220398666756413126698531)
      ·
        refine ⟨190830598000134619690047797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127220398666756413126698531 190830598000134619690047797)
        ·
          refine ⟨17890368562512620595941981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 190830598000134619690047797 17890368562512620595941981)
          ·
            refine ⟨6708888210942232723478243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17890368562512620595941981 6708888210942232723478243)
            ·
              refine ⟨10063332316413349085217365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6708888210942232723478243 10063332316413349085217365)
              ·
                refine ⟨117929675582968934592391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10063332316413349085217365 117929675582968934592391)
                ·
                  rfl

theorem cell23_6201015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 8].length) (baseStart_6201015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6201015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6201015 prefixEnd_6201015 := by exact prefixLift 6201015
  have htrace : WordTrace (prefixWord ++ tailWord_6201015) baseStart_6201015 baseEnd_6201015 := by
    simpa [prefixWord, tailWord_6201015, baseEnd_6201015] using wordTrace_append hprefix tailTrace_6201015
  have hstable : (prefixWord ++ tailWord_6201015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6201015).length < 2 ^ (prefixWord ++ tailWord_6201015).sum := by decide
  have hdescent : baseEnd_6201015 < baseStart_6201015 := by decide
  rcases family_descends (prefixWord ++ tailWord_6201015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6201022 : List Nat := [4, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4]
def baseStart_6201022 : Nat := 118140960795 + 6201022 * 2 ^ 59
def prefixEnd_6201022 : Nat := 4983230072969 + 3 ^ 40 * 6201022 * 2
def baseEnd_6201022 : Nat := 3184104835104742706607025

theorem tailTrace_6201022 : CollatzResearch.WordTrace tailWord_6201022 prefixEnd_6201022 3184104835104742706607025 := by
  unfold tailWord_6201022
  simp only [CollatzResearch.WordTrace]
  refine ⟨28271231617595477385926665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150779901960509212724942213 28271231617595477385926665)
  ·
    refine ⟨21203423713196608039444999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28271231617595477385926665 21203423713196608039444999)
    ·
      refine ⟨31805135569794912059167499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21203423713196608039444999 31805135569794912059167499)
      ·
        refine ⟨47707703354692368088751249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31805135569794912059167499 47707703354692368088751249)
        ·
          refine ⟨35780777516019276066563437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47707703354692368088751249 35780777516019276066563437)
          ·
            refine ⟨13417791568507228524961289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35780777516019276066563437 13417791568507228524961289)
            ·
              refine ⟨10063343676380421393720967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13417791568507228524961289 10063343676380421393720967)
              ·
                refine ⟨15095015514570632090581451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10063343676380421393720967 15095015514570632090581451)
                ·
                  refine ⟨22642523271855948135872177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15095015514570632090581451 22642523271855948135872177)
                  ·
                    refine ⟨16981892453891961101904133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22642523271855948135872177 16981892453891961101904133)
                    ·
                      refine ⟨3184104835104742706607025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16981892453891961101904133 3184104835104742706607025)
                      ·
                        rfl

theorem cell23_6201022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4].length) (baseStart_6201022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6201022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6201022 prefixEnd_6201022 := by exact prefixLift 6201022
  have htrace : WordTrace (prefixWord ++ tailWord_6201022) baseStart_6201022 baseEnd_6201022 := by
    simpa [prefixWord, tailWord_6201022, baseEnd_6201022] using wordTrace_append hprefix tailTrace_6201022
  have hstable : (prefixWord ++ tailWord_6201022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6201022).length < 2 ^ (prefixWord ++ tailWord_6201022).sum := by decide
  have hdescent : baseEnd_6201022 < baseStart_6201022 := by decide
  rcases family_descends (prefixWord ++ tailWord_6201022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6201042 : List Nat := [3, 2, 2, 2, 2, 1, 2, 2, 1, 3, 3]
def baseStart_6201042 : Nat := 118140960795 + 6201042 * 2 ^ 59
def prefixEnd_6201042 : Nat := 4983230072969 + 3 ^ 40 * 6201042 * 2
def baseEnd_6201042 : Nat := 3184115104717832628356933

theorem tailTrace_6201042 : CollatzResearch.WordTrace tailWord_6201042 prefixEnd_6201042 3184115104717832628356933 := by
  unfold tailWord_6201042
  simp only [CollatzResearch.WordTrace]
  refine ⟨56542645600172840625785345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150780388267127575002094253 56542645600172840625785345)
  ·
    refine ⟨42406984200129630469339009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56542645600172840625785345 42406984200129630469339009)
    ·
      refine ⟨31805238150097222852004257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42406984200129630469339009 31805238150097222852004257)
      ·
        refine ⟨23853928612572917139003193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31805238150097222852004257 23853928612572917139003193)
        ·
          refine ⟨17890446459429687854252395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23853928612572917139003193 17890446459429687854252395)
          ·
            refine ⟨26835669689144531781378593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17890446459429687854252395 26835669689144531781378593)
            ·
              refine ⟨20126752266858398836033945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26835669689144531781378593 20126752266858398836033945)
              ·
                refine ⟨15095064200143799127025459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20126752266858398836033945 15095064200143799127025459)
                ·
                  refine ⟨22642596300215698690538189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15095064200143799127025459 22642596300215698690538189)
                  ·
                    refine ⟨8490973612580887008951821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22642596300215698690538189 8490973612580887008951821)
                    ·
                      refine ⟨3184115104717832628356933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8490973612580887008951821 3184115104717832628356933)
                      ·
                        rfl

theorem cell23_6201042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_6201042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6201042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6201042 prefixEnd_6201042 := by exact prefixLift 6201042
  have htrace : WordTrace (prefixWord ++ tailWord_6201042) baseStart_6201042 baseEnd_6201042 := by
    simpa [prefixWord, tailWord_6201042, baseEnd_6201042] using wordTrace_append hprefix tailTrace_6201042
  have hstable : (prefixWord ++ tailWord_6201042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6201042).length < 2 ^ (prefixWord ++ tailWord_6201042).sum := by decide
  have hdescent : baseEnd_6201042 < baseStart_6201042 := by decide
  rcases family_descends (prefixWord ++ tailWord_6201042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6201053 : List Nat := [1, 4, 3, 3, 2, 1, 1, 2, 2, 4]
def baseStart_6201053 : Nat := 118140960795 + 6201053 * 2 ^ 59
def prefixEnd_6201053 : Nat := 4983230072969 + 3 ^ 40 * 6201053 * 2
def baseEnd_6201053 : Nat := 1061373584335010695106461

theorem tailTrace_6201053 : CollatzResearch.WordTrace tailWord_6201053 prefixEnd_6201053 1061373584335010695106461 := by
  unfold tailWord_6201053
  simp only [CollatzResearch.WordTrace]
  refine ⟨226170983603651511381791813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150780655735767674254527875 226170983603651511381791813)
  ·
    refine ⟨42407059425684658384085965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 226170983603651511381791813 42407059425684658384085965)
    ·
      refine ⟨15902647284631746894032237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42407059425684658384085965 15902647284631746894032237)
      ·
        refine ⟨5963492731736905085262089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15902647284631746894032237 5963492731736905085262089)
        ·
          refine ⟨4472619548802678813946567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5963492731736905085262089 4472619548802678813946567)
          ·
            refine ⟨6708929323204018220919851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4472619548802678813946567 6708929323204018220919851)
            ·
              refine ⟨10063393984806027331379777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6708929323204018220919851 10063393984806027331379777)
              ·
                refine ⟨7547545488604520498534833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10063393984806027331379777 7547545488604520498534833)
                ·
                  refine ⟨5660659116453390373901125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7547545488604520498534833 5660659116453390373901125)
                  ·
                    refine ⟨1061373584335010695106461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5660659116453390373901125 1061373584335010695106461)
                    ·
                      rfl

theorem cell23_6201053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_6201053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6201053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6201053 prefixEnd_6201053 := by exact prefixLift 6201053
  have htrace : WordTrace (prefixWord ++ tailWord_6201053) baseStart_6201053 baseEnd_6201053 := by
    simpa [prefixWord, tailWord_6201053, baseEnd_6201053] using wordTrace_append hprefix tailTrace_6201053
  have hstable : (prefixWord ++ tailWord_6201053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6201053).length < 2 ^ (prefixWord ++ tailWord_6201053).sum := by decide
  have hdescent : baseEnd_6201053 < baseStart_6201053 := by decide
  rcases family_descends (prefixWord ++ tailWord_6201053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6201059 : List Nat := [1, 1, 1, 7, 2, 1, 1, 1, 4, 1, 3]
def baseStart_6201059 : Nat := 118140960795 + 6201059 * 2 ^ 59
def prefixEnd_6201059 : Nat := 4983230072969 + 3 ^ 40 * 6201059 * 2
def baseEnd_6201059 : Nat := 3184123833888959061844355

theorem tailTrace_6201059 : CollatzResearch.WordTrace tailWord_6201059 prefixEnd_6201059 3184123833888959061844355 := by
  unfold tailWord_6201059
  simp only [CollatzResearch.WordTrace]
  refine ⟨226171202441629774406510231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150780801627753182937673487 226171202441629774406510231)
  ·
    refine ⟨339256803662444661609765347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226171202441629774406510231 339256803662444661609765347)
    ·
      refine ⟨508885205493666992414648021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339256803662444661609765347 508885205493666992414648021)
      ·
        refine ⟨11926997003757820134718313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 508885205493666992414648021 11926997003757820134718313)
        ·
          refine ⟨8945247752818365101038735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11926997003757820134718313 8945247752818365101038735)
          ·
            refine ⟨13417871629227547651558103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8945247752818365101038735 13417871629227547651558103)
            ·
              refine ⟨20126807443841321477337155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13417871629227547651558103 20126807443841321477337155)
              ·
                refine ⟨30190211165761982216005733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20126807443841321477337155 30190211165761982216005733)
                ·
                  refine ⟨5660664593580371665501075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30190211165761982216005733 5660664593580371665501075)
                  ·
                    refine ⟨8490996890370557498251613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5660664593580371665501075 8490996890370557498251613)
                    ·
                      refine ⟨3184123833888959061844355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8490996890370557498251613 3184123833888959061844355)
                      ·
                        rfl

theorem cell23_6201059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_6201059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6201059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6201059 prefixEnd_6201059 := by exact prefixLift 6201059
  have htrace : WordTrace (prefixWord ++ tailWord_6201059) baseStart_6201059 baseEnd_6201059 := by
    simpa [prefixWord, tailWord_6201059, baseEnd_6201059] using wordTrace_append hprefix tailTrace_6201059
  have hstable : (prefixWord ++ tailWord_6201059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6201059).length < 2 ^ (prefixWord ++ tailWord_6201059).sum := by decide
  have hdescent : baseEnd_6201059 < baseStart_6201059 := by decide
  rcases family_descends (prefixWord ++ tailWord_6201059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6201076 : List Nat := [2, 6, 1, 1, 1, 1, 3, 1, 1, 3, 3]
def baseStart_6201076 : Nat := 118140960795 + 6201076 * 2 ^ 59
def prefixEnd_6201076 : Nat := 4983230072969 + 3 ^ 40 * 6201076 * 2
def baseEnd_6201076 : Nat := 3184132563060085495331777

theorem tailTrace_6201076 : CollatzResearch.WordTrace tailWord_6201076 prefixEnd_6201076 3184132563060085495331777 := by
  unfold tailWord_6201076
  simp only [CollatzResearch.WordTrace]
  refine ⟨113085911241284093154939541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150781214988378790873252721 113085911241284093154939541)
  ·
    refine ⟨5300902089435191866637791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 113085911241284093154939541 5300902089435191866637791)
    ·
      refine ⟨7951353134152787799956687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5300902089435191866637791 7951353134152787799956687)
      ·
        refine ⟨11927029701229181699935031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7951353134152787799956687 11927029701229181699935031)
        ·
          refine ⟨17890544551843772549902547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11927029701229181699935031 17890544551843772549902547)
          ·
            refine ⟨26835816827765658824853821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17890544551843772549902547 26835816827765658824853821)
            ·
              refine ⟨10063431310412122059320183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26835816827765658824853821 10063431310412122059320183)
              ·
                refine ⟨15095146965618183088980275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10063431310412122059320183 15095146965618183088980275)
                ·
                  refine ⟨22642720448427274633470413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15095146965618183088980275 22642720448427274633470413)
                  ·
                    refine ⟨8491020168160227987551405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22642720448427274633470413 8491020168160227987551405)
                    ·
                      refine ⟨3184132563060085495331777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8491020168160227987551405 3184132563060085495331777)
                      ·
                        rfl

theorem cell23_6201076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_6201076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6201076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6201076 prefixEnd_6201076 := by exact prefixLift 6201076
  have htrace : WordTrace (prefixWord ++ tailWord_6201076) baseStart_6201076 baseEnd_6201076 := by
    simpa [prefixWord, tailWord_6201076, baseEnd_6201076] using wordTrace_append hprefix tailTrace_6201076
  have hstable : (prefixWord ++ tailWord_6201076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6201076).length < 2 ^ (prefixWord ++ tailWord_6201076).sum := by decide
  have hdescent : baseEnd_6201076 < baseStart_6201076 := by decide
  rcases family_descends (prefixWord ++ tailWord_6201076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6201192 : List Nat := [2, 1, 4, 2, 1, 1, 2, 2, 1, 4, 3]
def baseStart_6201192 : Nat := 118140960795 + 6201192 * 2 ^ 59
def prefixEnd_6201192 : Nat := 4983230072969 + 3 ^ 40 * 6201192 * 2
def baseEnd_6201192 : Nat := 3184192126816007041481243

theorem tailTrace_6201192 : CollatzResearch.WordTrace tailWord_6201192 prefixEnd_6201192 3184192126816007041481243 := by
  unfold tailWord_6201192
  simp only [CollatzResearch.WordTrace]
  refine ⟨113088026675073969060550915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150784035566765292080734553 113088026675073969060550915)
  ·
    refine ⟨169632040012610953590826373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113088026675073969060550915 169632040012610953590826373)
    ·
      refine ⟨31806007502364553798279945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 169632040012610953590826373 31806007502364553798279945)
      ·
        refine ⟨23854505626773415348709959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31806007502364553798279945 23854505626773415348709959)
        ·
          refine ⟨35781758440160123023064939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23854505626773415348709959 35781758440160123023064939)
          ·
            refine ⟨53672637660240184534597409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35781758440160123023064939 53672637660240184534597409)
            ·
              refine ⟨40254478245180138400948057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53672637660240184534597409 40254478245180138400948057)
              ·
                refine ⟨30190858683885103800711043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40254478245180138400948057 30190858683885103800711043)
                ·
                  refine ⟨45286288025827655701066565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30190858683885103800711043 45286288025827655701066565)
                  ·
                    refine ⟨8491179004842685443949981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45286288025827655701066565 8491179004842685443949981)
                    ·
                      refine ⟨3184192126816007041481243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8491179004842685443949981 3184192126816007041481243)
                      ·
                        rfl

theorem cell23_6201192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_6201192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6201192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6201192 prefixEnd_6201192 := by exact prefixLift 6201192
  have htrace : WordTrace (prefixWord ++ tailWord_6201192) baseStart_6201192 baseEnd_6201192 := by
    simpa [prefixWord, tailWord_6201192, baseEnd_6201192] using wordTrace_append hprefix tailTrace_6201192
  have hstable : (prefixWord ++ tailWord_6201192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6201192).length < 2 ^ (prefixWord ++ tailWord_6201192).sum := by decide
  have hdescent : baseEnd_6201192 < baseStart_6201192 := by decide
  rcases family_descends (prefixWord ++ tailWord_6201192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6201232 : List Nat := [2, 1, 1, 1, 1, 1, 2, 4, 3, 5, 2]
def baseStart_6201232 : Nat := 118140960795 + 6201232 * 2 ^ 59
def prefixEnd_6201232 : Nat := 4983230072969 + 3 ^ 40 * 6201232 * 2
def baseEnd_6201232 : Nat := 3184212666042186884981059

theorem tailTrace_6201232 : CollatzResearch.WordTrace tailWord_6201232 prefixEnd_6201232 3184212666042186884981059 := by
  unfold tailWord_6201232
  simp only [CollatzResearch.WordTrace]
  refine ⟨113088756135001512476278975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150785008180002016635038633 113088756135001512476278975)
  ·
    refine ⟨169633134202502268714418463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113088756135001512476278975 169633134202502268714418463)
    ·
      refine ⟨254449701303753403071627695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169633134202502268714418463 254449701303753403071627695)
      ·
        refine ⟨381674551955630104607441543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254449701303753403071627695 381674551955630104607441543)
        ·
          refine ⟨572511827933445156911162315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 381674551955630104607441543 572511827933445156911162315)
          ·
            refine ⟨858767741900167735366743473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 572511827933445156911162315 858767741900167735366743473)
            ·
              refine ⟨644075806425125801525057605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 858767741900167735366743473 644075806425125801525057605)
              ·
                refine ⟨120764213704711087785948301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 644075806425125801525057605 120764213704711087785948301)
                ·
                  refine ⟨45286580139266657919730613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 120764213704711087785948301 45286580139266657919730613)
                  ·
                    refine ⟨4245616888056249179974745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45286580139266657919730613 4245616888056249179974745)
                    ·
                      refine ⟨3184212666042186884981059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4245616888056249179974745 3184212666042186884981059)
                      ·
                        rfl

theorem cell23_6201232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 3, 5, 2].length) (baseStart_6201232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6201232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6201232 prefixEnd_6201232 := by exact prefixLift 6201232
  have htrace : WordTrace (prefixWord ++ tailWord_6201232) baseStart_6201232 baseEnd_6201232 := by
    simpa [prefixWord, tailWord_6201232, baseEnd_6201232] using wordTrace_append hprefix tailTrace_6201232
  have hstable : (prefixWord ++ tailWord_6201232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6201232).length < 2 ^ (prefixWord ++ tailWord_6201232).sum := by decide
  have hdescent : baseEnd_6201232 < baseStart_6201232 := by decide
  rcases family_descends (prefixWord ++ tailWord_6201232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6201239 : List Nat := [1, 1, 3, 3, 1, 3, 1, 3, 3, 1, 3]
def baseStart_6201239 : Nat := 118140960795 + 6201239 * 2 ^ 59
def prefixEnd_6201239 : Nat := 4983230072969 + 3 ^ 40 * 6201239 * 2
def baseEnd_6201239 : Nat := 3184216260406768357593527

theorem tailTrace_6201239 : CollatzResearch.WordTrace tailWord_6201239 prefixEnd_6201239 3184216260406768357593527 := by
  unfold tailWord_6201239
  simp only [CollatzResearch.WordTrace]
  refine ⟨226177767580977665148062771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150785178387318443432041847 226177767580977665148062771)
  ·
    refine ⟨339266651371466497722094157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226177767580977665148062771 339266651371466497722094157)
    ·
      refine ⟨127224994264299936645785309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 339266651371466497722094157 127224994264299936645785309)
      ·
        refine ⟨47709372849112476242169491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127224994264299936645785309 47709372849112476242169491)
        ·
          refine ⟨71564059273668714363254237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47709372849112476242169491 71564059273668714363254237)
          ·
            refine ⟨26836522227625767886220339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71564059273668714363254237 26836522227625767886220339)
            ·
              refine ⟨40254783341438651829330509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26836522227625767886220339 40254783341438651829330509)
              ·
                refine ⟨15095543753039494435998941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40254783341438651829330509 15095543753039494435998941)
                ·
                  refine ⟨5660828907389810413499603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15095543753039494435998941 5660828907389810413499603)
                  ·
                    refine ⟨8491243361084715620249405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5660828907389810413499603 8491243361084715620249405)
                    ·
                      refine ⟨3184216260406768357593527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8491243361084715620249405 3184216260406768357593527)
                      ·
                        rfl

theorem cell23_6201239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 3, 3, 1, 3].length) (baseStart_6201239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6201239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6201239 prefixEnd_6201239 := by exact prefixLift 6201239
  have htrace : WordTrace (prefixWord ++ tailWord_6201239) baseStart_6201239 baseEnd_6201239 := by
    simpa [prefixWord, tailWord_6201239, baseEnd_6201239] using wordTrace_append hprefix tailTrace_6201239
  have hstable : (prefixWord ++ tailWord_6201239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6201239).length < 2 ^ (prefixWord ++ tailWord_6201239).sum := by decide
  have hdescent : baseEnd_6201239 < baseStart_6201239 := by decide
  rcases family_descends (prefixWord ++ tailWord_6201239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6201272 : List Nat := [2, 1, 2, 1, 2, 3, 1, 1, 6, 4]
def baseStart_6201272 : Nat := 118140960795 + 6201272 * 2 ^ 59
def prefixEnd_6201272 : Nat := 4983230072969 + 3 ^ 40 * 6201272 * 2
def baseEnd_6201272 : Nat := 1061411068422788909493625

theorem tailTrace_6201272 : CollatzResearch.WordTrace tailWord_6201272 prefixEnd_6201272 1061411068422788909493625 := by
  unfold tailWord_6201272
  simp only [CollatzResearch.WordTrace]
  refine ⟨113089485594929055892007035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150785980793238741189342713 113089485594929055892007035)
  ·
    refine ⟨169634228392393583838010553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113089485594929055892007035 169634228392393583838010553)
    ·
      refine ⟨127225671294295187878507915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169634228392393583838010553 127225671294295187878507915)
      ·
        refine ⟨190838506941442781817761873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127225671294295187878507915 190838506941442781817761873)
        ·
          refine ⟨143128880206082086363321405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190838506941442781817761873 143128880206082086363321405)
          ·
            refine ⟨53673330077280782386245527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143128880206082086363321405 53673330077280782386245527)
            ·
              refine ⟨80509995115921173579368291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53673330077280782386245527 80509995115921173579368291)
              ·
                refine ⟨120764992673881760369052437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80509995115921173579368291 120764992673881760369052437)
                ·
                  refine ⟨5660859031588207517299333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 120764992673881760369052437 5660859031588207517299333)
                  ·
                    refine ⟨1061411068422788909493625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5660859031588207517299333 1061411068422788909493625)
                    ·
                      rfl

theorem cell23_6201272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 6, 4].length) (baseStart_6201272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6201272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6201272 prefixEnd_6201272 := by exact prefixLift 6201272
  have htrace : WordTrace (prefixWord ++ tailWord_6201272) baseStart_6201272 baseEnd_6201272 := by
    simpa [prefixWord, tailWord_6201272, baseEnd_6201272] using wordTrace_append hprefix tailTrace_6201272
  have hstable : (prefixWord ++ tailWord_6201272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6201272).length < 2 ^ (prefixWord ++ tailWord_6201272).sum := by decide
  have hdescent : baseEnd_6201272 < baseStart_6201272 := by decide
  rcases family_descends (prefixWord ++ tailWord_6201272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6201275 : List Nat := [1, 1, 1, 1, 1, 2, 2, 4, 3, 1, 6]
def baseStart_6201275 : Nat := 118140960795 + 6201275 * 2 ^ 59
def prefixEnd_6201275 : Nat := 4983230072969 + 3 ^ 40 * 6201275 * 2
def baseEnd_6201275 : Nat := 3184234745710330216743361

theorem tailTrace_6201275 : CollatzResearch.WordTrace tailWord_6201275 prefixEnd_6201275 3184234745710330216743361 := by
  unfold tailWord_6201275
  simp only [CollatzResearch.WordTrace]
  refine ⟨226179080608847243296373279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150786053739231495530915519 226179080608847243296373279)
  ·
    refine ⟨339268620913270864944559919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226179080608847243296373279 339268620913270864944559919)
    ·
      refine ⟨508902931369906297416839879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339268620913270864944559919 508902931369906297416839879)
      ·
        refine ⟨763354397054859446125259819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 508902931369906297416839879 763354397054859446125259819)
        ·
          refine ⟨1145031595582289169187889729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 763354397054859446125259819 1145031595582289169187889729)
          ·
            refine ⟨858773696686716876890917297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1145031595582289169187889729 858773696686716876890917297)
            ·
              refine ⟨644080272515037657668187973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 858773696686716876890917297 644080272515037657668187973)
              ·
                refine ⟨120765051096569560812785245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 644080272515037657668187973 120765051096569560812785245)
                ·
                  refine ⟨45286894161213585304794467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 120765051096569560812785245 45286894161213585304794467)
                  ·
                    refine ⟨67930341241820377957191701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45286894161213585304794467 67930341241820377957191701)
                    ·
                      refine ⟨3184234745710330216743361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67930341241820377957191701 3184234745710330216743361)
                      ·
                        rfl

theorem cell23_6201275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 3, 1, 6].length) (baseStart_6201275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6201275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6201275 prefixEnd_6201275 := by exact prefixLift 6201275
  have htrace : WordTrace (prefixWord ++ tailWord_6201275) baseStart_6201275 baseEnd_6201275 := by
    simpa [prefixWord, tailWord_6201275, baseEnd_6201275] using wordTrace_append hprefix tailTrace_6201275
  have hstable : (prefixWord ++ tailWord_6201275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6201275).length < 2 ^ (prefixWord ++ tailWord_6201275).sum := by decide
  have hdescent : baseEnd_6201275 < baseStart_6201275 := by decide
  rcases family_descends (prefixWord ++ tailWord_6201275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6201292 : List Nat := [2, 2, 1, 4, 1, 2, 1, 2, 1, 1, 6]
def baseStart_6201292 : Nat := 118140960795 + 6201292 * 2 ^ 59
def prefixEnd_6201292 : Nat := 4983230072969 + 3 ^ 40 * 6201292 * 2
def baseEnd_6201292 : Nat := 3184243474881456650230783

theorem tailTrace_6201292 : CollatzResearch.WordTrace tailWord_6201292 prefixEnd_6201292 3184243474881456650230783 := by
  unfold tailWord_6201292
  simp only [CollatzResearch.WordTrace]
  refine ⟨113089850324892827599871065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150786467099857103466494753 113089850324892827599871065)
  ·
    refine ⟨84817387743669620699903299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113089850324892827599871065 84817387743669620699903299)
    ·
      refine ⟨127226081615504431049854949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84817387743669620699903299 127226081615504431049854949)
      ·
        refine ⟨23854890302907080821847803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127226081615504431049854949 23854890302907080821847803)
        ·
          refine ⟨35782335454360621232771705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23854890302907080821847803 35782335454360621232771705)
          ·
            refine ⟨26836751590770465924578779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35782335454360621232771705 26836751590770465924578779)
            ·
              refine ⟨40255127386155698886868169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26836751590770465924578779 40255127386155698886868169)
              ·
                refine ⟨30191345539616774165151127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40255127386155698886868169 30191345539616774165151127)
                ·
                  refine ⟨45287018309425161247726691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30191345539616774165151127 45287018309425161247726691)
                  ·
                    refine ⟨67930527464137741871590037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45287018309425161247726691 67930527464137741871590037)
                    ·
                      refine ⟨3184243474881456650230783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67930527464137741871590037 3184243474881456650230783)
                      ·
                        rfl

theorem cell23_6201292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_6201292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6201292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6201292 prefixEnd_6201292 := by exact prefixLift 6201292
  have htrace : WordTrace (prefixWord ++ tailWord_6201292) baseStart_6201292 baseEnd_6201292 := by
    simpa [prefixWord, tailWord_6201292, baseEnd_6201292] using wordTrace_append hprefix tailTrace_6201292
  have hstable : (prefixWord ++ tailWord_6201292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6201292).length < 2 ^ (prefixWord ++ tailWord_6201292).sum := by decide
  have hdescent : baseEnd_6201292 < baseStart_6201292 := by decide
  rcases family_descends (prefixWord ++ tailWord_6201292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6201296 : List Nat := [2, 1, 1, 1, 1, 2, 7, 1, 3, 2, 2]
def baseStart_6201296 : Nat := 118140960795 + 6201296 * 2 ^ 59
def prefixEnd_6201296 : Nat := 4983230072969 + 3 ^ 40 * 6201296 * 2
def baseEnd_6201296 : Nat := 3184245528804074634580765

theorem tailTrace_6201296 : CollatzResearch.WordTrace tailWord_6201296 prefixEnd_6201296 3184245528804074634580765 := by
  unfold tailWord_6201296
  simp only [CollatzResearch.WordTrace]
  refine ⟨113089923270885581941443871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150786564361180775921925161 113089923270885581941443871)
  ·
    refine ⟨169634884906328372912165807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113089923270885581941443871 169634884906328372912165807)
    ·
      refine ⟨254452327359492559368248711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169634884906328372912165807 254452327359492559368248711)
      ·
        refine ⟨381678491039238839052373067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254452327359492559368248711 381678491039238839052373067)
        ·
          refine ⟨572517736558858258578559601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 381678491039238839052373067 572517736558858258578559601)
          ·
            refine ⟨429388302419143693933919701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 572517736558858258578559601 429388302419143693933919701)
            ·
              refine ⟨10063788337948680326576243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 429388302419143693933919701 10063788337948680326576243)
              ·
                refine ⟨15095682506923020489864365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10063788337948680326576243 15095682506923020489864365)
                ·
                  refine ⟨5660880940096132683699137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15095682506923020489864365 5660880940096132683699137)
                  ·
                    refine ⟨4245660705072099512774353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5660880940096132683699137 4245660705072099512774353)
                    ·
                      refine ⟨3184245528804074634580765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4245660705072099512774353 3184245528804074634580765)
                      ·
                        rfl

theorem cell23_6201296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 1, 3, 2, 2].length) (baseStart_6201296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6201296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6201296 prefixEnd_6201296 := by exact prefixLift 6201296
  have htrace : WordTrace (prefixWord ++ tailWord_6201296) baseStart_6201296 baseEnd_6201296 := by
    simpa [prefixWord, tailWord_6201296, baseEnd_6201296] using wordTrace_append hprefix tailTrace_6201296
  have hstable : (prefixWord ++ tailWord_6201296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6201296).length < 2 ^ (prefixWord ++ tailWord_6201296).sum := by decide
  have hdescent : baseEnd_6201296 < baseStart_6201296 := by decide
  rcases family_descends (prefixWord ++ tailWord_6201296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6201306 : List Nat := [3, 1, 1, 2, 5, 1, 1, 3, 2, 4]
def baseStart_6201306 : Nat := 118140960795 + 6201306 * 2 ^ 59
def prefixEnd_6201306 : Nat := 4983230072969 + 3 ^ 40 * 6201306 * 2
def baseEnd_6201306 : Nat := 1061416887870206531818573

theorem tailTrace_6201306 : CollatzResearch.WordTrace tailWord_6201306 prefixEnd_6201306 1061416887870206531818573 := by
  unfold tailWord_6201306
  simp only [CollatzResearch.WordTrace]
  refine ⟨56545052817933733897687943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150786807514489957060501181 56545052817933733897687943)
  ·
    refine ⟨84817579226900600846531915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56545052817933733897687943 84817579226900600846531915)
    ·
      refine ⟨127226368840350901269797873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84817579226900600846531915 127226368840350901269797873)
      ·
        refine ⟨95419776630263175952348405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127226368840350901269797873 95419776630263175952348405)
        ·
          refine ⟨8945604059087172745532663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 95419776630263175952348405 8945604059087172745532663)
          ·
            refine ⟨13418406088630759118298995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8945604059087172745532663 13418406088630759118298995)
            ·
              refine ⟨20127609132946138677448493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13418406088630759118298995 20127609132946138677448493)
              ·
                refine ⟨7547853424854802004043185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20127609132946138677448493 7547853424854802004043185)
                ·
                  refine ⟨5660890068641101503032389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7547853424854802004043185 5660890068641101503032389)
                  ·
                    refine ⟨1061416887870206531818573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5660890068641101503032389 1061416887870206531818573)
                    ·
                      rfl

theorem cell23_6201306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 3, 2, 4].length) (baseStart_6201306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6201306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6201306 prefixEnd_6201306 := by exact prefixLift 6201306
  have htrace : WordTrace (prefixWord ++ tailWord_6201306) baseStart_6201306 baseEnd_6201306 := by
    simpa [prefixWord, tailWord_6201306, baseEnd_6201306] using wordTrace_append hprefix tailTrace_6201306
  have hstable : (prefixWord ++ tailWord_6201306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6201306).length < 2 ^ (prefixWord ++ tailWord_6201306).sum := by decide
  have hdescent : baseEnd_6201306 < baseStart_6201306 := by decide
  rcases family_descends (prefixWord ++ tailWord_6201306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6201312 : List Nat := [2, 1, 1, 3, 1, 1, 1, 2, 5, 3, 3]
def baseStart_6201312 : Nat := 118140960795 + 6201312 * 2 ^ 59
def prefixEnd_6201312 : Nat := 4983230072969 + 3 ^ 40 * 6201312 * 2
def baseEnd_6201312 : Nat := 3184253744494546571980691

theorem tailTrace_6201312 : CollatzResearch.WordTrace tailWord_6201312 prefixEnd_6201312 3184253744494546571980691 := by
  unfold tailWord_6201312
  simp only [CollatzResearch.WordTrace]
  refine ⟨113090215054856599307735095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150786953406475465743646793 113090215054856599307735095)
  ·
    refine ⟨169635322582284898961602643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113090215054856599307735095 169635322582284898961602643)
    ·
      refine ⟨254452983873427348442403965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169635322582284898961602643 254452983873427348442403965)
      ·
        refine ⟨95419868952535255665901487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 254452983873427348442403965 95419868952535255665901487)
        ·
          refine ⟨143129803428802883498852231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95419868952535255665901487 143129803428802883498852231)
          ·
            refine ⟨214694705143204325248278347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143129803428802883498852231 214694705143204325248278347)
            ·
              refine ⟨322042057714806487872417521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214694705143204325248278347 322042057714806487872417521)
              ·
                refine ⟨241531543286104865904313141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 322042057714806487872417521 241531543286104865904313141)
                ·
                  refine ⟨22643582183072331178529357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 241531543286104865904313141 22643582183072331178529357)
                  ·
                    refine ⟨8491343318652124191948509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22643582183072331178529357 8491343318652124191948509)
                    ·
                      refine ⟨3184253744494546571980691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8491343318652124191948509 3184253744494546571980691)
                      ·
                        rfl

theorem cell23_6201312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 5, 3, 3].length) (baseStart_6201312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6201312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6201312 prefixEnd_6201312 := by exact prefixLift 6201312
  have htrace : WordTrace (prefixWord ++ tailWord_6201312) baseStart_6201312 baseEnd_6201312 := by
    simpa [prefixWord, tailWord_6201312, baseEnd_6201312] using wordTrace_append hprefix tailTrace_6201312
  have hstable : (prefixWord ++ tailWord_6201312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6201312).length < 2 ^ (prefixWord ++ tailWord_6201312).sum := by decide
  have hdescent : baseEnd_6201312 < baseStart_6201312 := by decide
  rcases family_descends (prefixWord ++ tailWord_6201312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6201352 : List Nat := [2, 1, 3, 2, 1, 2, 1, 1, 1, 5, 4]
def baseStart_6201352 : Nat := 118140960795 + 6201352 * 2 ^ 59
def prefixEnd_6201352 : Nat := 4983230072969 + 3 ^ 40 * 6201352 * 2
def baseEnd_6201352 : Nat := 3184274283720726415480507

theorem tailTrace_6201352 : CollatzResearch.WordTrace tailWord_6201352 prefixEnd_6201352 3184274283720726415480507 := by
  unfold tailWord_6201352
  simp only [CollatzResearch.WordTrace]
  refine ⟨113090944514784142723463155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150787926019712190297950873 113090944514784142723463155)
  ·
    refine ⟨169636416772176214085194733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113090944514784142723463155 169636416772176214085194733)
    ·
      refine ⟨63613656289566080281948025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169636416772176214085194733 63613656289566080281948025)
      ·
        refine ⟨47710242217174560211461019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63613656289566080281948025 47710242217174560211461019)
        ·
          refine ⟨71565363325761840317191529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47710242217174560211461019 71565363325761840317191529)
          ·
            refine ⟨53674022494321380237893647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71565363325761840317191529 53674022494321380237893647)
            ·
              refine ⟨80511033741482070356840471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53674022494321380237893647 80511033741482070356840471)
              ·
                refine ⟨120766550612223105535260707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80511033741482070356840471 120766550612223105535260707)
                ·
                  refine ⟨181149825918334658302891061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 120766550612223105535260707 181149825918334658302891061)
                  ·
                    refine ⟨16982796179843874215896037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 181149825918334658302891061 16982796179843874215896037)
                    ·
                      refine ⟨3184274283720726415480507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16982796179843874215896037 3184274283720726415480507)
                      ·
                        rfl

theorem cell23_6201352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_6201352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6201352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6201352 prefixEnd_6201352 := by exact prefixLift 6201352
  have htrace : WordTrace (prefixWord ++ tailWord_6201352) baseStart_6201352 baseEnd_6201352 := by
    simpa [prefixWord, tailWord_6201352, baseEnd_6201352] using wordTrace_append hprefix tailTrace_6201352
  have hstable : (prefixWord ++ tailWord_6201352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6201352).length < 2 ^ (prefixWord ++ tailWord_6201352).sum := by decide
  have hdescent : baseEnd_6201352 < baseStart_6201352 := by decide
  rcases family_descends (prefixWord ++ tailWord_6201352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6201390 : List Nat := [4, 1, 3, 1, 1, 2, 4, 1, 1, 3, 2]
def baseStart_6201390 : Nat := 118140960795 + 6201390 * 2 ^ 59
def prefixEnd_6201390 : Nat := 4983230072969 + 3 ^ 40 * 6201390 * 2
def baseEnd_6201390 : Nat := 3184293795985597266805333

theorem tailTrace_6201390 : CollatzResearch.WordTrace tailWord_6201390 prefixEnd_6201390 3184293795985597266805333 := by
  unfold tailWord_6201390
  simp only [CollatzResearch.WordTrace]
  refine ⟨28272909375428827242101203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150788850002287078624539749 28272909375428827242101203)
  ·
    refine ⟨42409364063143240863151805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28272909375428827242101203 42409364063143240863151805)
    ·
      refine ⟨15903511523678715323681927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42409364063143240863151805 15903511523678715323681927)
      ·
        refine ⟨23855267285518072985522891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15903511523678715323681927 23855267285518072985522891)
        ·
          refine ⟨35782900928277109478284337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23855267285518072985522891 35782900928277109478284337)
          ·
            refine ⟨26837175696207832108713253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35782900928277109478284337 26837175696207832108713253)
            ·
              refine ⟨5031970443038968520383735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26837175696207832108713253 5031970443038968520383735)
              ·
                refine ⟨7547955664558452780575603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5031970443038968520383735 7547955664558452780575603)
                ·
                  refine ⟨11321933496837679170863405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7547955664558452780575603 11321933496837679170863405)
                  ·
                    refine ⟨4245725061314129689073777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11321933496837679170863405 4245725061314129689073777)
                    ·
                      refine ⟨3184293795985597266805333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4245725061314129689073777 3184293795985597266805333)
                      ·
                        rfl

theorem cell23_6201390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 4, 1, 1, 3, 2].length) (baseStart_6201390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6201390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6201390 prefixEnd_6201390 := by exact prefixLift 6201390
  have htrace : WordTrace (prefixWord ++ tailWord_6201390) baseStart_6201390 baseEnd_6201390 := by
    simpa [prefixWord, tailWord_6201390, baseEnd_6201390] using wordTrace_append hprefix tailTrace_6201390
  have hstable : (prefixWord ++ tailWord_6201390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6201390).length < 2 ^ (prefixWord ++ tailWord_6201390).sum := by decide
  have hdescent : baseEnd_6201390 < baseStart_6201390 := by decide
  rcases family_descends (prefixWord ++ tailWord_6201390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6201409 : List Nat := [1, 2, 5, 1, 2, 1, 1, 3, 7]
def baseStart_6201409 : Nat := 118140960795 + 6201409 * 2 ^ 59
def prefixEnd_6201409 : Nat := 4983230072969 + 3 ^ 40 * 6201409 * 2
def baseEnd_6201409 : Nat := 353811505790892521385305

theorem tailTrace_6201409 : CollatzResearch.WordTrace tailWord_6201409 prefixEnd_6201409 353811505790892521385305 := by
  unfold tailWord_6201409
  simp only [CollatzResearch.WordTrace]
  refine ⟨226183967990361784181751281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150789311993574522787834187 226183967990361784181751281)
  ·
    refine ⟨169637975992771338136313461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226183967990361784181751281 169637975992771338136313461)
    ·
      refine ⟨15903560249322312950279387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 169637975992771338136313461 15903560249322312950279387)
      ·
        refine ⟨23855340373983469425419081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15903560249322312950279387 23855340373983469425419081)
        ·
          refine ⟨17891505280487602069064311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23855340373983469425419081 17891505280487602069064311)
          ·
            refine ⟨26837257920731403103596467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17891505280487602069064311 26837257920731403103596467)
            ·
              refine ⟨40255886881097104655394701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26837257920731403103596467 40255886881097104655394701)
              ·
                refine ⟨15095957580411414245773013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40255886881097104655394701 15095957580411414245773013)
                ·
                  refine ⟨353811505790892521385305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15095957580411414245773013 353811505790892521385305)
                  ·
                    rfl

theorem cell23_6201409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 3, 7].length) (baseStart_6201409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6201409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6201409 prefixEnd_6201409 := by exact prefixLift 6201409
  have htrace : WordTrace (prefixWord ++ tailWord_6201409) baseStart_6201409 baseEnd_6201409 := by
    simpa [prefixWord, tailWord_6201409, baseEnd_6201409] using wordTrace_append hprefix tailTrace_6201409
  have hstable : (prefixWord ++ tailWord_6201409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6201409).length < 2 ^ (prefixWord ++ tailWord_6201409).sum := by decide
  have hdescent : baseEnd_6201409 < baseStart_6201409 := by decide
  rcases family_descends (prefixWord ++ tailWord_6201409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6201476 : List Nat := [2, 3, 2, 1, 2, 1, 2, 1, 1, 6, 2]
def baseStart_6201476 : Nat := 118140960795 + 6201476 * 2 ^ 59
def prefixEnd_6201476 : Nat := 4983230072969 + 3 ^ 40 * 6201476 * 2
def baseEnd_6201476 : Nat := 3184337955321883930329937

theorem tailTrace_6201476 : CollatzResearch.WordTrace tailWord_6201476 prefixEnd_6201476 3184337955321883930329937 := by
  unfold tailWord_6201476
  simp only [CollatzResearch.WordTrace]
  refine ⟨113093205840559527312220141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150790941120746036416293521 113093205840559527312220141)
  ·
    refine ⟨42409952190209822742082553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113093205840559527312220141 42409952190209822742082553)
    ·
      refine ⟨31807464142657367056561915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42409952190209822742082553 31807464142657367056561915)
      ·
        refine ⟨47711196213986050584842873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31807464142657367056561915 47711196213986050584842873)
        ·
          refine ⟨35783397160489537938632155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47711196213986050584842873 35783397160489537938632155)
          ·
            refine ⟨53675095740734306907948233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35783397160489537938632155 53675095740734306907948233)
            ·
              refine ⟨40256321805550730180961175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53675095740734306907948233 40256321805550730180961175)
              ·
                refine ⟨60384482708326095271441763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40256321805550730180961175 60384482708326095271441763)
                ·
                  refine ⟨90576724062489142907162645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60384482708326095271441763 90576724062489142907162645)
                  ·
                    refine ⟨4245783940429178573773249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 90576724062489142907162645 4245783940429178573773249)
                    ·
                      refine ⟨3184337955321883930329937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4245783940429178573773249 3184337955321883930329937)
                      ·
                        rfl

theorem cell23_6201476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 1, 6, 2].length) (baseStart_6201476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6201476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6201476 prefixEnd_6201476 := by exact prefixLift 6201476
  have htrace : WordTrace (prefixWord ++ tailWord_6201476) baseStart_6201476 baseEnd_6201476 := by
    simpa [prefixWord, tailWord_6201476, baseEnd_6201476] using wordTrace_append hprefix tailTrace_6201476
  have hstable : (prefixWord ++ tailWord_6201476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6201476).length < 2 ^ (prefixWord ++ tailWord_6201476).sum := by decide
  have hdescent : baseEnd_6201476 < baseStart_6201476 := by decide
  rcases family_descends (prefixWord ++ tailWord_6201476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6201479 : List Nat := [1, 1, 4, 2, 1, 1, 2, 1, 3, 4, 3]
def baseStart_6201479 : Nat := 118140960795 + 6201479 * 2 ^ 59
def prefixEnd_6201479 : Nat := 4983230072969 + 3 ^ 40 * 6201479 * 2
def baseEnd_6201479 : Nat := 3184339495763847418592423

theorem tailTrace_6201479 : CollatzResearch.WordTrace tailWord_6201479 prefixEnd_6201479 3184339495763847418592423 := by
  unfold tailWord_6201479
  simp only [CollatzResearch.WordTrace]
  refine ⟨226186521100108186136799491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150791014066738790757866327 226186521100108186136799491)
  ·
    refine ⟨339279781650162279205199237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226186521100108186136799491 339279781650162279205199237)
    ·
      refine ⟨63614959059405427350974857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 339279781650162279205199237 63614959059405427350974857)
      ·
        refine ⟨47711219294554070513231143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63614959059405427350974857 47711219294554070513231143)
        ·
          refine ⟨71566828941831105769846715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47711219294554070513231143 71566828941831105769846715)
          ·
            refine ⟨107350243412746658654770073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71566828941831105769846715 107350243412746658654770073)
            ·
              refine ⟨80512682559559993991077555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107350243412746658654770073 80512682559559993991077555)
              ·
                refine ⟨120769023839339990986616333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80512682559559993991077555 120769023839339990986616333)
                ·
                  refine ⟨45288383939752496619981125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 120769023839339990986616333 45288383939752496619981125)
                  ·
                    refine ⟨8491571988703593116246461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45288383939752496619981125 8491571988703593116246461)
                    ·
                      refine ⟨3184339495763847418592423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8491571988703593116246461 3184339495763847418592423)
                      ·
                        rfl

theorem cell23_6201479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 3, 4, 3].length) (baseStart_6201479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6201479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6201479 prefixEnd_6201479 := by exact prefixLift 6201479
  have htrace : WordTrace (prefixWord ++ tailWord_6201479) baseStart_6201479 baseEnd_6201479 := by
    simpa [prefixWord, tailWord_6201479, baseEnd_6201479] using wordTrace_append hprefix tailTrace_6201479
  have hstable : (prefixWord ++ tailWord_6201479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6201479).length < 2 ^ (prefixWord ++ tailWord_6201479).sum := by decide
  have hdescent : baseEnd_6201479 < baseStart_6201479 := by decide
  rcases family_descends (prefixWord ++ tailWord_6201479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6201529 : List Nat := [1, 2, 1, 4, 1, 2, 1, 1, 5, 5]
def baseStart_6201529 : Nat := 118140960795 + 6201529 * 2 ^ 59
def prefixEnd_6201529 : Nat := 4983230072969 + 3 ^ 40 * 6201529 * 2
def baseEnd_6201529 : Nat := 1061455056598857407655731

theorem tailTrace_6201529 : CollatzResearch.WordTrace tailWord_6201529 prefixEnd_6201529 1061455056598857407655731 := by
  unfold tailWord_6201529
  simp only [CollatzResearch.WordTrace]
  refine ⟨226188344749927044676119641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150792229833284696450746427 226188344749927044676119641)
  ·
    refine ⟨169641258562445283507089731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226188344749927044676119641 169641258562445283507089731)
    ·
      refine ⟨254461887843667925260634597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169641258562445283507089731 254461887843667925260634597)
      ·
        refine ⟨47711603970687735986368987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 254461887843667925260634597 47711603970687735986368987)
        ·
          refine ⟨71567405956031603979553481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47711603970687735986368987 71567405956031603979553481)
          ·
            refine ⟨53675554467023702984665111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71567405956031603979553481 53675554467023702984665111)
            ·
              refine ⟨80513331700535554476997667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53675554467023702984665111 80513331700535554476997667)
              ·
                refine ⟨120769997550803331715496501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80513331700535554476997667 120769997550803331715496501)
                ·
                  refine ⟨11322187270387812348327797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 120769997550803331715496501 11322187270387812348327797)
                  ·
                    refine ⟨1061455056598857407655731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11322187270387812348327797 1061455056598857407655731)
                    ·
                      rfl

theorem cell23_6201529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 5, 5].length) (baseStart_6201529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6201529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6201529 prefixEnd_6201529 := by exact prefixLift 6201529
  have htrace : WordTrace (prefixWord ++ tailWord_6201529) baseStart_6201529 baseEnd_6201529 := by
    simpa [prefixWord, tailWord_6201529, baseEnd_6201529] using wordTrace_append hprefix tailTrace_6201529
  have hstable : (prefixWord ++ tailWord_6201529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6201529).length < 2 ^ (prefixWord ++ tailWord_6201529).sum := by decide
  have hdescent : baseEnd_6201529 < baseStart_6201529 := by decide
  rcases family_descends (prefixWord ++ tailWord_6201529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6201546 : List Nat := [3, 1, 2, 1, 3, 1, 2, 4, 1, 5]
def baseStart_6201546 : Nat := 118140960795 + 6201546 * 2 ^ 59
def prefixEnd_6201546 : Nat := 4983230072969 + 3 ^ 40 * 6201546 * 2
def baseEnd_6201546 : Nat := 1061457966322566218818205

theorem tailTrace_6201546 : CollatzResearch.WordTrace tailWord_6201546 prefixEnd_6201546 1061457966322566218818205 := by
  unfold tailWord_6201546
  simp only [CollatzResearch.WordTrace]
  refine ⟨56547241197716364144872123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150792643193910304386325661 56547241197716364144872123)
  ·
    refine ⟨84820861796574546217308185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56547241197716364144872123 84820861796574546217308185)
    ·
      refine ⟨63615646347430909662981139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84820861796574546217308185 63615646347430909662981139)
      ·
        refine ⟨95423469521146364494471709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63615646347430909662981139 95423469521146364494471709)
        ·
          refine ⟨35783801070429886685426891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95423469521146364494471709 35783801070429886685426891)
          ·
            refine ⟨53675701605644830028140337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35783801070429886685426891 53675701605644830028140337)
            ·
              refine ⟨40256776204233622521105253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53675701605644830028140337 40256776204233622521105253)
              ·
                refine ⟨7548145538293804222707235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40256776204233622521105253 7548145538293804222707235)
                ·
                  refine ⟨11322218307440706334060853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7548145538293804222707235 11322218307440706334060853)
                  ·
                    refine ⟨1061457966322566218818205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11322218307440706334060853 1061457966322566218818205)
                    ·
                      rfl

theorem cell23_6201546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 4, 1, 5].length) (baseStart_6201546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6201546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6201546 prefixEnd_6201546 := by exact prefixLift 6201546
  have htrace : WordTrace (prefixWord ++ tailWord_6201546) baseStart_6201546 baseEnd_6201546 := by
    simpa [prefixWord, tailWord_6201546, baseEnd_6201546] using wordTrace_append hprefix tailTrace_6201546
  have hstable : (prefixWord ++ tailWord_6201546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6201546).length < 2 ^ (prefixWord ++ tailWord_6201546).sum := by decide
  have hdescent : baseEnd_6201546 < baseStart_6201546 := by decide
  rcases family_descends (prefixWord ++ tailWord_6201546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6201553 : List Nat := [1, 2, 2, 1, 2, 2, 5, 1, 2, 3, 2]
def baseStart_6201553 : Nat := 118140960795 + 6201553 * 2 ^ 59
def prefixEnd_6201553 : Nat := 4983230072969 + 3 ^ 40 * 6201553 * 2
def baseEnd_6201553 : Nat := 3184377493332280129067083

theorem tailTrace_6201553 : CollatzResearch.WordTrace tailWord_6201553 prefixEnd_6201553 3184377493332280129067083 := by
  unfold tailWord_6201553
  simp only [CollatzResearch.WordTrace]
  refine ⟨226189220101840096774993313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150792813401226731183328875 226189220101840096774993313)
  ·
    refine ⟨169641915076380072581244985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226189220101840096774993313 169641915076380072581244985)
    ·
      refine ⟨127231436307285054435933739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169641915076380072581244985 127231436307285054435933739)
      ·
        refine ⟨190847154460927581653900609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127231436307285054435933739 190847154460927581653900609)
        ·
          refine ⟨143135365845695686240425457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190847154460927581653900609 143135365845695686240425457)
          ·
            refine ⟨107351524384271764680319093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143135365845695686240425457 107351524384271764680319093)
            ·
              refine ⟨10064205411025477938779915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 107351524384271764680319093 10064205411025477938779915)
              ·
                refine ⟨15096308116538216908169873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10064205411025477938779915 15096308116538216908169873)
                ·
                  refine ⟨11322231087403662681127405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15096308116538216908169873 11322231087403662681127405)
                  ·
                    refine ⟨4245836657776373505422777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11322231087403662681127405 4245836657776373505422777)
                    ·
                      refine ⟨3184377493332280129067083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4245836657776373505422777 3184377493332280129067083)
                      ·
                        rfl

theorem cell23_6201553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 1, 2, 3, 2].length) (baseStart_6201553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6201553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6201553 prefixEnd_6201553 := by exact prefixLift 6201553
  have htrace : WordTrace (prefixWord ++ tailWord_6201553) baseStart_6201553 baseEnd_6201553 := by
    simpa [prefixWord, tailWord_6201553, baseEnd_6201553] using wordTrace_append hprefix tailTrace_6201553
  have hstable : (prefixWord ++ tailWord_6201553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6201553).length < 2 ^ (prefixWord ++ tailWord_6201553).sum := by decide
  have hdescent : baseEnd_6201553 < baseStart_6201553 := by decide
  rcases family_descends (prefixWord ++ tailWord_6201553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6201560 : List Nat := [2, 1, 2, 2, 4, 1, 1, 5, 1, 1, 3]
def baseStart_6201560 : Nat := 118140960795 + 6201560 * 2 ^ 59
def prefixEnd_6201560 : Nat := 4983230072969 + 3 ^ 40 * 6201560 * 2
def baseEnd_6201560 : Nat := 3184381087696861601679551

theorem tailTrace_6201560 : CollatzResearch.WordTrace tailWord_6201560 prefixEnd_6201560 3184381087696861601679551 := by
  unfold tailWord_6201560
  simp only [CollatzResearch.WordTrace]
  refine ⟨113094737706407368485249067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150792983608543157980332089 113094737706407368485249067)
  ·
    refine ⟨169642106559611052727873601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113094737706407368485249067 169642106559611052727873601)
    ·
      refine ⟨127231579919708289545905201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169642106559611052727873601 127231579919708289545905201)
      ·
        refine ⟨95423684939781217159428901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127231579919708289545905201 95423684939781217159428901)
        ·
          refine ⟨17891940926208978217392919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95423684939781217159428901 17891940926208978217392919)
          ·
            refine ⟨26837911389313467326089379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17891940926208978217392919 26837911389313467326089379)
            ·
              refine ⟨40256867083970200989134069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26837911389313467326089379 40256867083970200989134069)
              ·
                refine ⟨3774081289122206342731319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40256867083970200989134069 3774081289122206342731319)
                ·
                  refine ⟨5661121933683309514096979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3774081289122206342731319 5661121933683309514096979)
                  ·
                    refine ⟨8491682900524964271145469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5661121933683309514096979 8491682900524964271145469)
                    ·
                      refine ⟨3184381087696861601679551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8491682900524964271145469 3184381087696861601679551)
                      ·
                        rfl

theorem cell23_6201560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 5, 1, 1, 3].length) (baseStart_6201560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6201560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6201560 prefixEnd_6201560 := by exact prefixLift 6201560
  have htrace : WordTrace (prefixWord ++ tailWord_6201560) baseStart_6201560 baseEnd_6201560 := by
    simpa [prefixWord, tailWord_6201560, baseEnd_6201560] using wordTrace_append hprefix tailTrace_6201560
  have hstable : (prefixWord ++ tailWord_6201560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6201560).length < 2 ^ (prefixWord ++ tailWord_6201560).sum := by decide
  have hdescent : baseEnd_6201560 < baseStart_6201560 := by decide
  rcases family_descends (prefixWord ++ tailWord_6201560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6201579 : List Nat := [1, 1, 1, 1, 2, 5, 2, 2, 1, 1, 6]
def baseStart_6201579 : Nat := 118140960795 + 6201579 * 2 ^ 59
def prefixEnd_6201579 : Nat := 4983230072969 + 3 ^ 40 * 6201579 * 2
def baseEnd_6201579 : Nat := 3184390843829297027341963

theorem tailTrace_6201579 : CollatzResearch.WordTrace tailWord_6201579 prefixEnd_6201579 3184390843829297027341963 := by
  unfold tailWord_6201579
  simp only [CollatzResearch.WordTrace]
  refine ⟨226190168399745903215439791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150793445599830602143626527 226190168399745903215439791)
  ·
    refine ⟨339285252599618854823159687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226190168399745903215439791 339285252599618854823159687)
    ·
      refine ⟨508927878899428282234739531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339285252599618854823159687 508927878899428282234739531)
      ·
        refine ⟨763391818349142423352109297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 508927878899428282234739531 763391818349142423352109297)
        ·
          refine ⟨572543863761856817514081973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 763391818349142423352109297 572543863761856817514081973)
          ·
            refine ⟨53675987227674076641945185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 572543863761856817514081973 53675987227674076641945185)
            ·
              refine ⟨40256990420755557481458889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53675987227674076641945185 40256990420755557481458889)
              ·
                refine ⟨30192742815566668111094167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40256990420755557481458889 30192742815566668111094167)
                ·
                  refine ⟨45289114223350002166641251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30192742815566668111094167 45289114223350002166641251)
                  ·
                    refine ⟨67933671335025003249961877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45289114223350002166641251 67933671335025003249961877)
                    ·
                      refine ⟨3184390843829297027341963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67933671335025003249961877 3184390843829297027341963)
                      ·
                        rfl

theorem cell23_6201579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 2, 1, 1, 6].length) (baseStart_6201579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6201579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6201579 prefixEnd_6201579 := by exact prefixLift 6201579
  have htrace : WordTrace (prefixWord ++ tailWord_6201579) baseStart_6201579 baseEnd_6201579 := by
    simpa [prefixWord, tailWord_6201579, baseEnd_6201579] using wordTrace_append hprefix tailTrace_6201579
  have hstable : (prefixWord ++ tailWord_6201579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6201579).length < 2 ^ (prefixWord ++ tailWord_6201579).sum := by decide
  have hdescent : baseEnd_6201579 < baseStart_6201579 := by decide
  rcases family_descends (prefixWord ++ tailWord_6201579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6201586 : List Nat := [3, 2, 1, 3, 2, 1, 1, 1, 3, 1, 5]
def baseStart_6201586 : Nat := 118140960795 + 6201586 * 2 ^ 59
def prefixEnd_6201586 : Nat := 4983230072969 + 3 ^ 40 * 6201586 * 2
def baseEnd_6201586 : Nat := 3184394438193878499954431

theorem tailTrace_6201586 : CollatzResearch.WordTrace tailWord_6201586 prefixEnd_6201586 3184394438193878499954431 := by
  unfold tailWord_6201586
  simp only [CollatzResearch.WordTrace]
  refine ⟨56547605927680135852736153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150793615807147028940629741 56547605927680135852736153)
  ·
    refine ⟨42410704445760101889552115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56547605927680135852736153 42410704445760101889552115)
    ·
      refine ⟨63616056668640152834328173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42410704445760101889552115 63616056668640152834328173)
      ·
        refine ⟨23856021250740057312873065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63616056668640152834328173 23856021250740057312873065)
        ·
          refine ⟨17892015938055042984654799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23856021250740057312873065 17892015938055042984654799)
          ·
            refine ⟨26838023907082564476982199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17892015938055042984654799 26838023907082564476982199)
            ·
              refine ⟨40257035860623846715473299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26838023907082564476982199 40257035860623846715473299)
              ·
                refine ⟨60385553790935770073209949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40257035860623846715473299 60385553790935770073209949)
                ·
                  refine ⟨22644582671600913777453731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60385553790935770073209949 22644582671600913777453731)
                  ·
                    refine ⟨33966874007401370666180597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22644582671600913777453731 33966874007401370666180597)
                    ·
                      refine ⟨3184394438193878499954431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33966874007401370666180597 3184394438193878499954431)
                      ·
                        rfl

theorem cell23_6201586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_6201586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6201586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6201586 prefixEnd_6201586 := by exact prefixLift 6201586
  have htrace : WordTrace (prefixWord ++ tailWord_6201586) baseStart_6201586 baseEnd_6201586 := by
    simpa [prefixWord, tailWord_6201586, baseEnd_6201586] using wordTrace_append hprefix tailTrace_6201586
  have hstable : (prefixWord ++ tailWord_6201586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6201586).length < 2 ^ (prefixWord ++ tailWord_6201586).sum := by decide
  have hdescent : baseEnd_6201586 < baseStart_6201586 := by decide
  rcases family_descends (prefixWord ++ tailWord_6201586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6201596 : List Nat := [2, 2, 2, 1, 4, 2, 1, 1, 1, 1, 6]
def baseStart_6201596 : Nat := 118140960795 + 6201596 * 2 ^ 59
def prefixEnd_6201596 : Nat := 4983230072969 + 3 ^ 40 * 6201596 * 2
def baseEnd_6201596 : Nat := 3184399573000423460829385

theorem tailTrace_6201596 : CollatzResearch.WordTrace tailWord_6201596 prefixEnd_6201596 3184399573000423460829385 := by
  unfold tailWord_6201596
  simp only [CollatzResearch.WordTrace]
  refine ⟨113095394220342157559404321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150793858960456210079205761 113095394220342157559404321)
  ·
    refine ⟨84821545665256618169553241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113095394220342157559404321 84821545665256618169553241)
    ·
      refine ⟨63616159248942463627164931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84821545665256618169553241 63616159248942463627164931)
      ·
        refine ⟨95424238873413695440747397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63616159248942463627164931 95424238873413695440747397)
        ·
          refine ⟨17892044788765067895140137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95424238873413695440747397 17892044788765067895140137)
          ·
            refine ⟨13419033591573800921355103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17892044788765067895140137 13419033591573800921355103)
            ·
              refine ⟨20128550387360701382032655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13419033591573800921355103 20128550387360701382032655)
              ·
                refine ⟨30192825581041052073048983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20128550387360701382032655 30192825581041052073048983)
                ·
                  refine ⟨45289238371561578109573475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30192825581041052073048983 45289238371561578109573475)
                  ·
                    refine ⟨67933857557342367164360213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45289238371561578109573475 67933857557342367164360213)
                    ·
                      refine ⟨3184399573000423460829385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67933857557342367164360213 3184399573000423460829385)
                      ·
                        rfl

theorem cell23_6201596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 1, 1, 1, 6].length) (baseStart_6201596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6201596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6201596 prefixEnd_6201596 := by exact prefixLift 6201596
  have htrace : WordTrace (prefixWord ++ tailWord_6201596) baseStart_6201596 baseEnd_6201596 := by
    simpa [prefixWord, tailWord_6201596, baseEnd_6201596] using wordTrace_append hprefix tailTrace_6201596
  have hstable : (prefixWord ++ tailWord_6201596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6201596).length < 2 ^ (prefixWord ++ tailWord_6201596).sum := by decide
  have hdescent : baseEnd_6201596 < baseStart_6201596 := by decide
  rcases family_descends (prefixWord ++ tailWord_6201596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6201603 : List Nat := [1, 1, 1, 3, 2, 3, 4, 2, 1, 2, 3]
def baseStart_6201603 : Nat := 118140960795 + 6201603 * 2 ^ 59
def prefixEnd_6201603 : Nat := 4983230072969 + 3 ^ 40 * 6201603 * 2
def baseEnd_6201603 : Nat := 3184403167365004933441853

theorem tailTrace_6201603 : CollatzResearch.WordTrace tailWord_6201603 prefixEnd_6201603 3184403167365004933441853 := by
  unfold tailWord_6201603
  simp only [CollatzResearch.WordTrace]
  refine ⟨226191043751658955314313463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150794029167772636876208975 226191043751658955314313463)
  ·
    refine ⟨339286565627488432971470195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226191043751658955314313463 339286565627488432971470195)
    ·
      refine ⟨508929848441232649457205293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339286565627488432971470195 508929848441232649457205293)
      ·
        refine ⟨190848693165462243546451985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 508929848441232649457205293 190848693165462243546451985)
        ·
          refine ⟨143136519874096682659838989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190848693165462243546451985 143136519874096682659838989)
          ·
            refine ⟨53676194952786255997439621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143136519874096682659838989 53676194952786255997439621)
            ·
              refine ⟨10064286553647422999519929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53676194952786255997439621 10064286553647422999519929)
              ·
                refine ⟨7548214915235567249639947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10064286553647422999519929 7548214915235567249639947)
                ·
                  refine ⟨11322322372853350874459921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7548214915235567249639947 11322322372853350874459921)
                  ·
                    refine ⟨8491741779640013155844941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11322322372853350874459921 8491741779640013155844941)
                    ·
                      refine ⟨3184403167365004933441853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8491741779640013155844941 3184403167365004933441853)
                      ·
                        rfl

theorem cell23_6201603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 2, 1, 2, 3].length) (baseStart_6201603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6201603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6201603 prefixEnd_6201603 := by exact prefixLift 6201603
  have htrace : WordTrace (prefixWord ++ tailWord_6201603) baseStart_6201603 baseEnd_6201603 := by
    simpa [prefixWord, tailWord_6201603, baseEnd_6201603] using wordTrace_append hprefix tailTrace_6201603
  have hstable : (prefixWord ++ tailWord_6201603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6201603).length < 2 ^ (prefixWord ++ tailWord_6201603).sum := by decide
  have hdescent : baseEnd_6201603 < baseStart_6201603 := by decide
  rcases family_descends (prefixWord ++ tailWord_6201603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6201617 : List Nat := [1, 2, 2, 1, 1, 5, 3, 3, 1, 2, 2]
def baseStart_6201617 : Nat := 118140960795 + 6201617 * 2 ^ 59
def prefixEnd_6201617 : Nat := 4983230072969 + 3 ^ 40 * 6201617 * 2
def baseEnd_6201617 : Nat := 3184410356094167878666789

theorem tailTrace_6201617 : CollatzResearch.WordTrace tailWord_6201617 prefixEnd_6201617 3184410356094167878666789 := by
  unfold tailWord_6201617
  simp only [CollatzResearch.WordTrace]
  refine ⟨226191554373608235705323105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150794369582405490470215403 226191554373608235705323105)
  ·
    refine ⟨169643665780206176778992329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226191554373608235705323105 169643665780206176778992329)
    ·
      refine ⟨127232749335154632584244247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169643665780206176778992329 127232749335154632584244247)
      ·
        refine ⟨190849124002731948876366371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127232749335154632584244247 190849124002731948876366371)
        ·
          refine ⟨286273686004097923314549557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190849124002731948876366371 286273686004097923314549557)
          ·
            refine ⟨26838158062884180310739021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 286273686004097923314549557 26838158062884180310739021)
            ·
              refine ⟨10064309273581567616527133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26838158062884180310739021 10064309273581567616527133)
              ·
                refine ⟨3774115977593087856197675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10064309273581567616527133 3774115977593087856197675)
                ·
                  refine ⟨5661173966389631784296513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3774115977593087856197675 5661173966389631784296513)
                  ·
                    refine ⟨4245880474792223838222385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5661173966389631784296513 4245880474792223838222385)
                    ·
                      refine ⟨3184410356094167878666789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4245880474792223838222385 3184410356094167878666789)
                      ·
                        rfl

theorem cell23_6201617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 3, 1, 2, 2].length) (baseStart_6201617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6201617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6201617 prefixEnd_6201617 := by exact prefixLift 6201617
  have htrace : WordTrace (prefixWord ++ tailWord_6201617) baseStart_6201617 baseEnd_6201617 := by
    simpa [prefixWord, tailWord_6201617, baseEnd_6201617] using wordTrace_append hprefix tailTrace_6201617
  have hstable : (prefixWord ++ tailWord_6201617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6201617).length < 2 ^ (prefixWord ++ tailWord_6201617).sum := by decide
  have hdescent : baseEnd_6201617 < baseStart_6201617 := by decide
  rcases family_descends (prefixWord ++ tailWord_6201617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6201633 : List Nat := [1, 2, 3, 2, 1, 1, 4, 1, 4, 1, 3]
def baseStart_6201633 : Nat := 118140960795 + 6201633 * 2 ^ 59
def prefixEnd_6201633 : Nat := 4983230072969 + 3 ^ 40 * 6201633 * 2
def baseEnd_6201633 : Nat := 3184418571784639816066715

theorem tailTrace_6201633 : CollatzResearch.WordTrace tailWord_6201633 prefixEnd_6201633 3184418571784639816066715 := by
  unfold tailWord_6201633
  simp only [CollatzResearch.WordTrace]
  refine ⟨226192137941550270437905553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150794758627700180291937035 226192137941550270437905553)
  ·
    refine ⟨169644103456162702828429165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226192137941550270437905553 169644103456162702828429165)
    ·
      refine ⟨63616538796061013560660937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169644103456162702828429165 63616538796061013560660937)
      ·
        refine ⟨47712404097045760170495703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63616538796061013560660937 47712404097045760170495703)
        ·
          refine ⟨71568606145568640255743555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47712404097045760170495703 71568606145568640255743555)
          ·
            refine ⟨107352909218352960383615333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71568606145568640255743555 107352909218352960383615333)
            ·
              refine ⟨20128670478441180071927875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 107352909218352960383615333 20128670478441180071927875)
              ·
                refine ⟨30193005717661770107891813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20128670478441180071927875 30193005717661770107891813)
                ·
                  refine ⟨5661188572061581895229715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30193005717661770107891813 5661188572061581895229715)
                  ·
                    refine ⟨8491782858092372842844573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5661188572061581895229715 8491782858092372842844573)
                    ·
                      refine ⟨3184418571784639816066715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8491782858092372842844573 3184418571784639816066715)
                      ·
                        rfl

theorem cell23_6201633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 1, 4, 1, 3].length) (baseStart_6201633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6201633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6201633 prefixEnd_6201633 := by exact prefixLift 6201633
  have htrace : WordTrace (prefixWord ++ tailWord_6201633) baseStart_6201633 baseEnd_6201633 := by
    simpa [prefixWord, tailWord_6201633, baseEnd_6201633] using wordTrace_append hprefix tailTrace_6201633
  have hstable : (prefixWord ++ tailWord_6201633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6201633).length < 2 ^ (prefixWord ++ tailWord_6201633).sum := by decide
  have hdescent : baseEnd_6201633 < baseStart_6201633 := by decide
  rcases family_descends (prefixWord ++ tailWord_6201633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6201659 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 2, 7, 5]
def baseStart_6201659 : Nat := 118140960795 + 6201659 * 2 ^ 59
def prefixEnd_6201659 : Nat := 4983230072969 + 3 ^ 40 * 6201659 * 2
def baseEnd_6201659 : Nat := 3184431922281656714341595

theorem tailTrace_6201659 : CollatzResearch.WordTrace tailWord_6201659 prefixEnd_6201659 3184431922281656714341595 := by
  unfold tailWord_6201659
  simp only [CollatzResearch.WordTrace]
  refine ⟨226193086239456076878352031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150795390826304051252234687 226193086239456076878352031)
  ·
    refine ⟨339289629359184115317528047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226193086239456076878352031 339289629359184115317528047)
    ·
      refine ⟨508934444038776172976292071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339289629359184115317528047 508934444038776172976292071)
      ·
        refine ⟨763401666058164259464438107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 508934444038776172976292071 763401666058164259464438107)
        ·
          refine ⟨1145102499087246389196657161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 763401666058164259464438107 1145102499087246389196657161)
          ·
            refine ⟨858826874315434791897492871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1145102499087246389196657161 858826874315434791897492871)
            ·
              refine ⟨1288240311473152187846239307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 858826874315434791897492871 1288240311473152187846239307)
              ·
                refine ⟨1932360467209728281769358961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1288240311473152187846239307 1932360467209728281769358961)
                ·
                  refine ⟨1449270350407296211327019221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1932360467209728281769358961 1449270350407296211327019221)
                  ·
                    refine ⟨33967273837671004952977013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1449270350407296211327019221 33967273837671004952977013)
                    ·
                      refine ⟨3184431922281656714341595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33967273837671004952977013 3184431922281656714341595)
                      ·
                        rfl

theorem cell23_6201659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 7, 5].length) (baseStart_6201659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6201659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6201659 prefixEnd_6201659 := by exact prefixLift 6201659
  have htrace : WordTrace (prefixWord ++ tailWord_6201659) baseStart_6201659 baseEnd_6201659 := by
    simpa [prefixWord, tailWord_6201659, baseEnd_6201659] using wordTrace_append hprefix tailTrace_6201659
  have hstable : (prefixWord ++ tailWord_6201659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6201659).length < 2 ^ (prefixWord ++ tailWord_6201659).sum := by decide
  have hdescent : baseEnd_6201659 < baseStart_6201659 := by decide
  rcases family_descends (prefixWord ++ tailWord_6201659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6201676 : List Nat := [2, 2, 1, 3, 2, 1, 1, 3, 2, 1, 5]
def baseStart_6201676 : Nat := 118140960795 + 6201676 * 2 ^ 59
def prefixEnd_6201676 : Nat := 4983230072969 + 3 ^ 40 * 6201676 * 2
def baseEnd_6201676 : Nat := 3184440651452783147829017

theorem tailTrace_6201676 : CollatzResearch.WordTrace tailWord_6201676 prefixEnd_6201676 3184440651452783147829017 := by
  unfold tailWord_6201676
  simp only [CollatzResearch.WordTrace]
  refine ⟨113096853140197244390860441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150795804186929659187813921 113096853140197244390860441)
  ·
    refine ⟨84822639855147933293145331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113096853140197244390860441 84822639855147933293145331)
    ·
      refine ⟨127233959782721899939717997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84822639855147933293145331 127233959782721899939717997)
      ·
        refine ⟨47712734918520712477394249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127233959782721899939717997 47712734918520712477394249)
        ·
          refine ⟨35784551188890534358045687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47712734918520712477394249 35784551188890534358045687)
          ·
            refine ⟨53676826783335801537068531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35784551188890534358045687 53676826783335801537068531)
            ·
              refine ⟨80515240175003702305602797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53676826783335801537068531 80515240175003702305602797)
              ·
                refine ⟨30193215065626388364601049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80515240175003702305602797 30193215065626388364601049)
                ·
                  refine ⟨22644911299219791273450787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30193215065626388364601049 22644911299219791273450787)
                  ·
                    refine ⟨33967366948829686910176181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22644911299219791273450787 33967366948829686910176181)
                    ·
                      refine ⟨3184440651452783147829017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33967366948829686910176181 3184440651452783147829017)
                      ·
                        rfl

theorem cell23_6201676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_6201676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6201676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6201676 prefixEnd_6201676 := by exact prefixLift 6201676
  have htrace : WordTrace (prefixWord ++ tailWord_6201676) baseStart_6201676 baseEnd_6201676 := by
    simpa [prefixWord, tailWord_6201676, baseEnd_6201676] using wordTrace_append hprefix tailTrace_6201676
  have hstable : (prefixWord ++ tailWord_6201676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6201676).length < 2 ^ (prefixWord ++ tailWord_6201676).sum := by decide
  have hdescent : baseEnd_6201676 < baseStart_6201676 := by decide
  rcases family_descends (prefixWord ++ tailWord_6201676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6201679 : List Nat := [1, 1, 2, 1, 1, 2, 1, 3, 11]
def baseStart_6201679 : Nat := 118140960795 + 6201679 * 2 ^ 59
def prefixEnd_6201679 : Nat := 4983230072969 + 3 ^ 40 * 6201679 * 2
def baseEnd_6201679 : Nat := 353826910210527404010167

theorem tailTrace_6201679 : CollatzResearch.WordTrace tailWord_6201679 prefixEnd_6201679 353826910210527404010167 := by
  unfold tailWord_6201679
  simp only [CollatzResearch.WordTrace]
  refine ⟨226193815699383620294080091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150795877132922413529386727 226193815699383620294080091)
  ·
    refine ⟨339290723549075430441120137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226193815699383620294080091 339290723549075430441120137)
    ·
      refine ⟨254468042661806572830840103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 339290723549075430441120137 254468042661806572830840103)
      ·
        refine ⟨381702063992709859246260155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254468042661806572830840103 381702063992709859246260155)
        ·
          refine ⟨572553095989064788869390233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 381702063992709859246260155 572553095989064788869390233)
          ·
            refine ⟨429414821991798591652042675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 572553095989064788869390233 429414821991798591652042675)
            ·
              refine ⟨644122232987697887478064013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 429414821991798591652042675 644122232987697887478064013)
              ·
                refine ⟨241545837370386707804274005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 644122232987697887478064013 241545837370386707804274005)
                ·
                  refine ⟨353826910210527404010167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 241545837370386707804274005 353826910210527404010167)
                  ·
                    rfl

theorem cell23_6201679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 11].length) (baseStart_6201679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6201679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6201679 prefixEnd_6201679 := by exact prefixLift 6201679
  have htrace : WordTrace (prefixWord ++ tailWord_6201679) baseStart_6201679 baseEnd_6201679 := by
    simpa [prefixWord, tailWord_6201679, baseEnd_6201679] using wordTrace_append hprefix tailTrace_6201679
  have hstable : (prefixWord ++ tailWord_6201679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6201679).length < 2 ^ (prefixWord ++ tailWord_6201679).sum := by decide
  have hdescent : baseEnd_6201679 < baseStart_6201679 := by decide
  rcases family_descends (prefixWord ++ tailWord_6201679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6201703 : List Nat := [1, 1, 5, 1, 3, 2, 1, 1, 2, 2, 4]
def baseStart_6201703 : Nat := 118140960795 + 6201703 * 2 ^ 59
def prefixEnd_6201703 : Nat := 4983230072969 + 3 ^ 40 * 6201703 * 2
def baseEnd_6201703 : Nat := 3184454515430454542191393

theorem tailTrace_6201703 : CollatzResearch.WordTrace tailWord_6201703 prefixEnd_6201703 3184454515430454542191393 := by
  unfold tailWord_6201703
  simp only [CollatzResearch.WordTrace]
  refine ⟨226194691051296672392953763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150796460700864448261969175 226194691051296672392953763)
  ·
    refine ⟨339292036576945008589430645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226194691051296672392953763 339292036576945008589430645)
    ·
      refine ⟨31808628429088594555259123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 339292036576945008589430645 31808628429088594555259123)
      ·
        refine ⟨47712942643632891832888685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31808628429088594555259123 47712942643632891832888685)
        ·
          refine ⟨17892353491362334437333257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47712942643632891832888685 17892353491362334437333257)
          ·
            refine ⟨13419265118521750827999943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17892353491362334437333257 13419265118521750827999943)
            ·
              refine ⟨20128897677782626241999915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13419265118521750827999943 20128897677782626241999915)
              ·
                refine ⟨30193346516673939362999873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20128897677782626241999915 30193346516673939362999873)
                ·
                  refine ⟨22645009887505454522249905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30193346516673939362999873 22645009887505454522249905)
                  ·
                    refine ⟨16983757415629090891687429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22645009887505454522249905 16983757415629090891687429)
                    ·
                      refine ⟨3184454515430454542191393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16983757415629090891687429 3184454515430454542191393)
                      ·
                        rfl

theorem cell23_6201703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_6201703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6201703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6201703 prefixEnd_6201703 := by exact prefixLift 6201703
  have htrace : WordTrace (prefixWord ++ tailWord_6201703) baseStart_6201703 baseEnd_6201703 := by
    simpa [prefixWord, tailWord_6201703, baseEnd_6201703] using wordTrace_append hprefix tailTrace_6201703
  have hstable : (prefixWord ++ tailWord_6201703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6201703).length < 2 ^ (prefixWord ++ tailWord_6201703).sum := by decide
  have hdescent : baseEnd_6201703 < baseStart_6201703 := by decide
  rcases family_descends (prefixWord ++ tailWord_6201703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6201783 : List Nat := [1, 1, 3, 1, 3, 3, 2, 1, 1, 4, 3]
def baseStart_6201783 : Nat := 118140960795 + 6201783 * 2 ^ 59
def prefixEnd_6201783 : Nat := 4983230072969 + 3 ^ 40 * 6201783 * 2
def baseEnd_6201783 : Nat := 3184495593882814229191025

theorem tailTrace_6201783 : CollatzResearch.WordTrace tailWord_6201783 prefixEnd_6201783 3184495593882814229191025 := by
  unfold tailWord_6201783
  simp only [CollatzResearch.WordTrace]
  refine ⟨226197608891006846055866003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150798405927337897370577335 226197608891006846055866003)
  ·
    refine ⟨339296413336510269083799005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226197608891006846055866003 339296413336510269083799005)
    ·
      refine ⟨127236155001191350906424627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 339296413336510269083799005 127236155001191350906424627)
      ·
        refine ⟨190854232501787026359636941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127236155001191350906424627 190854232501787026359636941)
        ·
          refine ⟨71570337188170134884863853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 190854232501787026359636941 71570337188170134884863853)
          ·
            refine ⟨26838876445563800581823945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71570337188170134884863853 26838876445563800581823945)
            ·
              refine ⟨20129157334172850436367959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26838876445563800581823945 20129157334172850436367959)
              ·
                refine ⟨30193736001259275654551939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20129157334172850436367959 30193736001259275654551939)
                ·
                  refine ⟨45290604001888913481827909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30193736001259275654551939 45290604001888913481827909)
                  ·
                    refine ⟨8491988250354171277842733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45290604001888913481827909 8491988250354171277842733)
                    ·
                      refine ⟨3184495593882814229191025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8491988250354171277842733 3184495593882814229191025)
                      ·
                        rfl

theorem cell23_6201783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 1, 1, 4, 3].length) (baseStart_6201783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6201783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6201783 prefixEnd_6201783 := by exact prefixLift 6201783
  have htrace : WordTrace (prefixWord ++ tailWord_6201783) baseStart_6201783 baseEnd_6201783 := by
    simpa [prefixWord, tailWord_6201783, baseEnd_6201783] using wordTrace_append hprefix tailTrace_6201783
  have hstable : (prefixWord ++ tailWord_6201783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6201783).length < 2 ^ (prefixWord ++ tailWord_6201783).sum := by decide
  have hdescent : baseEnd_6201783 < baseStart_6201783 := by decide
  rcases family_descends (prefixWord ++ tailWord_6201783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6201800 : List Nat := [2, 1, 3, 1, 3, 3, 1, 2, 2, 2, 3]
def baseStart_6201800 : Nat := 118140960795 + 6201800 * 2 ^ 59
def prefixEnd_6201800 : Nat := 4983230072969 + 3 ^ 40 * 6201800 * 2
def baseEnd_6201800 : Nat := 3184504323053940662678447

theorem tailTrace_6201800 : CollatzResearch.WordTrace tailWord_6201800 prefixEnd_6201800 3184504323053940662678447 := by
  unfold tailWord_6201800
  simp only [CollatzResearch.WordTrace]
  refine ⟨113099114465972628979617427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150798819287963505306156569 113099114465972628979617427)
  ·
    refine ⟨169648671698958943469426141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113099114465972628979617427 169648671698958943469426141)
    ·
      refine ⟨63618251887109603801034803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169648671698958943469426141 63618251887109603801034803)
      ·
        refine ⟨95427377830664405701552205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63618251887109603801034803 95427377830664405701552205)
        ·
          refine ⟨35785266686499152138082077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95427377830664405701552205 35785266686499152138082077)
          ·
            refine ⟨13419475007437182051780779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35785266686499152138082077 13419475007437182051780779)
            ·
              refine ⟨20129212511155773077671169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13419475007437182051780779 20129212511155773077671169)
              ·
                refine ⟨15096909383366829808253377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20129212511155773077671169 15096909383366829808253377)
                ·
                  refine ⟨11322682037525122356190033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15096909383366829808253377 11322682037525122356190033)
                  ·
                    refine ⟨8492011528143841767142525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11322682037525122356190033 8492011528143841767142525)
                    ·
                      refine ⟨3184504323053940662678447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8492011528143841767142525 3184504323053940662678447)
                      ·
                        rfl

theorem cell23_6201800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 2, 2, 2, 3].length) (baseStart_6201800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6201800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6201800 prefixEnd_6201800 := by exact prefixLift 6201800
  have htrace : WordTrace (prefixWord ++ tailWord_6201800) baseStart_6201800 baseEnd_6201800 := by
    simpa [prefixWord, tailWord_6201800, baseEnd_6201800] using wordTrace_append hprefix tailTrace_6201800
  have hstable : (prefixWord ++ tailWord_6201800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6201800).length < 2 ^ (prefixWord ++ tailWord_6201800).sum := by decide
  have hdescent : baseEnd_6201800 < baseStart_6201800 := by decide
  rcases family_descends (prefixWord ++ tailWord_6201800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6201816 : List Nat := [2, 1, 2, 2, 2, 1, 1, 1, 2, 9]
def baseStart_6201816 : Nat := 118140960795 + 6201816 * 2 ^ 59
def prefixEnd_6201816 : Nat := 4983230072969 + 3 ^ 40 * 6201816 * 2
def baseEnd_6201816 : Nat := 1061504179581470866692791

theorem tailTrace_6201816 : CollatzResearch.WordTrace tailWord_6201816 prefixEnd_6201816 1061504179581470866692791 := by
  unfold tailWord_6201816
  simp only [CollatzResearch.WordTrace]
  refine ⟨113099406249943646345908651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150799208333258195127878201 113099406249943646345908651)
  ·
    refine ⟨169649109374915469518862977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113099406249943646345908651 169649109374915469518862977)
    ·
      refine ⟨127236832031186602139147233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169649109374915469518862977 127236832031186602139147233)
      ·
        refine ⟨95427624023389951604360425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127236832031186602139147233 95427624023389951604360425)
        ·
          refine ⟨71570718017542463703270319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95427624023389951604360425 71570718017542463703270319)
          ·
            refine ⟨107356077026313695554905479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71570718017542463703270319 107356077026313695554905479)
            ·
              refine ⟨161034115539470543332358219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107356077026313695554905479 161034115539470543332358219)
              ·
                refine ⟨241551173309205814998537329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 161034115539470543332358219 241551173309205814998537329)
                ·
                  refine ⟨181163379981904361248902997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 241551173309205814998537329 181163379981904361248902997)
                  ·
                    refine ⟨1061504179581470866692791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 181163379981904361248902997 1061504179581470866692791)
                    ·
                      rfl

theorem cell23_6201816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 2, 9].length) (baseStart_6201816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6201816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6201816 prefixEnd_6201816 := by exact prefixLift 6201816
  have htrace : WordTrace (prefixWord ++ tailWord_6201816) baseStart_6201816 baseEnd_6201816 := by
    simpa [prefixWord, tailWord_6201816, baseEnd_6201816] using wordTrace_append hprefix tailTrace_6201816
  have hstable : (prefixWord ++ tailWord_6201816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6201816).length < 2 ^ (prefixWord ++ tailWord_6201816).sum := by decide
  have hdescent : baseEnd_6201816 < baseStart_6201816 := by decide
  rcases family_descends (prefixWord ++ tailWord_6201816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6201833 : List Nat := [1, 2, 1, 1, 1, 2, 1, 8, 1, 5]
def baseStart_6201833 : Nat := 118140960795 + 6201833 * 2 ^ 59
def prefixEnd_6201833 : Nat := 4983230072969 + 3 ^ 40 * 6201833 * 2
def baseEnd_6201833 : Nat := 1061507089305179677855265

theorem tailTrace_6201833 : CollatzResearch.WordTrace tailWord_6201833 prefixEnd_6201833 1061507089305179677855265 := by
  unfold tailWord_6201833
  simp only [CollatzResearch.WordTrace]
  refine ⟨226199432540825704595186153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150799621693883803063457435 226199432540825704595186153)
  ·
    refine ⟨169649574405619278446389615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226199432540825704595186153 169649574405619278446389615)
    ·
      refine ⟨254474361608428917669584423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169649574405619278446389615 254474361608428917669584423)
      ·
        refine ⟨381711542412643376504376635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254474361608428917669584423 381711542412643376504376635)
        ·
          refine ⟨572567313618965064756564953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 381711542412643376504376635 572567313618965064756564953)
          ·
            refine ⟨429425485214223798567423715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 572567313618965064756564953 429425485214223798567423715)
            ·
              refine ⟨644138227821335697851135573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 429425485214223798567423715 644138227821335697851135573)
              ·
                refine ⟨7548494857281277709192995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 644138227821335697851135573 7548494857281277709192995)
                ·
                  refine ⟨11322742285921916563789493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7548494857281277709192995 11322742285921916563789493)
                  ·
                    refine ⟨1061507089305179677855265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11322742285921916563789493 1061507089305179677855265)
                    ·
                      rfl

theorem cell23_6201833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 8, 1, 5].length) (baseStart_6201833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6201833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6201833 prefixEnd_6201833 := by exact prefixLift 6201833
  have htrace : WordTrace (prefixWord ++ tailWord_6201833) baseStart_6201833 baseEnd_6201833 := by
    simpa [prefixWord, tailWord_6201833, baseEnd_6201833] using wordTrace_append hprefix tailTrace_6201833
  have hstable : (prefixWord ++ tailWord_6201833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6201833).length < 2 ^ (prefixWord ++ tailWord_6201833).sum := by decide
  have hdescent : baseEnd_6201833 < baseStart_6201833 := by decide
  rcases family_descends (prefixWord ++ tailWord_6201833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6201857 : List Nat := [1, 2, 4, 1, 3, 1, 2, 2, 2, 3, 2]
def baseStart_6201857 : Nat := 118140960795 + 6201857 * 2 ^ 59
def prefixEnd_6201857 : Nat := 4983230072969 + 3 ^ 40 * 6201857 * 2
def baseEnd_6201857 : Nat := 3184533591451246939665685

theorem tailTrace_6201857 : CollatzResearch.WordTrace tailWord_6201857 prefixEnd_6201857 3184533591451246939665685 := by
  unfold tailWord_6201857
  simp only [CollatzResearch.WordTrace]
  refine ⟨226200307892738756694059825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150800205261825837796039883 226200307892738756694059825)
  ·
    refine ⟨169650230919554067520544869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226200307892738756694059825 169650230919554067520544869)
    ·
      refine ⟨31809418297416387660102163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 169650230919554067520544869 31809418297416387660102163)
      ·
        refine ⟨47714127446124581490153245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31809418297416387660102163 47714127446124581490153245)
        ·
          refine ⟨17892797792296718058807467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47714127446124581490153245 17892797792296718058807467)
          ·
            refine ⟨26839196688445077088211201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17892797792296718058807467 26839196688445077088211201)
            ·
              refine ⟨20129397516333807816158401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26839196688445077088211201 20129397516333807816158401)
              ·
                refine ⟨15097048137250355862118801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20129397516333807816158401 15097048137250355862118801)
                ·
                  refine ⟨11322786102937766896589101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15097048137250355862118801 11322786102937766896589101)
                  ·
                    refine ⟨4246044788601662586220913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11322786102937766896589101 4246044788601662586220913)
                    ·
                      refine ⟨3184533591451246939665685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4246044788601662586220913 3184533591451246939665685)
                      ·
                        rfl

theorem cell23_6201857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 2, 2, 3, 2].length) (baseStart_6201857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6201857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6201857 prefixEnd_6201857 := by exact prefixLift 6201857
  have htrace : WordTrace (prefixWord ++ tailWord_6201857) baseStart_6201857 baseEnd_6201857 := by
    simpa [prefixWord, tailWord_6201857, baseEnd_6201857] using wordTrace_append hprefix tailTrace_6201857
  have hstable : (prefixWord ++ tailWord_6201857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6201857).length < 2 ^ (prefixWord ++ tailWord_6201857).sum := by decide
  have hdescent : baseEnd_6201857 < baseStart_6201857 := by decide
  rcases family_descends (prefixWord ++ tailWord_6201857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6201858 : List Nat := [3, 4, 1, 2, 2, 2, 2, 2, 1, 4]
def baseStart_6201858 : Nat := 118140960795 + 6201858 * 2 ^ 59
def prefixEnd_6201858 : Nat := 4983230072969 + 3 ^ 40 * 6201858 * 2
def baseEnd_6201858 : Nat := 1061511368310633811917727

theorem tailTrace_6201858 : CollatzResearch.WordTrace tailWord_6201858 prefixEnd_6201858 1061511368310633811917727 := by
  unfold tailWord_6201858
  simp only [CollatzResearch.WordTrace]
  refine ⟨56550086091433783466211557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150800229577156755909897485 56550086091433783466211557)
  ·
    refine ⟨10603141142143834399914667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56550086091433783466211557 10603141142143834399914667)
    ·
      refine ⟨15904711713215751599872001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10603141142143834399914667 15904711713215751599872001)
      ·
        refine ⟨11928533784911813699904001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15904711713215751599872001 11928533784911813699904001)
        ·
          refine ⟨8946400338683860274928001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11928533784911813699904001 8946400338683860274928001)
          ·
            refine ⟨6709800254012895206196001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8946400338683860274928001 6709800254012895206196001)
            ·
              refine ⟨5032350190509671404647001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6709800254012895206196001 5032350190509671404647001)
              ·
                refine ⟨3774262642882253553485251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5032350190509671404647001 3774262642882253553485251)
                ·
                  refine ⟨5661393964323380330227877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3774262642882253553485251 5661393964323380330227877)
                  ·
                    refine ⟨1061511368310633811917727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5661393964323380330227877 1061511368310633811917727)
                    ·
                      rfl

theorem cell23_6201858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_6201858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6201858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6201858 prefixEnd_6201858 := by exact prefixLift 6201858
  have htrace : WordTrace (prefixWord ++ tailWord_6201858) baseStart_6201858 baseEnd_6201858 := by
    simpa [prefixWord, tailWord_6201858, baseEnd_6201858] using wordTrace_append hprefix tailTrace_6201858
  have hstable : (prefixWord ++ tailWord_6201858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6201858).length < 2 ^ (prefixWord ++ tailWord_6201858).sum := by decide
  have hdescent : baseEnd_6201858 < baseStart_6201858 := by decide
  rcases family_descends (prefixWord ++ tailWord_6201858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6201870 : List Nat := [4, 1, 1, 2, 3, 1, 1, 2, 3, 1, 4]
def baseStart_6201870 : Nat := 118140960795 + 6201870 * 2 ^ 59
def prefixEnd_6201870 : Nat := 4983230072969 + 3 ^ 40 * 6201870 * 2
def baseEnd_6201870 : Nat := 3184540266699755388803125

theorem tailTrace_6201870 : CollatzResearch.WordTrace tailWord_6201870 prefixEnd_6201870 3184540266699755388803125 := by
  unfold tailWord_6201870
  simp only [CollatzResearch.WordTrace]
  refine ⟨28275097755211457489285383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150800521361127773276188709 28275097755211457489285383)
  ·
    refine ⟨42412646632817186233928075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28275097755211457489285383 42412646632817186233928075)
    ·
      refine ⟨63618969949225779350892113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42412646632817186233928075 63618969949225779350892113)
      ·
        refine ⟨47714227461919334513169085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63618969949225779350892113 47714227461919334513169085)
        ·
          refine ⟨17892835298219750442438407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47714227461919334513169085 17892835298219750442438407)
          ·
            refine ⟨26839252947329625663657611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17892835298219750442438407 26839252947329625663657611)
            ·
              refine ⟨40258879420994438495486417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26839252947329625663657611 40258879420994438495486417)
              ·
                refine ⟨30194159565745828871614813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40258879420994438495486417 30194159565745828871614813)
                ·
                  refine ⟨11322809837154685826855555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30194159565745828871614813 11322809837154685826855555)
                  ·
                    refine ⟨16984214755732028740283333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11322809837154685826855555 16984214755732028740283333)
                    ·
                      refine ⟨3184540266699755388803125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16984214755732028740283333 3184540266699755388803125)
                      ·
                        rfl

theorem cell23_6201870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_6201870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6201870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6201870 prefixEnd_6201870 := by exact prefixLift 6201870
  have htrace : WordTrace (prefixWord ++ tailWord_6201870) baseStart_6201870 baseEnd_6201870 := by
    simpa [prefixWord, tailWord_6201870, baseEnd_6201870] using wordTrace_append hprefix tailTrace_6201870
  have hstable : (prefixWord ++ tailWord_6201870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6201870).length < 2 ^ (prefixWord ++ tailWord_6201870).sum := by decide
  have hdescent : baseEnd_6201870 < baseStart_6201870 := by decide
  rcases family_descends (prefixWord ++ tailWord_6201870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6201880 : List Nat := [2, 1, 2, 3, 3, 2, 2, 1, 1, 6]
def baseStart_6201880 : Nat := 118140960795 + 6201880 * 2 ^ 59
def prefixEnd_6201880 : Nat := 4983230072969 + 3 ^ 40 * 6201880 * 2
def baseEnd_6201880 : Nat := 1061515133835433449892693

theorem tailTrace_6201880 : CollatzResearch.WordTrace tailWord_6201880 prefixEnd_6201880 1061515133835433449892693 := by
  unfold tailWord_6201880
  simp only [CollatzResearch.WordTrace]
  refine ⟨113100573385827715811073547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150800764514436954414764729 113100573385827715811073547)
  ·
    refine ⟨169650860078741573716610321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113100573385827715811073547 169650860078741573716610321)
    ·
      refine ⟨127238145059056180287457741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169650860078741573716610321 127238145059056180287457741)
      ·
        refine ⟨47714304397146067607796653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127238145059056180287457741 47714304397146067607796653)
        ·
          refine ⟨17892864148929775352923745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47714304397146067607796653 17892864148929775352923745)
          ·
            refine ⟨13419648111697331514692809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17892864148929775352923745 13419648111697331514692809)
            ·
              refine ⟨10064736083772998636019607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13419648111697331514692809 10064736083772998636019607)
              ·
                refine ⟨15097104125659497954029411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10064736083772998636019607 15097104125659497954029411)
                ·
                  refine ⟨22645656188489246931044117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15097104125659497954029411 22645656188489246931044117)
                  ·
                    refine ⟨1061515133835433449892693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22645656188489246931044117 1061515133835433449892693)
                    ·
                      rfl

theorem cell23_6201880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 1, 1, 6].length) (baseStart_6201880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6201880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6201880 prefixEnd_6201880 := by exact prefixLift 6201880
  have htrace : WordTrace (prefixWord ++ tailWord_6201880) baseStart_6201880 baseEnd_6201880 := by
    simpa [prefixWord, tailWord_6201880, baseEnd_6201880] using wordTrace_append hprefix tailTrace_6201880
  have hstable : (prefixWord ++ tailWord_6201880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6201880).length < 2 ^ (prefixWord ++ tailWord_6201880).sum := by decide
  have hdescent : baseEnd_6201880 < baseStart_6201880 := by decide
  rcases family_descends (prefixWord ++ tailWord_6201880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6201901 : List Nat := [1, 5, 4, 1, 1, 1, 1, 3, 1, 5]
def baseStart_6201901 : Nat := 118140960795 + 6201901 * 2 ^ 59
def prefixEnd_6201901 : Nat := 4983230072969 + 3 ^ 40 * 6201901 * 2
def baseEnd_6201901 : Nat := 1061518728200014922505161

theorem tailTrace_6201901 : CollatzResearch.WordTrace tailWord_6201901 prefixEnd_6201901 1061518728200014922505161 := by
  unfold tailWord_6201901
  simp only [CollatzResearch.WordTrace]
  refine ⟨226201912704579352208661557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150801275136386234805774371 226201912704579352208661557)
  ·
    refine ⟨21206429316054314269562021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 226201912704579352208661557 21206429316054314269562021)
    ·
      refine ⟨3976205496760183925542879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21206429316054314269562021 3976205496760183925542879)
      ·
        refine ⟨5964308245140275888314319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3976205496760183925542879 5964308245140275888314319)
        ·
          refine ⟨8946462367710413832471479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5964308245140275888314319 8946462367710413832471479)
          ·
            refine ⟨13419693551565620748707219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8946462367710413832471479 13419693551565620748707219)
            ·
              refine ⟨20129540327348431123060829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13419693551565620748707219 20129540327348431123060829)
              ·
                refine ⟨7548577622755661671147811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20129540327348431123060829 7548577622755661671147811)
                ·
                  refine ⟨11322866434133492506721717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7548577622755661671147811 11322866434133492506721717)
                  ·
                    refine ⟨1061518728200014922505161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11322866434133492506721717 1061518728200014922505161)
                    ·
                      rfl

theorem cell23_6201901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_6201901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6201901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6201901 prefixEnd_6201901 := by exact prefixLift 6201901
  have htrace : WordTrace (prefixWord ++ tailWord_6201901) baseStart_6201901 baseEnd_6201901 := by
    simpa [prefixWord, tailWord_6201901, baseEnd_6201901] using wordTrace_append hprefix tailTrace_6201901
  have hstable : (prefixWord ++ tailWord_6201901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6201901).length < 2 ^ (prefixWord ++ tailWord_6201901).sum := by decide
  have hdescent : baseEnd_6201901 < baseStart_6201901 := by decide
  rcases family_descends (prefixWord ++ tailWord_6201901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6201904 : List Nat := [2, 1, 1, 1, 2, 3, 3, 5, 1, 2, 2]
def baseStart_6201904 : Nat := 118140960795 + 6201904 * 2 ^ 59
def prefixEnd_6201904 : Nat := 4983230072969 + 3 ^ 40 * 6201904 * 2
def baseEnd_6201904 : Nat := 3184557725042008255777969

theorem tailTrace_6201904 : CollatzResearch.WordTrace tailWord_6201904 prefixEnd_6201904 3184557725042008255777969 := by
  unfold tailWord_6201904
  simp only [CollatzResearch.WordTrace]
  refine ⟨113101011061784241860510383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150801348082378989147347177 113101011061784241860510383)
  ·
    refine ⟨169651516592676362790765575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113101011061784241860510383 169651516592676362790765575)
    ·
      refine ⟨254477274889014544186148363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169651516592676362790765575 254477274889014544186148363)
      ·
        refine ⟨381715912333521816279222545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254477274889014544186148363 381715912333521816279222545)
        ·
          refine ⟨286286934250141362209416909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 381715912333521816279222545 286286934250141362209416909)
          ·
            refine ⟨107357600343803010828531341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 286286934250141362209416909 107357600343803010828531341)
            ·
              refine ⟨40259100128926129060699253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107357600343803010828531341 40259100128926129060699253)
              ·
                refine ⟨3774290637086824599440555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40259100128926129060699253 3774290637086824599440555)
                ·
                  refine ⟨5661435955630236899160833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3774290637086824599440555 5661435955630236899160833)
                  ·
                    refine ⟨4246076966722677674370625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5661435955630236899160833 4246076966722677674370625)
                    ·
                      refine ⟨3184557725042008255777969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4246076966722677674370625 3184557725042008255777969)
                      ·
                        rfl

theorem cell23_6201904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 5, 1, 2, 2].length) (baseStart_6201904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6201904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6201904 prefixEnd_6201904 := by exact prefixLift 6201904
  have htrace : WordTrace (prefixWord ++ tailWord_6201904) baseStart_6201904 baseEnd_6201904 := by
    simpa [prefixWord, tailWord_6201904, baseEnd_6201904] using wordTrace_append hprefix tailTrace_6201904
  have hstable : (prefixWord ++ tailWord_6201904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6201904).length < 2 ^ (prefixWord ++ tailWord_6201904).sum := by decide
  have hdescent : baseEnd_6201904 < baseStart_6201904 := by decide
  rcases family_descends (prefixWord ++ tailWord_6201904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6201910 : List Nat := [5, 1, 2, 1, 2, 2, 10]
def baseStart_6201910 : Nat := 118140960795 + 6201910 * 2 ^ 59
def prefixEnd_6201910 : Nat := 4983230072969 + 3 ^ 40 * 6201910 * 2
def baseEnd_6201910 : Nat := 39315565505258459658061

theorem tailTrace_6201910 : CollatzResearch.WordTrace tailWord_6201910 prefixEnd_6201910 39315565505258459658061 := by
  unfold tailWord_6201910
  simp only [CollatzResearch.WordTrace]
  refine ⟨14137640060096671671608699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 150801493974364497830492789 14137640060096671671608699)
  ·
    refine ⟨21206460090145007507413049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14137640060096671671608699 21206460090145007507413049)
    ·
      refine ⟨15904845067608755630559787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21206460090145007507413049 15904845067608755630559787)
      ·
        refine ⟨23857267601413133445839681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15904845067608755630559787 23857267601413133445839681)
        ·
          refine ⟨17892950701059850084379761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23857267601413133445839681 17892950701059850084379761)
          ·
            refine ⟨13419713025794887563284821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17892950701059850084379761 13419713025794887563284821)
            ·
              refine ⟨39315565505258459658061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13419713025794887563284821 39315565505258459658061)
              ·
                rfl

theorem cell23_6201910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 10].length) (baseStart_6201910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6201910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6201910 prefixEnd_6201910 := by exact prefixLift 6201910
  have htrace : WordTrace (prefixWord ++ tailWord_6201910) baseStart_6201910 baseEnd_6201910 := by
    simpa [prefixWord, tailWord_6201910, baseEnd_6201910] using wordTrace_append hprefix tailTrace_6201910
  have hstable : (prefixWord ++ tailWord_6201910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6201910).length < 2 ^ (prefixWord ++ tailWord_6201910).sum := by decide
  have hdescent : baseEnd_6201910 < baseStart_6201910 := by decide
  rcases family_descends (prefixWord ++ tailWord_6201910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6201921 : List Nat := [1, 2, 5, 1, 1, 2, 2, 4, 1, 2, 2]
def baseStart_6201921 : Nat := 118140960795 + 6201921 * 2 ^ 59
def prefixEnd_6201921 : Nat := 4983230072969 + 3 ^ 40 * 6201921 * 2
def baseEnd_6201921 : Nat := 3184566454213134689265391

theorem tailTrace_6201921 : CollatzResearch.WordTrace tailWord_6201921 prefixEnd_6201921 3184566454213134689265391 := by
  unfold tailWord_6201921
  simp only [CollatzResearch.WordTrace]
  refine ⟨226202642164506895624389617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150801761443004597082926411 226202642164506895624389617)
  ·
    refine ⟨169651981623380171718292213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226202642164506895624389617 169651981623380171718292213)
    ·
      refine ⟨15904873277191891098589895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 169651981623380171718292213 15904873277191891098589895)
      ·
        refine ⟨23857309915787836647884843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15904873277191891098589895 23857309915787836647884843)
        ·
          refine ⟨35785964873681754971827265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23857309915787836647884843 35785964873681754971827265)
          ·
            refine ⟨26839473655261316228870449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35785964873681754971827265 26839473655261316228870449)
            ·
              refine ⟨20129605241445987171652837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26839473655261316228870449 20129605241445987171652837)
              ·
                refine ⟨3774300982771122594684907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20129605241445987171652837 3774300982771122594684907)
                ·
                  refine ⟨5661451474156683892027361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3774300982771122594684907 5661451474156683892027361)
                  ·
                    refine ⟨4246088605617512919020521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5661451474156683892027361 4246088605617512919020521)
                    ·
                      refine ⟨3184566454213134689265391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4246088605617512919020521 3184566454213134689265391)
                      ·
                        rfl

theorem cell23_6201921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 4, 1, 2, 2].length) (baseStart_6201921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6201921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6201921 prefixEnd_6201921 := by exact prefixLift 6201921
  have htrace : WordTrace (prefixWord ++ tailWord_6201921) baseStart_6201921 baseEnd_6201921 := by
    simpa [prefixWord, tailWord_6201921, baseEnd_6201921] using wordTrace_append hprefix tailTrace_6201921
  have hstable : (prefixWord ++ tailWord_6201921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6201921).length < 2 ^ (prefixWord ++ tailWord_6201921).sum := by decide
  have hdescent : baseEnd_6201921 < baseStart_6201921 := by decide
  rcases family_descends (prefixWord ++ tailWord_6201921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6201937 : List Nat := [1, 2, 2, 1, 3, 5, 1, 1, 1, 3, 3]
def baseStart_6201937 : Nat := 118140960795 + 6201937 * 2 ^ 59
def prefixEnd_6201937 : Nat := 4983230072969 + 3 ^ 40 * 6201937 * 2
def baseEnd_6201937 : Nat := 3184574669903606626665317

theorem tailTrace_6201937 : CollatzResearch.WordTrace tailWord_6201937 prefixEnd_6201937 3184574669903606626665317 := by
  unfold tailWord_6201937
  simp only [CollatzResearch.WordTrace]
  refine ⟨226203225732448930356972065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150802150488299286904648043 226203225732448930356972065)
  ·
    refine ⟨169652419299336697767729049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226203225732448930356972065 169652419299336697767729049)
    ·
      refine ⟨127239314474502523325796787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169652419299336697767729049 127239314474502523325796787)
      ·
        refine ⟨190858971711753784988695181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127239314474502523325796787 190858971711753784988695181)
        ·
          refine ⟨71572114391907669370760693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 190858971711753784988695181 71572114391907669370760693)
          ·
            refine ⟨6709885724241344003508815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 71572114391907669370760693 6709885724241344003508815)
            ·
              refine ⟨10064828586362016005263223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6709885724241344003508815 10064828586362016005263223)
              ·
                refine ⟨15097242879543024007894835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10064828586362016005263223 15097242879543024007894835)
                ·
                  refine ⟨22645864319314536011842253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15097242879543024007894835 22645864319314536011842253)
                  ·
                    refine ⟨8492199119742951004440845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22645864319314536011842253 8492199119742951004440845)
                    ·
                      refine ⟨3184574669903606626665317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8492199119742951004440845 3184574669903606626665317)
                      ·
                        rfl

theorem cell23_6201937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 1, 1, 3, 3].length) (baseStart_6201937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6201937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6201937 prefixEnd_6201937 := by exact prefixLift 6201937
  have htrace : WordTrace (prefixWord ++ tailWord_6201937) baseStart_6201937 baseEnd_6201937 := by
    simpa [prefixWord, tailWord_6201937, baseEnd_6201937] using wordTrace_append hprefix tailTrace_6201937
  have hstable : (prefixWord ++ tailWord_6201937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6201937).length < 2 ^ (prefixWord ++ tailWord_6201937).sum := by decide
  have hdescent : baseEnd_6201937 < baseStart_6201937 := by decide
  rcases family_descends (prefixWord ++ tailWord_6201937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6201983 : List Nat := [1, 1, 2, 2, 1, 1, 1, 7, 7]
def baseStart_6201983 : Nat := 118140960795 + 6201983 * 2 ^ 59
def prefixEnd_6201983 : Nat := 4983230072969 + 3 ^ 40 * 6201983 * 2
def baseEnd_6201983 : Nat := 353844254445968160743345

theorem tailTrace_6201983 : CollatzResearch.WordTrace tailWord_6201983 prefixEnd_6201983 353844254445968160743345 := by
  unfold tailWord_6201983
  simp only [CollatzResearch.WordTrace]
  refine ⟨226204903490282280213146603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150803268993521520142097735 226204903490282280213146603)
  ·
    refine ⟨339307355235423420319719905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226204903490282280213146603 339307355235423420319719905)
    ·
      refine ⟨254480516426567565239789929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 339307355235423420319719905 254480516426567565239789929)
      ·
        refine ⟨190860387319925673929842447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 254480516426567565239789929 190860387319925673929842447)
        ·
          refine ⟨286290580979888510894763671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190860387319925673929842447 286290580979888510894763671)
          ·
            refine ⟨429435871469832766342145507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286290580979888510894763671 429435871469832766342145507)
            ·
              refine ⟨644153807204749149513218261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 429435871469832766342145507 644153807204749149513218261)
              ·
                refine ⟨15097354856361308191716053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 644153807204749149513218261 15097354856361308191716053)
                ·
                  refine ⟨353844254445968160743345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15097354856361308191716053 353844254445968160743345)
                  ·
                    rfl

theorem cell23_6201983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 7, 7].length) (baseStart_6201983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6201983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6201983 prefixEnd_6201983 := by exact prefixLift 6201983
  have htrace : WordTrace (prefixWord ++ tailWord_6201983) baseStart_6201983 baseEnd_6201983 := by
    simpa [prefixWord, tailWord_6201983, baseEnd_6201983] using wordTrace_append hprefix tailTrace_6201983
  have hstable : (prefixWord ++ tailWord_6201983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6201983).length < 2 ^ (prefixWord ++ tailWord_6201983).sum := by decide
  have hdescent : baseEnd_6201983 < baseStart_6201983 := by decide
  rcases family_descends (prefixWord ++ tailWord_6201983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6202043 : List Nat := [1, 1, 1, 1, 1, 2, 3, 1, 4, 8]
def baseStart_6202043 : Nat := 118140960795 + 6202043 * 2 ^ 59
def prefixEnd_6202043 : Nat := 4983230072969 + 3 ^ 40 * 6202043 * 2
def baseEnd_6202043 : Nat := 1061543032950994403979943

theorem tailTrace_6202043 : CollatzResearch.WordTrace tailWord_6202043 prefixEnd_6202043 1061543032950994403979943 := by
  unfold tailWord_6202043
  simp only [CollatzResearch.WordTrace]
  refine ⟨226207091870064910460330783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150804727913376606973553855 226207091870064910460330783)
  ·
    refine ⟨339310637805097365690496175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226207091870064910460330783 339310637805097365690496175)
    ·
      refine ⟨508965956707646048535744263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339310637805097365690496175 508965956707646048535744263)
      ·
        refine ⟨763448935061469072803616395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 508965956707646048535744263 763448935061469072803616395)
        ·
          refine ⟨1145173402592203609205424593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 763448935061469072803616395 1145173402592203609205424593)
          ·
            refine ⟨858880051944152706904068445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1145173402592203609205424593 858880051944152706904068445)
            ·
              refine ⟨322080019479057265089025667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 858880051944152706904068445 322080019479057265089025667)
              ·
                refine ⟨483120029218585897633538501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 322080019479057265089025667 483120029218585897633538501)
                ·
                  refine ⟨90585005478484855806288469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 483120029218585897633538501 90585005478484855806288469)
                  ·
                    refine ⟨1061543032950994403979943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 90585005478484855806288469 1061543032950994403979943)
                    ·
                      rfl

theorem cell23_6202043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 8].length) (baseStart_6202043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6202043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6202043 prefixEnd_6202043 := by exact prefixLift 6202043
  have htrace : WordTrace (prefixWord ++ tailWord_6202043) baseStart_6202043 baseEnd_6202043 := by
    simpa [prefixWord, tailWord_6202043, baseEnd_6202043] using wordTrace_append hprefix tailTrace_6202043
  have hstable : (prefixWord ++ tailWord_6202043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6202043).length < 2 ^ (prefixWord ++ tailWord_6202043).sum := by decide
  have hdescent : baseEnd_6202043 < baseStart_6202043 := by decide
  rcases family_descends (prefixWord ++ tailWord_6202043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6202094 : List Nat := [4, 1, 2, 1, 1, 4, 2, 1, 3, 4]
def baseStart_6202094 : Nat := 118140960795 + 6202094 * 2 ^ 59
def prefixEnd_6202094 : Nat := 4983230072969 + 3 ^ 40 * 6202094 * 2
def baseEnd_6202094 : Nat := 1061551762122120837467365

theorem tailTrace_6202094 : CollatzResearch.WordTrace tailWord_6202094 prefixEnd_6202094 1061551762122120837467365 := by
  unfold tailWord_6202094
  simp only [CollatzResearch.WordTrace]
  refine ⟨28276118999110018271304667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150805967995253430780291557 28276118999110018271304667)
  ·
    refine ⟨42414178498665027406957001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28276118999110018271304667 42414178498665027406957001)
    ·
      refine ⟨31810633873998770555217751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42414178498665027406957001 31810633873998770555217751)
      ·
        refine ⟨47715950810998155832826627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31810633873998770555217751 47715950810998155832826627)
        ·
          refine ⟨71573926216497233749239941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47715950810998155832826627 71573926216497233749239941)
          ·
            refine ⟨13420111165593231327982489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71573926216497233749239941 13420111165593231327982489)
            ·
              refine ⟨10065083374194923495986867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13420111165593231327982489 10065083374194923495986867)
              ·
                refine ⟨15097625061292385243980301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10065083374194923495986867 15097625061292385243980301)
                ·
                  refine ⟨5661609397984644466492613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15097625061292385243980301 5661609397984644466492613)
                  ·
                    refine ⟨1061551762122120837467365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5661609397984644466492613 1061551762122120837467365)
                    ·
                      rfl

theorem cell23_6202094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 1, 3, 4].length) (baseStart_6202094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6202094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6202094 prefixEnd_6202094 := by exact prefixLift 6202094
  have htrace : WordTrace (prefixWord ++ tailWord_6202094) baseStart_6202094 baseEnd_6202094 := by
    simpa [prefixWord, tailWord_6202094, baseEnd_6202094] using wordTrace_append hprefix tailTrace_6202094
  have hstable : (prefixWord ++ tailWord_6202094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6202094).length < 2 ^ (prefixWord ++ tailWord_6202094).sum := by decide
  have hdescent : baseEnd_6202094 < baseStart_6202094 := by decide
  rcases family_descends (prefixWord ++ tailWord_6202094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6202127 : List Nat := [1, 1, 2, 1, 1, 1, 5, 3, 1, 5, 2]
def baseStart_6202127 : Nat := 118140960795 + 6202127 * 2 ^ 59
def prefixEnd_6202127 : Nat := 4983230072969 + 3 ^ 40 * 6202127 * 2
def baseEnd_6202127 : Nat := 3184672231227960883289443

theorem tailTrace_6202127 : CollatzResearch.WordTrace tailWord_6202127 prefixEnd_6202127 3184672231227960883289443 := by
  unfold tailWord_6202127
  simp only [CollatzResearch.WordTrace]
  refine ⟨226210155601760592806388635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150806770401173728537592423 226210155601760592806388635)
  ·
    refine ⟨339315233402640889209582953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226210155601760592806388635 339315233402640889209582953)
    ·
      refine ⟨254486425051980666907187215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 339315233402640889209582953 254486425051980666907187215)
      ·
        refine ⟨381729637577971000360780823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254486425051980666907187215 381729637577971000360780823)
        ·
          refine ⟨572594456366956500541171235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 381729637577971000360780823 572594456366956500541171235)
          ·
            refine ⟨858891684550434750811756853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 572594456366956500541171235 858891684550434750811756853)
            ·
              refine ⟨80521095426603257888602205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 858891684550434750811756853 80521095426603257888602205)
              ·
                refine ⟨30195410784976221708225827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80521095426603257888602205 30195410784976221708225827)
                ·
                  refine ⟨45293116177464332562338741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30195410784976221708225827 45293116177464332562338741)
                  ·
                    refine ⟨4246229641637281177719257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45293116177464332562338741 4246229641637281177719257)
                    ·
                      refine ⟨3184672231227960883289443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4246229641637281177719257 3184672231227960883289443)
                      ·
                        rfl

theorem cell23_6202127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 3, 1, 5, 2].length) (baseStart_6202127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6202127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6202127 prefixEnd_6202127 := by exact prefixLift 6202127
  have htrace : WordTrace (prefixWord ++ tailWord_6202127) baseStart_6202127 baseEnd_6202127 := by
    simpa [prefixWord, tailWord_6202127, baseEnd_6202127] using wordTrace_append hprefix tailTrace_6202127
  have hstable : (prefixWord ++ tailWord_6202127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6202127).length < 2 ^ (prefixWord ++ tailWord_6202127).sum := by decide
  have hdescent : baseEnd_6202127 < baseStart_6202127 := by decide
  rcases family_descends (prefixWord ++ tailWord_6202127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6202144 : List Nat := [2, 1, 1, 5, 1, 2, 1, 1, 4, 3, 2]
def baseStart_6202144 : Nat := 118140960795 + 6202144 * 2 ^ 59
def prefixEnd_6202144 : Nat := 4983230072969 + 3 ^ 40 * 6202144 * 2
def baseEnd_6202144 : Nat := 3184680960399087316776865

theorem tailTrace_6202144 : CollatzResearch.WordTrace tailWord_6202144 prefixEnd_6202144 3184680960399087316776865 := by
  unfold tailWord_6202144
  simp only [CollatzResearch.WordTrace]
  refine ⟨113105387821349502354878743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150807183761799336473171657 113105387821349502354878743)
  ·
    refine ⟨169658081732024253532318115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113105387821349502354878743 169658081732024253532318115)
    ·
      refine ⟨254487122598036380298477173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169658081732024253532318115 254487122598036380298477173)
      ·
        refine ⟨23858167743565910652982235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 254487122598036380298477173 23858167743565910652982235)
        ·
          refine ⟨35787251615348865979473353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23858167743565910652982235 35787251615348865979473353)
          ·
            refine ⟨26840438711511649484605015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35787251615348865979473353 26840438711511649484605015)
            ·
              refine ⟨40260658067267474226907523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26840438711511649484605015 40260658067267474226907523)
              ·
                refine ⟨60390987100901211340361285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40260658067267474226907523 60390987100901211340361285)
                ·
                  refine ⟨11323310081418977126317741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60390987100901211340361285 11323310081418977126317741)
                  ·
                    refine ⟨4246241280532116422369153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11323310081418977126317741 4246241280532116422369153)
                    ·
                      refine ⟨3184680960399087316776865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4246241280532116422369153 3184680960399087316776865)
                      ·
                        rfl

theorem cell23_6202144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 4, 3, 2].length) (baseStart_6202144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6202144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6202144 prefixEnd_6202144 := by exact prefixLift 6202144
  have htrace : WordTrace (prefixWord ++ tailWord_6202144) baseStart_6202144 baseEnd_6202144 := by
    simpa [prefixWord, tailWord_6202144, baseEnd_6202144] using wordTrace_append hprefix tailTrace_6202144
  have hstable : (prefixWord ++ tailWord_6202144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6202144).length < 2 ^ (prefixWord ++ tailWord_6202144).sum := by decide
  have hdescent : baseEnd_6202144 < baseStart_6202144 := by decide
  rcases family_descends (prefixWord ++ tailWord_6202144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6202207 : List Nat := [1, 1, 2, 3, 1, 3, 1, 2, 3, 3, 3]
def baseStart_6202207 : Nat := 118140960795 + 6202207 * 2 ^ 59
def prefixEnd_6202207 : Nat := 4983230072969 + 3 ^ 40 * 6202207 * 2
def baseEnd_6202207 : Nat := 3184713309680320570289075

theorem tailTrace_6202207 : CollatzResearch.WordTrace tailWord_6202207 prefixEnd_6202207 3184713309680320570289075 := by
  unfold tailWord_6202207
  simp only [CollatzResearch.WordTrace]
  refine ⟨226213073441470766469300875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150808715627647177646200583 226213073441470766469300875)
  ·
    refine ⟨339319610162206149703951313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226213073441470766469300875 339319610162206149703951313)
    ·
      refine ⟨254489707621654612277963485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 339319610162206149703951313 254489707621654612277963485)
      ·
        refine ⟨95433640358120479604236307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 254489707621654612277963485 95433640358120479604236307)
        ·
          refine ⟨143150460537180719406354461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95433640358120479604236307 143150460537180719406354461)
          ·
            refine ⟨53681422701442769777382923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143150460537180719406354461 53681422701442769777382923)
            ·
              refine ⟨80522134052164154666074385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53681422701442769777382923 80522134052164154666074385)
              ·
                refine ⟨60391600539123115999555789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80522134052164154666074385 60391600539123115999555789)
                ·
                  refine ⟨22646850202171168499833421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60391600539123115999555789 22646850202171168499833421)
                  ·
                    refine ⟨8492568825814188187437533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22646850202171168499833421 8492568825814188187437533)
                    ·
                      refine ⟨3184713309680320570289075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8492568825814188187437533 3184713309680320570289075)
                      ·
                        rfl

theorem cell23_6202207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 3, 3, 3].length) (baseStart_6202207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6202207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6202207 prefixEnd_6202207 := by exact prefixLift 6202207
  have htrace : WordTrace (prefixWord ++ tailWord_6202207) baseStart_6202207 baseEnd_6202207 := by
    simpa [prefixWord, tailWord_6202207, baseEnd_6202207] using wordTrace_append hprefix tailTrace_6202207
  have hstable : (prefixWord ++ tailWord_6202207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6202207).length < 2 ^ (prefixWord ++ tailWord_6202207).sum := by decide
  have hdescent : baseEnd_6202207 < baseStart_6202207 := by decide
  rcases family_descends (prefixWord ++ tailWord_6202207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6202208 : List Nat := [2, 1, 1, 3, 3, 1, 3, 4, 1, 2, 2]
def baseStart_6202208 : Nat := 118140960795 + 6202208 * 2 ^ 59
def prefixEnd_6202208 : Nat := 4983230072969 + 3 ^ 40 * 6202208 * 2
def baseEnd_6202208 : Nat := 3184713823160975066376571

theorem tailTrace_6202208 : CollatzResearch.WordTrace tailWord_6202208 prefixEnd_6202208 3184713823160975066376571 := by
  unfold tailWord_6202208
  simp only [CollatzResearch.WordTrace]
  refine ⟨113106554957233571820043639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150808739942978095760058185 113106554957233571820043639)
  ·
    refine ⟨169659832435850357730065459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113106554957233571820043639 169659832435850357730065459)
    ·
      refine ⟨254489748653775536595098189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169659832435850357730065459 254489748653775536595098189)
      ·
        refine ⟨95433655745165826223161821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 254489748653775536595098189 95433655745165826223161821)
        ·
          refine ⟨35787620904437184833685683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95433655745165826223161821 35787620904437184833685683)
          ·
            refine ⟨53681431356655777250528525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35787620904437184833685683 53681431356655777250528525)
            ·
              refine ⟨20130536758745916468948197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53681431356655777250528525 20130536758745916468948197)
              ·
                refine ⟨3774475642264859337927787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20130536758745916468948197 3774475642264859337927787)
                ·
                  refine ⟨5661713463397289006891681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3774475642264859337927787 5661713463397289006891681)
                  ·
                    refine ⟨4246285097547966755168761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5661713463397289006891681 4246285097547966755168761)
                    ·
                      refine ⟨3184713823160975066376571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4246285097547966755168761 3184713823160975066376571)
                      ·
                        rfl

theorem cell23_6202208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 4, 1, 2, 2].length) (baseStart_6202208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6202208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6202208 prefixEnd_6202208 := by exact prefixLift 6202208
  have htrace : WordTrace (prefixWord ++ tailWord_6202208) baseStart_6202208 baseEnd_6202208 := by
    simpa [prefixWord, tailWord_6202208, baseEnd_6202208] using wordTrace_append hprefix tailTrace_6202208
  have hstable : (prefixWord ++ tailWord_6202208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6202208).length < 2 ^ (prefixWord ++ tailWord_6202208).sum := by decide
  have hdescent : baseEnd_6202208 < baseStart_6202208 := by decide
  rcases family_descends (prefixWord ++ tailWord_6202208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6202242 : List Nat := [3, 4, 2, 2, 1, 2, 2, 1, 1, 1, 4]
def baseStart_6202242 : Nat := 118140960795 + 6202242 * 2 ^ 59
def prefixEnd_6202242 : Nat := 4983230072969 + 3 ^ 40 * 6202242 * 2
def baseEnd_6202242 : Nat := 3184731281503227933351415

theorem tailTrace_6202242 : CollatzResearch.WordTrace tailWord_6202242 prefixEnd_6202242 3184731281503227933351415 := by
  unfold tailWord_6202242
  simp only [CollatzResearch.WordTrace]
  refine ⟨56553587499085991861706245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150809566664229311631216653 56553587499085991861706245)
  ·
    refine ⟨10603797656078623474069921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56553587499085991861706245 10603797656078623474069921)
    ·
      refine ⟨7952848242058967605552441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10603797656078623474069921 7952848242058967605552441)
      ·
        refine ⟨5964636181544225704164331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7952848242058967605552441 5964636181544225704164331)
        ·
          refine ⟨8946954272316338556246497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5964636181544225704164331 8946954272316338556246497)
          ·
            refine ⟨6710215704237253917184873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8946954272316338556246497 6710215704237253917184873)
            ·
              refine ⟨5032661778177940437888655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6710215704237253917184873 5032661778177940437888655)
              ·
                refine ⟨7548992667266910656832983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5032661778177940437888655 7548992667266910656832983)
                ·
                  refine ⟨11323489000900365985249475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7548992667266910656832983 11323489000900365985249475)
                  ·
                    refine ⟨16985233501350548977874213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11323489000900365985249475 16985233501350548977874213)
                    ·
                      refine ⟨3184731281503227933351415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16985233501350548977874213 3184731281503227933351415)
                      ·
                        rfl

theorem cell23_6202242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_6202242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6202242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6202242 prefixEnd_6202242 := by exact prefixLift 6202242
  have htrace : WordTrace (prefixWord ++ tailWord_6202242) baseStart_6202242 baseEnd_6202242 := by
    simpa [prefixWord, tailWord_6202242, baseEnd_6202242] using wordTrace_append hprefix tailTrace_6202242
  have hstable : (prefixWord ++ tailWord_6202242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6202242).length < 2 ^ (prefixWord ++ tailWord_6202242).sum := by decide
  have hdescent : baseEnd_6202242 < baseStart_6202242 := by decide
  rcases family_descends (prefixWord ++ tailWord_6202242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6202258 : List Nat := [3, 2, 3, 2, 2, 1, 1, 1, 4, 1, 3]
def baseStart_6202258 : Nat := 118140960795 + 6202258 * 2 ^ 59
def prefixEnd_6202258 : Nat := 4983230072969 + 3 ^ 40 * 6202258 * 2
def baseEnd_6202258 : Nat := 3184739497193699870751341

theorem tailTrace_6202258 : CollatzResearch.WordTrace tailWord_6202258 prefixEnd_6202258 3184739497193699870751341 := by
  unfold tailWord_6202258
  simp only [CollatzResearch.WordTrace]
  refine ⟨56553733391071500544851857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150809955709524001452938285 56553733391071500544851857)
  ·
    refine ⟨42415300043303625408638893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56553733391071500544851857 42415300043303625408638893)
    ·
      refine ⟨15905737516238859528239585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42415300043303625408638893 15905737516238859528239585)
      ·
        refine ⟨11929303137179144646179689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15905737516238859528239585 11929303137179144646179689)
        ·
          refine ⟨8946977352884358484634767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11929303137179144646179689 8946977352884358484634767)
          ·
            refine ⟨13420466029326537726952151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8946977352884358484634767 13420466029326537726952151)
            ·
              refine ⟨20130699043989806590428227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13420466029326537726952151 20130699043989806590428227)
              ·
                refine ⟨30196048565984709885642341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20130699043989806590428227 30196048565984709885642341)
                ·
                  refine ⟨5661759106122133103557939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30196048565984709885642341 5661759106122133103557939)
                  ·
                    refine ⟨8492638659183199655336909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5661759106122133103557939 8492638659183199655336909)
                    ·
                      refine ⟨3184739497193699870751341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8492638659183199655336909 3184739497193699870751341)
                      ·
                        rfl

theorem cell23_6202258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_6202258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6202258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6202258 prefixEnd_6202258 := by exact prefixLift 6202258
  have htrace : WordTrace (prefixWord ++ tailWord_6202258) baseStart_6202258 baseEnd_6202258 := by
    simpa [prefixWord, tailWord_6202258, baseEnd_6202258] using wordTrace_append hprefix tailTrace_6202258
  have hstable : (prefixWord ++ tailWord_6202258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6202258).length < 2 ^ (prefixWord ++ tailWord_6202258).sum := by decide
  have hdescent : baseEnd_6202258 < baseStart_6202258 := by decide
  rcases family_descends (prefixWord ++ tailWord_6202258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6202274 : List Nat := [3, 3, 1, 2, 2, 1, 2, 1, 2, 6]
def baseStart_6202274 : Nat := 118140960795 + 6202274 * 2 ^ 59
def prefixEnd_6202274 : Nat := 4983230072969 + 3 ^ 40 * 6202274 * 2
def baseEnd_6202274 : Nat := 1061582570961390602717089

theorem tailTrace_6202274 : CollatzResearch.WordTrace tailWord_6202274 prefixEnd_6202274 1061582570961390602717089 := by
  unfold tailWord_6202274
  simp only [CollatzResearch.WordTrace]
  refine ⟨56553879283057009227997469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150810344754818691274659917 56553879283057009227997469)
  ·
    refine ⟨21207704731146378460499051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56553879283057009227997469 21207704731146378460499051)
    ·
      refine ⟨31811557096719567690748577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21207704731146378460499051 31811557096719567690748577)
      ·
        refine ⟨23858667822539675768061433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31811557096719567690748577 23858667822539675768061433)
        ·
          refine ⟨17894000866904756826046075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23858667822539675768061433 17894000866904756826046075)
          ·
            refine ⟨26841001300357135239069113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17894000866904756826046075 26841001300357135239069113)
            ·
              refine ⟨20130750975267851429301835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26841001300357135239069113 20130750975267851429301835)
              ·
                refine ⟨30196126462901777143952753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20130750975267851429301835 30196126462901777143952753)
                ·
                  refine ⟨22647094847176332857964565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30196126462901777143952753 22647094847176332857964565)
                  ·
                    refine ⟨1061582570961390602717089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22647094847176332857964565 1061582570961390602717089)
                    ·
                      rfl

theorem cell23_6202274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 1, 2, 6].length) (baseStart_6202274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6202274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6202274 prefixEnd_6202274 := by exact prefixLift 6202274
  have htrace : WordTrace (prefixWord ++ tailWord_6202274) baseStart_6202274 baseEnd_6202274 := by
    simpa [prefixWord, tailWord_6202274, baseEnd_6202274] using wordTrace_append hprefix tailTrace_6202274
  have hstable : (prefixWord ++ tailWord_6202274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6202274).length < 2 ^ (prefixWord ++ tailWord_6202274).sum := by decide
  have hdescent : baseEnd_6202274 < baseStart_6202274 := by decide
  rcases family_descends (prefixWord ++ tailWord_6202274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6202321 : List Nat := [1, 2, 2, 1, 2, 1, 7, 2, 5]
def baseStart_6202321 : Nat := 118140960795 + 6202321 * 2 ^ 59
def prefixEnd_6202321 : Nat := 4983230072969 + 3 ^ 40 * 6202321 * 2
def baseEnd_6202321 : Nat := 353863538497214791584839

theorem tailTrace_6202321 : CollatzResearch.WordTrace tailWord_6202321 prefixEnd_6202321 353863538497214791584839 := by
  unfold tailWord_6202321
  simp only [CollatzResearch.WordTrace]
  refine ⟨226217231363057763938950817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150811487575371842625967211 226217231363057763938950817)
  ·
    refine ⟨169662923522293322954213113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226217231363057763938950817 169662923522293322954213113)
    ·
      refine ⟨127247192641719992215659835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169662923522293322954213113 127247192641719992215659835)
      ·
        refine ⟨190870788962579988323489753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127247192641719992215659835 190870788962579988323489753)
        ·
          refine ⟨143153091721934991242617315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190870788962579988323489753 143153091721934991242617315)
          ·
            refine ⟨214729637582902486863925973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143153091721934991242617315 214729637582902486863925973)
            ·
              refine ⟨5032725880849277035873265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 214729637582902486863925973 5032725880849277035873265)
              ·
                refine ⟨3774544410636957776904949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5032725880849277035873265 3774544410636957776904949)
                ·
                  refine ⟨353863538497214791584839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3774544410636957776904949 353863538497214791584839)
                  ·
                    rfl

theorem cell23_6202321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 7, 2, 5].length) (baseStart_6202321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6202321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6202321 prefixEnd_6202321 := by exact prefixLift 6202321
  have htrace : WordTrace (prefixWord ++ tailWord_6202321) baseStart_6202321 baseEnd_6202321 := by
    simpa [prefixWord, tailWord_6202321, baseEnd_6202321] using wordTrace_append hprefix tailTrace_6202321
  have hstable : (prefixWord ++ tailWord_6202321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6202321).length < 2 ^ (prefixWord ++ tailWord_6202321).sum := by decide
  have hdescent : baseEnd_6202321 < baseStart_6202321 := by decide
  rcases family_descends (prefixWord ++ tailWord_6202321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6202377 : List Nat := [1, 2, 1, 1, 3, 1, 1, 5, 8]
def baseStart_6202377 : Nat := 118140960795 + 6202377 * 2 ^ 59
def prefixEnd_6202377 : Nat := 4983230072969 + 3 ^ 40 * 6202377 * 2
def baseEnd_6202377 : Nat := 353866733487953878351477

theorem tailTrace_6202377 : CollatzResearch.WordTrace tailWord_6202377 prefixEnd_6202377 353866733487953878351477 := by
  unfold tailWord_6202377
  simp only [CollatzResearch.WordTrace]
  refine ⟨226219273850854885502989385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150812849233903257001992923 226219273850854885502989385)
  ·
    refine ⟨169664455388141164127242039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226219273850854885502989385 169664455388141164127242039)
    ·
      refine ⟨254496683082211746190863059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169664455388141164127242039 254496683082211746190863059)
      ·
        refine ⟨381745024623317619286294589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254496683082211746190863059 381745024623317619286294589)
        ·
          refine ⟨143154384233744107232360471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 381745024623317619286294589 143154384233744107232360471)
          ·
            refine ⟨214731576350616160848540707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143154384233744107232360471 214731576350616160848540707)
            ·
              refine ⟨322097364525924241272811061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214731576350616160848540707 322097364525924241272811061)
              ·
                refine ⟨30196627924305397619326037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 322097364525924241272811061 30196627924305397619326037)
                ·
                  refine ⟨353866733487953878351477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30196627924305397619326037 353866733487953878351477)
                  ·
                    rfl

theorem cell23_6202377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 5, 8].length) (baseStart_6202377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6202377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6202377 prefixEnd_6202377 := by exact prefixLift 6202377
  have htrace : WordTrace (prefixWord ++ tailWord_6202377) baseStart_6202377 baseEnd_6202377 := by
    simpa [prefixWord, tailWord_6202377, baseEnd_6202377] using wordTrace_append hprefix tailTrace_6202377
  have hstable : (prefixWord ++ tailWord_6202377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6202377).length < 2 ^ (prefixWord ++ tailWord_6202377).sum := by decide
  have hdescent : baseEnd_6202377 < baseStart_6202377 := by decide
  rcases family_descends (prefixWord ++ tailWord_6202377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6202394 : List Nat := [3, 1, 1, 3, 1, 2, 1, 5, 6]
def baseStart_6202394 : Nat := 118140960795 + 6202394 * 2 ^ 59
def prefixEnd_6202394 : Nat := 4983230072969 + 3 ^ 40 * 6202394 * 2
def baseEnd_6202394 : Nat := 353867703395856815405635

theorem tailTrace_6202394 : CollatzResearch.WordTrace tailWord_6202394 prefixEnd_6202394 353867703395856815405635 := by
  unfold tailWord_6202394
  simp only [CollatzResearch.WordTrace]
  refine ⟨56554973472948324351589559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150813262594528864937572157 56554973472948324351589559)
  ·
    refine ⟨84832460209422486527384339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56554973472948324351589559 84832460209422486527384339)
    ·
      refine ⟨127248690314133729791076509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84832460209422486527384339 127248690314133729791076509)
      ·
        refine ⟨47718258867800148671653691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127248690314133729791076509 47718258867800148671653691)
        ·
          refine ⟨71577388301700223007480537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47718258867800148671653691 71577388301700223007480537)
          ·
            refine ⟨53683041226275167255610403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71577388301700223007480537 53683041226275167255610403)
            ·
              refine ⟨80524561839412750883415605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53683041226275167255610403 80524561839412750883415605)
              ·
                refine ⟨7549177672444945395320213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 80524561839412750883415605 7549177672444945395320213)
                ·
                  refine ⟨353867703395856815405635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7549177672444945395320213 353867703395856815405635)
                  ·
                    rfl

theorem cell23_6202394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 5, 6].length) (baseStart_6202394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6202394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6202394 prefixEnd_6202394 := by exact prefixLift 6202394
  have htrace : WordTrace (prefixWord ++ tailWord_6202394) baseStart_6202394 baseEnd_6202394 := by
    simpa [prefixWord, tailWord_6202394, baseEnd_6202394] using wordTrace_append hprefix tailTrace_6202394
  have hstable : (prefixWord ++ tailWord_6202394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6202394).length < 2 ^ (prefixWord ++ tailWord_6202394).sum := by decide
  have hdescent : baseEnd_6202394 < baseStart_6202394 := by decide
  rcases family_descends (prefixWord ++ tailWord_6202394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6202421 : List Nat := [1, 3, 3, 1, 1, 1, 1, 1, 7, 1, 3]
def baseStart_6202421 : Nat := 118140960795 + 6202421 * 2 ^ 59
def prefixEnd_6202421 : Nat := 4983230072969 + 3 ^ 40 * 6202421 * 2
def baseEnd_6202421 : Nat := 3184823194540382733013091

theorem tailTrace_6202421 : CollatzResearch.WordTrace tailWord_6202421 prefixEnd_6202421 3184823194540382733013091 := by
  unfold tailWord_6202421
  simp only [CollatzResearch.WordTrace]
  refine ⟨226220878662695481017591117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150813919108463654011727411 226220878662695481017591117)
  ·
    refine ⟨84832829498510805381596669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226220878662695481017591117 84832829498510805381596669)
    ·
      refine ⟨31812311061941552018098751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84832829498510805381596669 31812311061941552018098751)
      ·
        refine ⟨47718466592912328027148127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31812311061941552018098751 47718466592912328027148127)
        ·
          refine ⟨71577699889368492040722191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47718466592912328027148127 71577699889368492040722191)
          ·
            refine ⟨107366549834052738061083287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71577699889368492040722191 107366549834052738061083287)
            ·
              refine ⟨161049824751079107091624931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107366549834052738061083287 161049824751079107091624931)
              ·
                refine ⟨241574737126618660637437397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 161049824751079107091624931 241574737126618660637437397)
                ·
                  refine ⟨5661907901405124858689939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 241574737126618660637437397 5661907901405124858689939)
                  ·
                    refine ⟨8492861852107687288034909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5661907901405124858689939 8492861852107687288034909)
                    ·
                      refine ⟨3184823194540382733013091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8492861852107687288034909 3184823194540382733013091)
                      ·
                        rfl

theorem cell23_6202421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 7, 1, 3].length) (baseStart_6202421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6202421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6202421 prefixEnd_6202421 := by exact prefixLift 6202421
  have htrace : WordTrace (prefixWord ++ tailWord_6202421) baseStart_6202421 baseEnd_6202421 := by
    simpa [prefixWord, tailWord_6202421, baseEnd_6202421] using wordTrace_append hprefix tailTrace_6202421
  have hstable : (prefixWord ++ tailWord_6202421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6202421).length < 2 ^ (prefixWord ++ tailWord_6202421).sum := by decide
  have hdescent : baseEnd_6202421 < baseStart_6202421 := by decide
  rcases family_descends (prefixWord ++ tailWord_6202421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6202431 : List Nat := [1, 1, 2, 2, 3, 1, 1, 3, 4, 3, 2]
def baseStart_6202431 : Nat := 118140960795 + 6202431 * 2 ^ 59
def prefixEnd_6202431 : Nat := 4983230072969 + 3 ^ 40 * 6202431 * 2
def baseEnd_6202431 : Nat := 3184828329346927693888045

theorem tailTrace_6202431 : CollatzResearch.WordTrace tailWord_6202431 prefixEnd_6202431 3184828329346927693888045 := by
  unfold tailWord_6202431
  simp only [CollatzResearch.WordTrace]
  refine ⟨226221243392659252725455147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150814162261772835150303431 226221243392659252725455147)
  ·
    refine ⟨339331865088988879088182721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226221243392659252725455147 339331865088988879088182721)
    ·
      refine ⟨254498898816741659316137041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 339331865088988879088182721 254498898816741659316137041)
      ·
        refine ⟨190874174112556244487102781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 254498898816741659316137041 190874174112556244487102781)
        ·
          refine ⟨71577815292208591682663543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 190874174112556244487102781 71577815292208591682663543)
          ·
            refine ⟨107366722938312887523995315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71577815292208591682663543 107366722938312887523995315)
            ·
              refine ⟨161050084407469331285992973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107366722938312887523995315 161050084407469331285992973)
              ·
                refine ⟨60393781652800999232247365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 161050084407469331285992973 60393781652800999232247365)
                ·
                  refine ⟨11323834059900187356046381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60393781652800999232247365 11323834059900187356046381)
                  ·
                    refine ⟨4246437772462570258517393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11323834059900187356046381 4246437772462570258517393)
                    ·
                      refine ⟨3184828329346927693888045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4246437772462570258517393 3184828329346927693888045)
                      ·
                        rfl

theorem cell23_6202431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 4, 3, 2].length) (baseStart_6202431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6202431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6202431 prefixEnd_6202431 := by exact prefixLift 6202431
  have htrace : WordTrace (prefixWord ++ tailWord_6202431) baseStart_6202431 baseEnd_6202431 := by
    simpa [prefixWord, tailWord_6202431, baseEnd_6202431] using wordTrace_append hprefix tailTrace_6202431
  have hstable : (prefixWord ++ tailWord_6202431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6202431).length < 2 ^ (prefixWord ++ tailWord_6202431).sum := by decide
  have hdescent : baseEnd_6202431 < baseStart_6202431 := by decide
  rcases family_descends (prefixWord ++ tailWord_6202431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6202464 : List Nat := [2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 5]
def baseStart_6202464 : Nat := 118140960795 + 6202464 * 2 ^ 59
def prefixEnd_6202464 : Nat := 4983230072969 + 3 ^ 40 * 6202464 * 2
def baseEnd_6202464 : Nat := 3184845274208526064775393

theorem tailTrace_6202464 : CollatzResearch.WordTrace tailWord_6202464 prefixEnd_6202464 3184845274208526064775393 := by
  unfold tailWord_6202464
  simp only [CollatzResearch.WordTrace]
  refine ⟨113111223500769849680703223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150814964667693132907604297 113111223500769849680703223)
  ·
    refine ⟨169666835251154774521054835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113111223500769849680703223 169666835251154774521054835)
    ·
      refine ⟨254500252876732161781582253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169666835251154774521054835 254500252876732161781582253)
      ·
        refine ⟨95437594828774560668093345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 254500252876732161781582253 95437594828774560668093345)
        ·
          refine ⟨71578196121580920501070009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95437594828774560668093345 71578196121580920501070009)
          ·
            refine ⟨53683647091185690375802507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71578196121580920501070009 53683647091185690375802507)
            ·
              refine ⟨80525470636778535563703761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53683647091185690375802507 80525470636778535563703761)
              ·
                refine ⟨60394102977583901672777821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80525470636778535563703761 60394102977583901672777821)
                ·
                  refine ⟨22647788616593963127291683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60394102977583901672777821 22647788616593963127291683)
                  ·
                    refine ⟨33971682924890944690937525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22647788616593963127291683 33971682924890944690937525)
                    ·
                      refine ⟨3184845274208526064775393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33971682924890944690937525 3184845274208526064775393)
                      ·
                        rfl

theorem cell23_6202464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 5].length) (baseStart_6202464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6202464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6202464 prefixEnd_6202464 := by exact prefixLift 6202464
  have htrace : WordTrace (prefixWord ++ tailWord_6202464) baseStart_6202464 baseEnd_6202464 := by
    simpa [prefixWord, tailWord_6202464, baseEnd_6202464] using wordTrace_append hprefix tailTrace_6202464
  have hstable : (prefixWord ++ tailWord_6202464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6202464).length < 2 ^ (prefixWord ++ tailWord_6202464).sum := by decide
  have hdescent : baseEnd_6202464 < baseStart_6202464 := by decide
  rcases family_descends (prefixWord ++ tailWord_6202464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6202471 : List Nat := [1, 1, 5, 1, 1, 3, 1, 2, 4, 4]
def baseStart_6202471 : Nat := 118140960795 + 6202471 * 2 ^ 59
def prefixEnd_6202471 : Nat := 4983230072969 + 3 ^ 40 * 6202471 * 2
def baseEnd_6202471 : Nat := 1061616289524369179129287

theorem tailTrace_6202471 : CollatzResearch.WordTrace tailWord_6202471 prefixEnd_6202471 1061616289524369179129287 := by
  unfold tailWord_6202471
  simp only [CollatzResearch.WordTrace]
  refine ⟨226222702312514339556911267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150815134875009559704607511 226222702312514339556911267)
  ·
    refine ⟨339334053468771509335366901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226222702312514339556911267 339334053468771509335366901)
    ·
      refine ⟨31812567512697329000190647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 339334053468771509335366901 31812567512697329000190647)
      ·
        refine ⟨47718851269045993500285971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31812567512697329000190647 47718851269045993500285971)
        ·
          refine ⟨71578276903568990250428957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47718851269045993500285971 71578276903568990250428957)
          ·
            refine ⟨26841853838838371343910859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71578276903568990250428957 26841853838838371343910859)
            ·
              refine ⟨40262780758257557015866289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26841853838838371343910859 40262780758257557015866289)
              ·
                refine ⟨30197085568693167761899717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40262780758257557015866289 30197085568693167761899717)
                ·
                  refine ⟨5661953544129968955356197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30197085568693167761899717 5661953544129968955356197)
                  ·
                    refine ⟨1061616289524369179129287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5661953544129968955356197 1061616289524369179129287)
                    ·
                      rfl

theorem cell23_6202471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 2, 4, 4].length) (baseStart_6202471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6202471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6202471 prefixEnd_6202471 := by exact prefixLift 6202471
  have htrace : WordTrace (prefixWord ++ tailWord_6202471) baseStart_6202471 baseEnd_6202471 := by
    simpa [prefixWord, tailWord_6202471, baseEnd_6202471] using wordTrace_append hprefix tailTrace_6202471
  have hstable : (prefixWord ++ tailWord_6202471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6202471).length < 2 ^ (prefixWord ++ tailWord_6202471).sum := by decide
  have hdescent : baseEnd_6202471 < baseStart_6202471 := by decide
  rcases family_descends (prefixWord ++ tailWord_6202471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6202478 : List Nat := [4, 1, 2, 2, 1, 2, 2, 3, 1, 1, 4]
def baseStart_6202478 : Nat := 118140960795 + 6202478 * 2 ^ 59
def prefixEnd_6202478 : Nat := 4983230072969 + 3 ^ 40 * 6202478 * 2
def baseEnd_6202478 : Nat := 3184852462937689010000329

theorem tailTrace_6202478 : CollatzResearch.WordTrace tailWord_6202478 prefixEnd_6202478 3184852462937689010000329 := by
  unfold tailWord_6202478
  simp only [CollatzResearch.WordTrace]
  refine ⟨28277869702936122469052011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150815305082325986501610725 28277869702936122469052011)
  ·
    refine ⟨42416804554404183703578017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28277869702936122469052011 42416804554404183703578017)
    ·
      refine ⟨31812603415803137777683513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42416804554404183703578017 31812603415803137777683513)
      ·
        refine ⟨23859452561852353333262635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31812603415803137777683513 23859452561852353333262635)
        ·
          refine ⟨35789178842778529999893953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23859452561852353333262635 35789178842778529999893953)
          ·
            refine ⟨26841884132083897499920465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35789178842778529999893953 26841884132083897499920465)
            ·
              refine ⟨20131413099062923124940349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26841884132083897499920465 20131413099062923124940349)
              ·
                refine ⟨7549279912148596171852631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20131413099062923124940349 7549279912148596171852631)
                ·
                  refine ⟨11323919868222894257778947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7549279912148596171852631 11323919868222894257778947)
                  ·
                    refine ⟨16985879802334341386668421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11323919868222894257778947 16985879802334341386668421)
                    ·
                      refine ⟨3184852462937689010000329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16985879802334341386668421 3184852462937689010000329)
                      ·
                        rfl

theorem cell23_6202478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_6202478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6202478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6202478 prefixEnd_6202478 := by exact prefixLift 6202478
  have htrace : WordTrace (prefixWord ++ tailWord_6202478) baseStart_6202478 baseEnd_6202478 := by
    simpa [prefixWord, tailWord_6202478, baseEnd_6202478] using wordTrace_append hprefix tailTrace_6202478
  have hstable : (prefixWord ++ tailWord_6202478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6202478).length < 2 ^ (prefixWord ++ tailWord_6202478).sum := by decide
  have hdescent : baseEnd_6202478 < baseStart_6202478 := by decide
  rcases family_descends (prefixWord ++ tailWord_6202478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6202501 : List Nat := [1, 3, 1, 1, 6, 1, 2, 8]
def baseStart_6202501 : Nat := 118140960795 + 6202501 * 2 ^ 59
def prefixEnd_6202501 : Nat := 4983230072969 + 3 ^ 40 * 6202501 * 2
def baseEnd_6202501 : Nat := 117957936036768237778249

theorem tailTrace_6202501 : CollatzResearch.WordTrace tailWord_6202501 prefixEnd_6202501 117957936036768237778249 := by
  unfold tailWord_6202501
  simp only [CollatzResearch.WordTrace]
  refine ⟨226223796502405654680503357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150815864334937103120335571 226223796502405654680503357)
  ·
    refine ⟨84833923688402120505188759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226223796502405654680503357 84833923688402120505188759)
    ·
      refine ⟨127250885532603180757783139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84833923688402120505188759 127250885532603180757783139)
      ·
        refine ⟨190876328298904771136674709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127250885532603180757783139 190876328298904771136674709)
        ·
          refine ⟨8947327889011161147031627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 190876328298904771136674709 8947327889011161147031627)
          ·
            refine ⟨13420991833516741720547441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8947327889011161147031627 13420991833516741720547441)
            ·
              refine ⟨10065743875137556290410581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13420991833516741720547441 10065743875137556290410581)
              ·
                refine ⟨117957936036768237778249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10065743875137556290410581 117957936036768237778249)
                ·
                  rfl

theorem cell23_6202501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 8].length) (baseStart_6202501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6202501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6202501 prefixEnd_6202501 := by exact prefixLift 6202501
  have htrace : WordTrace (prefixWord ++ tailWord_6202501) baseStart_6202501 baseEnd_6202501 := by
    simpa [prefixWord, tailWord_6202501, baseEnd_6202501] using wordTrace_append hprefix tailTrace_6202501
  have hstable : (prefixWord ++ tailWord_6202501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6202501).length < 2 ^ (prefixWord ++ tailWord_6202501).sum := by decide
  have hdescent : baseEnd_6202501 < baseStart_6202501 := by decide
  rcases family_descends (prefixWord ++ tailWord_6202501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6202505 : List Nat := [1, 2, 1, 1, 4, 5, 2, 1, 2, 4]
def baseStart_6202505 : Nat := 118140960795 + 6202505 * 2 ^ 59
def prefixEnd_6202505 : Nat := 4983230072969 + 3 ^ 40 * 6202505 * 2
def baseEnd_6202505 : Nat := 1061622108971786801454235

theorem tailTrace_6202505 : CollatzResearch.WordTrace tailWord_6202505 prefixEnd_6202505 1061622108971786801454235 := by
  unfold tailWord_6202505
  simp only [CollatzResearch.WordTrace]
  refine ⟨226223942394391163363648969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150815961596260775575765979 226223942394391163363648969)
  ·
    refine ⟨169667956795793372522736727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226223942394391163363648969 169667956795793372522736727)
    ·
      refine ⟨254501935193690058784105091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169667956795793372522736727 254501935193690058784105091)
      ·
        refine ⟨381752902790535088176157637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254501935193690058784105091 381752902790535088176157637)
        ·
          refine ⟨71578669273225329033029557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 381752902790535088176157637 71578669273225329033029557)
          ·
            refine ⟨6710500244364874596846521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 71578669273225329033029557 6710500244364874596846521)
            ·
              refine ⟨5032875183273655947634891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6710500244364874596846521 5032875183273655947634891)
              ·
                refine ⟨7549312774910483921452337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5032875183273655947634891 7549312774910483921452337)
                ·
                  refine ⟨5661984581182862941089253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7549312774910483921452337 5661984581182862941089253)
                  ·
                    refine ⟨1061622108971786801454235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5661984581182862941089253 1061622108971786801454235)
                    ·
                      rfl

theorem cell23_6202505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 2, 1, 2, 4].length) (baseStart_6202505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6202505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6202505 prefixEnd_6202505 := by exact prefixLift 6202505
  have htrace : WordTrace (prefixWord ++ tailWord_6202505) baseStart_6202505 baseEnd_6202505 := by
    simpa [prefixWord, tailWord_6202505, baseEnd_6202505] using wordTrace_append hprefix tailTrace_6202505
  have hstable : (prefixWord ++ tailWord_6202505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6202505).length < 2 ^ (prefixWord ++ tailWord_6202505).sum := by decide
  have hdescent : baseEnd_6202505 < baseStart_6202505 := by decide
  rcases family_descends (prefixWord ++ tailWord_6202505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6202544 : List Nat := [2, 1, 1, 1, 2, 1, 2, 3, 4, 6]
def baseStart_6202544 : Nat := 118140960795 + 6202544 * 2 ^ 59
def prefixEnd_6202544 : Nat := 4983230072969 + 3 ^ 40 * 6202544 * 2
def baseEnd_6202544 : Nat := 1061628784220295250591675

theorem tailTrace_6202544 : CollatzResearch.WordTrace tailWord_6202544 prefixEnd_6202544 1061628784220295250591675 := by
  unfold tailWord_6202544
  simp only [CollatzResearch.WordTrace]
  refine ⟨113112682420624936512159343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150816909894166582016212457 113112682420624936512159343)
  ·
    refine ⟨169669023630937404768239015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113112682420624936512159343 169669023630937404768239015)
    ·
      refine ⟨254503535446406107152358523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169669023630937404768239015 254503535446406107152358523)
      ·
        refine ⟨381755303169609160728537785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254503535446406107152358523 381755303169609160728537785)
        ·
          refine ⟨286316477377206870546403339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 381755303169609160728537785 286316477377206870546403339)
          ·
            refine ⟨429474716065810305819605009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286316477377206870546403339 429474716065810305819605009)
            ·
              refine ⟨322106037049357729364703757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 429474716065810305819605009 322106037049357729364703757)
              ·
                refine ⟨120789763893509148511763909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 322106037049357729364703757 120789763893509148511763909)
                ·
                  refine ⟨22648080730032965345955733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 120789763893509148511763909 22648080730032965345955733)
                  ·
                    refine ⟨1061628784220295250591675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22648080730032965345955733 1061628784220295250591675)
                    ·
                      rfl

theorem cell23_6202544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 4, 6].length) (baseStart_6202544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6202544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6202544 prefixEnd_6202544 := by exact prefixLift 6202544
  have htrace : WordTrace (prefixWord ++ tailWord_6202544) baseStart_6202544 baseEnd_6202544 := by
    simpa [prefixWord, tailWord_6202544, baseEnd_6202544] using wordTrace_append hprefix tailTrace_6202544
  have hstable : (prefixWord ++ tailWord_6202544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6202544).length < 2 ^ (prefixWord ++ tailWord_6202544).sum := by decide
  have hdescent : baseEnd_6202544 < baseStart_6202544 := by decide
  rcases family_descends (prefixWord ++ tailWord_6202544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6202545 : List Nat := [1, 2, 2, 5, 1, 1, 1, 4, 2, 1, 3]
def baseStart_6202545 : Nat := 118140960795 + 6202545 * 2 ^ 59
def prefixEnd_6202545 : Nat := 4983230072969 + 3 ^ 40 * 6202545 * 2
def baseEnd_6202545 : Nat := 3184886866141540247862521

theorem tailTrace_6202545 : CollatzResearch.WordTrace tailWord_6202545 prefixEnd_6202545 3184886866141540247862521 := by
  unfold tailWord_6202545
  simp only [CollatzResearch.WordTrace]
  refine ⟨226225401314246250195105089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150816934209497500130070059 226225401314246250195105089)
  ·
    refine ⟨169669050985684687646328817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226225401314246250195105089 169669050985684687646328817)
    ·
      refine ⟨127251788239263515734746613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169669050985684687646328817 127251788239263515734746613)
      ·
        refine ⟨11929855147430954600132495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 127251788239263515734746613 11929855147430954600132495)
        ·
          refine ⟨17894782721146431900198743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11929855147430954600132495 17894782721146431900198743)
          ·
            refine ⟨26842174081719647850298115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17894782721146431900198743 26842174081719647850298115)
            ·
              refine ⟨40263261122579471775447173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26842174081719647850298115 40263261122579471775447173)
              ·
                refine ⟨7549361460483650957896345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40263261122579471775447173 7549361460483650957896345)
                ·
                  refine ⟨5662021095362738218422259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7549361460483650957896345 5662021095362738218422259)
                  ·
                    refine ⟨8493031643044107327633389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5662021095362738218422259 8493031643044107327633389)
                    ·
                      refine ⟨3184886866141540247862521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8493031643044107327633389 3184886866141540247862521)
                      ·
                        rfl

theorem cell23_6202545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_6202545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6202545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6202545 prefixEnd_6202545 := by exact prefixLift 6202545
  have htrace : WordTrace (prefixWord ++ tailWord_6202545) baseStart_6202545 baseEnd_6202545 := by
    simpa [prefixWord, tailWord_6202545, baseEnd_6202545] using wordTrace_append hprefix tailTrace_6202545
  have hstable : (prefixWord ++ tailWord_6202545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6202545).length < 2 ^ (prefixWord ++ tailWord_6202545).sum := by decide
  have hdescent : baseEnd_6202545 < baseStart_6202545 := by decide
  rcases family_descends (prefixWord ++ tailWord_6202545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6202568 : List Nat := [2, 1, 3, 1, 2, 1, 3, 3, 1, 4, 2]
def baseStart_6202568 : Nat := 118140960795 + 6202568 * 2 ^ 59
def prefixEnd_6202568 : Nat := 4983230072969 + 3 ^ 40 * 6202568 * 2
def baseEnd_6202568 : Nat := 3184898676196593657874915

theorem tailTrace_6202568 : CollatzResearch.WordTrace tailWord_6202568 prefixEnd_6202568 3184898676196593657874915 := by
  unfold tailWord_6202568
  simp only [CollatzResearch.WordTrace]
  refine ⟨113113120096581462561596179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150817493462108616748794905 113113120096581462561596179)
  ·
    refine ⟨169669680144872193842394269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113113120096581462561596179 169669680144872193842394269)
    ·
      refine ⟨63626130054327072690897851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169669680144872193842394269 63626130054327072690897851)
      ·
        refine ⟨95439195081490609036346777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63626130054327072690897851 95439195081490609036346777)
        ·
          refine ⟨71579396311117956777260083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95439195081490609036346777 71579396311117956777260083)
          ·
            refine ⟨107369094466676935165890125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71579396311117956777260083 107369094466676935165890125)
            ·
              refine ⟨40263410425003850687208797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107369094466676935165890125 40263410425003850687208797)
              ·
                refine ⟨15098778909376444007703299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40263410425003850687208797 15098778909376444007703299)
                ·
                  refine ⟨22648168364064666011554949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15098778909376444007703299 22648168364064666011554949)
                  ·
                    refine ⟨4246531568262124877166553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22648168364064666011554949 4246531568262124877166553)
                    ·
                      refine ⟨3184898676196593657874915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4246531568262124877166553 3184898676196593657874915)
                      ·
                        rfl

theorem cell23_6202568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 3, 1, 4, 2].length) (baseStart_6202568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6202568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6202568 prefixEnd_6202568 := by exact prefixLift 6202568
  have htrace : WordTrace (prefixWord ++ tailWord_6202568) baseStart_6202568 baseEnd_6202568 := by
    simpa [prefixWord, tailWord_6202568, baseEnd_6202568] using wordTrace_append hprefix tailTrace_6202568
  have hstable : (prefixWord ++ tailWord_6202568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6202568).length < 2 ^ (prefixWord ++ tailWord_6202568).sum := by decide
  have hdescent : baseEnd_6202568 < baseStart_6202568 := by decide
  rcases family_descends (prefixWord ++ tailWord_6202568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6202602 : List Nat := [3, 1, 3, 1, 1, 3, 3, 2, 2, 2, 2]
def baseStart_6202602 : Nat := 118140960795 + 6202602 * 2 ^ 59
def prefixEnd_6202602 : Nat := 4983230072969 + 3 ^ 40 * 6202602 * 2
def baseEnd_6202602 : Nat := 3184916134538846524849759

theorem tailTrace_6202602 : CollatzResearch.WordTrace tailWord_6202602 prefixEnd_6202602 3184916134538846524849759 := by
  unfold tailWord_6202602
  simp only [CollatzResearch.WordTrace]
  refine ⟨56556870068759937232482515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150818320183359832619953373 56556870068759937232482515)
  ·
    refine ⟨84835305103139905848723773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56556870068759937232482515 84835305103139905848723773)
    ·
      refine ⟨31813239413677464693271415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84835305103139905848723773 31813239413677464693271415)
      ·
        refine ⟨47719859120516197039907123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31813239413677464693271415 47719859120516197039907123)
        ·
          refine ⟨71579788680774295559860685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47719859120516197039907123 71579788680774295559860685)
          ·
            refine ⟨26842420755290360834947757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71579788680774295559860685 26842420755290360834947757)
            ·
              refine ⟨10065907783233885313105409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26842420755290360834947757 10065907783233885313105409)
              ·
                refine ⟨7549430837425413984829057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10065907783233885313105409 7549430837425413984829057)
                ·
                  refine ⟨5662073128069060488621793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7549430837425413984829057 5662073128069060488621793)
                  ·
                    refine ⟨4246554846051795366466345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5662073128069060488621793 4246554846051795366466345)
                    ·
                      refine ⟨3184916134538846524849759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4246554846051795366466345 3184916134538846524849759)
                      ·
                        rfl

theorem cell23_6202602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 2, 2, 2, 2].length) (baseStart_6202602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6202602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6202602 prefixEnd_6202602 := by exact prefixLift 6202602
  have htrace : WordTrace (prefixWord ++ tailWord_6202602) baseStart_6202602 baseEnd_6202602 := by
    simpa [prefixWord, tailWord_6202602, baseEnd_6202602] using wordTrace_append hprefix tailTrace_6202602
  have hstable : (prefixWord ++ tailWord_6202602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6202602).length < 2 ^ (prefixWord ++ tailWord_6202602).sum := by decide
  have hdescent : baseEnd_6202602 < baseStart_6202602 := by decide
  rcases family_descends (prefixWord ++ tailWord_6202602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6202641 : List Nat := [1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 4]
def baseStart_6202641 : Nat := 118140960795 + 6202641 * 2 ^ 59
def prefixEnd_6202641 : Nat := 4983230072969 + 3 ^ 40 * 6202641 * 2
def baseEnd_6202641 : Nat := 3184936160284371872262079

theorem tailTrace_6202641 : CollatzResearch.WordTrace tailWord_6202641 prefixEnd_6202641 3184936160284371872262079 := by
  unfold tailWord_6202641
  simp only [CollatzResearch.WordTrace]
  refine ⟨226228902721898458590599777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150819268481265639060399851 226228902721898458590599777)
  ·
    refine ⟨169671677041423843942949833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226228902721898458590599777 169671677041423843942949833)
    ·
      refine ⟨127253757781067882957212375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169671677041423843942949833 127253757781067882957212375)
      ·
        refine ⟨190880636671601824435818563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127253757781067882957212375 190880636671601824435818563)
        ·
          refine ⟨286320955007402736653727845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190880636671601824435818563 286320955007402736653727845)
          ·
            refine ⟨53685179063888013122573971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 286320955007402736653727845 53685179063888013122573971)
            ·
              refine ⟨80527768595832019683860957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53685179063888013122573971 80527768595832019683860957)
              ·
                refine ⟨30197913223437007381447859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80527768595832019683860957 30197913223437007381447859)
                ·
                  refine ⟨45296869835155511072171789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30197913223437007381447859 45296869835155511072171789)
                  ·
                    refine ⟨16986326188183316652064421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45296869835155511072171789 16986326188183316652064421)
                    ·
                      refine ⟨3184936160284371872262079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16986326188183316652064421 3184936160284371872262079)
                      ·
                        rfl

theorem cell23_6202641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 4].length) (baseStart_6202641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6202641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6202641 prefixEnd_6202641 := by exact prefixLift 6202641
  have htrace : WordTrace (prefixWord ++ tailWord_6202641) baseStart_6202641 baseEnd_6202641 := by
    simpa [prefixWord, tailWord_6202641, baseEnd_6202641] using wordTrace_append hprefix tailTrace_6202641
  have hstable : (prefixWord ++ tailWord_6202641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6202641).length < 2 ^ (prefixWord ++ tailWord_6202641).sum := by decide
  have hdescent : baseEnd_6202641 < baseStart_6202641 := by decide
  rcases family_descends (prefixWord ++ tailWord_6202641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6202692 : List Nat := [2, 3, 4, 1, 1, 2, 2, 1, 2, 1, 4]
def baseStart_6202692 : Nat := 118140960795 + 6202692 * 2 ^ 59
def prefixEnd_6202692 : Nat := 4983230072969 + 3 ^ 40 * 6202692 * 2
def baseEnd_6202692 : Nat := 3184962347797751172724345

theorem tailTrace_6202692 : CollatzResearch.WordTrace tailWord_6202692 prefixEnd_6202692 3184962347797751172724345 := by
  unfold tailWord_6202692
  simp only [CollatzResearch.WordTrace]
  refine ⟨113115381422356847150353165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150820508563142462867137553 113115381422356847150353165)
  ·
    refine ⟨42418268033383817681382437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113115381422356847150353165 42418268033383817681382437)
    ·
      refine ⟨7953425256259465815259207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42418268033383817681382437 7953425256259465815259207)
      ·
        refine ⟨11930137884389198722888811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7953425256259465815259207 11930137884389198722888811)
        ·
          refine ⟨17895206826583798084333217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11930137884389198722888811 17895206826583798084333217)
          ·
            refine ⟨13421405119937848563249913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17895206826583798084333217 13421405119937848563249913)
            ·
              refine ⟨10066053839953386422437435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13421405119937848563249913 10066053839953386422437435)
              ·
                refine ⟨15099080759930079633656153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10066053839953386422437435 15099080759930079633656153)
                ·
                  refine ⟨11324310569947559725242115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15099080759930079633656153 11324310569947559725242115)
                  ·
                    refine ⟨16986465854921339587863173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11324310569947559725242115 16986465854921339587863173)
                    ·
                      refine ⟨3184962347797751172724345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16986465854921339587863173 3184962347797751172724345)
                      ·
                        rfl

theorem cell23_6202692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_6202692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6202692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6202692 prefixEnd_6202692 := by exact prefixLift 6202692
  have htrace : WordTrace (prefixWord ++ tailWord_6202692) baseStart_6202692 baseEnd_6202692 := by
    simpa [prefixWord, tailWord_6202692, baseEnd_6202692] using wordTrace_append hprefix tailTrace_6202692
  have hstable : (prefixWord ++ tailWord_6202692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6202692).length < 2 ^ (prefixWord ++ tailWord_6202692).sum := by decide
  have hdescent : baseEnd_6202692 < baseStart_6202692 := by decide
  rcases family_descends (prefixWord ++ tailWord_6202692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6202695 : List Nat := [1, 1, 4, 1, 2, 4, 2, 1, 2, 2, 3]
def baseStart_6202695 : Nat := 118140960795 + 6202695 * 2 ^ 59
def prefixEnd_6202695 : Nat := 4983230072969 + 3 ^ 40 * 6202695 * 2
def baseEnd_6202695 : Nat := 3184963888239714660986831

theorem tailTrace_6202695 : CollatzResearch.WordTrace tailWord_6202695 prefixEnd_6202695 3184963888239714660986831 := by
  unfold tailWord_6202695
  simp only [CollatzResearch.WordTrace]
  refine ⟨226230872263702825813065539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150820581509135217208710359 226230872263702825813065539)
  ·
    refine ⟨339346308395554238719598309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226230872263702825813065539 339346308395554238719598309)
    ·
      refine ⟨63627432824166419759924683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 339346308395554238719598309 63627432824166419759924683)
      ·
        refine ⟨95441149236249629639887025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63627432824166419759924683 95441149236249629639887025)
        ·
          refine ⟨71580861927187222229915269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95441149236249629639887025 71580861927187222229915269)
          ·
            refine ⟨13421411611347604168109113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71580861927187222229915269 13421411611347604168109113)
            ·
              refine ⟨10066058708510703126081835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13421411611347604168109113 10066058708510703126081835)
              ·
                refine ⟨15099088062766054689122753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10066058708510703126081835 15099088062766054689122753)
                ·
                  refine ⟨11324316047074541016842065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15099088062766054689122753 11324316047074541016842065)
                  ·
                    refine ⟨8493237035305905762631549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11324316047074541016842065 8493237035305905762631549)
                    ·
                      refine ⟨3184963888239714660986831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8493237035305905762631549 3184963888239714660986831)
                      ·
                        rfl

theorem cell23_6202695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 1, 2, 2, 3].length) (baseStart_6202695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6202695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6202695 prefixEnd_6202695 := by exact prefixLift 6202695
  have htrace : WordTrace (prefixWord ++ tailWord_6202695) baseStart_6202695 baseEnd_6202695 := by
    simpa [prefixWord, tailWord_6202695, baseEnd_6202695] using wordTrace_append hprefix tailTrace_6202695
  have hstable : (prefixWord ++ tailWord_6202695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6202695).length < 2 ^ (prefixWord ++ tailWord_6202695).sum := by decide
  have hdescent : baseEnd_6202695 < baseStart_6202695 := by decide
  rcases family_descends (prefixWord ++ tailWord_6202695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6202710 : List Nat := [5, 2, 3, 1, 2, 1, 2, 2, 5]
def baseStart_6202710 : Nat := 118140960795 + 6202710 * 2 ^ 59
def prefixEnd_6202710 : Nat := 4983230072969 + 3 ^ 40 * 6202710 * 2
def baseEnd_6202710 : Nat := 353885732272170233588807

theorem tailTrace_6202710 : CollatzResearch.WordTrace tailWord_6202710 prefixEnd_6202710 353885732272170233588807 := by
  unfold tailWord_6202710
  simp only [CollatzResearch.WordTrace]
  refine ⟨14139463709915530210928849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 150820946239098988916574389 14139463709915530210928849)
  ·
    refine ⟨10604597782436647658196637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14139463709915530210928849 10604597782436647658196637)
    ·
      refine ⟨3976724168413742871823739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10604597782436647658196637 3976724168413742871823739)
      ·
        refine ⟨5965086252620614307735609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3976724168413742871823739 5965086252620614307735609)
        ·
          refine ⟨4473814689465460730801707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5965086252620614307735609 4473814689465460730801707)
          ·
            refine ⟨6710722034198191096202561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4473814689465460730801707 6710722034198191096202561)
            ·
              refine ⟨5033041525648643322151921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6710722034198191096202561 5033041525648643322151921)
              ·
                refine ⟨3774781144236482491613941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5033041525648643322151921 3774781144236482491613941)
                ·
                  refine ⟨353885732272170233588807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3774781144236482491613941 353885732272170233588807)
                  ·
                    rfl

theorem cell23_6202710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 2, 2, 5].length) (baseStart_6202710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6202710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6202710 prefixEnd_6202710 := by exact prefixLift 6202710
  have htrace : WordTrace (prefixWord ++ tailWord_6202710) baseStart_6202710 baseEnd_6202710 := by
    simpa [prefixWord, tailWord_6202710, baseEnd_6202710] using wordTrace_append hprefix tailTrace_6202710
  have hstable : (prefixWord ++ tailWord_6202710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6202710).length < 2 ^ (prefixWord ++ tailWord_6202710).sum := by decide
  have hdescent : baseEnd_6202710 < baseStart_6202710 := by decide
  rcases family_descends (prefixWord ++ tailWord_6202710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6202721 : List Nat := [1, 2, 3, 1, 1, 1, 1, 2, 2, 4, 5]
def baseStart_6202721 : Nat := 118140960795 + 6202721 * 2 ^ 59
def prefixEnd_6202721 : Nat := 4983230072969 + 3 ^ 40 * 6202721 * 2
def baseEnd_6202721 : Nat := 3184977238736731559261711

theorem tailTrace_6202721 : CollatzResearch.WordTrace tailWord_6202721 prefixEnd_6202721 3184977238736731559261711 := by
  unfold tailWord_6202721
  simp only [CollatzResearch.WordTrace]
  refine ⟨226231820561608632253512017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150821213707739088169008011 226231820561608632253512017)
  ·
    refine ⟨169673865421206474190134013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226231820561608632253512017 169673865421206474190134013)
    ·
      refine ⟨63627699532952427821300255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169673865421206474190134013 63627699532952427821300255)
      ·
        refine ⟨95441549299428641731950383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63627699532952427821300255 95441549299428641731950383)
        ·
          refine ⟨143162323949142962597925575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95441549299428641731950383 143162323949142962597925575)
          ·
            refine ⟨214743485923714443896888363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143162323949142962597925575 214743485923714443896888363)
            ·
              refine ⟨322115228885571665845332545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214743485923714443896888363 322115228885571665845332545)
              ·
                refine ⟨241586421664178749383999409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 322115228885571665845332545 241586421664178749383999409)
                ·
                  refine ⟨181189816248134062037999557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 241586421664178749383999409 181189816248134062037999557)
                  ·
                    refine ⟨33973090546525136632124917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 181189816248134062037999557 33973090546525136632124917)
                    ·
                      refine ⟨3184977238736731559261711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33973090546525136632124917 3184977238736731559261711)
                      ·
                        rfl

theorem cell23_6202721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 4, 5].length) (baseStart_6202721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6202721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6202721 prefixEnd_6202721 := by exact prefixLift 6202721
  have htrace : WordTrace (prefixWord ++ tailWord_6202721) baseStart_6202721 baseEnd_6202721 := by
    simpa [prefixWord, tailWord_6202721, baseEnd_6202721] using wordTrace_append hprefix tailTrace_6202721
  have hstable : (prefixWord ++ tailWord_6202721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6202721).length < 2 ^ (prefixWord ++ tailWord_6202721).sum := by decide
  have hdescent : baseEnd_6202721 < baseStart_6202721 := by decide
  rcases family_descends (prefixWord ++ tailWord_6202721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6202725 : List Nat := [1, 3, 1, 3, 1, 2, 2, 3, 3, 1, 3]
def baseStart_6202725 : Nat := 118140960795 + 6202725 * 2 ^ 59
def prefixEnd_6202725 : Nat := 4983230072969 + 3 ^ 40 * 6202725 * 2
def baseEnd_6202725 : Nat := 3184979292659349543611693

theorem tailTrace_6202725 : CollatzResearch.WordTrace tailWord_6202725 prefixEnd_6202725 3184979292659349543611693 := by
  unfold tailWord_6202725
  simp only [CollatzResearch.WordTrace]
  refine ⟨226231966453594140936657629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150821310969062760624438419 226231966453594140936657629)
  ·
    refine ⟨84836987420097802851246611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226231966453594140936657629 84836987420097802851246611)
    ·
      refine ⟨127255481130146704276869917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84836987420097802851246611 127255481130146704276869917)
      ·
        refine ⟨47720805423805014103826219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127255481130146704276869917 47720805423805014103826219)
        ·
          refine ⟨71581208135707521155739329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47720805423805014103826219 71581208135707521155739329)
          ·
            refine ⟨53685906101780640866804497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71581208135707521155739329 53685906101780640866804497)
            ·
              refine ⟨40264429576335480650103373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53685906101780640866804497 40264429576335480650103373)
              ·
                refine ⟨15099161091125805243788765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40264429576335480650103373 15099161091125805243788765)
                ·
                  refine ⟨5662185409172176966420787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15099161091125805243788765 5662185409172176966420787)
                  ·
                    refine ⟨8493278113758265449631181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5662185409172176966420787 8493278113758265449631181)
                    ·
                      refine ⟨3184979292659349543611693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8493278113758265449631181 3184979292659349543611693)
                      ·
                        rfl

theorem cell23_6202725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 3, 3, 1, 3].length) (baseStart_6202725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6202725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6202725 prefixEnd_6202725 := by exact prefixLift 6202725
  have htrace : WordTrace (prefixWord ++ tailWord_6202725) baseStart_6202725 baseEnd_6202725 := by
    simpa [prefixWord, tailWord_6202725, baseEnd_6202725] using wordTrace_append hprefix tailTrace_6202725
  have hstable : (prefixWord ++ tailWord_6202725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6202725).length < 2 ^ (prefixWord ++ tailWord_6202725).sum := by decide
  have hdescent : baseEnd_6202725 < baseStart_6202725 := by decide
  rcases family_descends (prefixWord ++ tailWord_6202725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6202731 : List Nat := [1, 1, 1, 1, 2, 2, 2, 1, 1, 7, 4]
def baseStart_6202731 : Nat := 118140960795 + 6202731 * 2 ^ 59
def prefixEnd_6202731 : Nat := 4983230072969 + 3 ^ 40 * 6202731 * 2
def baseEnd_6202731 : Nat := 3184982373543276520136665

theorem tailTrace_6202731 : CollatzResearch.WordTrace tailWord_6202731 prefixEnd_6202731 3184982373543276520136665 := by
  unfold tailWord_6202731
  simp only [CollatzResearch.WordTrace]
  refine ⟨226232185291572403961376047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150821456861048269307584031 226232185291572403961376047)
  ·
    refine ⟨339348277937358605942064071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226232185291572403961376047 339348277937358605942064071)
    ·
      refine ⟨509022416906037908913096107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339348277937358605942064071 509022416906037908913096107)
      ·
        refine ⟨763533625359056863369644161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 509022416906037908913096107 763533625359056863369644161)
        ·
          refine ⟨572650219019292647527233121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 763533625359056863369644161 572650219019292647527233121)
          ·
            refine ⟨429487664264469485645424841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 572650219019292647527233121 429487664264469485645424841)
            ·
              refine ⟨322115748198352114234068631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 429487664264469485645424841 322115748198352114234068631)
              ·
                refine ⟨483173622297528171351102947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 322115748198352114234068631 483173622297528171351102947)
                ·
                  refine ⟨724760433446292257026654421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 483173622297528171351102947 724760433446292257026654421)
                  ·
                    refine ⟨16986572658897474774062213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 724760433446292257026654421 16986572658897474774062213)
                    ·
                      refine ⟨3184982373543276520136665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16986572658897474774062213 3184982373543276520136665)
                      ·
                        rfl

theorem cell23_6202731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 7, 4].length) (baseStart_6202731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6202731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6202731 prefixEnd_6202731 := by exact prefixLift 6202731
  have htrace : WordTrace (prefixWord ++ tailWord_6202731) baseStart_6202731 baseEnd_6202731 := by
    simpa [prefixWord, tailWord_6202731, baseEnd_6202731] using wordTrace_append hprefix tailTrace_6202731
  have hstable : (prefixWord ++ tailWord_6202731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6202731).length < 2 ^ (prefixWord ++ tailWord_6202731).sum := by decide
  have hdescent : baseEnd_6202731 < baseStart_6202731 := by decide
  rcases family_descends (prefixWord ++ tailWord_6202731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6202748 : List Nat := [2, 2, 2, 1, 1, 1, 3, 3, 3, 1, 4]
def baseStart_6202748 : Nat := 118140960795 + 6202748 * 2 ^ 59
def prefixEnd_6202748 : Nat := 4983230072969 + 3 ^ 40 * 6202748 * 2
def baseEnd_6202748 : Nat := 3184991102714402953624087

theorem tailTrace_6202748 : CollatzResearch.WordTrace tailWord_6202748 prefixEnd_6202748 3184991102714402953624087 := by
  unfold tailWord_6202748
  simp only [CollatzResearch.WordTrace]
  refine ⟨113116402666255407932372449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150821870221673877243163265 113116402666255407932372449)
  ·
    refine ⟨84837301999691555949279337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113116402666255407932372449 84837301999691555949279337)
    ·
      refine ⟨63627976499768666961959503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84837301999691555949279337 63627976499768666961959503)
      ·
        refine ⟨95441964749653000442939255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63627976499768666961959503 95441964749653000442939255)
        ·
          refine ⟨143162947124479500664408883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95441964749653000442939255 143162947124479500664408883)
          ·
            refine ⟨214744420686719250996613325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143162947124479500664408883 214744420686719250996613325)
            ·
              refine ⟨80529157757519719123729997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 214744420686719250996613325 80529157757519719123729997)
              ·
                refine ⟨30198434159069894671398749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80529157757519719123729997 30198434159069894671398749)
                ·
                  refine ⟨11324412809651210501774531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30198434159069894671398749 11324412809651210501774531)
                  ·
                    refine ⟨16986619214476815752661797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11324412809651210501774531 16986619214476815752661797)
                    ·
                      refine ⟨3184991102714402953624087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16986619214476815752661797 3184991102714402953624087)
                      ·
                        rfl

theorem cell23_6202748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 3, 3, 1, 4].length) (baseStart_6202748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6202748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6202748 prefixEnd_6202748 := by exact prefixLift 6202748
  have htrace : WordTrace (prefixWord ++ tailWord_6202748) baseStart_6202748 baseEnd_6202748 := by
    simpa [prefixWord, tailWord_6202748, baseEnd_6202748] using wordTrace_append hprefix tailTrace_6202748
  have hstable : (prefixWord ++ tailWord_6202748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6202748).length < 2 ^ (prefixWord ++ tailWord_6202748).sum := by decide
  have hdescent : baseEnd_6202748 < baseStart_6202748 := by decide
  rcases family_descends (prefixWord ++ tailWord_6202748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6202751 : List Nat := [1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 5]
def baseStart_6202751 : Nat := 118140960795 + 6202751 * 2 ^ 59
def prefixEnd_6202751 : Nat := 4983230072969 + 3 ^ 40 * 6202751 * 2
def baseEnd_6202751 : Nat := 3184992643156366441886573

theorem tailTrace_6202751 : CollatzResearch.WordTrace tailWord_6202751 prefixEnd_6202751 3184992643156366441886573 := by
  unfold tailWord_6202751
  simp only [CollatzResearch.WordTrace]
  refine ⟨226232914751499947377104107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150821943167666631584736071 226232914751499947377104107)
  ·
    refine ⟨339349372127249921065656161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226232914751499947377104107 339349372127249921065656161)
    ·
      refine ⟨254512029095437440799242121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 339349372127249921065656161 254512029095437440799242121)
      ·
        refine ⟨190884021821578080599431591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 254512029095437440799242121 190884021821578080599431591)
        ·
          refine ⟨286326032732367120899147387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190884021821578080599431591 286326032732367120899147387)
          ·
            refine ⟨429489049098550681348721081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286326032732367120899147387 429489049098550681348721081)
            ·
              refine ⟨322116786823913011011540811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 429489049098550681348721081 322116786823913011011540811)
              ·
                refine ⟨483175180235869516517311217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 322116786823913011011540811 483175180235869516517311217)
                ·
                  refine ⟨362381385176902137387983413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 483175180235869516517311217 362381385176902137387983413)
                  ·
                    refine ⟨33973254860334575380123445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 362381385176902137387983413 33973254860334575380123445)
                    ·
                      refine ⟨3184992643156366441886573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33973254860334575380123445 3184992643156366441886573)
                      ·
                        rfl

theorem cell23_6202751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 5].length) (baseStart_6202751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6202751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6202751 prefixEnd_6202751 := by exact prefixLift 6202751
  have htrace : WordTrace (prefixWord ++ tailWord_6202751) baseStart_6202751 baseEnd_6202751 := by
    simpa [prefixWord, tailWord_6202751, baseEnd_6202751] using wordTrace_append hprefix tailTrace_6202751
  have hstable : (prefixWord ++ tailWord_6202751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6202751).length < 2 ^ (prefixWord ++ tailWord_6202751).sum := by decide
  have hdescent : baseEnd_6202751 < baseStart_6202751 := by decide
  rcases family_descends (prefixWord ++ tailWord_6202751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6202759 : List Nat := [1, 1, 4, 2, 2, 3, 2, 3, 1, 1, 3]
def baseStart_6202759 : Nat := 118140960795 + 6202759 * 2 ^ 59
def prefixEnd_6202759 : Nat := 4983230072969 + 3 ^ 40 * 6202759 * 2
def baseEnd_6202759 : Nat := 3184996751001602410586537

theorem tailTrace_6202759 : CollatzResearch.WordTrace tailWord_6202759 prefixEnd_6202759 3184996751001602410586537 := by
  unfold tailWord_6202759
  simp only [CollatzResearch.WordTrace]
  refine ⟨226233206535470964743395331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150822137690313976495596887 226233206535470964743395331)
  ·
    refine ⟨339349809803206447115092997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226233206535470964743395331 339349809803206447115092997)
    ·
      refine ⟨63628089338101208834079937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 339349809803206447115092997 63628089338101208834079937)
      ·
        refine ⟨47721067003575906625559953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63628089338101208834079937 47721067003575906625559953)
        ·
          refine ⟨35790800252681929969169965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47721067003575906625559953 35790800252681929969169965)
          ·
            refine ⟨13421550094755723738438737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35790800252681929969169965 13421550094755723738438737)
            ·
              refine ⟨10066162571066792803829053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13421550094755723738438737 10066162571066792803829053)
              ·
                refine ⟨3774810964150047301435895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10066162571066792803829053 3774810964150047301435895)
                ·
                  refine ⟨5662216446225070952153843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3774810964150047301435895 5662216446225070952153843)
                  ·
                    refine ⟨8493324669337606428230765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5662216446225070952153843 8493324669337606428230765)
                    ·
                      refine ⟨3184996751001602410586537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8493324669337606428230765 3184996751001602410586537)
                      ·
                        rfl

theorem cell23_6202759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 3, 1, 1, 3].length) (baseStart_6202759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6202759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6202759 prefixEnd_6202759 := by exact prefixLift 6202759
  have htrace : WordTrace (prefixWord ++ tailWord_6202759) baseStart_6202759 baseEnd_6202759 := by
    simpa [prefixWord, tailWord_6202759, baseEnd_6202759] using wordTrace_append hprefix tailTrace_6202759
  have hstable : (prefixWord ++ tailWord_6202759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6202759).length < 2 ^ (prefixWord ++ tailWord_6202759).sum := by decide
  have hdescent : baseEnd_6202759 < baseStart_6202759 := by decide
  rcases family_descends (prefixWord ++ tailWord_6202759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6202778 : List Nat := [3, 1, 1, 4, 1, 1, 2, 2, 1, 1, 6]
def baseStart_6202778 : Nat := 118140960795 + 6202778 * 2 ^ 59
def prefixEnd_6202778 : Nat := 4983230072969 + 3 ^ 40 * 6202778 * 2
def baseEnd_6202778 : Nat := 3185006507134037836248949

theorem tailTrace_6202778 : CollatzResearch.WordTrace tailWord_6202778 prefixEnd_6202778 3185006507134037836248949 := by
  unfold tailWord_6202778
  simp only [CollatzResearch.WordTrace]
  refine ⟨56558474880600532747084247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150822599681601420658891325 56558474880600532747084247)
  ·
    refine ⟨84837712320900799120626371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56558474880600532747084247 84837712320900799120626371)
    ·
      refine ⟨127256568481351198680939557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84837712320900799120626371 127256568481351198680939557)
      ·
        refine ⟨23860606590253349752676167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127256568481351198680939557 23860606590253349752676167)
        ·
          refine ⟨35790909885380024629014251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23860606590253349752676167 35790909885380024629014251)
          ·
            refine ⟨53686364828070036943521377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35790909885380024629014251 53686364828070036943521377)
            ·
              refine ⟨40264773621052527707641033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53686364828070036943521377 40264773621052527707641033)
              ·
                refine ⟨30198580215789395780730775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40264773621052527707641033 30198580215789395780730775)
                ·
                  refine ⟨45297870323684093671096163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30198580215789395780730775 45297870323684093671096163)
                  ·
                    refine ⟨67946805485526140506644245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45297870323684093671096163 67946805485526140506644245)
                    ·
                      refine ⟨3185006507134037836248949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67946805485526140506644245 3185006507134037836248949)
                      ·
                        rfl

theorem cell23_6202778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_6202778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6202778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6202778 prefixEnd_6202778 := by exact prefixLift 6202778
  have htrace : WordTrace (prefixWord ++ tailWord_6202778) baseStart_6202778 baseEnd_6202778 := by
    simpa [prefixWord, tailWord_6202778, baseEnd_6202778] using wordTrace_append hprefix tailTrace_6202778
  have hstable : (prefixWord ++ tailWord_6202778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6202778).length < 2 ^ (prefixWord ++ tailWord_6202778).sum := by decide
  have hdescent : baseEnd_6202778 < baseStart_6202778 := by decide
  rcases family_descends (prefixWord ++ tailWord_6202778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6202805 : List Nat := [1, 3, 3, 2, 2, 1, 4, 7]
def baseStart_6202805 : Nat := 118140960795 + 6202805 * 2 ^ 59
def prefixEnd_6202805 : Nat := 4983230072969 + 3 ^ 40 * 6202805 * 2
def baseEnd_6202805 : Nat := 117963717448581823355975

theorem tailTrace_6202805 : CollatzResearch.WordTrace tailWord_6202805 prefixEnd_6202805 117963717448581823355975 := by
  unfold tailWord_6202805
  simp only [CollatzResearch.WordTrace]
  refine ⟨226234884293304314599569869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150823256195536209733046579 226234884293304314599569869)
  ·
    refine ⟨84838081609989117974838701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226234884293304314599569869 84838081609989117974838701)
    ·
      refine ⟨31814280603745919240564513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84838081609989117974838701 31814280603745919240564513)
      ·
        refine ⟨23860710452809439430423385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31814280603745919240564513 23860710452809439430423385)
        ·
          refine ⟨17895532839607079572817539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23860710452809439430423385 17895532839607079572817539)
          ·
            refine ⟨26843299259410619359226309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17895532839607079572817539 26843299259410619359226309)
            ·
              refine ⟨5033118611139491129854933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26843299259410619359226309 5033118611139491129854933)
              ·
                refine ⟨117963717448581823355975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5033118611139491129854933 117963717448581823355975)
                ·
                  rfl

theorem cell23_6202805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 4, 7].length) (baseStart_6202805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6202805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6202805 prefixEnd_6202805 := by exact prefixLift 6202805
  have htrace : WordTrace (prefixWord ++ tailWord_6202805) baseStart_6202805 baseEnd_6202805 := by
    simpa [prefixWord, tailWord_6202805, baseEnd_6202805] using wordTrace_append hprefix tailTrace_6202805
  have hstable : (prefixWord ++ tailWord_6202805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6202805).length < 2 ^ (prefixWord ++ tailWord_6202805).sum := by decide
  have hdescent : baseEnd_6202805 < baseStart_6202805 := by decide
  rcases family_descends (prefixWord ++ tailWord_6202805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6202825 : List Nat := [1, 2, 1, 1, 2, 1, 3, 2, 5, 3, 2]
def baseStart_6202825 : Nat := 118140960795 + 6202825 * 2 ^ 59
def prefixEnd_6202825 : Nat := 4983230072969 + 3 ^ 40 * 6202825 * 2
def baseEnd_6202825 : Nat := 3185030640724799152361233

theorem tailTrace_6202825 : CollatzResearch.WordTrace tailWord_6202825 prefixEnd_6202825 3185030640724799152361233 := by
  unfold tailWord_6202825
  simp only [CollatzResearch.WordTrace]
  refine ⟨226235613753231858015297929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150823742502154572010198619 226235613753231858015297929)
  ·
    refine ⟨169676710314923893511473447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226235613753231858015297929 169676710314923893511473447)
    ·
      refine ⟨254515065472385840267210171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169676710314923893511473447 254515065472385840267210171)
      ·
        refine ⟨381772598208578760400815257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254515065472385840267210171 381772598208578760400815257)
        ·
          refine ⟨286329448656434070300611443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 381772598208578760400815257 286329448656434070300611443)
          ·
            refine ⟨429494172984651105450917165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286329448656434070300611443 429494172984651105450917165)
            ·
              refine ⟨161060314869244164544093937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 429494172984651105450917165 161060314869244164544093937)
              ·
                refine ⟨120795236151933123408070453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161060314869244164544093937 120795236151933123408070453)
                ·
                  refine ⟨11324553389243730319506605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 120795236151933123408070453 11324553389243730319506605)
                  ·
                    refine ⟨4246707520966398869814977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11324553389243730319506605 4246707520966398869814977)
                    ·
                      refine ⟨3185030640724799152361233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4246707520966398869814977 3185030640724799152361233)
                      ·
                        rfl

theorem cell23_6202825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 5, 3, 2].length) (baseStart_6202825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6202825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6202825 prefixEnd_6202825 := by exact prefixLift 6202825
  have htrace : WordTrace (prefixWord ++ tailWord_6202825) baseStart_6202825 baseEnd_6202825 := by
    simpa [prefixWord, tailWord_6202825, baseEnd_6202825] using wordTrace_append hprefix tailTrace_6202825
  have hstable : (prefixWord ++ tailWord_6202825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6202825).length < 2 ^ (prefixWord ++ tailWord_6202825).sum := by decide
  have hdescent : baseEnd_6202825 < baseStart_6202825 := by decide
  rcases family_descends (prefixWord ++ tailWord_6202825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6202849 : List Nat := [1, 2, 3, 1, 2, 3, 4, 1, 2, 1, 3]
def baseStart_6202849 : Nat := 118140960795 + 6202849 * 2 ^ 59
def prefixEnd_6202849 : Nat := 4983230072969 + 3 ^ 40 * 6202849 * 2
def baseEnd_6202849 : Nat := 3185042964260507058461123

theorem tailTrace_6202849 : CollatzResearch.WordTrace tailWord_6202849 prefixEnd_6202849 3185042964260507058461123 := by
  unfold tailWord_6202849
  simp only [CollatzResearch.WordTrace]
  refine ⟨226236489105144910114171601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150824326070096606742781067 226236489105144910114171601)
  ·
    refine ⟨169677366828858682585628701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226236489105144910114171601 169677366828858682585628701)
    ·
      refine ⟨63629012560822005969610763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169677366828858682585628701 63629012560822005969610763)
      ·
        refine ⟨95443518841233008954416145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63629012560822005969610763 95443518841233008954416145)
        ·
          refine ⟨71582639130924756715812109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95443518841233008954416145 71582639130924756715812109)
          ·
            refine ⟨26843489674096783768429541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71582639130924756715812109 26843489674096783768429541)
            ·
              refine ⟨5033154313893146956580539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26843489674096783768429541 5033154313893146956580539)
              ·
                refine ⟨7549731470839720434870809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5033154313893146956580539 7549731470839720434870809)
                ·
                  refine ⟨5662298603129790326153107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7549731470839720434870809 5662298603129790326153107)
                  ·
                    refine ⟨8493447904694685489229661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5662298603129790326153107 8493447904694685489229661)
                    ·
                      refine ⟨3185042964260507058461123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8493447904694685489229661 3185042964260507058461123)
                      ·
                        rfl

theorem cell23_6202849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 4, 1, 2, 1, 3].length) (baseStart_6202849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6202849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6202849 prefixEnd_6202849 := by exact prefixLift 6202849
  have htrace : WordTrace (prefixWord ++ tailWord_6202849) baseStart_6202849 baseEnd_6202849 := by
    simpa [prefixWord, tailWord_6202849, baseEnd_6202849] using wordTrace_append hprefix tailTrace_6202849
  have hstable : (prefixWord ++ tailWord_6202849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6202849).length < 2 ^ (prefixWord ++ tailWord_6202849).sum := by decide
  have hdescent : baseEnd_6202849 < baseStart_6202849 := by decide
  rcases family_descends (prefixWord ++ tailWord_6202849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6202872 : List Nat := [2, 1, 2, 1, 1, 6, 1, 2, 1, 4, 2]
def baseStart_6202872 : Nat := 118140960795 + 6202872 * 2 ^ 59
def prefixEnd_6202872 : Nat := 4983230072969 + 3 ^ 40 * 6202872 * 2
def baseEnd_6202872 : Nat := 3185054774315560468473517

theorem tailTrace_6202872 : CollatzResearch.WordTrace tailWord_6202872 prefixEnd_6202872 3185054774315560468473517 := by
  unfold tailWord_6202872
  simp only [CollatzResearch.WordTrace]
  refine ⟨113118663992030792521129435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150824885322707723361505913 113118663992030792521129435)
  ·
    refine ⟨169677995988046188781694153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113118663992030792521129435 169677995988046188781694153)
    ·
      refine ⟨127258496991034641586270615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169677995988046188781694153 127258496991034641586270615)
      ·
        refine ⟨190887745486551962379405923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127258496991034641586270615 190887745486551962379405923)
        ·
          refine ⟨286331618229827943569108885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190887745486551962379405923 286331618229827943569108885)
          ·
            refine ⟨13421794604523184854801979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 286331618229827943569108885 13421794604523184854801979)
            ·
              refine ⟨20132691906784777282202969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13421794604523184854801979 20132691906784777282202969)
              ·
                refine ⟨15099518930088582961652227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20132691906784777282202969 15099518930088582961652227)
                ·
                  refine ⟨22649278395132874442478341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15099518930088582961652227 22649278395132874442478341)
                  ·
                    refine ⟨4246739699087413957964689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22649278395132874442478341 4246739699087413957964689)
                    ·
                      refine ⟨3185054774315560468473517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4246739699087413957964689 3185054774315560468473517)
                      ·
                        rfl

theorem cell23_6202872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 2, 1, 4, 2].length) (baseStart_6202872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6202872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6202872 prefixEnd_6202872 := by exact prefixLift 6202872
  have htrace : WordTrace (prefixWord ++ tailWord_6202872) baseStart_6202872 baseEnd_6202872 := by
    simpa [prefixWord, tailWord_6202872, baseEnd_6202872] using wordTrace_append hprefix tailTrace_6202872
  have hstable : (prefixWord ++ tailWord_6202872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6202872).length < 2 ^ (prefixWord ++ tailWord_6202872).sum := by decide
  have hdescent : baseEnd_6202872 < baseStart_6202872 := by decide
  rcases family_descends (prefixWord ++ tailWord_6202872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6202888 : List Nat := [2, 1, 3, 2, 1, 1, 2, 1, 1, 2, 7]
def baseStart_6202888 : Nat := 118140960795 + 6202888 * 2 ^ 59
def prefixEnd_6202888 : Nat := 4983230072969 + 3 ^ 40 * 6202888 * 2
def baseEnd_6202888 : Nat := 3185062990006032405873443

theorem tailTrace_6202888 : CollatzResearch.WordTrace tailWord_6202888 prefixEnd_6202888 3185062990006032405873443 := by
  unfold tailWord_6202888
  simp only [CollatzResearch.WordTrace]
  refine ⟨113118955776001809887420659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150825274368002413183227545 113118955776001809887420659)
  ·
    refine ⟨169678433664002714831130989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113118955776001809887420659 169678433664002714831130989)
    ·
      refine ⟨63629412624001018061674121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169678433664002714831130989 63629412624001018061674121)
      ·
        refine ⟨47722059468000763546255591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63629412624001018061674121 47722059468000763546255591)
        ·
          refine ⟨71583089202001145319383387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47722059468000763546255591 71583089202001145319383387)
          ·
            refine ⟨107374633803001717979075081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71583089202001145319383387 107374633803001717979075081)
            ·
              refine ⟨80530975352251288484306311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107374633803001717979075081 80530975352251288484306311)
              ·
                refine ⟨120796463028376932726459467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80530975352251288484306311 120796463028376932726459467)
                ·
                  refine ⟨181194694542565399089689201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 120796463028376932726459467 181194694542565399089689201)
                  ·
                    refine ⟨135896020906924049317266901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 181194694542565399089689201 135896020906924049317266901)
                    ·
                      refine ⟨3185062990006032405873443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 135896020906924049317266901 3185062990006032405873443)
                      ·
                        rfl

theorem cell23_6202888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_6202888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6202888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6202888 prefixEnd_6202888 := by exact prefixLift 6202888
  have htrace : WordTrace (prefixWord ++ tailWord_6202888) baseStart_6202888 baseEnd_6202888 := by
    simpa [prefixWord, tailWord_6202888, baseEnd_6202888] using wordTrace_append hprefix tailTrace_6202888
  have hstable : (prefixWord ++ tailWord_6202888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6202888).length < 2 ^ (prefixWord ++ tailWord_6202888).sum := by decide
  have hdescent : baseEnd_6202888 < baseStart_6202888 := by decide
  rcases family_descends (prefixWord ++ tailWord_6202888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6202889 : List Nat := [1, 2, 1, 1, 3, 1, 6, 2, 2, 2, 2]
def baseStart_6202889 : Nat := 118140960795 + 6202889 * 2 ^ 59
def prefixEnd_6202889 : Nat := 4983230072969 + 3 ^ 40 * 6202889 * 2
def baseEnd_6202889 : Nat := 3185063503486686901960939

theorem tailTrace_6202889 : CollatzResearch.WordTrace tailWord_6202889 prefixEnd_6202889 3185063503486686901960939 := by
  unfold tailWord_6202889
  simp only [CollatzResearch.WordTrace]
  refine ⟨226237948024999996945627721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150825298683333331297085147 226237948024999996945627721)
  ·
    refine ⟨169678461018749997709220791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226237948024999996945627721 169678461018749997709220791)
    ·
      refine ⟨254517691528124996563831187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169678461018749997709220791 254517691528124996563831187)
      ·
        refine ⟨381776537292187494845746781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254517691528124996563831187 381776537292187494845746781)
        ·
          refine ⟨143166201484570310567155043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 381776537292187494845746781 143166201484570310567155043)
          ·
            refine ⟨214749302226855465850732565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143166201484570310567155043 214749302226855465850732565)
            ·
              refine ⟨10066373541883849961753089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 214749302226855465850732565 10066373541883849961753089)
              ·
                refine ⟨7549780156412887471314817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10066373541883849961753089 7549780156412887471314817)
                ·
                  refine ⟨5662335117309665603486113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7549780156412887471314817 5662335117309665603486113)
                  ·
                    refine ⟨4246751337982249202614585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5662335117309665603486113 4246751337982249202614585)
                    ·
                      refine ⟨3185063503486686901960939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4246751337982249202614585 3185063503486686901960939)
                      ·
                        rfl

theorem cell23_6202889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 2, 2, 2, 2].length) (baseStart_6202889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6202889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6202889 prefixEnd_6202889 := by exact prefixLift 6202889
  have htrace : WordTrace (prefixWord ++ tailWord_6202889) baseStart_6202889 baseEnd_6202889 := by
    simpa [prefixWord, tailWord_6202889, baseEnd_6202889] using wordTrace_append hprefix tailTrace_6202889
  have hstable : (prefixWord ++ tailWord_6202889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6202889).length < 2 ^ (prefixWord ++ tailWord_6202889).sum := by decide
  have hdescent : baseEnd_6202889 < baseStart_6202889 := by decide
  rcases family_descends (prefixWord ++ tailWord_6202889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6203032 : List Nat := [2, 1, 2, 4, 1, 3, 1, 1, 3, 5]
def baseStart_6203032 : Nat := 118140960795 + 6203032 * 2 ^ 59
def prefixEnd_6203032 : Nat := 4983230072969 + 3 ^ 40 * 6203032 * 2
def baseEnd_6203032 : Nat := 1061712310406759947490927

theorem tailTrace_6203032 : CollatzResearch.WordTrace tailWord_6203032 prefixEnd_6203032 1061712310406759947490927 := by
  unfold tailWord_6203032
  simp only [CollatzResearch.WordTrace]
  refine ⟨113121581831740966184041675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150828775775654621578722233 113121581831740966184041675)
  ·
    refine ⟨169682372747611449276062513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113121581831740966184041675 169682372747611449276062513)
    ·
      refine ⟨127261779560708586957046885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169682372747611449276062513 127261779560708586957046885)
      ·
        refine ⟨23861583667632860054446291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127261779560708586957046885 23861583667632860054446291)
        ·
          refine ⟨35792375501449290081669437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23861583667632860054446291 35792375501449290081669437)
          ·
            refine ⟨13422140813043483780626039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35792375501449290081669437 13422140813043483780626039)
            ·
              refine ⟨20133211219565225670939059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13422140813043483780626039 20133211219565225670939059)
              ·
                refine ⟨30199816829347838506408589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20133211219565225670939059 30199816829347838506408589)
                ·
                  refine ⟨11324931311005439439903221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30199816829347838506408589 11324931311005439439903221)
                  ·
                    refine ⟨1061712310406759947490927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11324931311005439439903221 1061712310406759947490927)
                    ·
                      rfl

theorem cell23_6203032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 1, 3, 5].length) (baseStart_6203032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6203032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6203032 prefixEnd_6203032 := by exact prefixLift 6203032
  have htrace : WordTrace (prefixWord ++ tailWord_6203032) baseStart_6203032 baseEnd_6203032 := by
    simpa [prefixWord, tailWord_6203032, baseEnd_6203032] using wordTrace_append hprefix tailTrace_6203032
  have hstable : (prefixWord ++ tailWord_6203032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6203032).length < 2 ^ (prefixWord ++ tailWord_6203032).sum := by decide
  have hdescent : baseEnd_6203032 < baseStart_6203032 := by decide
  rcases family_descends (prefixWord ++ tailWord_6203032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6203045 : List Nat := [1, 3, 1, 2, 1, 2, 3, 1, 3, 6]
def baseStart_6203045 : Nat := 118140960795 + 6203045 * 2 ^ 59
def prefixEnd_6203045 : Nat := 4983230072969 + 3 ^ 40 * 6203045 * 2
def baseEnd_6203045 : Nat := 1061714535489596097203407

theorem tailTrace_6203045 : CollatzResearch.WordTrace tailWord_6203045 prefixEnd_6203045 1061714535489596097203407 := by
  unfold tailWord_6203045
  simp only [CollatzResearch.WordTrace]
  refine ⟨226243637812434835588306589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150829091874956557058871059 226243637812434835588306589)
  ·
    refine ⟨84841364179663063345614971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226243637812434835588306589 84841364179663063345614971)
    ·
      refine ⟨127262046269494595018422457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84841364179663063345614971 127262046269494595018422457)
      ·
        refine ⟨95446534702120946263816843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127262046269494595018422457 95446534702120946263816843)
        ·
          refine ⟨143169802053181419395725265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95446534702120946263816843 143169802053181419395725265)
          ·
            refine ⟨107377351539886064546793949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143169802053181419395725265 107377351539886064546793949)
            ·
              refine ⟨40266506827457274205047731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107377351539886064546793949 40266506827457274205047731)
              ·
                refine ⟨60399760241185911307571597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40266506827457274205047731 60399760241185911307571597)
                ·
                  refine ⟨22649910090444716740339349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60399760241185911307571597 22649910090444716740339349)
                  ·
                    refine ⟨1061714535489596097203407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22649910090444716740339349 1061714535489596097203407)
                    ·
                      rfl

theorem cell23_6203045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 3, 6].length) (baseStart_6203045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6203045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6203045 prefixEnd_6203045 := by exact prefixLift 6203045
  have htrace : WordTrace (prefixWord ++ tailWord_6203045) baseStart_6203045 baseEnd_6203045 := by
    simpa [prefixWord, tailWord_6203045, baseEnd_6203045] using wordTrace_append hprefix tailTrace_6203045
  have hstable : (prefixWord ++ tailWord_6203045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6203045).length < 2 ^ (prefixWord ++ tailWord_6203045).sum := by decide
  have hdescent : baseEnd_6203045 < baseStart_6203045 := by decide
  rcases family_descends (prefixWord ++ tailWord_6203045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6203063 : List Nat := [1, 1, 3, 1, 5, 1, 4, 2, 1, 1, 3]
def baseStart_6203063 : Nat := 118140960795 + 6203063 * 2 ^ 59
def prefixEnd_6203063 : Nat := 4983230072969 + 3 ^ 40 * 6203063 * 2
def baseEnd_6203063 : Nat := 3185152849120569221185139

theorem tailTrace_6203063 : CollatzResearch.WordTrace tailWord_6203063 prefixEnd_6203063 3185152849120569221185139 := by
  unfold tailWord_6203063
  simp only [CollatzResearch.WordTrace]
  refine ⟨226244294326369624662461843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150829529550913083108307895 226244294326369624662461843)
  ·
    refine ⟨339366441489554436993692765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226244294326369624662461843 339366441489554436993692765)
    ·
      refine ⟨127262415558582913872634787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 339366441489554436993692765 127262415558582913872634787)
      ·
        refine ⟨190893623337874370808952181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127262415558582913872634787 190893623337874370808952181)
        ·
          refine ⟨17896277187925722263339267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 190893623337874370808952181 17896277187925722263339267)
          ·
            refine ⟨26844415781888583395008901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17896277187925722263339267 26844415781888583395008901)
            ·
              refine ⟨5033327959104109386564169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26844415781888583395008901 5033327959104109386564169)
              ·
                refine ⟨3774995969328082039923127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5033327959104109386564169 3774995969328082039923127)
                ·
                  refine ⟨5662493953992123059884691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3774995969328082039923127 5662493953992123059884691)
                  ·
                    refine ⟨8493740930988184589827037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5662493953992123059884691 8493740930988184589827037)
                    ·
                      refine ⟨3185152849120569221185139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8493740930988184589827037 3185152849120569221185139)
                      ·
                        rfl

theorem cell23_6203063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 4, 2, 1, 1, 3].length) (baseStart_6203063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6203063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6203063 prefixEnd_6203063 := by exact prefixLift 6203063
  have htrace : WordTrace (prefixWord ++ tailWord_6203063) baseStart_6203063 baseEnd_6203063 := by
    simpa [prefixWord, tailWord_6203063, baseEnd_6203063] using wordTrace_append hprefix tailTrace_6203063
  have hstable : (prefixWord ++ tailWord_6203063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6203063).length < 2 ^ (prefixWord ++ tailWord_6203063).sum := by decide
  have hdescent : baseEnd_6203063 < baseStart_6203063 := by decide
  rcases family_descends (prefixWord ++ tailWord_6203063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6203065 : List Nat := [1, 2, 1, 4, 1, 1, 2, 1, 3, 1, 6]
def baseStart_6203065 : Nat := 118140960795 + 6203065 * 2 ^ 59
def prefixEnd_6203065 : Nat := 4983230072969 + 3 ^ 40 * 6203065 * 2
def baseEnd_6203065 : Nat := 3185153876081878213360129

theorem tailTrace_6203065 : CollatzResearch.WordTrace tailWord_6203065 prefixEnd_6203065 3185153876081878213360129 := by
  unfold tailWord_6203065
  simp only [CollatzResearch.WordTrace]
  refine ⟨226244367272362379004034649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150829578181574919336023099 226244367272362379004034649)
  ·
    refine ⟨169683275454271784253025987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226244367272362379004034649 169683275454271784253025987)
    ·
      refine ⟨254524913181407676379538981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169683275454271784253025987 254524913181407676379538981)
      ·
        refine ⟨47723421221513939321163559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 254524913181407676379538981 47723421221513939321163559)
        ·
          refine ⟨71585131832270908981745339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47723421221513939321163559 71585131832270908981745339)
          ·
            refine ⟨107377697748406363472618009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71585131832270908981745339 107377697748406363472618009)
            ·
              refine ⟨80533273311304772604463507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107377697748406363472618009 80533273311304772604463507)
              ·
                refine ⟨120799909966957158906695261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80533273311304772604463507 120799909966957158906695261)
                ·
                  refine ⟨45299966237608934590010723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 120799909966957158906695261 45299966237608934590010723)
                  ·
                    refine ⟨67949949356413401885016085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45299966237608934590010723 67949949356413401885016085)
                    ·
                      refine ⟨3185153876081878213360129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67949949356413401885016085 3185153876081878213360129)
                      ·
                        rfl

theorem cell23_6203065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_6203065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6203065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6203065 prefixEnd_6203065 := by exact prefixLift 6203065
  have htrace : WordTrace (prefixWord ++ tailWord_6203065) baseStart_6203065 baseEnd_6203065 := by
    simpa [prefixWord, tailWord_6203065, baseEnd_6203065] using wordTrace_append hprefix tailTrace_6203065
  have hstable : (prefixWord ++ tailWord_6203065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6203065).length < 2 ^ (prefixWord ++ tailWord_6203065).sum := by decide
  have hdescent : baseEnd_6203065 < baseStart_6203065 := by decide
  rcases family_descends (prefixWord ++ tailWord_6203065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6203072 : List Nat := [2, 1, 1, 2, 4, 1, 1, 1, 5, 2, 3]
def baseStart_6203072 : Nat := 118140960795 + 6203072 * 2 ^ 59
def prefixEnd_6203072 : Nat := 4983230072969 + 3 ^ 40 * 6203072 * 2
def baseEnd_6203072 : Nat := 3185157470446459685972597

theorem tailTrace_6203072 : CollatzResearch.WordTrace tailWord_6203072 prefixEnd_6203072 3185157470446459685972597 := by
  unfold tailWord_6203072
  simp only [CollatzResearch.WordTrace]
  refine ⟨113122311291668509599769735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150829748388891346133026313 113122311291668509599769735)
  ·
    refine ⟨169683466937502764399654603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113122311291668509599769735 169683466937502764399654603)
    ·
      refine ⟨254525200406254146599481905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169683466937502764399654603 254525200406254146599481905)
      ·
        refine ⟨190893900304690609949611429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 254525200406254146599481905 190893900304690609949611429)
        ·
          refine ⟨35792606307129489365552143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 190893900304690609949611429 35792606307129489365552143)
          ·
            refine ⟨53688909460694234048328215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35792606307129489365552143 53688909460694234048328215)
            ·
              refine ⟨80533364191041351072492323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53688909460694234048328215 80533364191041351072492323)
              ·
                refine ⟨120800046286562026608738485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80533364191041351072492323 120800046286562026608738485)
                ·
                  refine ⟨11325004339365189994569233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 120800046286562026608738485 11325004339365189994569233)
                  ·
                    refine ⟨8493753254523892495926925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11325004339365189994569233 8493753254523892495926925)
                    ·
                      refine ⟨3185157470446459685972597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8493753254523892495926925 3185157470446459685972597)
                      ·
                        rfl

theorem cell23_6203072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 5, 2, 3].length) (baseStart_6203072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6203072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6203072 prefixEnd_6203072 := by exact prefixLift 6203072
  have htrace : WordTrace (prefixWord ++ tailWord_6203072) baseStart_6203072 baseEnd_6203072 := by
    simpa [prefixWord, tailWord_6203072, baseEnd_6203072] using wordTrace_append hprefix tailTrace_6203072
  have hstable : (prefixWord ++ tailWord_6203072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6203072).length < 2 ^ (prefixWord ++ tailWord_6203072).sum := by decide
  have hdescent : baseEnd_6203072 < baseStart_6203072 := by decide
  rcases family_descends (prefixWord ++ tailWord_6203072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6203086 : List Nat := [4, 1, 1, 1, 3, 1, 3, 2, 3, 2, 2]
def baseStart_6203086 : Nat := 118140960795 + 6203086 * 2 ^ 59
def prefixEnd_6203086 : Nat := 4983230072969 + 3 ^ 40 * 6203086 * 2
def baseEnd_6203086 : Nat := 3185164659175622631197533

theorem tailTrace_6203086 : CollatzResearch.WordTrace tailWord_6203086 prefixEnd_6203086 3185164659175622631197533 := by
  unfold tailWord_6203086
  simp only [CollatzResearch.WordTrace]
  refine ⟨28280641650660787448818639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150830088803524199727032741 28280641650660787448818639)
  ·
    refine ⟨42420962475991181173227959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28280641650660787448818639 42420962475991181173227959)
    ·
      refine ⟨63631443713986771759841939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42420962475991181173227959 63631443713986771759841939)
      ·
        refine ⟨95447165570980157639762909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63631443713986771759841939 95447165570980157639762909)
        ·
          refine ⟨35792687089117559114911091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95447165570980157639762909 35792687089117559114911091)
          ·
            refine ⟨53689030633676338672366637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35792687089117559114911091 53689030633676338672366637)
            ·
              refine ⟨20133386487628627002137489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53689030633676338672366637 20133386487628627002137489)
              ·
                refine ⟨15100039865721470251603117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20133386487628627002137489 15100039865721470251603117)
                ·
                  refine ⟨5662514949645551344351169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15100039865721470251603117 5662514949645551344351169)
                  ·
                    refine ⟨4246886212234163508263377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5662514949645551344351169 4246886212234163508263377)
                    ·
                      refine ⟨3185164659175622631197533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4246886212234163508263377 3185164659175622631197533)
                      ·
                        rfl

theorem cell23_6203086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 2, 3, 2, 2].length) (baseStart_6203086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6203086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6203086 prefixEnd_6203086 := by exact prefixLift 6203086
  have htrace : WordTrace (prefixWord ++ tailWord_6203086) baseStart_6203086 baseEnd_6203086 := by
    simpa [prefixWord, tailWord_6203086, baseEnd_6203086] using wordTrace_append hprefix tailTrace_6203086
  have hstable : (prefixWord ++ tailWord_6203086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6203086).length < 2 ^ (prefixWord ++ tailWord_6203086).sum := by decide
  have hdescent : baseEnd_6203086 < baseStart_6203086 := by decide
  rcases family_descends (prefixWord ++ tailWord_6203086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6203100 : List Nat := [2, 2, 5, 1, 3, 1, 2, 1, 1, 5]
def baseStart_6203100 : Nat := 118140960795 + 6203100 * 2 ^ 59
def prefixEnd_6203100 : Nat := 4983230072969 + 3 ^ 40 * 6203100 * 2
def baseEnd_6203100 : Nat := 1061723949301595192140823

theorem tailTrace_6203100 : CollatzResearch.WordTrace tailWord_6203100 prefixEnd_6203100 1061723949301595192140823 := by
  unfold tailWord_6203100
  simp only [CollatzResearch.WordTrace]
  refine ⟨113122821913617789990779377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150830429218157053321039169 113122821913617789990779377)
  ·
    refine ⟨84842116435213342493084533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113122821913617789990779377 84842116435213342493084533)
    ·
      refine ⟨7953948415801250858726675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 84842116435213342493084533 7953948415801250858726675)
      ·
        refine ⟨11930922623701876288090013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7953948415801250858726675 11930922623701876288090013)
        ·
          refine ⟨4474095983888203608033755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11930922623701876288090013 4474095983888203608033755)
          ·
            refine ⟨6711143975832305412050633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4474095983888203608033755 6711143975832305412050633)
            ·
              refine ⟨5033357981874229059037975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6711143975832305412050633 5033357981874229059037975)
              ·
                refine ⟨7550036972811343588556963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5033357981874229059037975 7550036972811343588556963)
                ·
                  refine ⟨11325055459217015382835445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7550036972811343588556963 11325055459217015382835445)
                  ·
                    refine ⟨1061723949301595192140823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11325055459217015382835445 1061723949301595192140823)
                    ·
                      rfl

theorem cell23_6203100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_6203100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6203100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6203100 prefixEnd_6203100 := by exact prefixLift 6203100
  have htrace : WordTrace (prefixWord ++ tailWord_6203100) baseStart_6203100 baseEnd_6203100 := by
    simpa [prefixWord, tailWord_6203100, baseEnd_6203100] using wordTrace_append hprefix tailTrace_6203100
  have hstable : (prefixWord ++ tailWord_6203100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6203100).length < 2 ^ (prefixWord ++ tailWord_6203100).sum := by decide
  have hdescent : baseEnd_6203100 < baseStart_6203100 := by decide
  rcases family_descends (prefixWord ++ tailWord_6203100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6203103 : List Nat := [1, 1, 2, 3, 2, 2, 4, 3, 1, 2, 2]
def baseStart_6203103 : Nat := 118140960795 + 6203103 * 2 ^ 59
def prefixEnd_6203103 : Nat := 4983230072969 + 3 ^ 40 * 6203103 * 2
def baseEnd_6203103 : Nat := 3185173388346749064684955

theorem tailTrace_6203103 : CollatzResearch.WordTrace tailWord_6203103 prefixEnd_6203103 3185173388346749064684955 := by
  unfold tailWord_6203103
  simp only [CollatzResearch.WordTrace]
  refine ⟨226245753246224711493917963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150830502164149807662611975 226245753246224711493917963)
  ·
    refine ⟨339368629869337067240876945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226245753246224711493917963 339368629869337067240876945)
    ·
      refine ⟨254526472402002800430657709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 339368629869337067240876945 254526472402002800430657709)
      ·
        refine ⟨95447427150751050161496641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 254526472402002800430657709 95447427150751050161496641)
        ·
          refine ⟨71585570363063287621122481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95447427150751050161496641 71585570363063287621122481)
          ·
            refine ⟨53689177772297465715841861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71585570363063287621122481 53689177772297465715841861)
            ·
              refine ⟨10066720832305774821720349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53689177772297465715841861 10066720832305774821720349)
              ·
                refine ⟨3775020312114665558145131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10066720832305774821720349 3775020312114665558145131)
                ·
                  refine ⟨5662530468171998337217697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3775020312114665558145131 5662530468171998337217697)
                  ·
                    refine ⟨4246897851128998752913273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5662530468171998337217697 4246897851128998752913273)
                    ·
                      refine ⟨3185173388346749064684955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4246897851128998752913273 3185173388346749064684955)
                      ·
                        rfl

theorem cell23_6203103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 3, 1, 2, 2].length) (baseStart_6203103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6203103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6203103 prefixEnd_6203103 := by exact prefixLift 6203103
  have htrace : WordTrace (prefixWord ++ tailWord_6203103) baseStart_6203103 baseEnd_6203103 := by
    simpa [prefixWord, tailWord_6203103, baseEnd_6203103] using wordTrace_append hprefix tailTrace_6203103
  have hstable : (prefixWord ++ tailWord_6203103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6203103).length < 2 ^ (prefixWord ++ tailWord_6203103).sum := by decide
  have hdescent : baseEnd_6203103 < baseStart_6203103 := by decide
  rcases family_descends (prefixWord ++ tailWord_6203103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6203119 : List Nat := [1, 1, 2, 1, 5, 1, 3, 1, 4, 1, 3]
def baseStart_6203119 : Nat := 118140960795 + 6203119 * 2 ^ 59
def prefixEnd_6203119 : Nat := 4983230072969 + 3 ^ 40 * 6203119 * 2
def baseEnd_6203119 : Nat := 3185181604037221002084881

theorem tailTrace_6203119 : CollatzResearch.WordTrace tailWord_6203119 prefixEnd_6203119 3185181604037221002084881 := by
  unfold tailWord_6203119
  simp only [CollatzResearch.WordTrace]
  refine ⟨226246336814166746226500411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150830891209444497484333607 226246336814166746226500411)
  ·
    refine ⟨339369505221250119339750617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226246336814166746226500411 339369505221250119339750617)
    ·
      refine ⟨254527128915937589504812963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 339369505221250119339750617 254527128915937589504812963)
      ·
        refine ⟨381790693373906384257219445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254527128915937589504812963 381790693373906384257219445)
        ·
          refine ⟨35792877503803723524114323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 381790693373906384257219445 35792877503803723524114323)
          ·
            refine ⟨53689316255705585286171485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35792877503803723524114323 53689316255705585286171485)
            ·
              refine ⟨20133493595889594482314307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53689316255705585286171485 20133493595889594482314307)
              ·
                refine ⟨30200240393834391723471461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20133493595889594482314307 30200240393834391723471461)
                ·
                  refine ⟨5662545073843948448150899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30200240393834391723471461 5662545073843948448150899)
                  ·
                    refine ⟨8493817610765922672226349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5662545073843948448150899 8493817610765922672226349)
                    ·
                      refine ⟨3185181604037221002084881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8493817610765922672226349 3185181604037221002084881)
                      ·
                        rfl

theorem cell23_6203119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 1, 4, 1, 3].length) (baseStart_6203119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6203119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6203119 prefixEnd_6203119 := by exact prefixLift 6203119
  have htrace : WordTrace (prefixWord ++ tailWord_6203119) baseStart_6203119 baseEnd_6203119 := by
    simpa [prefixWord, tailWord_6203119, baseEnd_6203119] using wordTrace_append hprefix tailTrace_6203119
  have hstable : (prefixWord ++ tailWord_6203119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6203119).length < 2 ^ (prefixWord ++ tailWord_6203119).sum := by decide
  have hdescent : baseEnd_6203119 < baseStart_6203119 := by decide
  rcases family_descends (prefixWord ++ tailWord_6203119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6203146 : List Nat := [3, 1, 2, 2, 1, 3, 1, 4, 1, 3, 2]
def baseStart_6203146 : Nat := 118140960795 + 6203146 * 2 ^ 59
def prefixEnd_6203146 : Nat := 4983230072969 + 3 ^ 40 * 6203146 * 2
def baseEnd_6203146 : Nat := 3185195468014892396447257

theorem tailTrace_6203146 : CollatzResearch.WordTrace tailWord_6203146 prefixEnd_6203146 3185195468014892396447257 := by
  unfold tailWord_6203146
  simp only [CollatzResearch.WordTrace]
  refine ⟨56561830396267232459433323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150831547723379286558488861 56561830396267232459433323)
  ·
    refine ⟨84842745594400848689149985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56561830396267232459433323 84842745594400848689149985)
    ·
      refine ⟨63632059195800636516862489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84842745594400848689149985 63632059195800636516862489)
      ·
        refine ⟨47724044396850477387646867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63632059195800636516862489 47724044396850477387646867)
        ·
          refine ⟨71586066595275716081470301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47724044396850477387646867 71586066595275716081470301)
          ·
            refine ⟨26844774973228393530551363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71586066595275716081470301 26844774973228393530551363)
            ·
              refine ⟨40267162459842590295827045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26844774973228393530551363 40267162459842590295827045)
              ·
                refine ⟨7550092961220485680467571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40267162459842590295827045 7550092961220485680467571)
                ·
                  refine ⟨11325139441830728520701357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7550092961220485680467571 11325139441830728520701357)
                  ·
                    refine ⟨4246927290686523195263009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11325139441830728520701357 4246927290686523195263009)
                    ·
                      refine ⟨3185195468014892396447257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4246927290686523195263009 3185195468014892396447257)
                      ·
                        rfl

theorem cell23_6203146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 4, 1, 3, 2].length) (baseStart_6203146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6203146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6203146 prefixEnd_6203146 := by exact prefixLift 6203146
  have htrace : WordTrace (prefixWord ++ tailWord_6203146) baseStart_6203146 baseEnd_6203146 := by
    simpa [prefixWord, tailWord_6203146, baseEnd_6203146] using wordTrace_append hprefix tailTrace_6203146
  have hstable : (prefixWord ++ tailWord_6203146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6203146).length < 2 ^ (prefixWord ++ tailWord_6203146).sum := by decide
  have hdescent : baseEnd_6203146 < baseStart_6203146 := by decide
  rcases family_descends (prefixWord ++ tailWord_6203146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6203162 : List Nat := [3, 1, 1, 3, 2, 2, 1, 1, 1, 3, 5]
def baseStart_6203162 : Nat := 118140960795 + 6203162 * 2 ^ 59
def prefixEnd_6203162 : Nat := 4983230072969 + 3 ^ 40 * 6203162 * 2
def baseEnd_6203162 : Nat := 3185203683705364333847183

theorem tailTrace_6203162 : CollatzResearch.WordTrace tailWord_6203162 prefixEnd_6203162 3185203683705364333847183 := by
  unfold tailWord_6203162
  simp only [CollatzResearch.WordTrace]
  refine ⟨56561976288252741142578935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150831936768673976380210493 56561976288252741142578935)
  ·
    refine ⟨84842964432379111713868403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56561976288252741142578935 84842964432379111713868403)
    ·
      refine ⟨127264446648568667570802605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84842964432379111713868403 127264446648568667570802605)
      ·
        refine ⟨47724167493213250339050977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127264446648568667570802605 47724167493213250339050977)
        ·
          refine ⟨35793125619909937754288233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47724167493213250339050977 35793125619909937754288233)
          ·
            refine ⟨26844844214932453315716175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35793125619909937754288233 26844844214932453315716175)
            ·
              refine ⟨40267266322398679973574263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26844844214932453315716175 40267266322398679973574263)
              ·
                refine ⟨60400899483598019960361395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40267266322398679973574263 60400899483598019960361395)
                ·
                  refine ⟨90601349225397029940542093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60400899483598019960361395 90601349225397029940542093)
                  ·
                    refine ⟨33975505959523886227703285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 90601349225397029940542093 33975505959523886227703285)
                    ·
                      refine ⟨3185203683705364333847183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33975505959523886227703285 3185203683705364333847183)
                      ·
                        rfl

theorem cell23_6203162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_6203162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6203162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6203162 prefixEnd_6203162 := by exact prefixLift 6203162
  have htrace : WordTrace (prefixWord ++ tailWord_6203162) baseStart_6203162 baseEnd_6203162 := by
    simpa [prefixWord, tailWord_6203162, baseEnd_6203162] using wordTrace_append hprefix tailTrace_6203162
  have hstable : (prefixWord ++ tailWord_6203162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6203162).length < 2 ^ (prefixWord ++ tailWord_6203162).sum := by decide
  have hdescent : baseEnd_6203162 < baseStart_6203162 := by decide
  rcases family_descends (prefixWord ++ tailWord_6203162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6203269 : List Nat := [1, 3, 1, 1, 3, 2, 3, 1, 1, 4, 3]
def baseStart_6203269 : Nat := 118140960795 + 6203269 * 2 ^ 59
def prefixEnd_6203269 : Nat := 4983230072969 + 3 ^ 40 * 6203269 * 2
def baseEnd_6203269 : Nat := 3185258626135395415209191

theorem tailTrace_6203269 : CollatzResearch.WordTrace tailWord_6203269 prefixEnd_6203269 3185258626135395415209191 := by
  unfold tailWord_6203269
  simp only [CollatzResearch.WordTrace]
  refine ⟨226251807763623321844460861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150834538509082214562973907 226251807763623321844460861)
  ·
    refine ⟨84844427911358745691672823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226251807763623321844460861 84844427911358745691672823)
    ·
      refine ⟨127266641867038118537509235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84844427911358745691672823 127266641867038118537509235)
      ·
        refine ⟨190899962800557177806263853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127266641867038118537509235 190899962800557177806263853)
        ·
          refine ⟨71587486050208941677348945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 190899962800557177806263853 71587486050208941677348945)
          ·
            refine ⟨53690614537656706258011709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71587486050208941677348945 53690614537656706258011709)
            ·
              refine ⟨20133980451621264846754391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53690614537656706258011709 20133980451621264846754391)
              ·
                refine ⟨30200970677431897270131587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20133980451621264846754391 30200970677431897270131587)
                ·
                  refine ⟨45301456016147845905197381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30200970677431897270131587 45301456016147845905197381)
                  ·
                    refine ⟨8494023003027721107224509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45301456016147845905197381 8494023003027721107224509)
                    ·
                      refine ⟨3185258626135395415209191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8494023003027721107224509 3185258626135395415209191)
                      ·
                        rfl

theorem cell23_6203269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 1, 1, 4, 3].length) (baseStart_6203269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6203269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6203269 prefixEnd_6203269 := by exact prefixLift 6203269
  have htrace : WordTrace (prefixWord ++ tailWord_6203269) baseStart_6203269 baseEnd_6203269 := by
    simpa [prefixWord, tailWord_6203269, baseEnd_6203269] using wordTrace_append hprefix tailTrace_6203269
  have hstable : (prefixWord ++ tailWord_6203269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6203269).length < 2 ^ (prefixWord ++ tailWord_6203269).sum := by decide
  have hdescent : baseEnd_6203269 < baseStart_6203269 := by decide
  rcases family_descends (prefixWord ++ tailWord_6203269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6203289 : List Nat := [1, 2, 1, 2, 1, 3, 5, 2, 6]
def baseStart_6203289 : Nat := 118140960795 + 6203289 * 2 ^ 59
def prefixEnd_6203289 : Nat := 4983230072969 + 3 ^ 40 * 6203289 * 2
def baseEnd_6203289 : Nat := 353918766194276148551011

theorem tailTrace_6203289 : CollatzResearch.WordTrace tailWord_6203289 prefixEnd_6203289 353918766194276148551011 := by
  unfold tailWord_6203289
  simp only [CollatzResearch.WordTrace]
  refine ⟨226252537223550865260188921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150835024815700576840125947 226252537223550865260188921)
  ·
    refine ⟨169689402917663148945141691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226252537223550865260188921 169689402917663148945141691)
    ·
      refine ⟨254534104376494723417712537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169689402917663148945141691 254534104376494723417712537)
      ·
        refine ⟨190900578282371042563284403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 254534104376494723417712537 190900578282371042563284403)
        ·
          refine ⟨286350867423556563844926605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190900578282371042563284403 286350867423556563844926605)
          ·
            refine ⟨107381575283833711441847477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 286350867423556563844926605 107381575283833711441847477)
            ·
              refine ⟨10067022682859410447673201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 107381575283833711441847477 10067022682859410447673201)
              ·
                refine ⟨7550267012144557835754901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10067022682859410447673201 7550267012144557835754901)
                ·
                  refine ⟨353918766194276148551011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7550267012144557835754901 353918766194276148551011)
                  ·
                    rfl

theorem cell23_6203289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 2, 6].length) (baseStart_6203289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6203289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6203289 prefixEnd_6203289 := by exact prefixLift 6203289
  have htrace : WordTrace (prefixWord ++ tailWord_6203289) baseStart_6203289 baseEnd_6203289 := by
    simpa [prefixWord, tailWord_6203289, baseEnd_6203289] using wordTrace_append hprefix tailTrace_6203289
  have hstable : (prefixWord ++ tailWord_6203289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6203289).length < 2 ^ (prefixWord ++ tailWord_6203289).sum := by decide
  have hdescent : baseEnd_6203289 < baseStart_6203289 := by decide
  rcases family_descends (prefixWord ++ tailWord_6203289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6203293 : List Nat := [1, 4, 2, 1, 2, 2, 2, 4, 1, 4]
def baseStart_6203293 : Nat := 118140960795 + 6203293 * 2 ^ 59
def prefixEnd_6203293 : Nat := 4983230072969 + 3 ^ 40 * 6203293 * 2
def baseEnd_6203293 : Nat := 1061756983223701107103027

theorem tailTrace_6203293 : CollatzResearch.WordTrace tailWord_6203293 prefixEnd_6203293 1061756983223701107103027 := by
  unfold tailWord_6203293
  simp only [CollatzResearch.WordTrace]
  refine ⟨226252683115536373943334533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150835122077024249295556355 226252683115536373943334533)
  ·
    refine ⟨42422378084163070114375225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 226252683115536373943334533 42422378084163070114375225)
    ·
      refine ⟨31816783563122302585781419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42422378084163070114375225 31816783563122302585781419)
      ·
        refine ⟨47725175344683453878672129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31816783563122302585781419 47725175344683453878672129)
        ·
          refine ⟨35793881508512590409004097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47725175344683453878672129 35793881508512590409004097)
          ·
            refine ⟨26845411131384442806753073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35793881508512590409004097 26845411131384442806753073)
            ·
              refine ⟨20134058348538332105064805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26845411131384442806753073 20134058348538332105064805)
              ·
                refine ⟨3775135940350937269699651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20134058348538332105064805 3775135940350937269699651)
                ·
                  refine ⟨5662703910526405904549477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3775135940350937269699651 5662703910526405904549477)
                  ·
                    refine ⟨1061756983223701107103027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5662703910526405904549477 1061756983223701107103027)
                    ·
                      rfl

theorem cell23_6203293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 4, 1, 4].length) (baseStart_6203293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6203293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6203293 prefixEnd_6203293 := by exact prefixLift 6203293
  have htrace : WordTrace (prefixWord ++ tailWord_6203293) baseStart_6203293 baseEnd_6203293 := by
    simpa [prefixWord, tailWord_6203293, baseEnd_6203293] using wordTrace_append hprefix tailTrace_6203293
  have hstable : (prefixWord ++ tailWord_6203293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6203293).length < 2 ^ (prefixWord ++ tailWord_6203293).sum := by decide
  have hdescent : baseEnd_6203293 < baseStart_6203293 := by decide
  rcases family_descends (prefixWord ++ tailWord_6203293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6203333 : List Nat := [1, 3, 1, 1, 1, 1, 1, 9, 1, 1, 3]
def baseStart_6203333 : Nat := 118140960795 + 6203333 * 2 ^ 59
def prefixEnd_6203333 : Nat := 4983230072969 + 3 ^ 40 * 6203333 * 2
def baseEnd_6203333 : Nat := 3185291488897283164808897

theorem tailTrace_6203333 : CollatzResearch.WordTrace tailWord_6203333 prefixEnd_6203333 3185291488897283164808897 := by
  unfold tailWord_6203333
  simp only [CollatzResearch.WordTrace]
  refine ⟨226254142035391460774790653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150836094690260973849860435 226254142035391460774790653)
  ·
    refine ⟨84845303263271797790546495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226254142035391460774790653 84845303263271797790546495)
    ·
      refine ⟨127267954894907696685819743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84845303263271797790546495 127267954894907696685819743)
      ·
        refine ⟨190901932342361545028729615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127267954894907696685819743 190901932342361545028729615)
        ·
          refine ⟨286352898513542317543094423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190901932342361545028729615 286352898513542317543094423)
          ·
            refine ⟨429529347770313476314641635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286352898513542317543094423 429529347770313476314641635)
            ·
              refine ⟨644294021655470214471962453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 429529347770313476314641635 644294021655470214471962453)
              ·
                refine ⟨3775160283137520787921655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 644294021655470214471962453 3775160283137520787921655)
                ·
                  refine ⟨5662740424706281181882483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3775160283137520787921655 5662740424706281181882483)
                  ·
                    refine ⟨8494110637059421772823725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5662740424706281181882483 8494110637059421772823725)
                    ·
                      refine ⟨3185291488897283164808897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8494110637059421772823725 3185291488897283164808897)
                      ·
                        rfl

theorem cell23_6203333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 9, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 9, 1, 1, 3].length) (baseStart_6203333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6203333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6203333 prefixEnd_6203333 := by exact prefixLift 6203333
  have htrace : WordTrace (prefixWord ++ tailWord_6203333) baseStart_6203333 baseEnd_6203333 := by
    simpa [prefixWord, tailWord_6203333, baseEnd_6203333] using wordTrace_append hprefix tailTrace_6203333
  have hstable : (prefixWord ++ tailWord_6203333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6203333).length < 2 ^ (prefixWord ++ tailWord_6203333).sum := by decide
  have hdescent : baseEnd_6203333 < baseStart_6203333 := by decide
  rcases family_descends (prefixWord ++ tailWord_6203333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6203336 : List Nat := [2, 1, 3, 1, 4, 1, 2, 3, 1, 5]
def baseStart_6203336 : Nat := 118140960795 + 6203336 * 2 ^ 59
def prefixEnd_6203336 : Nat := 4983230072969 + 3 ^ 40 * 6203336 * 2
def baseEnd_6203336 : Nat := 1061764343113082217690461

theorem tailTrace_6203336 : CollatzResearch.WordTrace tailWord_6203336 prefixEnd_6203336 1061764343113082217690461 := by
  unfold tailWord_6203336
  simp only [CollatzResearch.WordTrace]
  refine ⟨113127125727190296143574931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150836167636253728191433241 113127125727190296143574931)
  ·
    refine ⟨169690688590785444215362397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113127125727190296143574931 169690688590785444215362397)
    ·
      refine ⟨63634008221544541580760899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169690688590785444215362397 63634008221544541580760899)
      ·
        refine ⟨95451012332316812371141349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63634008221544541580760899 95451012332316812371141349)
        ·
          refine ⟨17897064812309402319589003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95451012332316812371141349 17897064812309402319589003)
          ·
            refine ⟨26845597218464103479383505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17897064812309402319589003 26845597218464103479383505)
            ·
              refine ⟨20134197913848077609537629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26845597218464103479383505 20134197913848077609537629)
              ·
                refine ⟨7550324217693029103576611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20134197913848077609537629 7550324217693029103576611)
                ·
                  refine ⟨11325486326539543655364917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7550324217693029103576611 11325486326539543655364917)
                  ·
                    refine ⟨1061764343113082217690461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11325486326539543655364917 1061764343113082217690461)
                    ·
                      rfl

theorem cell23_6203336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 3, 1, 5].length) (baseStart_6203336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6203336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6203336 prefixEnd_6203336 := by exact prefixLift 6203336
  have htrace : WordTrace (prefixWord ++ tailWord_6203336) baseStart_6203336 baseEnd_6203336 := by
    simpa [prefixWord, tailWord_6203336, baseEnd_6203336] using wordTrace_append hprefix tailTrace_6203336
  have hstable : (prefixWord ++ tailWord_6203336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6203336).length < 2 ^ (prefixWord ++ tailWord_6203336).sum := by decide
  have hdescent : baseEnd_6203336 < baseStart_6203336 := by decide
  rcases family_descends (prefixWord ++ tailWord_6203336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6203396 : List Nat := [2, 3, 2, 4, 1, 11]
def baseStart_6203396 : Nat := 118140960795 + 6203396 * 2 ^ 59
def prefixEnd_6203396 : Nat := 4983230072969 + 3 ^ 40 * 6203396 * 2
def baseEnd_6203396 : Nat := 13108328552174964684449

theorem tailTrace_6203396 : CollatzResearch.WordTrace tailWord_6203396 prefixEnd_6203396 13108328552174964684449 := by
  unfold tailWord_6203396
  simp only [CollatzResearch.WordTrace]
  refine ⟨113128219917081611267167021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150837626556108815022889361 113128219917081611267167021)
  ·
    refine ⟨42423082468905604225187633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113128219917081611267167021 42423082468905604225187633)
    ·
      refine ⟨31817311851679203168890725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42423082468905604225187633 31817311851679203168890725)
      ·
        refine ⟨5965745972189850594167011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31817311851679203168890725 5965745972189850594167011)
        ·
          refine ⟨8948618958284775891250517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5965745972189850594167011 8948618958284775891250517)
          ·
            refine ⟨13108328552174964684449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8948618958284775891250517 13108328552174964684449)
            ·
              rfl

theorem cell23_6203396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 11].length) (baseStart_6203396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6203396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6203396 prefixEnd_6203396 := by exact prefixLift 6203396
  have htrace : WordTrace (prefixWord ++ tailWord_6203396) baseStart_6203396 baseEnd_6203396 := by
    simpa [prefixWord, tailWord_6203396, baseEnd_6203396] using wordTrace_append hprefix tailTrace_6203396
  have hstable : (prefixWord ++ tailWord_6203396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6203396).length < 2 ^ (prefixWord ++ tailWord_6203396).sum := by decide
  have hdescent : baseEnd_6203396 < baseStart_6203396 := by decide
  rcases family_descends (prefixWord ++ tailWord_6203396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6203406 : List Nat := [4, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3]
def baseStart_6203406 : Nat := 118140960795 + 6203406 * 2 ^ 59
def prefixEnd_6203406 : Nat := 4983230072969 + 3 ^ 40 * 6203406 * 2
def baseEnd_6203406 : Nat := 3185328972985061379196061

theorem tailTrace_6203406 : CollatzResearch.WordTrace tailWord_6203406 prefixEnd_6203406 3185328972985061379196061 := by
  unfold tailWord_6203406
  simp only [CollatzResearch.WordTrace]
  refine ⟨28282100570515874280274759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150837869709417996161465381 28282100570515874280274759)
  ·
    refine ⟨42423150855773811420412139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28282100570515874280274759 42423150855773811420412139)
    ·
      refine ⟨63634726283660717130618209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42423150855773811420412139 63634726283660717130618209)
      ·
        refine ⟨47726044712745537847963657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63634726283660717130618209 47726044712745537847963657)
        ·
          refine ⟨35794533534559153385972743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47726044712745537847963657 35794533534559153385972743)
          ·
            refine ⟨53691800301838730078959115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35794533534559153385972743 53691800301838730078959115)
            ·
              refine ⟨80537700452758095118438673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53691800301838730078959115 80537700452758095118438673)
              ·
                refine ⟨60403275339568571338829005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80537700452758095118438673 60403275339568571338829005)
                ·
                  refine ⟨22651228252338214252060877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60403275339568571338829005 22651228252338214252060877)
                  ·
                    refine ⟨8494210594626830344522829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22651228252338214252060877 8494210594626830344522829)
                    ·
                      refine ⟨3185328972985061379196061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8494210594626830344522829 3185328972985061379196061)
                      ·
                        rfl

theorem cell23_6203406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3].length) (baseStart_6203406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6203406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6203406 prefixEnd_6203406 := by exact prefixLift 6203406
  have htrace : WordTrace (prefixWord ++ tailWord_6203406) baseStart_6203406 baseEnd_6203406 := by
    simpa [prefixWord, tailWord_6203406, baseEnd_6203406] using wordTrace_append hprefix tailTrace_6203406
  have hstable : (prefixWord ++ tailWord_6203406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6203406).length < 2 ^ (prefixWord ++ tailWord_6203406).sum := by decide
  have hdescent : baseEnd_6203406 < baseStart_6203406 := by decide
  rcases family_descends (prefixWord ++ tailWord_6203406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6203413 : List Nat := [1, 3, 2, 1, 6, 1, 1, 8]
def baseStart_6203413 : Nat := 118140960795 + 6203413 * 2 ^ 59
def prefixEnd_6203413 : Nat := 4983230072969 + 3 ^ 40 * 6203413 * 2
def baseEnd_6203413 : Nat := 117975280272208994511427

theorem tailTrace_6203413 : CollatzResearch.WordTrace tailWord_6203413 prefixEnd_6203413 117975280272208994511427 := by
  unfold tailWord_6203413
  simp only [CollatzResearch.WordTrace]
  refine ⟨226257059875101634437702893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150838039916734422958468595 226257059875101634437702893)
  ·
    refine ⟨84846397453163112914138585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226257059875101634437702893 84846397453163112914138585)
    ·
      refine ⟨63634798089872334685603939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84846397453163112914138585 63634798089872334685603939)
      ·
        refine ⟨95452197134808502028405909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63634798089872334685603939 95452197134808502028405909)
        ·
          refine ⟨4474321740694148532581527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 95452197134808502028405909 4474321740694148532581527)
          ·
            refine ⟨6711482611041222798872291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4474321740694148532581527 6711482611041222798872291)
            ·
              refine ⟨10067223916561834198308437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6711482611041222798872291 10067223916561834198308437)
              ·
                refine ⟨117975280272208994511427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10067223916561834198308437 117975280272208994511427)
                ·
                  rfl

theorem cell23_6203413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 8].length) (baseStart_6203413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6203413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6203413 prefixEnd_6203413 := by exact prefixLift 6203413
  have htrace : WordTrace (prefixWord ++ tailWord_6203413) baseStart_6203413 baseEnd_6203413 := by
    simpa [prefixWord, tailWord_6203413, baseEnd_6203413] using wordTrace_append hprefix tailTrace_6203413
  have hstable : (prefixWord ++ tailWord_6203413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6203413).length < 2 ^ (prefixWord ++ tailWord_6203413).sum := by decide
  have hdescent : baseEnd_6203413 < baseStart_6203413 := by decide
  rcases family_descends (prefixWord ++ tailWord_6203413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6203423 : List Nat := [1, 1, 2, 4, 1, 2, 1, 5, 2, 1, 3]
def baseStart_6203423 : Nat := 118140960795 + 6203423 * 2 ^ 59
def prefixEnd_6203423 : Nat := 4983230072969 + 3 ^ 40 * 6203423 * 2
def baseEnd_6203423 : Nat := 3185337702156187812683483

theorem tailTrace_6203423 : CollatzResearch.WordTrace tailWord_6203423 prefixEnd_6203423 3185337702156187812683483 := by
  unfold tailWord_6203423
  simp only [CollatzResearch.WordTrace]
  refine ⟨226257424605065406145566923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150838283070043604097044615 226257424605065406145566923)
  ·
    refine ⟨339386136907598109218350385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226257424605065406145566923 339386136907598109218350385)
    ·
      refine ⟨254539602680698581913762789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 339386136907598109218350385 254539602680698581913762789)
      ·
        refine ⟨47726175502630984108830523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 254539602680698581913762789 47726175502630984108830523)
        ·
          refine ⟨71589263253946476163245785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47726175502630984108830523 71589263253946476163245785)
          ·
            refine ⟨53691947440459857122434339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71589263253946476163245785 53691947440459857122434339)
            ·
              refine ⟨80537921160689785683651509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53691947440459857122434339 80537921160689785683651509)
              ·
                refine ⟨7550430108814667407842329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 80537921160689785683651509 7550430108814667407842329)
                ·
                  refine ⟨5662822581611000555881747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7550430108814667407842329 5662822581611000555881747)
                  ·
                    refine ⟨8494233872416500833822621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5662822581611000555881747 8494233872416500833822621)
                    ·
                      refine ⟨3185337702156187812683483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8494233872416500833822621 3185337702156187812683483)
                      ·
                        rfl

theorem cell23_6203423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 5, 2, 1, 3].length) (baseStart_6203423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6203423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6203423 prefixEnd_6203423 := by exact prefixLift 6203423
  have htrace : WordTrace (prefixWord ++ tailWord_6203423) baseStart_6203423 baseEnd_6203423 := by
    simpa [prefixWord, tailWord_6203423, baseEnd_6203423] using wordTrace_append hprefix tailTrace_6203423
  have hstable : (prefixWord ++ tailWord_6203423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6203423).length < 2 ^ (prefixWord ++ tailWord_6203423).sum := by decide
  have hdescent : baseEnd_6203423 < baseStart_6203423 := by decide
  rcases family_descends (prefixWord ++ tailWord_6203423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6203444 : List Nat := [2, 5, 1, 2, 2, 2, 2, 1, 1, 2, 3]
def baseStart_6203444 : Nat := 118140960795 + 6203444 * 2 ^ 59
def prefixEnd_6203444 : Nat := 4983230072969 + 3 ^ 40 * 6203444 * 2
def baseEnd_6203444 : Nat := 3185348485249932230520887

theorem tailTrace_6203444 : CollatzResearch.WordTrace tailWord_6203444 prefixEnd_6203444 3185348485249932230520887 := by
  unfold tailWord_6203444
  simp only [CollatzResearch.WordTrace]
  refine ⟨113129095268994663366040693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150838793691992884488054257 113129095268994663366040693)
  ·
    refine ⟨10605852681468249690566315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 113129095268994663366040693 10605852681468249690566315)
    ·
      refine ⟨15908779022202374535849473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10605852681468249690566315 15908779022202374535849473)
      ·
        refine ⟨11931584266651780901887105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15908779022202374535849473 11931584266651780901887105)
        ·
          refine ⟨8948688199988835676415329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11931584266651780901887105 8948688199988835676415329)
          ·
            refine ⟨6711516149991626757311497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8948688199988835676415329 6711516149991626757311497)
            ·
              refine ⟨5033637112493720067983623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6711516149991626757311497 5033637112493720067983623)
              ·
                refine ⟨7550455668740580101975435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5033637112493720067983623 7550455668740580101975435)
                ·
                  refine ⟨11325683503110870152963153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7550455668740580101975435 11325683503110870152963153)
                  ·
                    refine ⟨8494262627333152614722365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11325683503110870152963153 8494262627333152614722365)
                    ·
                      refine ⟨3185348485249932230520887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8494262627333152614722365 3185348485249932230520887)
                      ·
                        rfl

theorem cell23_6203444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_6203444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6203444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6203444 prefixEnd_6203444 := by exact prefixLift 6203444
  have htrace : WordTrace (prefixWord ++ tailWord_6203444) baseStart_6203444 baseEnd_6203444 := by
    simpa [prefixWord, tailWord_6203444, baseEnd_6203444] using wordTrace_append hprefix tailTrace_6203444
  have hstable : (prefixWord ++ tailWord_6203444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6203444).length < 2 ^ (prefixWord ++ tailWord_6203444).sum := by decide
  have hdescent : baseEnd_6203444 < baseStart_6203444 := by decide
  rcases family_descends (prefixWord ++ tailWord_6203444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6203457 : List Nat := [1, 2, 5, 1, 2, 3, 1, 2, 2, 1, 3]
def baseStart_6203457 : Nat := 118140960795 + 6203457 * 2 ^ 59
def prefixEnd_6203457 : Nat := 4983230072969 + 3 ^ 40 * 6203457 * 2
def baseEnd_6203457 : Nat := 3185355160498440679658327

theorem tailTrace_6203457 : CollatzResearch.WordTrace tailWord_6203457 prefixEnd_6203457 3185355160498440679658327 := by
  unfold tailWord_6203457
  simp only [CollatzResearch.WordTrace]
  refine ⟨226258664686942229952304625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150839109791294819968203083 226258664686942229952304625)
  ·
    refine ⟨169693998515206672464228469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226258664686942229952304625 169693998515206672464228469)
    ·
      refine ⟨15908812360800625543521419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 169693998515206672464228469 15908812360800625543521419)
      ·
        refine ⟨23863218541200938315282129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15908812360800625543521419 23863218541200938315282129)
        ·
          refine ⟨17897413905900703736461597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23863218541200938315282129 17897413905900703736461597)
          ·
            refine ⟨6711530214712763901173099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17897413905900703736461597 6711530214712763901173099)
            ·
              refine ⟨10067295322069145851759649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6711530214712763901173099 10067295322069145851759649)
              ·
                refine ⟨7550471491551859388819737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10067295322069145851759649 7550471491551859388819737)
                ·
                  refine ⟨5662853618663894541614803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7550471491551859388819737 5662853618663894541614803)
                  ·
                    refine ⟨8494280427995841812422205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5662853618663894541614803 8494280427995841812422205)
                    ·
                      refine ⟨3185355160498440679658327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8494280427995841812422205 3185355160498440679658327)
                      ·
                        rfl

theorem cell23_6203457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_6203457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6203457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6203457 prefixEnd_6203457 := by exact prefixLift 6203457
  have htrace : WordTrace (prefixWord ++ tailWord_6203457) baseStart_6203457 baseEnd_6203457 := by
    simpa [prefixWord, tailWord_6203457, baseEnd_6203457] using wordTrace_append hprefix tailTrace_6203457
  have hstable : (prefixWord ++ tailWord_6203457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6203457).length < 2 ^ (prefixWord ++ tailWord_6203457).sum := by decide
  have hdescent : baseEnd_6203457 < baseStart_6203457 := by decide
  rcases family_descends (prefixWord ++ tailWord_6203457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6203480 : List Nat := [2, 1, 2, 2, 1, 6, 1, 1, 1, 4, 2]
def baseStart_6203480 : Nat := 118140960795 + 6203480 * 2 ^ 59
def prefixEnd_6203480 : Nat := 4983230072969 + 3 ^ 40 * 6203480 * 2
def baseEnd_6203480 : Nat := 3185366970553494089670721

theorem tailTrace_6203480 : CollatzResearch.WordTrace tailWord_6203480 prefixEnd_6203480 3185366970553494089670721 := by
  unfold tailWord_6203480
  simp only [CollatzResearch.WordTrace]
  refine ⟨113129751782929452440195947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150839669043905936586927929 113129751782929452440195947)
  ·
    refine ⟨169694627674394178660293921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113129751782929452440195947 169694627674394178660293921)
    ·
      refine ⟨127270970755795633995220441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169694627674394178660293921 127270970755795633995220441)
      ·
        refine ⟨95453228066846725496415331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127270970755795633995220441 95453228066846725496415331)
        ·
          refine ⟨143179842100270088244622997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95453228066846725496415331 143179842100270088244622997)
          ·
            refine ⟨6711555098450160386466703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 143179842100270088244622997 6711555098450160386466703)
            ·
              refine ⟨10067332647675240579700055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6711555098450160386466703 10067332647675240579700055)
              ·
                refine ⟨15100998971512860869550083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10067332647675240579700055 15100998971512860869550083)
                ·
                  refine ⟨22651498457269291304325125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15100998971512860869550083 22651498457269291304325125)
                  ·
                    refine ⟨4247155960737992119560961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22651498457269291304325125 4247155960737992119560961)
                    ·
                      refine ⟨3185366970553494089670721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4247155960737992119560961 3185366970553494089670721)
                      ·
                        rfl

theorem cell23_6203480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 1, 1, 4, 2].length) (baseStart_6203480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6203480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6203480 prefixEnd_6203480 := by exact prefixLift 6203480
  have htrace : WordTrace (prefixWord ++ tailWord_6203480) baseStart_6203480 baseEnd_6203480 := by
    simpa [prefixWord, tailWord_6203480, baseEnd_6203480] using wordTrace_append hprefix tailTrace_6203480
  have hstable : (prefixWord ++ tailWord_6203480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6203480).length < 2 ^ (prefixWord ++ tailWord_6203480).sum := by decide
  have hdescent : baseEnd_6203480 < baseStart_6203480 := by decide
  rcases family_descends (prefixWord ++ tailWord_6203480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6203503 : List Nat := [1, 1, 2, 1, 3, 4, 3, 3, 5]
def baseStart_6203503 : Nat := 118140960795 + 6203503 * 2 ^ 59
def prefixEnd_6203503 : Nat := 4983230072969 + 3 ^ 40 * 6203503 * 2
def baseEnd_6203503 : Nat := 353930975623171944409235

theorem tailTrace_6203503 : CollatzResearch.WordTrace tailWord_6203503 prefixEnd_6203503 353930975623171944409235 := by
  unfold tailWord_6203503
  simp only [CollatzResearch.WordTrace]
  refine ⟨226260342444775579808479163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150840228296517053205652775 226260342444775579808479163)
  ·
    refine ⟨339390513667163369712718745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226260342444775579808479163 339390513667163369712718745)
    ·
      refine ⟨254542885250372527284539059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 339390513667163369712718745 254542885250372527284539059)
      ·
        refine ⟨381814327875558790926808589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254542885250372527284539059 381814327875558790926808589)
        ·
          refine ⟨143180372953334546597553221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 381814327875558790926808589 143180372953334546597553221)
          ·
            refine ⟨26846319928750227487041229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 143180372953334546597553221 26846319928750227487041229)
            ·
              refine ⟨10067369973281335307640461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26846319928750227487041229 10067369973281335307640461)
              ·
                refine ⟨3775263739980500740365173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10067369973281335307640461 3775263739980500740365173)
                ·
                  refine ⟨353930975623171944409235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3775263739980500740365173 353930975623171944409235)
                  ·
                    rfl

theorem cell23_6203503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 3, 5].length) (baseStart_6203503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6203503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6203503 prefixEnd_6203503 := by exact prefixLift 6203503
  have htrace : WordTrace (prefixWord ++ tailWord_6203503) baseStart_6203503 baseEnd_6203503 := by
    simpa [prefixWord, tailWord_6203503, baseEnd_6203503] using wordTrace_append hprefix tailTrace_6203503
  have hstable : (prefixWord ++ tailWord_6203503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6203503).length < 2 ^ (prefixWord ++ tailWord_6203503).sum := by decide
  have hdescent : baseEnd_6203503 < baseStart_6203503 := by decide
  rcases family_descends (prefixWord ++ tailWord_6203503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6203516 : List Nat := [2, 2, 2, 1, 1, 4, 1, 1, 4, 5]
def baseStart_6203516 : Nat := 118140960795 + 6203516 * 2 ^ 59
def prefixEnd_6203516 : Nat := 4983230072969 + 3 ^ 40 * 6203516 * 2
def baseEnd_6203516 : Nat := 1061795151952351982940185

theorem tailTrace_6203516 : CollatzResearch.WordTrace tailWord_6203516 prefixEnd_6203516 1061795151952351982940185 := by
  unfold tailWord_6203516
  simp only [CollatzResearch.WordTrace]
  refine ⟨113130408296864241514351201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150840544395818988685801601 113130408296864241514351201)
  ·
    refine ⟨84847806222648181135763401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113130408296864241514351201 84847806222648181135763401)
    ·
      refine ⟨63635854666986135851822551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84847806222648181135763401 63635854666986135851822551)
      ·
        refine ⟨95453782000479203777733827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63635854666986135851822551 95453782000479203777733827)
        ·
          refine ⟨143180673000718805666600741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95453782000479203777733827 143180673000718805666600741)
          ·
            refine ⟨26846376187634776062487639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 143180673000718805666600741 26846376187634776062487639)
            ·
              refine ⟨40269564281452164093731459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26846376187634776062487639 40269564281452164093731459)
              ·
                refine ⟨60404346422178246140597189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40269564281452164093731459 60404346422178246140597189)
                ·
                  refine ⟨11325814954158421151361973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60404346422178246140597189 11325814954158421151361973)
                  ·
                    refine ⟨1061795151952351982940185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11325814954158421151361973 1061795151952351982940185)
                    ·
                      rfl

theorem cell23_6203516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 4, 5].length) (baseStart_6203516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6203516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6203516 prefixEnd_6203516 := by exact prefixLift 6203516
  have htrace : WordTrace (prefixWord ++ tailWord_6203516) baseStart_6203516 baseEnd_6203516 := by
    simpa [prefixWord, tailWord_6203516, baseEnd_6203516] using wordTrace_append hprefix tailTrace_6203516
  have hstable : (prefixWord ++ tailWord_6203516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6203516).length < 2 ^ (prefixWord ++ tailWord_6203516).sum := by decide
  have hdescent : baseEnd_6203516 < baseStart_6203516 := by decide
  rcases family_descends (prefixWord ++ tailWord_6203516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6203519 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 8]
def baseStart_6203519 : Nat := 118140960795 + 6203519 * 2 ^ 59
def prefixEnd_6203519 : Nat := 4983230072969 + 3 ^ 40 * 6203519 * 2
def baseEnd_6203519 : Nat := 3185386996299019437083041

theorem tailTrace_6203519 : CollatzResearch.WordTrace tailWord_6203519 prefixEnd_6203519 3185386996299019437083041 := by
  unfold tailWord_6203519
  simp only [CollatzResearch.WordTrace]
  refine ⟨226260926012717614541061611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150840617341811743027374407 226260926012717614541061611)
  ·
    refine ⟨339391389019076421811592417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226260926012717614541061611 339391389019076421811592417)
    ·
      refine ⟨254543541764307316358694313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 339391389019076421811592417 254543541764307316358694313)
      ·
        refine ⟨190907656323230487269020735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 254543541764307316358694313 190907656323230487269020735)
        ·
          refine ⟨286361484484845730903531103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190907656323230487269020735 286361484484845730903531103)
          ·
            refine ⟨429542226727268596355296655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286361484484845730903531103 429542226727268596355296655)
            ·
              refine ⟨644313340090902894532944983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 429542226727268596355296655 644313340090902894532944983)
              ·
                refine ⟨966470010136354341799417475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 644313340090902894532944983 966470010136354341799417475)
                ·
                  refine ⟨1449705015204531512699126213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 966470010136354341799417475 1449705015204531512699126213)
                  ·
                    refine ⟨271819690350849658631086165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1449705015204531512699126213 271819690350849658631086165)
                    ·
                      refine ⟨3185386996299019437083041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 271819690350849658631086165 3185386996299019437083041)
                      ·
                        rfl

theorem cell23_6203519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 8].length) (baseStart_6203519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6203519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6203519 prefixEnd_6203519 := by exact prefixLift 6203519
  have htrace : WordTrace (prefixWord ++ tailWord_6203519) baseStart_6203519 baseEnd_6203519 := by
    simpa [prefixWord, tailWord_6203519, baseEnd_6203519] using wordTrace_append hprefix tailTrace_6203519
  have hstable : (prefixWord ++ tailWord_6203519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6203519).length < 2 ^ (prefixWord ++ tailWord_6203519).sum := by decide
  have hdescent : baseEnd_6203519 < baseStart_6203519 := by decide
  rcases family_descends (prefixWord ++ tailWord_6203519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6203536 : List Nat := [2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 4]
def baseStart_6203536 : Nat := 118140960795 + 6203536 * 2 ^ 59
def prefixEnd_6203536 : Nat := 4983230072969 + 3 ^ 40 * 6203536 * 2
def baseEnd_6203536 : Nat := 3185395725470145870570463

theorem tailTrace_6203536 : CollatzResearch.WordTrace tailWord_6203536 prefixEnd_6203536 3185395725470145870570463 := by
  unfold tailWord_6203536
  simp only [CollatzResearch.WordTrace]
  refine ⟨113130773026828013222215231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150841030702437350962953641 113130773026828013222215231)
  ·
    refine ⟨169696159540242019833322847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113130773026828013222215231 169696159540242019833322847)
    ·
      refine ⟨254544239310363029749984271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169696159540242019833322847 254544239310363029749984271)
      ·
        refine ⟨381816358965544544624976407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254544239310363029749984271 381816358965544544624976407)
        ·
          refine ⟨572724538448316816937464611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 381816358965544544624976407 572724538448316816937464611)
          ·
            refine ⟨859086807672475225406196917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 572724538448316816937464611 859086807672475225406196917)
            ·
              refine ⟨80539388219294552381830961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 859086807672475225406196917 80539388219294552381830961)
              ·
                refine ⟨60404541164470914286373221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80539388219294552381830961 60404541164470914286373221)
                ·
                  refine ⟨11325851468338296428694979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60404541164470914286373221 11325851468338296428694979)
                  ·
                    refine ⟨16988777202507444643042469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11325851468338296428694979 16988777202507444643042469)
                    ·
                      refine ⟨3185395725470145870570463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16988777202507444643042469 3185395725470145870570463)
                      ·
                        rfl

theorem cell23_6203536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 4].length) (baseStart_6203536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6203536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6203536 prefixEnd_6203536 := by exact prefixLift 6203536
  have htrace : WordTrace (prefixWord ++ tailWord_6203536) baseStart_6203536 baseEnd_6203536 := by
    simpa [prefixWord, tailWord_6203536, baseEnd_6203536] using wordTrace_append hprefix tailTrace_6203536
  have hstable : (prefixWord ++ tailWord_6203536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6203536).length < 2 ^ (prefixWord ++ tailWord_6203536).sum := by decide
  have hdescent : baseEnd_6203536 < baseStart_6203536 := by decide
  rcases family_descends (prefixWord ++ tailWord_6203536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6203553 : List Nat := [1, 2, 3, 3, 1, 2, 1, 3, 2, 1, 4]
def baseStart_6203553 : Nat := 118140960795 + 6203553 * 2 ^ 59
def prefixEnd_6203553 : Nat := 4983230072969 + 3 ^ 40 * 6203553 * 2
def baseEnd_6203553 : Nat := 3185404454641272304057885

theorem tailTrace_6203553 : CollatzResearch.WordTrace tailWord_6203553 prefixEnd_6203553 3185404454641272304057885 := by
  unfold tailWord_6203553
  simp only [CollatzResearch.WordTrace]
  refine ⟨226262166094594438347799313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150841444063062958898532875 226262166094594438347799313)
  ·
    refine ⟨169696624570945828760849485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226262166094594438347799313 169696624570945828760849485)
    ·
      refine ⟨63636234214104685785318557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169696624570945828760849485 63636234214104685785318557)
      ·
        refine ⟨23863587830289257169494459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63636234214104685785318557 23863587830289257169494459)
        ·
          refine ⟨35795381745433885754241689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23863587830289257169494459 35795381745433885754241689)
          ·
            refine ⟨26846536309075414315681267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35795381745433885754241689 26846536309075414315681267)
            ·
              refine ⟨40269804463613121473521901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26846536309075414315681267 40269804463613121473521901)
              ·
                refine ⟨15101176673854920552570713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40269804463613121473521901 15101176673854920552570713)
                ·
                  refine ⟨11325882505391190414428035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15101176673854920552570713 11325882505391190414428035)
                  ·
                    refine ⟨16988823758086785621642053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11325882505391190414428035 16988823758086785621642053)
                    ·
                      refine ⟨3185404454641272304057885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16988823758086785621642053 3185404454641272304057885)
                      ·
                        rfl

theorem cell23_6203553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_6203553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6203553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6203553 prefixEnd_6203553 := by exact prefixLift 6203553
  have htrace : WordTrace (prefixWord ++ tailWord_6203553) baseStart_6203553 baseEnd_6203553 := by
    simpa [prefixWord, tailWord_6203553, baseEnd_6203553] using wordTrace_append hprefix tailTrace_6203553
  have hstable : (prefixWord ++ tailWord_6203553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6203553).length < 2 ^ (prefixWord ++ tailWord_6203553).sum := by decide
  have hdescent : baseEnd_6203553 < baseStart_6203553 := by decide
  rcases family_descends (prefixWord ++ tailWord_6203553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6203630 : List Nat := [4, 1, 2, 1, 1, 1, 1, 3, 4, 3, 2]
def baseStart_6203630 : Nat := 118140960795 + 6203630 * 2 ^ 59
def prefixEnd_6203630 : Nat := 4983230072969 + 3 ^ 40 * 6203630 * 2
def baseEnd_6203630 : Nat := 3185443992651668502795031

theorem tailTrace_6203630 : CollatzResearch.WordTrace tailWord_6203630 prefixEnd_6203630 3185443992651668502795031 := by
  unfold tailWord_6203630
  simp only [CollatzResearch.WordTrace]
  refine ⟨28283121814414435062294043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150843316343543653665568229 28283121814414435062294043)
  ·
    refine ⟨42424682721621652593441065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28283121814414435062294043 42424682721621652593441065)
    ·
      refine ⟨31818512041216239445080799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42424682721621652593441065 31818512041216239445080799)
      ·
        refine ⟨47727768061824359167621199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31818512041216239445080799 47727768061824359167621199)
        ·
          refine ⟨71591652092736538751431799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47727768061824359167621199 71591652092736538751431799)
          ·
            refine ⟨107387478139104808127147699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71591652092736538751431799 107387478139104808127147699)
            ·
              refine ⟨161081217208657212190721549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107387478139104808127147699 161081217208657212190721549)
              ·
                refine ⟨60405456453246454571520581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 161081217208657212190721549 60405456453246454571520581)
                ·
                  refine ⟨11326023084983710232160109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60405456453246454571520581 11326023084983710232160109)
                  ·
                    refine ⟨4247258656868891337060041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11326023084983710232160109 4247258656868891337060041)
                    ·
                      refine ⟨3185443992651668502795031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4247258656868891337060041 3185443992651668502795031)
                      ·
                        rfl

theorem cell23_6203630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 4, 3, 2].length) (baseStart_6203630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6203630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6203630 prefixEnd_6203630 := by exact prefixLift 6203630
  have htrace : WordTrace (prefixWord ++ tailWord_6203630) baseStart_6203630 baseEnd_6203630 := by
    simpa [prefixWord, tailWord_6203630, baseEnd_6203630] using wordTrace_append hprefix tailTrace_6203630
  have hstable : (prefixWord ++ tailWord_6203630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6203630).length < 2 ^ (prefixWord ++ tailWord_6203630).sum := by decide
  have hdescent : baseEnd_6203630 < baseStart_6203630 := by decide
  rcases family_descends (prefixWord ++ tailWord_6203630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6203660 : List Nat := [2, 2, 1, 2, 2, 2, 4, 2, 1, 1, 4]
def baseStart_6203660 : Nat := 118140960795 + 6203660 * 2 ^ 59
def prefixEnd_6203660 : Nat := 4983230072969 + 3 ^ 40 * 6203660 * 2
def baseEnd_6203660 : Nat := 3185459397071303385419893

theorem tailTrace_6203660 : CollatzResearch.WordTrace tailWord_6203660 prefixEnd_6203660 3185459397071303385419893 := by
  unfold tailWord_6203660
  simp only [CollatzResearch.WordTrace]
  refine ⟨113133034352603397810972217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150844045803471197081296289 113133034352603397810972217)
  ·
    refine ⟨84849775764452548358229163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113133034352603397810972217 84849775764452548358229163)
    ·
      refine ⟨127274663646678822537343745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84849775764452548358229163 127274663646678822537343745)
      ·
        refine ⟨95455997735009116903007809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127274663646678822537343745 95455997735009116903007809)
        ·
          refine ⟨71591998301256837677255857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95455997735009116903007809 71591998301256837677255857)
          ·
            refine ⟨53693998725942628257941893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71591998301256837677255857 53693998725942628257941893)
            ·
              refine ⟨10067624761114242798364105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53693998725942628257941893 10067624761114242798364105)
              ·
                refine ⟨7550718570835682098773079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10067624761114242798364105 7550718570835682098773079)
                ·
                  refine ⟨11326077856253523148159619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7550718570835682098773079 11326077856253523148159619)
                  ·
                    refine ⟨16989116784380284722239429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11326077856253523148159619 16989116784380284722239429)
                    ·
                      refine ⟨3185459397071303385419893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16989116784380284722239429 3185459397071303385419893)
                      ·
                        rfl

theorem cell23_6203660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 2, 1, 1, 4].length) (baseStart_6203660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6203660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6203660 prefixEnd_6203660 := by exact prefixLift 6203660
  have htrace : WordTrace (prefixWord ++ tailWord_6203660) baseStart_6203660 baseEnd_6203660 := by
    simpa [prefixWord, tailWord_6203660, baseEnd_6203660] using wordTrace_append hprefix tailTrace_6203660
  have hstable : (prefixWord ++ tailWord_6203660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6203660).length < 2 ^ (prefixWord ++ tailWord_6203660).sum := by decide
  have hdescent : baseEnd_6203660 < baseStart_6203660 := by decide
  rcases family_descends (prefixWord ++ tailWord_6203660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6203663 : List Nat := [1, 1, 2, 1, 1, 1, 3, 5, 3, 2, 3]
def baseStart_6203663 : Nat := 118140960795 + 6203663 * 2 ^ 59
def prefixEnd_6203663 : Nat := 4983230072969 + 3 ^ 40 * 6203663 * 2
def baseEnd_6203663 : Nat := 3185460937513266873682379

theorem tailTrace_6203663 : CollatzResearch.WordTrace tailWord_6203663 prefixEnd_6203663 3185460937513266873682379 := by
  unfold tailWord_6203663
  simp only [CollatzResearch.WordTrace]
  refine ⟨226266178124195927134303643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150844118749463951422869095 226266178124195927134303643)
  ·
    refine ⟨339399267186293890701455465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226266178124195927134303643 339399267186293890701455465)
    ·
      refine ⟨254549450389720418026091599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 339399267186293890701455465 254549450389720418026091599)
      ·
        refine ⟨381824175584580627039137399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254549450389720418026091599 381824175584580627039137399)
        ·
          refine ⟨572736263376870940558706099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 381824175584580627039137399 572736263376870940558706099)
          ·
            refine ⟨859104395065306410838059149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 572736263376870940558706099 859104395065306410838059149)
            ·
              refine ⟨322164148149489904064272181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 859104395065306410838059149 322164148149489904064272181)
              ·
                refine ⟨30202888889014678506025517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 322164148149489904064272181 30202888889014678506025517)
                ·
                  refine ⟨11326083333380504439759569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30202888889014678506025517 11326083333380504439759569)
                  ·
                    refine ⟨8494562500035378329819677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11326083333380504439759569 8494562500035378329819677)
                    ·
                      refine ⟨3185460937513266873682379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8494562500035378329819677 3185460937513266873682379)
                      ·
                        rfl

theorem cell23_6203663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 5, 3, 2, 3].length) (baseStart_6203663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6203663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6203663 prefixEnd_6203663 := by exact prefixLift 6203663
  have htrace : WordTrace (prefixWord ++ tailWord_6203663) baseStart_6203663 baseEnd_6203663 := by
    simpa [prefixWord, tailWord_6203663, baseEnd_6203663] using wordTrace_append hprefix tailTrace_6203663
  have hstable : (prefixWord ++ tailWord_6203663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6203663).length < 2 ^ (prefixWord ++ tailWord_6203663).sum := by decide
  have hdescent : baseEnd_6203663 < baseStart_6203663 := by decide
  rcases family_descends (prefixWord ++ tailWord_6203663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6203680 : List Nat := [2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 5]
def baseStart_6203680 : Nat := 118140960795 + 6203680 * 2 ^ 59
def prefixEnd_6203680 : Nat := 4983230072969 + 3 ^ 40 * 6203680 * 2
def baseEnd_6203680 : Nat := 3185469666684393307169801

theorem tailTrace_6203680 : CollatzResearch.WordTrace tailWord_6203680 prefixEnd_6203680 3185469666684393307169801 := by
  unfold tailWord_6203680
  simp only [CollatzResearch.WordTrace]
  refine ⟨113133399082567169518836247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150844532110089559358448329 113133399082567169518836247)
  ·
    refine ⟨169700098623850754278254371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113133399082567169518836247 169700098623850754278254371)
    ·
      refine ⟨254550147935776131417381557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169700098623850754278254371 254550147935776131417381557)
      ·
        refine ⟨23864076368979012320379521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 254550147935776131417381557 23864076368979012320379521)
        ·
          refine ⟨17898057276734259240284641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23864076368979012320379521 17898057276734259240284641)
          ·
            refine ⟨13423542957550694430213481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17898057276734259240284641 13423542957550694430213481)
            ·
              refine ⟨10067657218163020822660111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13423542957550694430213481 10067657218163020822660111)
              ·
                refine ⟨15101485827244531233990167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10067657218163020822660111 15101485827244531233990167)
                ·
                  refine ⟨22652228740866796850985251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15101485827244531233990167 22652228740866796850985251)
                  ·
                    refine ⟨33978343111300195276477877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22652228740866796850985251 33978343111300195276477877)
                    ·
                      refine ⟨3185469666684393307169801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33978343111300195276477877 3185469666684393307169801)
                      ·
                        rfl

theorem cell23_6203680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_6203680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6203680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6203680 prefixEnd_6203680 := by exact prefixLift 6203680
  have htrace : WordTrace (prefixWord ++ tailWord_6203680) baseStart_6203680 baseEnd_6203680 := by
    simpa [prefixWord, tailWord_6203680, baseEnd_6203680] using wordTrace_append hprefix tailTrace_6203680
  have hstable : (prefixWord ++ tailWord_6203680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6203680).length < 2 ^ (prefixWord ++ tailWord_6203680).sum := by decide
  have hdescent : baseEnd_6203680 < baseStart_6203680 := by decide
  rcases family_descends (prefixWord ++ tailWord_6203680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6203700 : List Nat := [2, 5, 1, 1, 1, 3, 2, 8]
def baseStart_6203700 : Nat := 118140960795 + 6203700 * 2 ^ 59
def prefixEnd_6203700 : Nat := 4983230072969 + 3 ^ 40 * 6203700 * 2
def baseEnd_6203700 : Nat := 117980738381388267737767

theorem tailTrace_6203700 : CollatzResearch.WordTrace tailWord_6203700 prefixEnd_6203700 117980738381388267737767 := by
  unfold tailWord_6203700
  simp only [CollatzResearch.WordTrace]
  refine ⟨113133763812530941226700277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150845018416707921635600369 113133763812530941226700277)
  ·
    refine ⟨10606290357424775740003151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 113133763812530941226700277 10606290357424775740003151)
    ·
      refine ⟨15909435536137163610004727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10606290357424775740003151 15909435536137163610004727)
      ·
        refine ⟨23864153304205745415007091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15909435536137163610004727 23864153304205745415007091)
        ·
          refine ⟨35796229956308618122510637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23864153304205745415007091 35796229956308618122510637)
          ·
            refine ⟨13423586233615731795941489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35796229956308618122510637 13423586233615731795941489)
            ·
              refine ⟨10067689675211798846956117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13423586233615731795941489 10067689675211798846956117)
              ·
                refine ⟨117980738381388267737767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10067689675211798846956117 117980738381388267737767)
                ·
                  rfl

theorem cell23_6203700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 8].length) (baseStart_6203700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6203700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6203700 prefixEnd_6203700 := by exact prefixLift 6203700
  have htrace : WordTrace (prefixWord ++ tailWord_6203700) baseStart_6203700 baseEnd_6203700 := by
    simpa [prefixWord, tailWord_6203700, baseEnd_6203700] using wordTrace_append hprefix tailTrace_6203700
  have hstable : (prefixWord ++ tailWord_6203700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6203700).length < 2 ^ (prefixWord ++ tailWord_6203700).sum := by decide
  have hdescent : baseEnd_6203700 < baseStart_6203700 := by decide
  rcases family_descends (prefixWord ++ tailWord_6203700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6203744 : List Nat := [2, 1, 1, 3, 5, 1, 2, 2, 2, 1, 3]
def baseStart_6203744 : Nat := 118140960795 + 6203744 * 2 ^ 59
def prefixEnd_6203744 : Nat := 4983230072969 + 3 ^ 40 * 6203744 * 2
def baseEnd_6203744 : Nat := 3185502529446281056769507

theorem tailTrace_6203744 : CollatzResearch.WordTrace tailWord_6203744 prefixEnd_6203744 3185502529446281056769507 := by
  unfold tailWord_6203744
  simp only [CollatzResearch.WordTrace]
  refine ⟨113134566218451238984001143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150846088291268318645334857 113134566218451238984001143)
  ·
    refine ⟨169701849327676858476001715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113134566218451238984001143 169701849327676858476001715)
    ·
      refine ⟨254552773991515287714002573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169701849327676858476001715 254552773991515287714002573)
      ·
        refine ⟨95457290246818232892750965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 254552773991515287714002573 95457290246818232892750965)
        ·
          refine ⟨8949120960639209333695403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 95457290246818232892750965 8949120960639209333695403)
          ·
            refine ⟨13423681440958814000543105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8949120960639209333695403 13423681440958814000543105)
            ·
              refine ⟨10067761080719110500407329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13423681440958814000543105 10067761080719110500407329)
              ·
                refine ⟨7550820810539332875305497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10067761080719110500407329 7550820810539332875305497)
                ·
                  refine ⟨5663115607904499656479123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7550820810539332875305497 5663115607904499656479123)
                  ·
                    refine ⟨8494673411856749484718685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5663115607904499656479123 8494673411856749484718685)
                    ·
                      refine ⟨3185502529446281056769507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8494673411856749484718685 3185502529446281056769507)
                      ·
                        rfl

theorem cell23_6203744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 2, 2, 1, 3].length) (baseStart_6203744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6203744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6203744 prefixEnd_6203744 := by exact prefixLift 6203744
  have htrace : WordTrace (prefixWord ++ tailWord_6203744) baseStart_6203744 baseEnd_6203744 := by
    simpa [prefixWord, tailWord_6203744, baseEnd_6203744] using wordTrace_append hprefix tailTrace_6203744
  have hstable : (prefixWord ++ tailWord_6203744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6203744).length < 2 ^ (prefixWord ++ tailWord_6203744).sum := by decide
  have hdescent : baseEnd_6203744 < baseStart_6203744 := by decide
  rcases family_descends (prefixWord ++ tailWord_6203744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6203753 : List Nat := [1, 2, 1, 1, 1, 3, 3, 1, 1, 6, 3]
def baseStart_6203753 : Nat := 118140960795 + 6203753 * 2 ^ 59
def prefixEnd_6203753 : Nat := 4983230072969 + 3 ^ 40 * 6203753 * 2
def baseEnd_6203753 : Nat := 3185507150772171521556965

theorem tailTrace_6203753 : CollatzResearch.WordTrace tailWord_6203753 prefixEnd_6203753 3185507150772171521556965 := by
  unfold tailWord_6203753
  simp only [CollatzResearch.WordTrace]
  refine ⟨226269460693869872505079913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150846307129246581670053275 226269460693869872505079913)
  ·
    refine ⟨169702095520402404378809935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226269460693869872505079913 169702095520402404378809935)
    ·
      refine ⟨254553143280603606568214903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169702095520402404378809935 254553143280603606568214903)
      ·
        refine ⟨381829714920905409852322355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254553143280603606568214903 381829714920905409852322355)
        ·
          refine ⟨572744572381358114778483533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 381829714920905409852322355 572744572381358114778483533)
          ·
            refine ⟨214779214643009293041931325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 572744572381358114778483533 214779214643009293041931325)
            ·
              refine ⟨80542205491128484890724247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 214779214643009293041931325 80542205491128484890724247)
              ·
                refine ⟨120813308236692727336086371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80542205491128484890724247 120813308236692727336086371)
                ·
                  refine ⟨181219962355039091004129557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 120813308236692727336086371 181219962355039091004129557)
                  ·
                    refine ⟨8494685735392457390818573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 181219962355039091004129557 8494685735392457390818573)
                    ·
                      refine ⟨3185507150772171521556965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8494685735392457390818573 3185507150772171521556965)
                      ·
                        rfl

theorem cell23_6203753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 6, 3].length) (baseStart_6203753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6203753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6203753 prefixEnd_6203753 := by exact prefixLift 6203753
  have htrace : WordTrace (prefixWord ++ tailWord_6203753) baseStart_6203753 baseEnd_6203753 := by
    simpa [prefixWord, tailWord_6203753, baseEnd_6203753] using wordTrace_append hprefix tailTrace_6203753
  have hstable : (prefixWord ++ tailWord_6203753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6203753).length < 2 ^ (prefixWord ++ tailWord_6203753).sum := by decide
  have hdescent : baseEnd_6203753 < baseStart_6203753 := by decide
  rcases family_descends (prefixWord ++ tailWord_6203753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6203763 : List Nat := [1, 1, 1, 2, 2, 1, 2, 5, 2, 2, 4]
def baseStart_6203763 : Nat := 118140960795 + 6203763 * 2 ^ 59
def prefixEnd_6203763 : Nat := 4983230072969 + 3 ^ 40 * 6203763 * 2
def baseEnd_6203763 : Nat := 3185512285578716482431919

theorem tailTrace_6203763 : CollatzResearch.WordTrace tailWord_6203763 prefixEnd_6203763 3185512285578716482431919 := by
  unfold tailWord_6203763
  simp only [CollatzResearch.WordTrace]
  refine ⟨226269825423833644212943943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150846550282555762808629295 226269825423833644212943943)
  ·
    refine ⟨339404738135750466319415915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226269825423833644212943943 339404738135750466319415915)
    ·
      refine ⟨509107107203625699479123873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339404738135750466319415915 509107107203625699479123873)
      ·
        refine ⟨381830330402719274609342905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 509107107203625699479123873 381830330402719274609342905)
        ·
          refine ⟨286372747802039455957007179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 381830330402719274609342905 286372747802039455957007179)
          ·
            refine ⟨429559121703059183935510769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286372747802039455957007179 429559121703059183935510769)
            ·
              refine ⟨322169341277294387951633077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 429559121703059183935510769 322169341277294387951633077)
              ·
                refine ⟨30203375744746348870465601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 322169341277294387951633077 30203375744746348870465601)
                ·
                  refine ⟨22652531808559761652849201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30203375744746348870465601 22652531808559761652849201)
                  ·
                    refine ⟨16989398856419821239636901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22652531808559761652849201 16989398856419821239636901)
                    ·
                      refine ⟨3185512285578716482431919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16989398856419821239636901 3185512285578716482431919)
                      ·
                        rfl

theorem cell23_6203763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 5, 2, 2, 4].length) (baseStart_6203763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6203763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6203763 prefixEnd_6203763 := by exact prefixLift 6203763
  have htrace : WordTrace (prefixWord ++ tailWord_6203763) baseStart_6203763 baseEnd_6203763 := by
    simpa [prefixWord, tailWord_6203763, baseEnd_6203763] using wordTrace_append hprefix tailTrace_6203763
  have hstable : (prefixWord ++ tailWord_6203763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6203763).length < 2 ^ (prefixWord ++ tailWord_6203763).sum := by decide
  have hdescent : baseEnd_6203763 < baseStart_6203763 := by decide
  rcases family_descends (prefixWord ++ tailWord_6203763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6203773 : List Nat := [1, 4, 1, 1, 2, 3, 1, 1, 9]
def baseStart_6203773 : Nat := 118140960795 + 6203773 * 2 ^ 59
def prefixEnd_6203773 : Nat := 4983230072969 + 3 ^ 40 * 6203773 * 2
def baseEnd_6203773 : Nat := 353946380042806827034097

theorem tailTrace_6203773 : CollatzResearch.WordTrace tailWord_6203773 prefixEnd_6203773 353946380042806827034097 := by
  unfold tailWord_6203773
  simp only [CollatzResearch.WordTrace]
  refine ⟨226270190153797415920807973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150846793435864943947205315 226270190153797415920807973)
  ·
    refine ⟨42425660653837015485151495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 226270190153797415920807973 42425660653837015485151495)
    ·
      refine ⟨63638490980755523227727243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42425660653837015485151495 63638490980755523227727243)
      ·
        refine ⟨95457736471133284841590865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63638490980755523227727243 95457736471133284841590865)
        ·
          refine ⟨71593302353349963631193149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95457736471133284841590865 71593302353349963631193149)
          ·
            refine ⟨26847488382506236361697431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71593302353349963631193149 26847488382506236361697431)
            ·
              refine ⟨40271232573759354542546147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26847488382506236361697431 40271232573759354542546147)
              ·
                refine ⟨60406848860639031813819221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40271232573759354542546147 60406848860639031813819221)
                ·
                  refine ⟨353946380042806827034097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 60406848860639031813819221 353946380042806827034097)
                  ·
                    rfl

theorem cell23_6203773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 9].length) (baseStart_6203773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6203773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6203773 prefixEnd_6203773 := by exact prefixLift 6203773
  have htrace : WordTrace (prefixWord ++ tailWord_6203773) baseStart_6203773 baseEnd_6203773 := by
    simpa [prefixWord, tailWord_6203773, baseEnd_6203773] using wordTrace_append hprefix tailTrace_6203773
  have hstable : (prefixWord ++ tailWord_6203773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6203773).length < 2 ^ (prefixWord ++ tailWord_6203773).sum := by decide
  have hdescent : baseEnd_6203773 < baseStart_6203773 := by decide
  rcases family_descends (prefixWord ++ tailWord_6203773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6203813 : List Nat := [1, 3, 1, 2, 1, 1, 4, 1, 1, 1, 7]
def baseStart_6203813 : Nat := 118140960795 + 6203813 * 2 ^ 59
def prefixEnd_6203813 : Nat := 4983230072969 + 3 ^ 40 * 6203813 * 2
def baseEnd_6203813 : Nat := 3185537959611441286806689

theorem tailTrace_6203813 : CollatzResearch.WordTrace tailWord_6203813 prefixEnd_6203813 3185537959611441286806689 := by
  unfold tailWord_6203813
  simp only [CollatzResearch.WordTrace]
  refine ⟨226271649073652502752264093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150847766049101668501509395 226271649073652502752264093)
  ·
    refine ⟨84851868402619688532099035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226271649073652502752264093 84851868402619688532099035)
    ·
      refine ⟨127277802603929532798148553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84851868402619688532099035 127277802603929532798148553)
      ·
        refine ⟨95458351952947149598611415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127277802603929532798148553 95458351952947149598611415)
        ·
          refine ⟨143187527929420724397917123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95458351952947149598611415 143187527929420724397917123)
          ·
            refine ⟨214781291894131086596875685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143187527929420724397917123 214781291894131086596875685)
            ·
              refine ⟨40271492230149578736914191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 214781291894131086596875685 40271492230149578736914191)
              ·
                refine ⟨60407238345224368105371287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40271492230149578736914191 60407238345224368105371287)
                ·
                  refine ⟨90610857517836552158056931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60407238345224368105371287 90610857517836552158056931)
                  ·
                    refine ⟨135916286276754828237085397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 90610857517836552158056931 135916286276754828237085397)
                    ·
                      refine ⟨3185537959611441286806689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 135916286276754828237085397 3185537959611441286806689)
                      ·
                        rfl

theorem cell23_6203813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 1, 7].length) (baseStart_6203813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6203813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6203813 prefixEnd_6203813 := by exact prefixLift 6203813
  have htrace : WordTrace (prefixWord ++ tailWord_6203813) baseStart_6203813 baseEnd_6203813 := by
    simpa [prefixWord, tailWord_6203813, baseEnd_6203813] using wordTrace_append hprefix tailTrace_6203813
  have hstable : (prefixWord ++ tailWord_6203813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6203813).length < 2 ^ (prefixWord ++ tailWord_6203813).sum := by decide
  have hdescent : baseEnd_6203813 < baseStart_6203813 := by decide
  rcases family_descends (prefixWord ++ tailWord_6203813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6203840 : List Nat := [2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 4]
def baseStart_6203840 : Nat := 118140960795 + 6203840 * 2 ^ 59
def prefixEnd_6203840 : Nat := 4983230072969 + 3 ^ 40 * 6203840 * 2
def baseEnd_6203840 : Nat := 3185551823589112681169065

theorem tailTrace_6203840 : CollatzResearch.WordTrace tailWord_6203840 prefixEnd_6203840 3185551823589112681169065 := by
  unfold tailWord_6203840
  simp only [CollatzResearch.WordTrace]
  refine ⟨113136316922277343181748487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150848422563036457575664649 113136316922277343181748487)
  ·
    refine ⟨169704475383416014772622731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113136316922277343181748487 169704475383416014772622731)
    ·
      refine ⟨254556713075124022158934097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169704475383416014772622731 254556713075124022158934097)
      ·
        refine ⟨190917534806343016619200573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 254556713075124022158934097 190917534806343016619200573)
        ·
          refine ⟨71594075552378631232200215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 190917534806343016619200573 71594075552378631232200215)
          ·
            refine ⟨107391113328567946848300323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71594075552378631232200215 107391113328567946848300323)
            ·
              refine ⟨161086669992851920272450485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107391113328567946848300323 161086669992851920272450485)
              ·
                refine ⟨15101875311829867525542233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 161086669992851920272450485 15101875311829867525542233)
                ·
                  refine ⟨11326406483872400644156675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15101875311829867525542233 11326406483872400644156675)
                  ·
                    refine ⟨16989609725808600966235013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11326406483872400644156675 16989609725808600966235013)
                    ·
                      refine ⟨3185551823589112681169065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16989609725808600966235013 3185551823589112681169065)
                      ·
                        rfl

theorem cell23_6203840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 4].length) (baseStart_6203840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6203840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6203840 prefixEnd_6203840 := by exact prefixLift 6203840
  have htrace : WordTrace (prefixWord ++ tailWord_6203840) baseStart_6203840 baseEnd_6203840 := by
    simpa [prefixWord, tailWord_6203840, baseEnd_6203840] using wordTrace_append hprefix tailTrace_6203840
  have hstable : (prefixWord ++ tailWord_6203840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6203840).length < 2 ^ (prefixWord ++ tailWord_6203840).sum := by decide
  have hdescent : baseEnd_6203840 < baseStart_6203840 := by decide
  rcases family_descends (prefixWord ++ tailWord_6203840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6203843 : List Nat := [1, 1, 1, 3, 1, 1, 3, 2, 2, 3, 5]
def baseStart_6203843 : Nat := 118140960795 + 6203843 * 2 ^ 59
def prefixEnd_6203843 : Nat := 4983230072969 + 3 ^ 40 * 6203843 * 2
def baseEnd_6203843 : Nat := 3185553364031076169431551

theorem tailTrace_6203843 : CollatzResearch.WordTrace tailWord_6203843 prefixEnd_6203843 3185553364031076169431551 := by
  unfold tailWord_6203843
  simp only [CollatzResearch.WordTrace]
  refine ⟨226272743263543817875856183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150848495509029211917237455 226272743263543817875856183)
  ·
    refine ⟨339409114895315726813784275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226272743263543817875856183 339409114895315726813784275)
    ·
      refine ⟨509113672342973590220676413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339409114895315726813784275 509113672342973590220676413)
      ·
        refine ⟨190917627128615096332753655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 509113672342973590220676413 190917627128615096332753655)
        ·
          refine ⟨286376440692922644499130483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190917627128615096332753655 286376440692922644499130483)
          ·
            refine ⟨429564661039383966748695725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286376440692922644499130483 429564661039383966748695725)
            ·
              refine ⟨161086747889768987530760897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 429564661039383966748695725 161086747889768987530760897)
              ·
                refine ⟨120815060917326740648070673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161086747889768987530760897 120815060917326740648070673)
                ·
                  refine ⟨90611295687995055486053005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 120815060917326740648070673 90611295687995055486053005)
                  ·
                    refine ⟨33979235882998145807269877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 90611295687995055486053005 33979235882998145807269877)
                    ·
                      refine ⟨3185553364031076169431551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33979235882998145807269877 3185553364031076169431551)
                      ·
                        rfl

theorem cell23_6203843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 3, 5].length) (baseStart_6203843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6203843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6203843 prefixEnd_6203843 := by exact prefixLift 6203843
  have htrace : WordTrace (prefixWord ++ tailWord_6203843) baseStart_6203843 baseEnd_6203843 := by
    simpa [prefixWord, tailWord_6203843, baseEnd_6203843] using wordTrace_append hprefix tailTrace_6203843
  have hstable : (prefixWord ++ tailWord_6203843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6203843).length < 2 ^ (prefixWord ++ tailWord_6203843).sum := by decide
  have hdescent : baseEnd_6203843 < baseStart_6203843 := by decide
  rcases family_descends (prefixWord ++ tailWord_6203843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6203894 : List Nat := [5, 1, 1, 1, 2, 1, 4, 1, 2, 2, 3]
def baseStart_6203894 : Nat := 118140960795 + 6203894 * 2 ^ 59
def prefixEnd_6203894 : Nat := 4983230072969 + 3 ^ 40 * 6203894 * 2
def baseEnd_6203894 : Nat := 3185579551544455469893817

theorem tailTrace_6203894 : CollatzResearch.WordTrace tailWord_6203894 prefixEnd_6203894 3185579551544455469893817 := by
  unfold tailWord_6203894
  simp only [CollatzResearch.WordTrace]
  refine ⟨14142162711647440849122671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 150849735590906035723975157 14142162711647440849122671)
  ·
    refine ⟨21213244067471161273684007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14142162711647440849122671 21213244067471161273684007)
    ·
      refine ⟨31819866101206741910526011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21213244067471161273684007 31819866101206741910526011)
      ·
        refine ⟨47729799151810112865789017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31819866101206741910526011 47729799151810112865789017)
        ·
          refine ⟨35797349363857584649341763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47729799151810112865789017 35797349363857584649341763)
          ·
            refine ⟨53696024045786376974012645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35797349363857584649341763 53696024045786376974012645)
            ·
              refine ⟨10068004508584945682627371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53696024045786376974012645 10068004508584945682627371)
              ·
                refine ⟨15102006762877418523941057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10068004508584945682627371 15102006762877418523941057)
                ·
                  refine ⟨11326505072158063892955793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15102006762877418523941057 11326505072158063892955793)
                  ·
                    refine ⟨8494878804118547919716845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11326505072158063892955793 8494878804118547919716845)
                    ·
                      refine ⟨3185579551544455469893817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8494878804118547919716845 3185579551544455469893817)
                      ·
                        rfl

theorem cell23_6203894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 1, 2, 2, 3].length) (baseStart_6203894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6203894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6203894 prefixEnd_6203894 := by exact prefixLift 6203894
  have htrace : WordTrace (prefixWord ++ tailWord_6203894) baseStart_6203894 baseEnd_6203894 := by
    simpa [prefixWord, tailWord_6203894, baseEnd_6203894] using wordTrace_append hprefix tailTrace_6203894
  have hstable : (prefixWord ++ tailWord_6203894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6203894).length < 2 ^ (prefixWord ++ tailWord_6203894).sum := by decide
  have hdescent : baseEnd_6203894 < baseStart_6203894 := by decide
  rcases family_descends (prefixWord ++ tailWord_6203894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6203918 : List Nat := [4, 1, 1, 2, 3, 3, 2, 2, 1, 4]
def baseStart_6203918 : Nat := 118140960795 + 6203918 * 2 ^ 59
def prefixEnd_6203918 : Nat := 4983230072969 + 3 ^ 40 * 6203918 * 2
def baseEnd_6203918 : Nat := 1061863958360054458664569

theorem tailTrace_6203918 : CollatzResearch.WordTrace tailWord_6203918 prefixEnd_6203918 1061863958360054458664569 := by
  unfold tailWord_6203918
  simp only [CollatzResearch.WordTrace]
  refine ⟨28284434842284013210604551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150850319158848070456557605 28284434842284013210604551)
  ·
    refine ⟨42426652263426019815906827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28284434842284013210604551 42426652263426019815906827)
    ·
      refine ⟨63639978395139029723860241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42426652263426019815906827 63639978395139029723860241)
      ·
        refine ⟨47729983796354272292895181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63639978395139029723860241 47729983796354272292895181)
        ·
          refine ⟨17898743923632852109835693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47729983796354272292895181 17898743923632852109835693)
          ·
            refine ⟨6712028971362319541188385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17898743923632852109835693 6712028971362319541188385)
            ·
              refine ⟨5034021728521739655891289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6712028971362319541188385 5034021728521739655891289)
              ·
                refine ⟨3775516296391304741918467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5034021728521739655891289 3775516296391304741918467)
                ·
                  refine ⟨5663274444586957112877701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3775516296391304741918467 5663274444586957112877701)
                  ·
                    refine ⟨1061863958360054458664569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5663274444586957112877701 1061863958360054458664569)
                    ·
                      rfl

theorem cell23_6203918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 2, 2, 1, 4].length) (baseStart_6203918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6203918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6203918 prefixEnd_6203918 := by exact prefixLift 6203918
  have htrace : WordTrace (prefixWord ++ tailWord_6203918) baseStart_6203918 baseEnd_6203918 := by
    simpa [prefixWord, tailWord_6203918, baseEnd_6203918] using wordTrace_append hprefix tailTrace_6203918
  have hstable : (prefixWord ++ tailWord_6203918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6203918).length < 2 ^ (prefixWord ++ tailWord_6203918).sum := by decide
  have hdescent : baseEnd_6203918 < baseStart_6203918 := by decide
  rcases family_descends (prefixWord ++ tailWord_6203918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6203957 : List Nat := [1, 3, 3, 1, 1, 2, 2, 2, 4, 4]
def baseStart_6203957 : Nat := 118140960795 + 6203957 * 2 ^ 59
def prefixEnd_6203957 : Nat := 4983230072969 + 3 ^ 40 * 6203957 * 2
def baseEnd_6203957 : Nat := 1061870633608562907802009

theorem tailTrace_6203957 : CollatzResearch.WordTrace tailWord_6203957 prefixEnd_6203957 1061870633608562907802009 := by
  unfold tailWord_6203957
  simp only [CollatzResearch.WordTrace]
  refine ⟨226276901185130815345506125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150851267456753876897004083 226276901185130815345506125)
  ·
    refine ⟨84853837944424055754564797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226276901185130815345506125 84853837944424055754564797)
    ·
      refine ⟨31820189229159020907961799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84853837944424055754564797 31820189229159020907961799)
      ·
        refine ⟨47730283843738531361942699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31820189229159020907961799 47730283843738531361942699)
        ·
          refine ⟨71595425765607797042914049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47730283843738531361942699 71595425765607797042914049)
          ·
            refine ⟨53696569324205847782185537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71595425765607797042914049 53696569324205847782185537)
            ·
              refine ⟨40272426993154385836639153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53696569324205847782185537 40272426993154385836639153)
              ·
                refine ⟨30204320244865789377479365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40272426993154385836639153 30204320244865789377479365)
                ·
                  refine ⟨5663310045912335508277381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30204320244865789377479365 5663310045912335508277381)
                  ·
                    refine ⟨1061870633608562907802009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5663310045912335508277381 1061870633608562907802009)
                    ·
                      rfl

theorem cell23_6203957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 2, 4, 4].length) (baseStart_6203957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6203957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6203957 prefixEnd_6203957 := by exact prefixLift 6203957
  have htrace : WordTrace (prefixWord ++ tailWord_6203957) baseStart_6203957 baseEnd_6203957 := by
    simpa [prefixWord, tailWord_6203957, baseEnd_6203957] using wordTrace_append hprefix tailTrace_6203957
  have hstable : (prefixWord ++ tailWord_6203957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6203957).length < 2 ^ (prefixWord ++ tailWord_6203957).sum := by decide
  have hdescent : baseEnd_6203957 < baseStart_6203957 := by decide
  rcases family_descends (prefixWord ++ tailWord_6203957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6203958 : List Nat := [5, 1, 2, 1, 2, 1, 1, 5, 1, 1, 3]
def baseStart_6203958 : Nat := 118140960795 + 6203958 * 2 ^ 59
def prefixEnd_6203958 : Nat := 4983230072969 + 3 ^ 40 * 6203958 * 2
def baseEnd_6203958 : Nat := 3185612414306343219493523

theorem tailTrace_6203958 : CollatzResearch.WordTrace tailWord_6203958 prefixEnd_6203958 3185612414306343219493523 := by
  unfold tailWord_6203958
  simp only [CollatzResearch.WordTrace]
  refine ⟨14142308603632949532268283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 150851291772084795010861685 14142308603632949532268283)
  ·
    refine ⟨21213462905449424298402425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14142308603632949532268283 21213462905449424298402425)
    ·
      refine ⟨15910097179087068223801819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21213462905449424298402425 15910097179087068223801819)
      ·
        refine ⟨23865145768630602335702729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15910097179087068223801819 23865145768630602335702729)
        ·
          refine ⟨17898859326472951751777047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23865145768630602335702729 17898859326472951751777047)
          ·
            refine ⟨26848288989709427627665571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17898859326472951751777047 26848288989709427627665571)
            ·
              refine ⟨40272433484564141441498357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26848288989709427627665571 40272433484564141441498357)
              ·
                refine ⟨3775540639177888260140471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40272433484564141441498357 3775540639177888260140471)
                ·
                  refine ⟨5663310958766832390210707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3775540639177888260140471 5663310958766832390210707)
                  ·
                    refine ⟨8494966438150248585316061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5663310958766832390210707 8494966438150248585316061)
                    ·
                      refine ⟨3185612414306343219493523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8494966438150248585316061 3185612414306343219493523)
                      ·
                        rfl

theorem cell23_6203958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 5, 1, 1, 3].length) (baseStart_6203958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6203958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6203958 prefixEnd_6203958 := by exact prefixLift 6203958
  have htrace : WordTrace (prefixWord ++ tailWord_6203958) baseStart_6203958 baseEnd_6203958 := by
    simpa [prefixWord, tailWord_6203958, baseEnd_6203958] using wordTrace_append hprefix tailTrace_6203958
  have hstable : (prefixWord ++ tailWord_6203958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6203958).length < 2 ^ (prefixWord ++ tailWord_6203958).sum := by decide
  have hdescent : baseEnd_6203958 < baseStart_6203958 := by decide
  rcases family_descends (prefixWord ++ tailWord_6203958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6203964 : List Nat := [2, 2, 2, 2, 3, 2, 1, 3, 1, 1, 4]
def baseStart_6203964 : Nat := 118140960795 + 6203964 * 2 ^ 59
def prefixEnd_6203964 : Nat := 4983230072969 + 3 ^ 40 * 6203964 * 2
def baseEnd_6203964 : Nat := 3185615495190270196018495

theorem tailTrace_6203964 : CollatzResearch.WordTrace tailWord_6203964 prefixEnd_6203964 3185615495190270196018495 := by
  unfold tailWord_6203964
  simp only [CollatzResearch.WordTrace]
  refine ⟨113138578248052727770505473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150851437664070303694007297 113138578248052727770505473)
  ·
    refine ⟨84853933686039545827879105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113138578248052727770505473 84853933686039545827879105)
    ·
      refine ⟨63640450264529659370909329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84853933686039545827879105 63640450264529659370909329)
      ·
        refine ⟨47730337698397244528181997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63640450264529659370909329 47730337698397244528181997)
        ·
          refine ⟨17898876636898966698068249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47730337698397244528181997 17898876636898966698068249)
          ·
            refine ⟨13424157477674225023551187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17898876636898966698068249 13424157477674225023551187)
            ·
              refine ⟨20136236216511337535326781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13424157477674225023551187 20136236216511337535326781)
              ·
                refine ⟨7551088581191751575747543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20136236216511337535326781 7551088581191751575747543)
                ·
                  refine ⟨11326632871787627363621315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7551088581191751575747543 11326632871787627363621315)
                  ·
                    refine ⟨16989949307681441045431973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11326632871787627363621315 16989949307681441045431973)
                    ·
                      refine ⟨3185615495190270196018495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16989949307681441045431973 3185615495190270196018495)
                      ·
                        rfl

theorem cell23_6203964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 3, 1, 1, 4].length) (baseStart_6203964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6203964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6203964 prefixEnd_6203964 := by exact prefixLift 6203964
  have htrace : WordTrace (prefixWord ++ tailWord_6203964) baseStart_6203964 baseEnd_6203964 := by
    simpa [prefixWord, tailWord_6203964, baseEnd_6203964] using wordTrace_append hprefix tailTrace_6203964
  have hstable : (prefixWord ++ tailWord_6203964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6203964).length < 2 ^ (prefixWord ++ tailWord_6203964).sum := by decide
  have hdescent : baseEnd_6203964 < baseStart_6203964 := by decide
  rcases family_descends (prefixWord ++ tailWord_6203964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6204000 : List Nat := [2, 1, 1, 3, 2, 1, 2, 2, 2, 7]
def baseStart_6204000 : Nat := 118140960795 + 6204000 * 2 ^ 59
def prefixEnd_6204000 : Nat := 4983230072969 + 3 ^ 40 * 6204000 * 2
def baseEnd_6204000 : Nat := 1061877993497944018389443

theorem tailTrace_6204000 : CollatzResearch.WordTrace tailWord_6204000 prefixEnd_6204000 1061877993497944018389443 := by
  unfold tailWord_6204000
  simp only [CollatzResearch.WordTrace]
  refine ⟨113139234761987516844660727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150852313015983355792880969 113139234761987516844660727)
  ·
    refine ⟨169708852142981275266991091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113139234761987516844660727 169708852142981275266991091)
    ·
      refine ⟨254563278214471912900486637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169708852142981275266991091 254563278214471912900486637)
      ·
        refine ⟨95461229330426967337682489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 254563278214471912900486637 95461229330426967337682489)
        ·
          refine ⟨71595921997820225503261867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95461229330426967337682489 71595921997820225503261867)
          ·
            refine ⟨107393882996730338254892801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71595921997820225503261867 107393882996730338254892801)
            ·
              refine ⟨80545412247547753691169601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107393882996730338254892801 80545412247547753691169601)
              ·
                refine ⟨60409059185660815268377201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80545412247547753691169601 60409059185660815268377201)
                ·
                  refine ⟨45306794389245611451282901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60409059185660815268377201 45306794389245611451282901)
                  ·
                    refine ⟨1061877993497944018389443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45306794389245611451282901 1061877993497944018389443)
                    ·
                      rfl

theorem cell23_6204000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 2, 7].length) (baseStart_6204000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6204000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6204000 prefixEnd_6204000 := by exact prefixLift 6204000
  have htrace : WordTrace (prefixWord ++ tailWord_6204000) baseStart_6204000 baseEnd_6204000 := by
    simpa [prefixWord, tailWord_6204000, baseEnd_6204000] using wordTrace_append hprefix tailTrace_6204000
  have hstable : (prefixWord ++ tailWord_6204000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6204000).length < 2 ^ (prefixWord ++ tailWord_6204000).sum := by decide
  have hdescent : baseEnd_6204000 < baseStart_6204000 := by decide
  rcases family_descends (prefixWord ++ tailWord_6204000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6204058 : List Nat := [3, 1, 1, 6, 1, 1, 1, 1, 3, 3, 2]
def baseStart_6204058 : Nat := 118140960795 + 6204058 * 2 ^ 59
def prefixEnd_6204058 : Nat := 4983230072969 + 3 ^ 40 * 6204058 * 2
def baseEnd_6204058 : Nat := 3185663762371792828243063

theorem tailTrace_6204058 : CollatzResearch.WordTrace tailWord_6204058 prefixEnd_6204058 3185663762371792828243063 := by
  unfold tailWord_6204058
  simp only [CollatzResearch.WordTrace]
  refine ⟨56570146239441227398733207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150853723305176606396621885 56570146239441227398733207)
  ·
    refine ⟨84855219359161841098099811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56570146239441227398733207 84855219359161841098099811)
    ·
      refine ⟨127282829038742761647149717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84855219359161841098099811 127282829038742761647149717)
      ·
        refine ⟨5966382611191066952210143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 127282829038742761647149717 5966382611191066952210143)
        ·
          refine ⟨8949573916786600428315215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5966382611191066952210143 8949573916786600428315215)
          ·
            refine ⟨13424360875179900642472823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8949573916786600428315215 13424360875179900642472823)
            ·
              refine ⟨20136541312769850963709235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13424360875179900642472823 20136541312769850963709235)
              ·
                refine ⟨30204811969154776445563853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20136541312769850963709235 30204811969154776445563853)
                ·
                  refine ⟨11326804488433041167086445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30204811969154776445563853 11326804488433041167086445)
                  ·
                    refine ⟨4247551683162390437657417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11326804488433041167086445 4247551683162390437657417)
                    ·
                      refine ⟨3185663762371792828243063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4247551683162390437657417 3185663762371792828243063)
                      ·
                        rfl

theorem cell23_6204058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_6204058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6204058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6204058 prefixEnd_6204058 := by exact prefixLift 6204058
  have htrace : WordTrace (prefixWord ++ tailWord_6204058) baseStart_6204058 baseEnd_6204058 := by
    simpa [prefixWord, tailWord_6204058, baseEnd_6204058] using wordTrace_append hprefix tailTrace_6204058
  have hstable : (prefixWord ++ tailWord_6204058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6204058).length < 2 ^ (prefixWord ++ tailWord_6204058).sum := by decide
  have hdescent : baseEnd_6204058 < baseStart_6204058 := by decide
  rcases family_descends (prefixWord ++ tailWord_6204058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6204104 : List Nat := [2, 1, 3, 1, 2, 4, 1, 1, 2, 3, 3]
def baseStart_6204104 : Nat := 118140960795 + 6204104 * 2 ^ 59
def prefixEnd_6204104 : Nat := 4983230072969 + 3 ^ 40 * 6204104 * 2
def baseEnd_6204104 : Nat := 3185687382481899648267851

theorem tailTrace_6204104 : CollatzResearch.WordTrace tailWord_6204104 prefixEnd_6204104 3185687382481899648267851 := by
  unfold tailWord_6204104
  simp only [CollatzResearch.WordTrace]
  refine ⟨113141131357799129725553683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150854841810398839634071577 113141131357799129725553683)
  ·
    refine ⟨169711697036698694588330525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113141131357799129725553683 169711697036698694588330525)
    ·
      refine ⟨63641886388762010470623947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169711697036698694588330525 63641886388762010470623947)
      ·
        refine ⟨95462829583143015705935921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63641886388762010470623947 95462829583143015705935921)
        ·
          refine ⟨71597122187357261779451941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95462829583143015705935921 71597122187357261779451941)
          ·
            refine ⟨13424460410129486583647239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71597122187357261779451941 13424460410129486583647239)
            ·
              refine ⟨20136690615194229875470859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13424460410129486583647239 20136690615194229875470859)
              ·
                refine ⟨30205035922791344813206289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20136690615194229875470859 30205035922791344813206289)
                ·
                  refine ⟨22653776942093508609904717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30205035922791344813206289 22653776942093508609904717)
                  ·
                    refine ⟨8495166353285065728714269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22653776942093508609904717 8495166353285065728714269)
                    ·
                      refine ⟨3185687382481899648267851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8495166353285065728714269 3185687382481899648267851)
                      ·
                        rfl

theorem cell23_6204104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 1, 2, 3, 3].length) (baseStart_6204104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6204104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6204104 prefixEnd_6204104 := by exact prefixLift 6204104
  have htrace : WordTrace (prefixWord ++ tailWord_6204104) baseStart_6204104 baseEnd_6204104 := by
    simpa [prefixWord, tailWord_6204104, baseEnd_6204104] using wordTrace_append hprefix tailTrace_6204104
  have hstable : (prefixWord ++ tailWord_6204104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6204104).length < 2 ^ (prefixWord ++ tailWord_6204104).sum := by decide
  have hdescent : baseEnd_6204104 < baseStart_6204104 := by decide
  rcases family_descends (prefixWord ++ tailWord_6204104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6204144 : List Nat := [2, 1, 1, 1, 3, 1, 3, 1, 4, 4, 2]
def baseStart_6204144 : Nat := 118140960795 + 6204144 * 2 ^ 59
def prefixEnd_6204144 : Nat := 4983230072969 + 3 ^ 40 * 6204144 * 2
def baseEnd_6204144 : Nat := 3185707921708079491767667

theorem tailTrace_6204144 : CollatzResearch.WordTrace tailWord_6204144 prefixEnd_6204144 3185707921708079491767667 := by
  unfold tailWord_6204144
  simp only [CollatzResearch.WordTrace]
  refine ⟨113141860817726673141281743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150855814423635564188375657 113141860817726673141281743)
  ·
    refine ⟨169712791226590009711922615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113141860817726673141281743 169712791226590009711922615)
    ·
      refine ⟨254569186839885014567883923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169712791226590009711922615 254569186839885014567883923)
      ·
        refine ⟨381853780259827521851825885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254569186839885014567883923 381853780259827521851825885)
        ·
          refine ⟨143195167597435320694434707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 381853780259827521851825885 143195167597435320694434707)
          ·
            refine ⟨214792751396152981041652061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143195167597435320694434707 214792751396152981041652061)
            ·
              refine ⟨80547281773557367890619523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 214792751396152981041652061 80547281773557367890619523)
              ·
                refine ⟨120820922660336051835929285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80547281773557367890619523 120820922660336051835929285)
                ·
                  refine ⟨22653922998813009719236741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 120820922660336051835929285 22653922998813009719236741)
                  ·
                    refine ⟨4247610562277439322356889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22653922998813009719236741 4247610562277439322356889)
                    ·
                      refine ⟨3185707921708079491767667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4247610562277439322356889 3185707921708079491767667)
                      ·
                        rfl

theorem cell23_6204144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 4, 4, 2].length) (baseStart_6204144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6204144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6204144 prefixEnd_6204144 := by exact prefixLift 6204144
  have htrace : WordTrace (prefixWord ++ tailWord_6204144) baseStart_6204144 baseEnd_6204144 := by
    simpa [prefixWord, tailWord_6204144, baseEnd_6204144] using wordTrace_append hprefix tailTrace_6204144
  have hstable : (prefixWord ++ tailWord_6204144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6204144).length < 2 ^ (prefixWord ++ tailWord_6204144).sum := by decide
  have hdescent : baseEnd_6204144 < baseStart_6204144 := by decide
  rcases family_descends (prefixWord ++ tailWord_6204144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6204154 : List Nat := [3, 1, 1, 1, 1, 3, 3, 3, 3, 4]
def baseStart_6204154 : Nat := 118140960795 + 6204154 * 2 ^ 59
def prefixEnd_6204154 : Nat := 4983230072969 + 3 ^ 40 * 6204154 * 2
def baseEnd_6204154 : Nat := 1061904352171541484214207

theorem tailTrace_6204154 : CollatzResearch.WordTrace tailWord_6204154 prefixEnd_6204154 1061904352171541484214207 := by
  unfold tailWord_6204154
  simp only [CollatzResearch.WordTrace]
  refine ⟨56571021591354279497606879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150856057576944745326951677 56571021591354279497606879)
  ·
    refine ⟨84856532387031419246410319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56571021591354279497606879 84856532387031419246410319)
    ·
      refine ⟨127284798580547128869615479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84856532387031419246410319 127284798580547128869615479)
      ·
        refine ⟨190927197870820693304423219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127284798580547128869615479 190927197870820693304423219)
        ·
          refine ⟨286390796806231039956634829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190927197870820693304423219 286390796806231039956634829)
          ·
            refine ⟨107396548802336639983738061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 286390796806231039956634829 107396548802336639983738061)
            ·
              refine ⟨40273705800876239993901773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107396548802336639983738061 40273705800876239993901773)
              ·
                refine ⟨15102639675328589997713165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40273705800876239993901773 15102639675328589997713165)
                ·
                  refine ⟨5663489878248221249142437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15102639675328589997713165 5663489878248221249142437)
                  ·
                    refine ⟨1061904352171541484214207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5663489878248221249142437 1061904352171541484214207)
                    ·
                      rfl

theorem cell23_6204154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 3, 3, 4].length) (baseStart_6204154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6204154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6204154 prefixEnd_6204154 := by exact prefixLift 6204154
  have htrace : WordTrace (prefixWord ++ tailWord_6204154) baseStart_6204154 baseEnd_6204154 := by
    simpa [prefixWord, tailWord_6204154, baseEnd_6204154] using wordTrace_append hprefix tailTrace_6204154
  have hstable : (prefixWord ++ tailWord_6204154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6204154).length < 2 ^ (prefixWord ++ tailWord_6204154).sum := by decide
  have hdescent : baseEnd_6204154 < baseStart_6204154 := by decide
  rcases family_descends (prefixWord ++ tailWord_6204154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6204157 : List Nat := [1, 4, 1, 1, 1, 1, 3, 2, 2, 1, 6]
def baseStart_6204157 : Nat := 118140960795 + 6204157 * 2 ^ 59
def prefixEnd_6204157 : Nat := 4983230072969 + 3 ^ 40 * 6204157 * 2
def baseEnd_6204157 : Nat := 3185714596956587940905107

theorem tailTrace_6204157 : CollatzResearch.WordTrace tailWord_6204157 prefixEnd_6204157 3185714596956587940905107 := by
  unfold tailWord_6204157
  simp only [CollatzResearch.WordTrace]
  refine ⟨226284195784406249502786725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150856130522937499668524483 226284195784406249502786725)
  ·
    refine ⟨42428286709576171781772511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 226284195784406249502786725 42428286709576171781772511)
    ·
      refine ⟨63642430064364257672658767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42428286709576171781772511 63642430064364257672658767)
      ·
        refine ⟨95463645096546386508988151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63642430064364257672658767 95463645096546386508988151)
        ·
          refine ⟨143195467644819579763482227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95463645096546386508988151 143195467644819579763482227)
          ·
            refine ⟨214793201467229369645223341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143195467644819579763482227 214793201467229369645223341)
            ·
              refine ⟨80547450550211013616958753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 214793201467229369645223341 80547450550211013616958753)
              ·
                refine ⟨60410587912658260212719065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80547450550211013616958753 60410587912658260212719065)
                ·
                  refine ⟨45307940934493695159539299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60410587912658260212719065 45307940934493695159539299)
                  ·
                    refine ⟨67961911401740542739308949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45307940934493695159539299 67961911401740542739308949)
                    ·
                      refine ⟨3185714596956587940905107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67961911401740542739308949 3185714596956587940905107)
                      ·
                        rfl

theorem cell23_6204157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 2, 1, 6].length) (baseStart_6204157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6204157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6204157 prefixEnd_6204157 := by exact prefixLift 6204157
  have htrace : WordTrace (prefixWord ++ tailWord_6204157) baseStart_6204157 baseEnd_6204157 := by
    simpa [prefixWord, tailWord_6204157, baseEnd_6204157] using wordTrace_append hprefix tailTrace_6204157
  have hstable : (prefixWord ++ tailWord_6204157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6204157).length < 2 ^ (prefixWord ++ tailWord_6204157).sum := by decide
  have hdescent : baseEnd_6204157 < baseStart_6204157 := by decide
  rcases family_descends (prefixWord ++ tailWord_6204157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6204164 : List Nat := [2, 3, 2, 2, 1, 1, 1, 1, 3, 4, 3]
def baseStart_6204164 : Nat := 118140960795 + 6204164 * 2 ^ 59
def prefixEnd_6204164 : Nat := 4983230072969 + 3 ^ 40 * 6204164 * 2
def baseEnd_6204164 : Nat := 3185718191321169413517575

theorem tailTrace_6204164 : CollatzResearch.WordTrace tailWord_6204164 prefixEnd_6204164 3185718191321169413517575 := by
  unfold tailWord_6204164
  simp only [CollatzResearch.WordTrace]
  refine ⟨113142225547690444849145773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150856300730253926465527697 113142225547690444849145773)
  ·
    refine ⟨42428334580383916818429665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113142225547690444849145773 42428334580383916818429665)
    ·
      refine ⟨31821250935287937613822249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42428334580383916818429665 31821250935287937613822249)
      ·
        refine ⟨23865938201465953210366687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31821250935287937613822249 23865938201465953210366687)
        ·
          refine ⟨35798907302198929815550031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23865938201465953210366687 35798907302198929815550031)
          ·
            refine ⟨53698360953298394723325047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35798907302198929815550031 53698360953298394723325047)
            ·
              refine ⟨80547541429947592084987571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53698360953298394723325047 80547541429947592084987571)
              ·
                refine ⟨120821312144921388127481357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80547541429947592084987571 120821312144921388127481357)
                ·
                  refine ⟨45307992054345520547805509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 120821312144921388127481357 45307992054345520547805509)
                  ·
                    refine ⟨8495248510189785102713533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45307992054345520547805509 8495248510189785102713533)
                    ·
                      refine ⟨3185718191321169413517575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8495248510189785102713533 3185718191321169413517575)
                      ·
                        rfl

theorem cell23_6204164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_6204164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6204164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6204164 prefixEnd_6204164 := by exact prefixLift 6204164
  have htrace : WordTrace (prefixWord ++ tailWord_6204164) baseStart_6204164 baseEnd_6204164 := by
    simpa [prefixWord, tailWord_6204164, baseEnd_6204164] using wordTrace_append hprefix tailTrace_6204164
  have hstable : (prefixWord ++ tailWord_6204164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6204164).length < 2 ^ (prefixWord ++ tailWord_6204164).sum := by decide
  have hdescent : baseEnd_6204164 < baseStart_6204164 := by decide
  rcases family_descends (prefixWord ++ tailWord_6204164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6204188 : List Nat := [2, 2, 3, 1, 1, 3, 3, 3, 1, 4]
def baseStart_6204188 : Nat := 118140960795 + 6204188 * 2 ^ 59
def prefixEnd_6204188 : Nat := 4983230072969 + 3 ^ 40 * 6204188 * 2
def baseEnd_6204188 : Nat := 1061910171618959106539155

theorem tailTrace_6204188 : CollatzResearch.WordTrace tailWord_6204188 prefixEnd_6204188 1061910171618959106539155 := by
  unfold tailWord_6204188
  simp only [CollatzResearch.WordTrace]
  refine ⟨113142663223646970898582609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150856884298195961198110145 113142663223646970898582609)
  ·
    refine ⟨84856997417735228173936957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113142663223646970898582609 84856997417735228173936957)
    ·
      refine ⟨31821374031650710565226359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84856997417735228173936957 31821374031650710565226359)
      ·
        refine ⟨47732061047476065847839539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31821374031650710565226359 47732061047476065847839539)
        ·
          refine ⟨71598091571214098771759309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47732061047476065847839539 71598091571214098771759309)
          ·
            refine ⟨26849284339205287039409741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71598091571214098771759309 26849284339205287039409741)
            ·
              refine ⟨10068481627201982639778653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26849284339205287039409741 10068481627201982639778653)
              ·
                refine ⟨3775680610200743489916995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10068481627201982639778653 3775680610200743489916995)
                ·
                  refine ⟨5663520915301115234875493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3775680610200743489916995 5663520915301115234875493)
                  ·
                    refine ⟨1061910171618959106539155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5663520915301115234875493 1061910171618959106539155)
                    ·
                      rfl

theorem cell23_6204188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 3, 1, 4].length) (baseStart_6204188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6204188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6204188 prefixEnd_6204188 := by exact prefixLift 6204188
  have htrace : WordTrace (prefixWord ++ tailWord_6204188) baseStart_6204188 baseEnd_6204188 := by
    simpa [prefixWord, tailWord_6204188, baseEnd_6204188] using wordTrace_append hprefix tailTrace_6204188
  have hstable : (prefixWord ++ tailWord_6204188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6204188).length < 2 ^ (prefixWord ++ tailWord_6204188).sum := by decide
  have hdescent : baseEnd_6204188 < baseStart_6204188 := by decide
  rcases family_descends (prefixWord ++ tailWord_6204188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6204218 : List Nat := [3, 1, 1, 1, 6, 2, 2, 1, 6]
def baseStart_6204218 : Nat := 118140960795 + 6204218 * 2 ^ 59
def prefixEnd_6204218 : Nat := 4983230072969 + 3 ^ 40 * 6204218 * 2
def baseEnd_6204218 : Nat := 353971768808501355804703

theorem tailTrace_6204218 : CollatzResearch.WordTrace tailWord_6204218 prefixEnd_6204218 353971768808501355804703 := by
  unfold tailWord_6204218
  simp only [CollatzResearch.WordTrace]
  refine ⟨56571605159296314230189327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150857613758123504613838205 56571605159296314230189327)
  ·
    refine ⟨84857407738944471345283991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56571605159296314230189327 84857407738944471345283991)
    ·
      refine ⟨127286111608416707017925987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84857407738944471345283991 127286111608416707017925987)
      ·
        refine ⟨190929167412625060526888981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127286111608416707017925987 190929167412625060526888981)
        ·
          refine ⟨8949804722466799712197921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 190929167412625060526888981 8949804722466799712197921)
          ·
            refine ⟨6712353541850099784148441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8949804722466799712197921 6712353541850099784148441)
            ·
              refine ⟨5034265156387574838111331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6712353541850099784148441 5034265156387574838111331)
              ·
                refine ⟨7551397734581362257166997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5034265156387574838111331 7551397734581362257166997)
                ·
                  refine ⟨353971768808501355804703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7551397734581362257166997 353971768808501355804703)
                  ·
                    rfl

theorem cell23_6204218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 2, 1, 6].length) (baseStart_6204218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6204218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6204218 prefixEnd_6204218 := by exact prefixLift 6204218
  have htrace : WordTrace (prefixWord ++ tailWord_6204218) baseStart_6204218 baseEnd_6204218 := by
    simpa [prefixWord, tailWord_6204218, baseEnd_6204218] using wordTrace_append hprefix tailTrace_6204218
  have hstable : (prefixWord ++ tailWord_6204218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6204218).length < 2 ^ (prefixWord ++ tailWord_6204218).sum := by decide
  have hdescent : baseEnd_6204218 < baseStart_6204218 := by decide
  rcases family_descends (prefixWord ++ tailWord_6204218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6204261 : List Nat := [1, 3, 1, 3, 1, 1, 3, 4, 2, 4]
def baseStart_6204261 : Nat := 118140960795 + 6204261 * 2 ^ 59
def prefixEnd_6204261 : Nat := 4983230072969 + 3 ^ 40 * 6204261 * 2
def baseEnd_6204261 : Nat := 1061922666314885178001543

theorem tailTrace_6204261 : CollatzResearch.WordTrace tailWord_6204261 prefixEnd_6204261 1061922666314885178001543 := by
  unfold tailWord_6204261
  simp only [CollatzResearch.WordTrace]
  refine ⟨226287988976029475264572637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150858659317352983509715091 226287988976029475264572637)
  ·
    refine ⟨84857995866011053224214739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226287988976029475264572637 84857995866011053224214739)
    ·
      refine ⟨127286993799016579836322109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84857995866011053224214739 127286993799016579836322109)
      ·
        refine ⟨47732622674631217438620791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127286993799016579836322109 47732622674631217438620791)
        ·
          refine ⟨71598934011946826157931187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47732622674631217438620791 71598934011946826157931187)
          ·
            refine ⟨107398401017920239236896781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71598934011946826157931187 107398401017920239236896781)
            ·
              refine ⟨40274400381720089713836293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107398401017920239236896781 40274400381720089713836293)
              ·
                refine ⟨7551450071572516821344305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40274400381720089713836293 7551450071572516821344305)
                ·
                  refine ⟨5663587553679387616008229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7551450071572516821344305 5663587553679387616008229)
                  ·
                    refine ⟨1061922666314885178001543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5663587553679387616008229 1061922666314885178001543)
                    ·
                      rfl

theorem cell23_6204261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 4, 2, 4].length) (baseStart_6204261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6204261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6204261 prefixEnd_6204261 := by exact prefixLift 6204261
  have htrace : WordTrace (prefixWord ++ tailWord_6204261) baseStart_6204261 baseEnd_6204261 := by
    simpa [prefixWord, tailWord_6204261, baseEnd_6204261] using wordTrace_append hprefix tailTrace_6204261
  have hstable : (prefixWord ++ tailWord_6204261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6204261).length < 2 ^ (prefixWord ++ tailWord_6204261).sum := by decide
  have hdescent : baseEnd_6204261 < baseStart_6204261 := by decide
  rcases family_descends (prefixWord ++ tailWord_6204261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6204268 : List Nat := [2, 2, 1, 1, 4, 1, 2, 3, 3, 2, 2]
def baseStart_6204268 : Nat := 118140960795 + 6204268 * 2 ^ 59
def prefixEnd_6204268 : Nat := 4983230072969 + 3 ^ 40 * 6204268 * 2
def baseEnd_6204268 : Nat := 3185771593309237006617097

theorem tailTrace_6204268 : CollatzResearch.WordTrace tailWord_6204268 prefixEnd_6204268 3185771593309237006617097 := by
  unfold tailWord_6204268
  simp only [CollatzResearch.WordTrace]
  refine ⟨113144122143502057730038729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150858829524669410306718305 113144122143502057730038729)
  ·
    refine ⟨84858091607626543297529047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113144122143502057730038729 84858091607626543297529047)
    ·
      refine ⟨127287137411439814946293571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84858091607626543297529047 127287137411439814946293571)
      ·
        refine ⟨190930706117159722419440357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127287137411439814946293571 190930706117159722419440357)
        ·
          refine ⟨35799507396967447953645067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 190930706117159722419440357 35799507396967447953645067)
          ·
            refine ⟨53699261095451171930467601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35799507396967447953645067 53699261095451171930467601)
            ·
              refine ⟨40274445821588378947850701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53699261095451171930467601 40274445821588378947850701)
              ·
                refine ⟨15102917183095642105444013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40274445821588378947850701 15102917183095642105444013)
                ·
                  refine ⟨5663593943660865789541505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15102917183095642105444013 5663593943660865789541505)
                  ·
                    refine ⟨4247695457745649342156129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5663593943660865789541505 4247695457745649342156129)
                    ·
                      refine ⟨3185771593309237006617097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4247695457745649342156129 3185771593309237006617097)
                      ·
                        rfl

theorem cell23_6204268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 2, 2].length) (baseStart_6204268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6204268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6204268 prefixEnd_6204268 := by exact prefixLift 6204268
  have htrace : WordTrace (prefixWord ++ tailWord_6204268) baseStart_6204268 baseEnd_6204268 := by
    simpa [prefixWord, tailWord_6204268, baseEnd_6204268] using wordTrace_append hprefix tailTrace_6204268
  have hstable : (prefixWord ++ tailWord_6204268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6204268).length < 2 ^ (prefixWord ++ tailWord_6204268).sum := by decide
  have hdescent : baseEnd_6204268 < baseStart_6204268 := by decide
  rcases family_descends (prefixWord ++ tailWord_6204268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6204274 : List Nat := [3, 2, 1, 2, 1, 1, 5, 8]
def baseStart_6204274 : Nat := 118140960795 + 6204274 * 2 ^ 59
def prefixEnd_6204274 : Nat := 4983230072969 + 3 ^ 40 * 6204274 * 2
def baseEnd_6204274 : Nat := 117991654599746814190447

theorem tailTrace_6204274 : CollatzResearch.WordTrace tailWord_6204274 prefixEnd_6204274 117991654599746814190447 := by
  unfold tailWord_6204274
  simp only [CollatzResearch.WordTrace]
  refine ⟨56572115781245594621198969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150858975416654918989863917 56572115781245594621198969)
  ·
    refine ⟨42429086835934195965899227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56572115781245594621198969 42429086835934195965899227)
    ·
      refine ⟨63643630253901293948848841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42429086835934195965899227 63643630253901293948848841)
      ·
        refine ⟨47732722690425970461636631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63643630253901293948848841 47732722690425970461636631)
        ·
          refine ⟨71599084035638955692454947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47732722690425970461636631 71599084035638955692454947)
          ·
            refine ⟨107398626053458433538682421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71599084035638955692454947 107398626053458433538682421)
            ·
              refine ⟨10068621192511728144251477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 107398626053458433538682421 10068621192511728144251477)
              ·
                refine ⟨117991654599746814190447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10068621192511728144251477 117991654599746814190447)
                ·
                  rfl

theorem cell23_6204274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 8].length) (baseStart_6204274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6204274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6204274 prefixEnd_6204274 := by exact prefixLift 6204274
  have htrace : WordTrace (prefixWord ++ tailWord_6204274) baseStart_6204274 baseEnd_6204274 := by
    simpa [prefixWord, tailWord_6204274, baseEnd_6204274] using wordTrace_append hprefix tailTrace_6204274
  have hstable : (prefixWord ++ tailWord_6204274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6204274).length < 2 ^ (prefixWord ++ tailWord_6204274).sum := by decide
  have hdescent : baseEnd_6204274 < baseStart_6204274 := by decide
  rcases family_descends (prefixWord ++ tailWord_6204274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6204278 : List Nat := [5, 1, 1, 3, 1, 2, 2, 1, 1, 6]
def baseStart_6204278 : Nat := 118140960795 + 6204278 * 2 ^ 59
def prefixEnd_6204278 : Nat := 4983230072969 + 3 ^ 40 * 6204278 * 2
def baseEnd_6204278 : Nat := 1061925576038593989164017

theorem tailTrace_6204278 : CollatzResearch.WordTrace tailWord_6204278 prefixEnd_6204278 1061925576038593989164017 := by
  unfold tailWord_6204278
  simp only [CollatzResearch.WordTrace]
  refine ⟨14143038063560492947996343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 150859072677978591445294325 14143038063560492947996343)
  ·
    refine ⟨21214557095340739421994515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14143038063560492947996343 21214557095340739421994515)
    ·
      refine ⟨31821835643011109132991773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21214557095340739421994515 31821835643011109132991773)
      ·
        refine ⟨11933188366129165924871915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31821835643011109132991773 11933188366129165924871915)
        ·
          refine ⟨17899782549193748887307873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11933188366129165924871915 17899782549193748887307873)
          ·
            refine ⟨13424836911895311665480905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17899782549193748887307873 13424836911895311665480905)
            ·
              refine ⟨10068627683921483749110679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13424836911895311665480905 10068627683921483749110679)
              ·
                refine ⟨15102941525882225623666019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10068627683921483749110679 15102941525882225623666019)
                ·
                  refine ⟨22654412288823338435499029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15102941525882225623666019 22654412288823338435499029)
                  ·
                    refine ⟨1061925576038593989164017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22654412288823338435499029 1061925576038593989164017)
                    ·
                      rfl

theorem cell23_6204278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 1, 1, 6].length) (baseStart_6204278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6204278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6204278 prefixEnd_6204278 := by exact prefixLift 6204278
  have htrace : WordTrace (prefixWord ++ tailWord_6204278) baseStart_6204278 baseEnd_6204278 := by
    simpa [prefixWord, tailWord_6204278, baseEnd_6204278] using wordTrace_append hprefix tailTrace_6204278
  have hstable : (prefixWord ++ tailWord_6204278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6204278).length < 2 ^ (prefixWord ++ tailWord_6204278).sum := by decide
  have hdescent : baseEnd_6204278 < baseStart_6204278 := by decide
  rcases family_descends (prefixWord ++ tailWord_6204278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6204281 : List Nat := [1, 2, 1, 3, 2, 4, 2, 1, 1, 2, 4]
def baseStart_6204281 : Nat := 118140960795 + 6204281 * 2 ^ 59
def prefixEnd_6204281 : Nat := 4983230072969 + 3 ^ 40 * 6204281 * 2
def baseEnd_6204281 : Nat := 3185778268557745455754537

theorem tailTrace_6204281 : CollatzResearch.WordTrace tailWord_6204281 prefixEnd_6204281 3185778268557745455754537 := by
  unfold tailWord_6204281
  simp only [CollatzResearch.WordTrace]
  refine ⟨226288718435957018680300697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150859145623971345786867131 226288718435957018680300697)
  ·
    refine ⟨169716538826967764010225523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226288718435957018680300697 169716538826967764010225523)
    ·
      refine ⟨254574808240451646015338285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169716538826967764010225523 254574808240451646015338285)
      ·
        refine ⟨95465553090169367255751857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 254574808240451646015338285 95465553090169367255751857)
        ·
          refine ⟨71599164817627025441813893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95465553090169367255751857 71599164817627025441813893)
          ·
            refine ⟨13424843403305067270340105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71599164817627025441813893 13424843403305067270340105)
            ·
              refine ⟨10068632552478800452755079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13424843403305067270340105 10068632552478800452755079)
              ·
                refine ⟨15102948828718200679132619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10068632552478800452755079 15102948828718200679132619)
                ·
                  refine ⟨22654423243077301018698929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15102948828718200679132619 22654423243077301018698929)
                  ·
                    refine ⟨16990817432307975764024197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22654423243077301018698929 16990817432307975764024197)
                    ·
                      refine ⟨3185778268557745455754537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16990817432307975764024197 3185778268557745455754537)
                      ·
                        rfl

theorem cell23_6204281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 1, 1, 2, 4].length) (baseStart_6204281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6204281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6204281 prefixEnd_6204281 := by exact prefixLift 6204281
  have htrace : WordTrace (prefixWord ++ tailWord_6204281) baseStart_6204281 baseEnd_6204281 := by
    simpa [prefixWord, tailWord_6204281, baseEnd_6204281] using wordTrace_append hprefix tailTrace_6204281
  have hstable : (prefixWord ++ tailWord_6204281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6204281).length < 2 ^ (prefixWord ++ tailWord_6204281).sum := by decide
  have hdescent : baseEnd_6204281 < baseStart_6204281 := by decide
  rcases family_descends (prefixWord ++ tailWord_6204281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6204345 : List Nat := [1, 2, 1, 4, 2, 3, 2, 2, 1, 3, 2]
def baseStart_6204345 : Nat := 118140960795 + 6204345 * 2 ^ 59
def prefixEnd_6204345 : Nat := 4983230072969 + 3 ^ 40 * 6204345 * 2
def baseEnd_6204345 : Nat := 3185811131319633205354243

theorem tailTrace_6204345 : CollatzResearch.WordTrace tailWord_6204345 prefixEnd_6204345 3185811131319633205354243 := by
  unfold tailWord_6204345
  simp only [CollatzResearch.WordTrace]
  refine ⟨226291052707725157610630489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150860701805150105073753659 226291052707725157610630489)
  ·
    refine ⟨169718289530793868207972867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226291052707725157610630489 169718289530793868207972867)
    ·
      refine ⟨254577434296190802311959301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169718289530793868207972867 254577434296190802311959301)
      ·
        refine ⟨47733268930535775433492369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 254577434296190802311959301 47733268930535775433492369)
        ·
          refine ⟨35799951697901831575119277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47733268930535775433492369 35799951697901831575119277)
          ·
            refine ⟨13424981886713186840669729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35799951697901831575119277 13424981886713186840669729)
            ·
              refine ⟨10068736415034890130502297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13424981886713186840669729 10068736415034890130502297)
              ·
                refine ⟨7551552311276167597876723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10068736415034890130502297 7551552311276167597876723)
                ·
                  refine ⟨11327328466914251396815085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7551552311276167597876723 11327328466914251396815085)
                  ·
                    refine ⟨4247748175092844273805657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11327328466914251396815085 4247748175092844273805657)
                    ·
                      refine ⟨3185811131319633205354243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4247748175092844273805657 3185811131319633205354243)
                      ·
                        rfl

theorem cell23_6204345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 2, 1, 3, 2].length) (baseStart_6204345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6204345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6204345 prefixEnd_6204345 := by exact prefixLift 6204345
  have htrace : WordTrace (prefixWord ++ tailWord_6204345) baseStart_6204345 baseEnd_6204345 := by
    simpa [prefixWord, tailWord_6204345, baseEnd_6204345] using wordTrace_append hprefix tailTrace_6204345
  have hstable : (prefixWord ++ tailWord_6204345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6204345).length < 2 ^ (prefixWord ++ tailWord_6204345).sum := by decide
  have hdescent : baseEnd_6204345 < baseStart_6204345 := by decide
  rcases family_descends (prefixWord ++ tailWord_6204345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6204392 : List Nat := [2, 1, 4, 1, 1, 1, 6, 1, 2, 2, 2]
def baseStart_6204392 : Nat := 118140960795 + 6204392 * 2 ^ 59
def prefixEnd_6204392 : Nat := 4983230072969 + 3 ^ 40 * 6204392 * 2
def baseEnd_6204392 : Nat := 3185835264910394521466527

theorem tailTrace_6204392 : CollatzResearch.WordTrace tailWord_6204392 prefixEnd_6204392 3185835264910394521466527 := by
  unfold tailWord_6204392
  simp only [CollatzResearch.WordTrace]
  refine ⟨113146383469277442318795715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150861844625703256425060953 113146383469277442318795715)
  ·
    refine ⟨169719575203916163478193573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113146383469277442318795715 169719575203916163478193573)
    ·
      refine ⟨31822420350734280652161295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 169719575203916163478193573 31822420350734280652161295)
      ·
        refine ⟨47733630526101420978241943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31822420350734280652161295 47733630526101420978241943)
        ·
          refine ⟨71600445789152131467362915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47733630526101420978241943 71600445789152131467362915)
          ·
            refine ⟨107400668683728197201044373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71600445789152131467362915 107400668683728197201044373)
            ·
              refine ⟨5034406344549759243798955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 107400668683728197201044373 5034406344549759243798955)
              ·
                refine ⟨7551609516824638865698433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5034406344549759243798955 7551609516824638865698433)
                ·
                  refine ⟨5663707137618479149273825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7551609516824638865698433 5663707137618479149273825)
                  ·
                    refine ⟨4247780353213859361955369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5663707137618479149273825 4247780353213859361955369)
                    ·
                      refine ⟨3185835264910394521466527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4247780353213859361955369 3185835264910394521466527)
                      ·
                        rfl

theorem cell23_6204392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 6, 1, 2, 2, 2].length) (baseStart_6204392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6204392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6204392 prefixEnd_6204392 := by exact prefixLift 6204392
  have htrace : WordTrace (prefixWord ++ tailWord_6204392) baseStart_6204392 baseEnd_6204392 := by
    simpa [prefixWord, tailWord_6204392, baseEnd_6204392] using wordTrace_append hprefix tailTrace_6204392
  have hstable : (prefixWord ++ tailWord_6204392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6204392).length < 2 ^ (prefixWord ++ tailWord_6204392).sum := by decide
  have hdescent : baseEnd_6204392 < baseStart_6204392 := by decide
  rcases family_descends (prefixWord ++ tailWord_6204392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6204478 : List Nat := [4, 2, 1, 3, 1, 1, 1, 1, 2, 1, 6]
def baseStart_6204478 : Nat := 118140960795 + 6204478 * 2 ^ 59
def prefixEnd_6204478 : Nat := 4983230072969 + 3 ^ 40 * 6204478 * 2
def baseEnd_6204478 : Nat := 3185879424246681184991131

theorem tailTrace_6204478 : CollatzResearch.WordTrace tailWord_6204478 prefixEnd_6204478 3185879424246681184991131 := by
  unfold tailWord_6204478
  simp only [CollatzResearch.WordTrace]
  refine ⟨28286987952030415165652761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150863935744162214216814725 28286987952030415165652761)
  ·
    refine ⟨21215240964022811374239571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28286987952030415165652761 21215240964022811374239571)
    ·
      refine ⟨31822861446034217061359357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21215240964022811374239571 31822861446034217061359357)
      ·
        refine ⟨11933573042262831398009759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31822861446034217061359357 11933573042262831398009759)
        ·
          refine ⟨17900359563394247097014639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11933573042262831398009759 17900359563394247097014639)
          ·
            refine ⟨26850539345091370645521959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17900359563394247097014639 26850539345091370645521959)
            ·
              refine ⟨40275809017637055968282939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26850539345091370645521959 40275809017637055968282939)
              ·
                refine ⟨60413713526455583952424409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40275809017637055968282939 60413713526455583952424409)
                ·
                  refine ⟨45310285144841687964318307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60413713526455583952424409 45310285144841687964318307)
                  ·
                    refine ⟨67965427717262531946477461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45310285144841687964318307 67965427717262531946477461)
                    ·
                      refine ⟨3185879424246681184991131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67965427717262531946477461 3185879424246681184991131)
                      ·
                        rfl

theorem cell23_6204478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_6204478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6204478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6204478 prefixEnd_6204478 := by exact prefixLift 6204478
  have htrace : WordTrace (prefixWord ++ tailWord_6204478) baseStart_6204478 baseEnd_6204478 := by
    simpa [prefixWord, tailWord_6204478, baseEnd_6204478] using wordTrace_append hprefix tailTrace_6204478
  have hstable : (prefixWord ++ tailWord_6204478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6204478).length < 2 ^ (prefixWord ++ tailWord_6204478).sum := by decide
  have hdescent : baseEnd_6204478 < baseStart_6204478 := by decide
  rcases family_descends (prefixWord ++ tailWord_6204478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6204525 : List Nat := [1, 5, 1, 1, 2, 2, 2, 1, 1, 5, 2]
def baseStart_6204525 : Nat := 118140960795 + 6204525 * 2 ^ 59
def prefixEnd_6204525 : Nat := 4983230072969 + 3 ^ 40 * 6204525 * 2
def baseEnd_6204525 : Nat := 3185903557837442501103415

theorem tailTrace_6204525 : CollatzResearch.WordTrace tailWord_6204525 prefixEnd_6204525 3185903557837442501103415 := by
  unfold tailWord_6204525
  simp only [CollatzResearch.WordTrace]
  refine ⟨226297617847073048352183029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150865078564715365568122019 226297617847073048352183029)
  ·
    refine ⟨21215401673163098283017159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 226297617847073048352183029 21215401673163098283017159)
    ·
      refine ⟨31823102509744647424525739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21215401673163098283017159 31823102509744647424525739)
      ·
        refine ⟨47734653764616971136788609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31823102509744647424525739 47734653764616971136788609)
        ·
          refine ⟨35800990323462728352591457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47734653764616971136788609 35800990323462728352591457)
          ·
            refine ⟨26850742742597046264443593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35800990323462728352591457 26850742742597046264443593)
            ·
              refine ⟨20138057056947784698332695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26850742742597046264443593 20138057056947784698332695)
              ·
                refine ⟨30207085585421677047499043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20138057056947784698332695 30207085585421677047499043)
                ·
                  refine ⟨45310628378132515571248565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30207085585421677047499043 45310628378132515571248565)
                  ·
                    refine ⟨4247871410449923334804553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45310628378132515571248565 4247871410449923334804553)
                    ·
                      refine ⟨3185903557837442501103415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4247871410449923334804553 3185903557837442501103415)
                      ·
                        rfl

theorem cell23_6204525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 1, 1, 5, 2].length) (baseStart_6204525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6204525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6204525 prefixEnd_6204525 := by exact prefixLift 6204525
  have htrace : WordTrace (prefixWord ++ tailWord_6204525) baseStart_6204525 baseEnd_6204525 := by
    simpa [prefixWord, tailWord_6204525, baseEnd_6204525] using wordTrace_append hprefix tailTrace_6204525
  have hstable : (prefixWord ++ tailWord_6204525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6204525).length < 2 ^ (prefixWord ++ tailWord_6204525).sum := by decide
  have hdescent : baseEnd_6204525 < baseStart_6204525 := by decide
  rcases family_descends (prefixWord ++ tailWord_6204525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6204549 : List Nat := [1, 3, 1, 1, 7, 1, 1, 1, 3, 1, 3]
def baseStart_6204549 : Nat := 118140960795 + 6204549 * 2 ^ 59
def prefixEnd_6204549 : Nat := 4983230072969 + 3 ^ 40 * 6204549 * 2
def baseEnd_6204549 : Nat := 3185915881373150407203305

theorem tailTrace_6204549 : CollatzResearch.WordTrace tailWord_6204549 prefixEnd_6204549 3185915881373150407203305 := by
  unfold tailWord_6204549
  simp only [CollatzResearch.WordTrace]
  refine ⟨226298493198986100451056701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150865662132657400300704467 226298493198986100451056701)
  ·
    refine ⟨84861934949619787669146263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226298493198986100451056701 84861934949619787669146263)
    ·
      refine ⟨127292902424429681503719395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84861934949619787669146263 127292902424429681503719395)
      ·
        refine ⟨190939353636644522255579093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127292902424429681503719395 190939353636644522255579093)
        ·
          refine ⟨4475141100858855990365135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 190939353636644522255579093 4475141100858855990365135)
          ·
            refine ⟨6712711651288283985547703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4475141100858855990365135 6712711651288283985547703)
            ·
              refine ⟨10069067476932425978321555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6712711651288283985547703 10069067476932425978321555)
              ·
                refine ⟨15103601215398638967482333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10069067476932425978321555 15103601215398638967482333)
                ·
                  refine ⟨5663850455774489612805875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15103601215398638967482333 5663850455774489612805875)
                  ·
                    refine ⟨8495775683661734419208813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5663850455774489612805875 8495775683661734419208813)
                    ·
                      refine ⟨3185915881373150407203305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8495775683661734419208813 3185915881373150407203305)
                      ·
                        rfl

theorem cell23_6204549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 1, 3, 1, 3].length) (baseStart_6204549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6204549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6204549 prefixEnd_6204549 := by exact prefixLift 6204549
  have htrace : WordTrace (prefixWord ++ tailWord_6204549) baseStart_6204549 baseEnd_6204549 := by
    simpa [prefixWord, tailWord_6204549, baseEnd_6204549] using wordTrace_append hprefix tailTrace_6204549
  have hstable : (prefixWord ++ tailWord_6204549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6204549).length < 2 ^ (prefixWord ++ tailWord_6204549).sum := by decide
  have hdescent : baseEnd_6204549 < baseStart_6204549 := by decide
  rcases family_descends (prefixWord ++ tailWord_6204549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6204568 : List Nat := [2, 1, 2, 4, 2, 1, 2, 1, 1, 1, 6]
def baseStart_6204568 : Nat := 118140960795 + 6204568 * 2 ^ 59
def prefixEnd_6204568 : Nat := 4983230072969 + 3 ^ 40 * 6204568 * 2
def baseEnd_6204568 : Nat := 3185925637505585832865717

theorem tailTrace_6204568 : CollatzResearch.WordTrace tailWord_6204568 prefixEnd_6204568 3185925637505585832865717 := by
  unfold tailWord_6204568
  simp only [CollatzResearch.WordTrace]
  refine ⟨113149593092958633347999179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150866124123944844463998905 113149593092958633347999179)
  ·
    refine ⟨169724389639437950021998769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113149593092958633347999179 169724389639437950021998769)
    ·
      refine ⟨127293292229578462516499077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169724389639437950021998769 127293292229578462516499077)
      ·
        refine ⟨23867492293045961721843577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127293292229578462516499077 23867492293045961721843577)
        ·
          refine ⟨17900619219784471291382683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23867492293045961721843577 17900619219784471291382683)
          ·
            refine ⟨26850928829676706937074025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17900619219784471291382683 26850928829676706937074025)
            ·
              refine ⟨20138196622257530202805519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26850928829676706937074025 20138196622257530202805519)
              ·
                refine ⟨30207294933386295304208279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20138196622257530202805519 30207294933386295304208279)
                ·
                  refine ⟨45310942400079442956312419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30207294933386295304208279 45310942400079442956312419)
                  ·
                    refine ⟨67966413600119164434468629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45310942400079442956312419 67966413600119164434468629)
                    ·
                      refine ⟨3185925637505585832865717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67966413600119164434468629 3185925637505585832865717)
                      ·
                        rfl

theorem cell23_6204568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_6204568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6204568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6204568 prefixEnd_6204568 := by exact prefixLift 6204568
  have htrace : WordTrace (prefixWord ++ tailWord_6204568) baseStart_6204568 baseEnd_6204568 := by
    simpa [prefixWord, tailWord_6204568, baseEnd_6204568] using wordTrace_append hprefix tailTrace_6204568
  have hstable : (prefixWord ++ tailWord_6204568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6204568).length < 2 ^ (prefixWord ++ tailWord_6204568).sum := by decide
  have hdescent : baseEnd_6204568 < baseStart_6204568 := by decide
  rcases family_descends (prefixWord ++ tailWord_6204568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6204572 : List Nat := [2, 2, 3, 2, 1, 4, 1, 2, 1, 1, 4]
def baseStart_6204572 : Nat := 118140960795 + 6204572 * 2 ^ 59
def prefixEnd_6204572 : Nat := 4983230072969 + 3 ^ 40 * 6204572 * 2
def baseEnd_6204572 : Nat := 3185927691428203817215699

theorem tailTrace_6204572 : CollatzResearch.WordTrace tailWord_6204572 prefixEnd_6204572 3185927691428203817215699 := by
  unfold tailWord_6204572
  simp only [CollatzResearch.WordTrace]
  refine ⟨113149666038951387689571985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150866221385268516919429313 113149666038951387689571985)
  ·
    refine ⟨84862249529213540767178989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113149666038951387689571985 84862249529213540767178989)
    ·
      refine ⟨31823343573455077787692121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84862249529213540767178989 31823343573455077787692121)
      ·
        refine ⟨23867507680091308340769091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31823343573455077787692121 23867507680091308340769091)
        ·
          refine ⟨35801261520136962511153637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23867507680091308340769091 35801261520136962511153637)
          ·
            refine ⟨6712736535025680470841307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35801261520136962511153637 6712736535025680470841307)
            ·
              refine ⟨10069104802538520706261961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6712736535025680470841307 10069104802538520706261961)
              ·
                refine ⟨7551828601903890529696471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10069104802538520706261961 7551828601903890529696471)
                ·
                  refine ⟨11327742902855835794544707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7551828601903890529696471 11327742902855835794544707)
                  ·
                    refine ⟨16991614354283753691817061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11327742902855835794544707 16991614354283753691817061)
                    ·
                      refine ⟨3185927691428203817215699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16991614354283753691817061 3185927691428203817215699)
                      ·
                        rfl

theorem cell23_6204572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_6204572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6204572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6204572 prefixEnd_6204572 := by exact prefixLift 6204572
  have htrace : WordTrace (prefixWord ++ tailWord_6204572) baseStart_6204572 baseEnd_6204572 := by
    simpa [prefixWord, tailWord_6204572, baseEnd_6204572] using wordTrace_append hprefix tailTrace_6204572
  have hstable : (prefixWord ++ tailWord_6204572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6204572).length < 2 ^ (prefixWord ++ tailWord_6204572).sum := by decide
  have hdescent : baseEnd_6204572 < baseStart_6204572 := by decide
  rcases family_descends (prefixWord ++ tailWord_6204572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6204589 : List Nat := [1, 5, 2, 1, 3, 1, 3, 1, 1, 1, 4]
def baseStart_6204589 : Nat := 118140960795 + 6204589 * 2 ^ 59
def prefixEnd_6204589 : Nat := 4983230072969 + 3 ^ 40 * 6204589 * 2
def baseEnd_6204589 : Nat := 3185936420599330250703121

theorem tailTrace_6204589 : CollatzResearch.WordTrace tailWord_6204589 prefixEnd_6204589 3185936420599330250703121 := by
  unfold tailWord_6204589
  simp only [CollatzResearch.WordTrace]
  refine ⟨226299952118841187282512821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150866634745894124855008547 226299952118841187282512821)
  ·
    refine ⟨21215620511141361307735577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 226299952118841187282512821 21215620511141361307735577)
    ·
      refine ⟨15911715383356020980801683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21215620511141361307735577 15911715383356020980801683)
      ·
        refine ⟨23867573075034031471202525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15911715383356020980801683 23867573075034031471202525)
        ·
          refine ⟨8950339903137761801700947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23867573075034031471202525 8950339903137761801700947)
          ·
            refine ⟨13425509854706642702551421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8950339903137761801700947 13425509854706642702551421)
            ·
              refine ⟨5034566195514991013456783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13425509854706642702551421 5034566195514991013456783)
              ·
                refine ⟨7551849293272486520185175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5034566195514991013456783 7551849293272486520185175)
                ·
                  refine ⟨11327773939908729780277763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7551849293272486520185175 11327773939908729780277763)
                  ·
                    refine ⟨16991660909863094670416645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11327773939908729780277763 16991660909863094670416645)
                    ·
                      refine ⟨3185936420599330250703121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16991660909863094670416645 3185936420599330250703121)
                      ·
                        rfl

theorem cell23_6204589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 3, 1, 1, 1, 4].length) (baseStart_6204589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6204589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6204589 prefixEnd_6204589 := by exact prefixLift 6204589
  have htrace : WordTrace (prefixWord ++ tailWord_6204589) baseStart_6204589 baseEnd_6204589 := by
    simpa [prefixWord, tailWord_6204589, baseEnd_6204589] using wordTrace_append hprefix tailTrace_6204589
  have hstable : (prefixWord ++ tailWord_6204589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6204589).length < 2 ^ (prefixWord ++ tailWord_6204589).sum := by decide
  have hdescent : baseEnd_6204589 < baseStart_6204589 := by decide
  rcases family_descends (prefixWord ++ tailWord_6204589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6204605 : List Nat := [1, 4, 1, 2, 1, 1, 2, 3, 4, 1, 3]
def baseStart_6204605 : Nat := 118140960795 + 6204605 * 2 ^ 59
def prefixEnd_6204605 : Nat := 4983230072969 + 3 ^ 40 * 6204605 * 2
def baseEnd_6204605 : Nat := 3185944636289802188103047

theorem tailTrace_6204605 : CollatzResearch.WordTrace tailWord_6204605 prefixEnd_6204605 3185944636289802188103047 := by
  unfold tailWord_6204605
  simp only [CollatzResearch.WordTrace]
  refine ⟨226300535686783222015095269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150867023791188814676730179 226300535686783222015095269)
  ·
    refine ⟨42431350441271854127830363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 226300535686783222015095269 42431350441271854127830363)
    ·
      refine ⟨63647025661907781191745545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42431350441271854127830363 63647025661907781191745545)
      ·
        refine ⟨47735269246430835893809159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63647025661907781191745545 47735269246430835893809159)
        ·
          refine ⟨71602903869646253840713739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47735269246430835893809159 71602903869646253840713739)
          ·
            refine ⟨107404355804469380761070609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71602903869646253840713739 107404355804469380761070609)
            ·
              refine ⟨80553266853352035570802957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107404355804469380761070609 80553266853352035570802957)
              ·
                refine ⟨30207475070007013339051109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80553266853352035570802957 30207475070007013339051109)
                ·
                  refine ⟨5663901575626315001072083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30207475070007013339051109 5663901575626315001072083)
                  ·
                    refine ⟨8495852363439472501608125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5663901575626315001072083 8495852363439472501608125)
                    ·
                      refine ⟨3185944636289802188103047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8495852363439472501608125 3185944636289802188103047)
                      ·
                        rfl

theorem cell23_6204605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 3, 4, 1, 3].length) (baseStart_6204605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6204605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6204605 prefixEnd_6204605 := by exact prefixLift 6204605
  have htrace : WordTrace (prefixWord ++ tailWord_6204605) baseStart_6204605 baseEnd_6204605 := by
    simpa [prefixWord, tailWord_6204605, baseEnd_6204605] using wordTrace_append hprefix tailTrace_6204605
  have hstable : (prefixWord ++ tailWord_6204605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6204605).length < 2 ^ (prefixWord ++ tailWord_6204605).sum := by decide
  have hdescent : baseEnd_6204605 < baseStart_6204605 := by decide
  rcases family_descends (prefixWord ++ tailWord_6204605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6204606 : List Nat := [4, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2]
def baseStart_6204606 : Nat := 118140960795 + 6204606 * 2 ^ 59
def prefixEnd_6204606 : Nat := 4983230072969 + 3 ^ 40 * 6204606 * 2
def baseEnd_6204606 : Nat := 3185945149770456684190543

theorem tailTrace_6204606 : CollatzResearch.WordTrace tailWord_6204606 prefixEnd_6204606 3185945149770456684190543 := by
  unfold tailWord_6204606
  simp only [CollatzResearch.WordTrace]
  refine ⟨28287571519972449898235209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150867048106519732790587781 28287571519972449898235209)
  ·
    refine ⟨21215678639979337423676407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28287571519972449898235209 21215678639979337423676407)
    ·
      refine ⟨31823517959969006135514611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21215678639979337423676407 31823517959969006135514611)
      ·
        refine ⟨47735276939953509203271917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31823517959969006135514611 47735276939953509203271917)
        ·
          refine ⟨17900728852482565951226969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47735276939953509203271917 17900728852482565951226969)
          ·
            refine ⟨13425546639361924463420227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17900728852482565951226969 13425546639361924463420227)
            ·
              refine ⟨20138319959042886695130341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13425546639361924463420227 20138319959042886695130341)
              ·
                refine ⟨3775934992320541255336939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20138319959042886695130341 3775934992320541255336939)
                ·
                  refine ⟨5663902488480811883005409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3775934992320541255336939 5663902488480811883005409)
                  ·
                    refine ⟨4247926866360608912254057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5663902488480811883005409 4247926866360608912254057)
                    ·
                      refine ⟨3185945149770456684190543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4247926866360608912254057 3185945149770456684190543)
                      ·
                        rfl

theorem cell23_6204606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2].length) (baseStart_6204606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6204606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6204606 prefixEnd_6204606 := by exact prefixLift 6204606
  have htrace : WordTrace (prefixWord ++ tailWord_6204606) baseStart_6204606 baseEnd_6204606 := by
    simpa [prefixWord, tailWord_6204606, baseEnd_6204606] using wordTrace_append hprefix tailTrace_6204606
  have hstable : (prefixWord ++ tailWord_6204606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6204606).length < 2 ^ (prefixWord ++ tailWord_6204606).sum := by decide
  have hdescent : baseEnd_6204606 < baseStart_6204606 := by decide
  rcases family_descends (prefixWord ++ tailWord_6204606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6204612 : List Nat := [2, 3, 3, 1, 4, 1, 1, 8]
def baseStart_6204612 : Nat := 118140960795 + 6204612 * 2 ^ 59
def prefixEnd_6204612 : Nat := 4983230072969 + 3 ^ 40 * 6204612 * 2
def baseEnd_6204612 : Nat := 117998082616829024470945

theorem tailTrace_6204612 : CollatzResearch.WordTrace tailWord_6204612 prefixEnd_6204612 117998082616829024470945 := by
  unfold tailWord_6204612
  simp only [CollatzResearch.WordTrace]
  refine ⟨113150395498878931105300045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150867193998505241473733393 113150395498878931105300045)
  ·
    refine ⟨42431398312079599164487517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113150395498878931105300045 42431398312079599164487517)
    ·
      refine ⟨15911774367029849686682819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42431398312079599164487517 15911774367029849686682819)
      ·
        refine ⟨23867661550544774530024229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15911774367029849686682819 23867661550544774530024229)
        ·
          refine ⟨4475186540727145224379543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23867661550544774530024229 4475186540727145224379543)
          ·
            refine ⟨6712779811090717836569315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4475186540727145224379543 6712779811090717836569315)
            ·
              refine ⟨10069169716636076754853973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6712779811090717836569315 10069169716636076754853973)
              ·
                refine ⟨117998082616829024470945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10069169716636076754853973 117998082616829024470945)
                ·
                  rfl

theorem cell23_6204612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 8].length) (baseStart_6204612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6204612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6204612 prefixEnd_6204612 := by exact prefixLift 6204612
  have htrace : WordTrace (prefixWord ++ tailWord_6204612) baseStart_6204612 baseEnd_6204612 := by
    simpa [prefixWord, tailWord_6204612, baseEnd_6204612] using wordTrace_append hprefix tailTrace_6204612
  have hstable : (prefixWord ++ tailWord_6204612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6204612).length < 2 ^ (prefixWord ++ tailWord_6204612).sum := by decide
  have hdescent : baseEnd_6204612 < baseStart_6204612 := by decide
  rcases family_descends (prefixWord ++ tailWord_6204612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6204622 : List Nat := [4, 1, 1, 1, 5, 1, 2, 1, 1, 3, 3]
def baseStart_6204622 : Nat := 118140960795 + 6204622 * 2 ^ 59
def prefixEnd_6204622 : Nat := 4983230072969 + 3 ^ 40 * 6204622 * 2
def baseEnd_6204622 : Nat := 3185953365460928621590469

theorem tailTrace_6204622 : CollatzResearch.WordTrace tailWord_6204622 prefixEnd_6204622 3185953365460928621590469 := by
  unfold tailWord_6204622
  simp only [CollatzResearch.WordTrace]
  refine ⟨28287644465965204239808015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150867437151814422612309413 28287644465965204239808015)
  ·
    refine ⟨42431466698947806359712023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28287644465965204239808015 42431466698947806359712023)
    ·
      refine ⟨63647200048421709539568035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42431466698947806359712023 63647200048421709539568035)
      ·
        refine ⟨95470800072632564309352053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63647200048421709539568035 95470800072632564309352053)
        ·
          refine ⟨8950387506809302904001755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 95470800072632564309352053 8950387506809302904001755)
          ·
            refine ⟨13425581260213954356002633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8950387506809302904001755 13425581260213954356002633)
            ·
              refine ⟨10069185945160465767001975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13425581260213954356002633 10069185945160465767001975)
              ·
                refine ⟨15103778917740698650502963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10069185945160465767001975 15103778917740698650502963)
                ·
                  refine ⟨22655668376611047975754445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15103778917740698650502963 22655668376611047975754445)
                  ·
                    refine ⟨8495875641229142990907917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22655668376611047975754445 8495875641229142990907917)
                    ·
                      refine ⟨3185953365460928621590469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8495875641229142990907917 3185953365460928621590469)
                      ·
                        rfl

theorem cell23_6204622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 1, 1, 3, 3].length) (baseStart_6204622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6204622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6204622 prefixEnd_6204622 := by exact prefixLift 6204622
  have htrace : WordTrace (prefixWord ++ tailWord_6204622) baseStart_6204622 baseEnd_6204622 := by
    simpa [prefixWord, tailWord_6204622, baseEnd_6204622] using wordTrace_append hprefix tailTrace_6204622
  have hstable : (prefixWord ++ tailWord_6204622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6204622).length < 2 ^ (prefixWord ++ tailWord_6204622).sum := by decide
  have hdescent : baseEnd_6204622 < baseStart_6204622 := by decide
  rcases family_descends (prefixWord ++ tailWord_6204622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6204648 : List Nat := [2, 1, 4, 1, 2, 1, 2, 1, 1, 3, 5]
def baseStart_6204648 : Nat := 118140960795 + 6204648 * 2 ^ 59
def prefixEnd_6204648 : Nat := 4983230072969 + 3 ^ 40 * 6204648 * 2
def baseEnd_6204648 : Nat := 3185966715957945519865349

theorem tailTrace_6204648 : CollatzResearch.WordTrace tailWord_6204648 prefixEnd_6204648 3185966715957945519865349 := by
  unfold tailWord_6204648
  simp only [CollatzResearch.WordTrace]
  refine ⟨113151052012813720179455299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150868069350418293572607065 113151052012813720179455299)
  ·
    refine ⟨169726578019220580269182949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113151052012813720179455299 169726578019220580269182949)
    ·
      refine ⟨31823733378603858800471803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 169726578019220580269182949 31823733378603858800471803)
      ·
        refine ⟨47735600067905788200707705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31823733378603858800471803 47735600067905788200707705)
        ·
          refine ⟨35801700050929341150530779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47735600067905788200707705 35801700050929341150530779)
          ·
            refine ⟨53702550076394011725796169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35801700050929341150530779 53702550076394011725796169)
            ·
              refine ⟨40276912557295508794347127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53702550076394011725796169 40276912557295508794347127)
              ·
                refine ⟨60415368835943263191520691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40276912557295508794347127 60415368835943263191520691)
                ·
                  refine ⟨90623053253914894787281037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60415368835943263191520691 90623053253914894787281037)
                  ·
                    refine ⟨33983644970218085545230389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 90623053253914894787281037 33983644970218085545230389)
                    ·
                      refine ⟨3185966715957945519865349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33983644970218085545230389 3185966715957945519865349)
                      ·
                        rfl

theorem cell23_6204648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_6204648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6204648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6204648 prefixEnd_6204648 := by exact prefixLift 6204648
  have htrace : WordTrace (prefixWord ++ tailWord_6204648) baseStart_6204648 baseEnd_6204648 := by
    simpa [prefixWord, tailWord_6204648, baseEnd_6204648] using wordTrace_append hprefix tailTrace_6204648
  have hstable : (prefixWord ++ tailWord_6204648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6204648).length < 2 ^ (prefixWord ++ tailWord_6204648).sum := by decide
  have hdescent : baseEnd_6204648 < baseStart_6204648 := by decide
  rcases family_descends (prefixWord ++ tailWord_6204648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6204705 : List Nat := [1, 2, 3, 2, 1, 1, 1, 2, 1, 7, 2]
def baseStart_6204705 : Nat := 118140960795 + 6204705 * 2 ^ 59
def prefixEnd_6204705 : Nat := 4983230072969 + 3 ^ 40 * 6204705 * 2
def baseEnd_6204705 : Nat := 3185995984355251796852587

theorem tailTrace_6204705 : CollatzResearch.WordTrace tailWord_6204705 prefixEnd_6204705 3185995984355251796852587 := by
  unfold tailWord_6204705
  simp only [CollatzResearch.WordTrace]
  refine ⟨226304182986420939093735569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150869455324280626062490379 226304182986420939093735569)
  ·
    refine ⟨169728137239815704320301677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226304182986420939093735569 169728137239815704320301677)
    ·
      refine ⟨63648051464930889120113129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169728137239815704320301677 63648051464930889120113129)
      ·
        refine ⟨47736038598698166840084847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63648051464930889120113129 47736038598698166840084847)
        ·
          refine ⟨71604057898047250260127271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47736038598698166840084847 71604057898047250260127271)
          ·
            refine ⟨107406086847070875390190907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71604057898047250260127271 107406086847070875390190907)
            ·
              refine ⟨161109130270606313085286361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107406086847070875390190907 161109130270606313085286361)
              ·
                refine ⟨120831847702954734813964771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161109130270606313085286361 120831847702954734813964771)
                ·
                  refine ⟨181247771554432102220947157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 120831847702954734813964771 181247771554432102220947157)
                  ·
                    refine ⟨4247994645807002395803449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 181247771554432102220947157 4247994645807002395803449)
                    ·
                      refine ⟨3185995984355251796852587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4247994645807002395803449 3185995984355251796852587)
                      ·
                        rfl

theorem cell23_6204705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 7, 2].length) (baseStart_6204705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6204705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6204705 prefixEnd_6204705 := by exact prefixLift 6204705
  have htrace : WordTrace (prefixWord ++ tailWord_6204705) baseStart_6204705 baseEnd_6204705 := by
    simpa [prefixWord, tailWord_6204705, baseEnd_6204705] using wordTrace_append hprefix tailTrace_6204705
  have hstable : (prefixWord ++ tailWord_6204705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6204705).length < 2 ^ (prefixWord ++ tailWord_6204705).sum := by decide
  have hdescent : baseEnd_6204705 < baseStart_6204705 := by decide
  rcases family_descends (prefixWord ++ tailWord_6204705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6204725 : List Nat := [1, 3, 3, 1, 2, 3, 1, 1, 1, 2, 5]
def baseStart_6204725 : Nat := 118140960795 + 6204725 * 2 ^ 59
def prefixEnd_6204725 : Nat := 4983230072969 + 3 ^ 40 * 6204725 * 2
def baseEnd_6204725 : Nat := 3186006253968341718602495

theorem tailTrace_6204725 : CollatzResearch.WordTrace tailWord_6204725 prefixEnd_6204725 3186006253968341718602495 := by
  unfold tailWord_6204725
  simp only [CollatzResearch.WordTrace]
  refine ⟨226304912446348482509463629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150869941630898988339642419 226304912446348482509463629)
  ·
    refine ⟨84864342167380680941048861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226304912446348482509463629 84864342167380680941048861)
    ·
      refine ⟨31824128312767755352893323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84864342167380680941048861 31824128312767755352893323)
      ·
        refine ⟨47736192469151633029339985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31824128312767755352893323 47736192469151633029339985)
        ·
          refine ⟨35802144351863724772004989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47736192469151633029339985 35802144351863724772004989)
          ·
            refine ⟨13425804131948896789501871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35802144351863724772004989 13425804131948896789501871)
            ·
              refine ⟨20138706197923345184252807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13425804131948896789501871 20138706197923345184252807)
              ·
                refine ⟨30208059296885017776379211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20138706197923345184252807 30208059296885017776379211)
                ·
                  refine ⟨45312088945327526664568817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30208059296885017776379211 45312088945327526664568817)
                  ·
                    refine ⟨33984066708995644998426613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45312088945327526664568817 33984066708995644998426613)
                    ·
                      refine ⟨3186006253968341718602495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33984066708995644998426613 3186006253968341718602495)
                      ·
                        rfl

theorem cell23_6204725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_6204725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6204725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6204725 prefixEnd_6204725 := by exact prefixLift 6204725
  have htrace : WordTrace (prefixWord ++ tailWord_6204725) baseStart_6204725 baseEnd_6204725 := by
    simpa [prefixWord, tailWord_6204725, baseEnd_6204725] using wordTrace_append hprefix tailTrace_6204725
  have hstable : (prefixWord ++ tailWord_6204725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6204725).length < 2 ^ (prefixWord ++ tailWord_6204725).sum := by decide
  have hdescent : baseEnd_6204725 < baseStart_6204725 := by decide
  rcases family_descends (prefixWord ++ tailWord_6204725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
