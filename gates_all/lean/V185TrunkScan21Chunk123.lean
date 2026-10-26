import V185TrunkScan21Chunk122

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1497665 : List Nat := [1, 2, 5, 1, 1, 11]
def baseStart_1497665 : Nat := 118140960795 + 1497665 * 2 ^ 59
def prefixEnd_1497665 : Nat := 4983230072969 + 3 ^ 40 * 1497665 * 2
def baseEnd_1497665 : Nat := 12658798426600627366253

theorem tailTrace_1497665 : CollatzResearch.WordTrace tailWord_1497665 prefixEnd_1497665 12658798426600627366253 := by
  unfold tailWord_1497665
  simp only [CollatzResearch.WordTrace]
  refine ⟨54624330119222960663358449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36416220079481973775572299 54624330119222960663358449)
  ·
    refine ⟨40968247589417220497518837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54624330119222960663358449 40968247589417220497518837)
    ·
      refine ⟨3840773211507864421642391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40968247589417220497518837 3840773211507864421642391)
      ·
        refine ⟨5761159817261796632463587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3840773211507864421642391 5761159817261796632463587)
        ·
          refine ⟨8641739725892694948695381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5761159817261796632463587 8641739725892694948695381)
          ·
            refine ⟨12658798426600627366253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8641739725892694948695381 12658798426600627366253)
            ·
              rfl

theorem cell21_1497665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 11].length) (baseStart_1497665 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1497665 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1497665 prefixEnd_1497665 := by exact prefixLift 1497665
  have htrace : WordTrace (prefixWord ++ tailWord_1497665) baseStart_1497665 baseEnd_1497665 := by
    simpa [prefixWord, tailWord_1497665, baseEnd_1497665] using wordTrace_append hprefix tailTrace_1497665
  have hstable : (prefixWord ++ tailWord_1497665).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497665).length < 2 ^ (prefixWord ++ tailWord_1497665).sum := by decide
  have hdescent : baseEnd_1497665 < baseStart_1497665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497671 : List Nat := [1, 1, 4, 1, 4, 3, 2, 2, 3]
def baseStart_1497671 : Nat := 118140960795 + 1497671 * 2 ^ 59
def prefixEnd_1497671 : Nat := 4983230072969 + 3 ^ 40 * 1497671 * 2
def baseEnd_1497671 : Nat := 341788926799962261788819

theorem tailTrace_1497671 : CollatzResearch.WordTrace tailWord_1497671 prefixEnd_1497671 341788926799962261788819 := by
  unfold tailWord_1497671
  simp only [CollatzResearch.WordTrace]
  refine ⟨54624548957201223688076867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36416365971467482458717911 54624548957201223688076867)
  ·
    refine ⟨81936823435801835532115301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54624548957201223688076867 81936823435801835532115301)
    ·
      refine ⟨15363154394212844162271619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81936823435801835532115301 15363154394212844162271619)
      ·
        refine ⟨23044731591319266243407429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15363154394212844162271619 23044731591319266243407429)
        ·
          refine ⟨4320887173372362420638893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23044731591319266243407429 4320887173372362420638893)
          ·
            refine ⟨1620332690014635907739585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4320887173372362420638893 1620332690014635907739585)
            ·
              refine ⟨1215249517510976930804689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1620332690014635907739585 1215249517510976930804689)
              ·
                refine ⟨911437138133232698103517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1215249517510976930804689 911437138133232698103517)
                ·
                  refine ⟨341788926799962261788819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 911437138133232698103517 341788926799962261788819)
                  ·
                    rfl

theorem cell21_1497671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 2, 2, 3].length) (baseStart_1497671 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1497671 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1497671 prefixEnd_1497671 := by exact prefixLift 1497671
  have htrace : WordTrace (prefixWord ++ tailWord_1497671) baseStart_1497671 baseEnd_1497671 := by
    simpa [prefixWord, tailWord_1497671, baseEnd_1497671] using wordTrace_append hprefix tailTrace_1497671
  have hstable : (prefixWord ++ tailWord_1497671).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497671).length < 2 ^ (prefixWord ++ tailWord_1497671).sum := by decide
  have hdescent : baseEnd_1497671 < baseStart_1497671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497758 : List Nat := [4, 3, 1, 1, 1, 1, 3, 7]
def baseStart_1497758 : Nat := 118140960795 + 1497758 * 2 ^ 59
def prefixEnd_1497758 : Nat := 4983230072969 + 3 ^ 40 * 1497758 * 2
def baseEnd_1497758 : Nat := 113936260461756481279547

theorem tailTrace_1497758 : CollatzResearch.WordTrace tailWord_1497758 prefixEnd_1497758 113936260461756481279547 := by
  unfold tailWord_1497758
  simp only [CollatzResearch.WordTrace]
  refine ⟨6828465263485754693311741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36418481405257358364329285 6828465263485754693311741)
  ·
    refine ⟨2560674473807158009991903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6828465263485754693311741 2560674473807158009991903)
    ·
      refine ⟨3841011710710737014987855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2560674473807158009991903 3841011710710737014987855)
      ·
        refine ⟨5761517566066105522481783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3841011710710737014987855 5761517566066105522481783)
        ·
          refine ⟨8642276349099158283722675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5761517566066105522481783 8642276349099158283722675)
          ·
            refine ⟨12963414523648737425584013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8642276349099158283722675 12963414523648737425584013)
            ·
              refine ⟨4861280446368276534594005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12963414523648737425584013 4861280446368276534594005)
              ·
                refine ⟨113936260461756481279547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4861280446368276534594005 113936260461756481279547)
                ·
                  rfl

theorem cell21_1497758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 7].length) (baseStart_1497758 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1497758 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1497758 prefixEnd_1497758 := by exact prefixLift 1497758
  have htrace : WordTrace (prefixWord ++ tailWord_1497758) baseStart_1497758 baseEnd_1497758 := by
    simpa [prefixWord, tailWord_1497758, baseEnd_1497758] using wordTrace_append hprefix tailTrace_1497758
  have hstable : (prefixWord ++ tailWord_1497758).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497758).length < 2 ^ (prefixWord ++ tailWord_1497758).sum := by decide
  have hdescent : baseEnd_1497758 < baseStart_1497758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497786 : List Nat := [3, 1, 1, 1, 2, 3, 1, 3, 6]
def baseStart_1497786 : Nat := 118140960795 + 1497786 * 2 ^ 59
def prefixEnd_1497786 : Nat := 4983230072969 + 3 ^ 40 * 1497786 * 2
def baseEnd_1497786 : Nat := 341815171366747617371917

theorem tailTrace_1497786 : CollatzResearch.WordTrace tailWord_1497786 prefixEnd_1497786 341815171366747617371917 := by
  unfold tailWord_1497786
  simp only [CollatzResearch.WordTrace]
  refine ⟨13657185837946149582128303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36419162234523065552342141 13657185837946149582128303)
  ·
    refine ⟨20485778756919224373192455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13657185837946149582128303 20485778756919224373192455)
    ·
      refine ⟨30728668135378836559788683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20485778756919224373192455 30728668135378836559788683)
      ·
        refine ⟨46093002203068254839683025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30728668135378836559788683 46093002203068254839683025)
        ·
          refine ⟨34569751652301191129762269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46093002203068254839683025 34569751652301191129762269)
          ·
            refine ⟨12963656869612946673660851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34569751652301191129762269 12963656869612946673660851)
            ·
              refine ⟨19445485304419420010491277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12963656869612946673660851 19445485304419420010491277)
              ·
                refine ⟨7292056989157282503934229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19445485304419420010491277 7292056989157282503934229)
                ·
                  refine ⟨341815171366747617371917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7292056989157282503934229 341815171366747617371917)
                  ·
                    rfl

theorem cell21_1497786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 3, 6].length) (baseStart_1497786 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1497786 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1497786 prefixEnd_1497786 := by exact prefixLift 1497786
  have htrace : WordTrace (prefixWord ++ tailWord_1497786) baseStart_1497786 baseEnd_1497786 := by
    simpa [prefixWord, tailWord_1497786, baseEnd_1497786] using wordTrace_append hprefix tailTrace_1497786
  have hstable : (prefixWord ++ tailWord_1497786).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497786).length < 2 ^ (prefixWord ++ tailWord_1497786).sum := by decide
  have hdescent : baseEnd_1497786 < baseStart_1497786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497789 : List Nat := [1, 4, 1, 2, 1, 5, 1, 1, 5]
def baseStart_1497789 : Nat := 118140960795 + 1497789 * 2 ^ 59
def prefixEnd_1497789 : Nat := 4983230072969 + 3 ^ 40 * 1497789 * 2
def baseEnd_1497789 : Nat := 341815856007620278821911

theorem tailTrace_1497789 : CollatzResearch.WordTrace tailWord_1497789 prefixEnd_1497789 341815856007620278821911 := by
  unfold tailWord_1497789
  simp only [CollatzResearch.WordTrace]
  refine ⟨54628852770773729840872421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36419235180515819893914947 54628852770773729840872421)
  ·
    refine ⟨10242909894520074345163579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54628852770773729840872421 10242909894520074345163579)
    ·
      refine ⟨15364364841780111517745369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10242909894520074345163579 15364364841780111517745369)
      ·
        refine ⟨11523273631335083638309027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15364364841780111517745369 11523273631335083638309027)
        ·
          refine ⟨17284910447002625457463541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11523273631335083638309027 17284910447002625457463541)
          ·
            refine ⟨1620460354406496136637207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17284910447002625457463541 1620460354406496136637207)
            ·
              refine ⟨2430690531609744204955811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1620460354406496136637207 2430690531609744204955811)
              ·
                refine ⟨3646035797414616307433717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2430690531609744204955811 3646035797414616307433717)
                ·
                  refine ⟨341815856007620278821911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3646035797414616307433717 341815856007620278821911)
                  ·
                    rfl

theorem cell21_1497789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 1, 5].length) (baseStart_1497789 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1497789 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1497789 prefixEnd_1497789 := by exact prefixLift 1497789
  have htrace : WordTrace (prefixWord ++ tailWord_1497789) baseStart_1497789 baseEnd_1497789 := by
    simpa [prefixWord, tailWord_1497789, baseEnd_1497789] using wordTrace_append hprefix tailTrace_1497789
  have hstable : (prefixWord ++ tailWord_1497789).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497789).length < 2 ^ (prefixWord ++ tailWord_1497789).sum := by decide
  have hdescent : baseEnd_1497789 < baseStart_1497789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497938 : List Nat := [3, 2, 2, 1, 1, 2, 1, 1, 8]
def baseStart_1497938 : Nat := 118140960795 + 1497938 * 2 ^ 59
def prefixEnd_1497938 : Nat := 4983230072969 + 3 ^ 40 * 1497938 * 2
def baseEnd_1497938 : Nat := 341849859837629130838273

theorem tailTrace_1497938 : CollatzResearch.WordTrace tailWord_1497938 prefixEnd_1497938 341849859837629130838273 := by
  unfold tailWord_1497938
  simp only [CollatzResearch.WordTrace]
  refine ⟨13658571811808482072011617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36422858164822618858697645 13658571811808482072011617)
  ·
    refine ⟨10243928858856361554008713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13658571811808482072011617 10243928858856361554008713)
    ·
      refine ⟨7682946644142271165506535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10243928858856361554008713 7682946644142271165506535)
      ·
        refine ⟨11524419966213406748259803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7682946644142271165506535 11524419966213406748259803)
        ·
          refine ⟨17286629949320110122389705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11524419966213406748259803 17286629949320110122389705)
          ·
            refine ⟨12964972461990082591792279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17286629949320110122389705 12964972461990082591792279)
            ·
              refine ⟨19447458692985123887688419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12964972461990082591792279 19447458692985123887688419)
              ·
                refine ⟨29171188039477685831532629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19447458692985123887688419 29171188039477685831532629)
                ·
                  refine ⟨341849859837629130838273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29171188039477685831532629 341849859837629130838273)
                  ·
                    rfl

theorem cell21_1497938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 8].length) (baseStart_1497938 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1497938 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1497938 prefixEnd_1497938 := by exact prefixLift 1497938
  have htrace : WordTrace (prefixWord ++ tailWord_1497938) baseStart_1497938 baseEnd_1497938 := by
    simpa [prefixWord, tailWord_1497938, baseEnd_1497938] using wordTrace_append hprefix tailTrace_1497938
  have hstable : (prefixWord ++ tailWord_1497938).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497938).length < 2 ^ (prefixWord ++ tailWord_1497938).sum := by decide
  have hdescent : baseEnd_1497938 < baseStart_1497938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497969 : List Nat := [1, 2, 2, 2, 1, 5, 2, 6]
def baseStart_1497969 : Nat := 118140960795 + 1497969 * 2 ^ 59
def prefixEnd_1497969 : Nat := 4983230072969 + 3 ^ 40 * 1497969 * 2
def baseEnd_1497969 : Nat := 113952311486659988607181

theorem tailTrace_1497969 : CollatzResearch.WordTrace tailWord_1497969 prefixEnd_1497969 113952311486659988607181 := by
  unfold tailWord_1497969
  simp only [CollatzResearch.WordTrace]
  refine ⟨54635417910121620582424961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36423611940081080388283307 54635417910121620582424961)
  ·
    refine ⟨40976563432591215436818721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54635417910121620582424961 40976563432591215436818721)
    ·
      refine ⟨30732422574443411577614041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40976563432591215436818721 30732422574443411577614041)
      ·
        refine ⟨23049316930832558683210531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30732422574443411577614041 23049316930832558683210531)
        ·
          refine ⟨34573975396248838024815797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23049316930832558683210531 34573975396248838024815797)
          ·
            refine ⟨3241310193398328564826481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34573975396248838024815797 3241310193398328564826481)
            ·
              refine ⟨2430982645048746423619861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3241310193398328564826481 2430982645048746423619861)
              ·
                refine ⟨113952311486659988607181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2430982645048746423619861 113952311486659988607181)
                ·
                  rfl

theorem cell21_1497969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 6].length) (baseStart_1497969 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1497969 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1497969 prefixEnd_1497969 := by exact prefixLift 1497969
  have htrace : WordTrace (prefixWord ++ tailWord_1497969) baseStart_1497969 baseEnd_1497969 := by
    simpa [prefixWord, tailWord_1497969, baseEnd_1497969] using wordTrace_append hprefix tailTrace_1497969
  have hstable : (prefixWord ++ tailWord_1497969).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497969).length < 2 ^ (prefixWord ++ tailWord_1497969).sum := by decide
  have hdescent : baseEnd_1497969 < baseStart_1497969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497983 : List Nat := [1, 1, 2, 2, 1, 1, 4, 4, 5]
def baseStart_1497983 : Nat := 118140960795 + 1497983 * 2 ^ 59
def prefixEnd_1497983 : Nat := 4983230072969 + 3 ^ 40 * 1497983 * 2
def baseEnd_1497983 : Nat := 341860129450719052588181

theorem tailTrace_1497983 : CollatzResearch.WordTrace tailWord_1497983 prefixEnd_1497983 341860129450719052588181 := by
  unfold tailWord_1497983
  simp only [CollatzResearch.WordTrace]
  refine ⟨54635928532070900973434603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36423952354713933982289735 54635928532070900973434603)
  ·
    refine ⟨81953892798106351460151905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54635928532070900973434603 81953892798106351460151905)
    ·
      refine ⟨61465419598579763595113929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81953892798106351460151905 61465419598579763595113929)
      ·
        refine ⟨46099064698934822696335447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61465419598579763595113929 46099064698934822696335447)
        ·
          refine ⟨69148597048402234044503171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46099064698934822696335447 69148597048402234044503171)
          ·
            refine ⟨103722895572603351066754757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69148597048402234044503171 103722895572603351066754757)
            ·
              refine ⟨19448042919863128325016517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 103722895572603351066754757 19448042919863128325016517)
              ·
                refine ⟨3646508047474336560940597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19448042919863128325016517 3646508047474336560940597)
                ·
                  refine ⟨341860129450719052588181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3646508047474336560940597 341860129450719052588181)
                  ·
                    rfl

theorem cell21_1497983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 4, 5].length) (baseStart_1497983 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1497983 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1497983 prefixEnd_1497983 := by exact prefixLift 1497983
  have htrace : WordTrace (prefixWord ++ tailWord_1497983) baseStart_1497983 baseEnd_1497983 := by
    simpa [prefixWord, tailWord_1497983, baseEnd_1497983] using wordTrace_append hprefix tailTrace_1497983
  have hstable : (prefixWord ++ tailWord_1497983).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497983).length < 2 ^ (prefixWord ++ tailWord_1497983).sum := by decide
  have hdescent : baseEnd_1497983 < baseStart_1497983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498006 : List Nat := [5, 3, 1, 1, 1, 2, 2, 2, 4]
def baseStart_1498006 : Nat := 118140960795 + 1498006 * 2 ^ 59
def prefixEnd_1498006 : Nat := 4983230072969 + 3 ^ 40 * 1498006 * 2
def baseEnd_1498006 : Nat := 341865378364076123704801

theorem tailTrace_1498006 : CollatzResearch.WordTrace tailWord_1498006 prefixEnd_1498006 341865378364076123704801 := by
  unfold tailWord_1498006
  simp only [CollatzResearch.WordTrace]
  refine ⟨3414797963186723493845117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36424511607325050601014581 3414797963186723493845117)
  ·
    refine ⟨1280549236195021310191919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3414797963186723493845117 1280549236195021310191919)
    ·
      refine ⟨1920823854292531965287879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1280549236195021310191919 1920823854292531965287879)
      ·
        refine ⟨2881235781438797947931819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1920823854292531965287879 2881235781438797947931819)
        ·
          refine ⟨4321853672158196921897729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2881235781438797947931819 4321853672158196921897729)
          ·
            refine ⟨3241390254118647691423297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4321853672158196921897729 3241390254118647691423297)
            ·
              refine ⟨2431042690588985768567473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3241390254118647691423297 2431042690588985768567473)
              ·
                refine ⟨1823282017941739326425605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2431042690588985768567473 1823282017941739326425605)
                ·
                  refine ⟨341865378364076123704801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1823282017941739326425605 341865378364076123704801)
                  ·
                    rfl

theorem cell21_1498006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_1498006 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1498006 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1498006 prefixEnd_1498006 := by exact prefixLift 1498006
  have htrace : WordTrace (prefixWord ++ tailWord_1498006) baseStart_1498006 baseEnd_1498006 := by
    simpa [prefixWord, tailWord_1498006, baseEnd_1498006] using wordTrace_append hprefix tailTrace_1498006
  have hstable : (prefixWord ++ tailWord_1498006).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498006).length < 2 ^ (prefixWord ++ tailWord_1498006).sum := by decide
  have hdescent : baseEnd_1498006 < baseStart_1498006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498141 : List Nat := [1, 4, 2, 2, 3, 2, 2, 1, 4]
def baseStart_1498141 : Nat := 118140960795 + 1498141 * 2 ^ 59
def prefixEnd_1498141 : Nat := 4983230072969 + 3 ^ 40 * 1498141 * 2
def baseEnd_1498141 : Nat := 341896187203345888954525

theorem tailTrace_1498141 : CollatzResearch.WordTrace tailWord_1498141 prefixEnd_1498141 341896187203345888954525 := by
  unfold tailWord_1498141
  simp only [CollatzResearch.WordTrace]
  refine ⟨54641691265498493957686277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36427794176998995971790851 54641691265498493957686277)
  ·
    refine ⟨10245317112280967617066177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54641691265498493957686277 10245317112280967617066177)
    ·
      refine ⟨7683987834210725712799633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10245317112280967617066177 7683987834210725712799633)
      ·
        refine ⟨5762990875658044284599725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7683987834210725712799633 5762990875658044284599725)
        ·
          refine ⟨2161121578371766606724897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5762990875658044284599725 2161121578371766606724897)
          ·
            refine ⟨1620841183778824955043673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2161121578371766606724897 1620841183778824955043673)
            ·
              refine ⟨1215630887834118716282755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1620841183778824955043673 1215630887834118716282755)
              ·
                refine ⟨1823446331751178074424133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1215630887834118716282755 1823446331751178074424133)
                ·
                  refine ⟨341896187203345888954525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1823446331751178074424133 341896187203345888954525)
                  ·
                    rfl

theorem cell21_1498141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 2, 1, 4].length) (baseStart_1498141 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1498141 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1498141 prefixEnd_1498141 := by exact prefixLift 1498141
  have htrace : WordTrace (prefixWord ++ tailWord_1498141) baseStart_1498141 baseEnd_1498141 := by
    simpa [prefixWord, tailWord_1498141, baseEnd_1498141] using wordTrace_append hprefix tailTrace_1498141
  have hstable : (prefixWord ++ tailWord_1498141).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498141).length < 2 ^ (prefixWord ++ tailWord_1498141).sum := by decide
  have hdescent : baseEnd_1498141 < baseStart_1498141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498183 : List Nat := [1, 1, 4, 1, 3, 3, 2, 2, 4]
def baseStart_1498183 : Nat := 118140960795 + 1498183 * 2 ^ 59
def prefixEnd_1498183 : Nat := 4983230072969 + 3 ^ 40 * 1498183 * 2
def baseEnd_1498183 : Nat := 341905772175563149254439

theorem tailTrace_1498183 : CollatzResearch.WordTrace tailWord_1498183 prefixEnd_1498183 341905772175563149254439 := by
  unfold tailWord_1498183
  simp only [CollatzResearch.WordTrace]
  refine ⟨54643223131346335130715203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36428815420897556753810135 54643223131346335130715203)
  ·
    refine ⟨81964834697019502696072805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54643223131346335130715203 81964834697019502696072805)
    ·
      refine ⟨15368406505691156755513651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81964834697019502696072805 15368406505691156755513651)
      ·
        refine ⟨23052609758536735133270477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15368406505691156755513651 23052609758536735133270477)
        ·
          refine ⟨8644728659451275674976429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23052609758536735133270477 8644728659451275674976429)
          ·
            refine ⟨3241773247294228378116161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8644728659451275674976429 3241773247294228378116161)
            ·
              refine ⟨2431329935470671283587121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3241773247294228378116161 2431329935470671283587121)
              ·
                refine ⟨1823497451603003462690341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2431329935470671283587121 1823497451603003462690341)
                ·
                  refine ⟨341905772175563149254439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1823497451603003462690341 341905772175563149254439)
                  ·
                    rfl

theorem cell21_1498183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 2, 4].length) (baseStart_1498183 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1498183 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1498183 prefixEnd_1498183 := by exact prefixLift 1498183
  have htrace : WordTrace (prefixWord ++ tailWord_1498183) baseStart_1498183 baseEnd_1498183 := by
    simpa [prefixWord, tailWord_1498183, baseEnd_1498183] using wordTrace_append hprefix tailTrace_1498183
  have hstable : (prefixWord ++ tailWord_1498183).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498183).length < 2 ^ (prefixWord ++ tailWord_1498183).sum := by decide
  have hdescent : baseEnd_1498183 < baseStart_1498183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498310 : List Nat := [6, 1, 2, 2, 1, 1, 1, 3, 4]
def baseStart_1498310 : Nat := 118140960795 + 1498310 * 2 ^ 59
def prefixEnd_1498310 : Nat := 4983230072969 + 3 ^ 40 * 1498310 * 2
def baseEnd_1498310 : Nat := 341934755305839150637513

theorem tailTrace_1498310 : CollatzResearch.WordTrace tailWord_1498310 prefixEnd_1498310 341934755305839150637513 := by
  unfold tailWord_1498310
  simp only [CollatzResearch.WordTrace]
  refine ⟨1707745475058944869393387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 36431903467924157213725589 1707745475058944869393387)
  ·
    refine ⟨2561618212588417304090081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1707745475058944869393387 2561618212588417304090081)
    ·
      refine ⟨1921213659441312978067561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2561618212588417304090081 1921213659441312978067561)
      ·
        refine ⟨1440910244580984733550671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1921213659441312978067561 1440910244580984733550671)
        ·
          refine ⟨2161365366871477100326007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1440910244580984733550671 2161365366871477100326007)
          ·
            refine ⟨3242048050307215650489011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2161365366871477100326007 3242048050307215650489011)
            ·
              refine ⟨4863072075460823475733517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3242048050307215650489011 4863072075460823475733517)
              ·
                refine ⟨1823652028297808803400069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4863072075460823475733517 1823652028297808803400069)
                ·
                  refine ⟨341934755305839150637513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1823652028297808803400069 341934755305839150637513)
                  ·
                    rfl

theorem cell21_1498310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_1498310 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1498310 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1498310 prefixEnd_1498310 := by exact prefixLift 1498310
  have htrace : WordTrace (prefixWord ++ tailWord_1498310) baseStart_1498310 baseEnd_1498310 := by
    simpa [prefixWord, tailWord_1498310, baseEnd_1498310] using wordTrace_append hprefix tailTrace_1498310
  have hstable : (prefixWord ++ tailWord_1498310).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498310).length < 2 ^ (prefixWord ++ tailWord_1498310).sum := by decide
  have hdescent : baseEnd_1498310 < baseStart_1498310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498366 : List Nat := [4, 2, 2, 1, 1, 4, 1, 6]
def baseStart_1498366 : Nat := 118140960795 + 1498366 * 2 ^ 59
def prefixEnd_1498366 : Nat := 4983230072969 + 3 ^ 40 * 1498366 * 2
def baseEnd_1498366 : Nat := 113982511756265165901355

theorem tailTrace_1498366 : CollatzResearch.WordTrace tailWord_1498366 prefixEnd_1498366 113982511756265165901355 := by
  unfold tailWord_1498366
  simp only [CollatzResearch.WordTrace]
  refine ⟨6831237211210419673078369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36433265126455571589751301 6831237211210419673078369)
  ·
    refine ⟨5123427908407814754808777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6831237211210419673078369 5123427908407814754808777)
    ·
      refine ⟨3842570931305861066106583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5123427908407814754808777 3842570931305861066106583)
      ·
        refine ⟨5763856396958791599159875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3842570931305861066106583 5763856396958791599159875)
        ·
          refine ⟨8645784595438187398739813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5763856396958791599159875 8645784595438187398739813)
          ·
            refine ⟨1621084611644660137263715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8645784595438187398739813 1621084611644660137263715)
            ·
              refine ⟨2431626917466990205895573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1621084611644660137263715 2431626917466990205895573)
              ·
                refine ⟨113982511756265165901355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2431626917466990205895573 113982511756265165901355)
                ·
                  rfl

theorem cell21_1498366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 6].length) (baseStart_1498366 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1498366 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1498366 prefixEnd_1498366 := by exact prefixLift 1498366
  have htrace : WordTrace (prefixWord ++ tailWord_1498366) baseStart_1498366 baseEnd_1498366 := by
    simpa [prefixWord, tailWord_1498366, baseEnd_1498366] using wordTrace_append hprefix tailTrace_1498366
  have hstable : (prefixWord ++ tailWord_1498366).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498366).length < 2 ^ (prefixWord ++ tailWord_1498366).sum := by decide
  have hdescent : baseEnd_1498366 < baseStart_1498366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498397 : List Nat := [1, 4, 2, 3, 1, 1, 1, 5, 3]
def baseStart_1498397 : Nat := 118140960795 + 1498397 * 2 ^ 59
def prefixEnd_1498397 : Nat := 4983230072969 + 3 ^ 40 * 1498397 * 2
def baseEnd_1498397 : Nat := 341954609891146332687335

theorem tailTrace_1498397 : CollatzResearch.WordTrace tailWord_1498397 prefixEnd_1498397 341954609891146332687335 := by
  unfold tailWord_1498397
  simp only [CollatzResearch.WordTrace]
  refine ⟨54651028352571049679005445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36434018901714033119336963 54651028352571049679005445)
  ·
    refine ⟨10247067816107071814813521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54651028352571049679005445 10247067816107071814813521)
    ·
      refine ⟨7685300862080303861110141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10247067816107071814813521 7685300862080303861110141)
      ·
        refine ⟨2881987823280113947916303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7685300862080303861110141 2881987823280113947916303)
        ·
          refine ⟨4322981734920170921874455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2881987823280113947916303 4322981734920170921874455)
          ·
            refine ⟨6484472602380256382811683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4322981734920170921874455 6484472602380256382811683)
            ·
              refine ⟨9726708903570384574217525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6484472602380256382811683 9726708903570384574217525)
              ·
                refine ⟨911878959709723553832893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9726708903570384574217525 911878959709723553832893)
                ·
                  refine ⟨341954609891146332687335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 911878959709723553832893 341954609891146332687335)
                  ·
                    rfl

theorem cell21_1498397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 5, 3].length) (baseStart_1498397 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1498397 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1498397 prefixEnd_1498397 := by exact prefixLift 1498397
  have htrace : WordTrace (prefixWord ++ tailWord_1498397) baseStart_1498397 baseEnd_1498397 := by
    simpa [prefixWord, tailWord_1498397, baseEnd_1498397] using wordTrace_append hprefix tailTrace_1498397
  have hstable : (prefixWord ++ tailWord_1498397).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498397).length < 2 ^ (prefixWord ++ tailWord_1498397).sum := by decide
  have hdescent : baseEnd_1498397 < baseStart_1498397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498439 : List Nat := [1, 1, 4, 1, 2, 3, 2, 2, 5]
def baseStart_1498439 : Nat := 118140960795 + 1498439 * 2 ^ 59
def prefixEnd_1498439 : Nat := 4983230072969 + 3 ^ 40 * 1498439 * 2
def baseEnd_1498439 : Nat := 341964194863363592987249

theorem tailTrace_1498439 : CollatzResearch.WordTrace tailWord_1498439 prefixEnd_1498439 341964194863363592987249 := by
  unfold tailWord_1498439
  simp only [CollatzResearch.WordTrace]
  refine ⟨54652560218418890852034371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36435040145612593901356247 54652560218418890852034371)
  ·
    refine ⟨81978840327628336278051557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54652560218418890852034371 81978840327628336278051557)
    ·
      refine ⟨15371032561430313052134667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81978840327628336278051557 15371032561430313052134667)
      ·
        refine ⟨23056548842145469578202001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15371032561430313052134667 23056548842145469578202001)
        ·
          refine ⟨17292411631609102183651501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23056548842145469578202001 17292411631609102183651501)
          ·
            refine ⟨6484654361853413318869313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17292411631609102183651501 6484654361853413318869313)
            ·
              refine ⟨4863490771390059989151985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6484654361853413318869313 4863490771390059989151985)
              ·
                refine ⟨3647618078542544991863989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4863490771390059989151985 3647618078542544991863989)
                ·
                  refine ⟨341964194863363592987249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3647618078542544991863989 341964194863363592987249)
                  ·
                    rfl

theorem cell21_1498439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 2, 5].length) (baseStart_1498439 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1498439 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1498439 prefixEnd_1498439 := by exact prefixLift 1498439
  have htrace : WordTrace (prefixWord ++ tailWord_1498439) baseStart_1498439 baseEnd_1498439 := by
    simpa [prefixWord, tailWord_1498439, baseEnd_1498439] using wordTrace_append hprefix tailTrace_1498439
  have hstable : (prefixWord ++ tailWord_1498439).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498439).length < 2 ^ (prefixWord ++ tailWord_1498439).sum := by decide
  have hdescent : baseEnd_1498439 < baseStart_1498439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498524 : List Nat := [2, 2, 3, 4, 2, 1, 2, 2, 3]
def baseStart_1498524 : Nat := 118140960795 + 1498524 * 2 ^ 59
def prefixEnd_1498524 : Nat := 4983230072969 + 3 ^ 40 * 1498524 * 2
def baseEnd_1498524 : Nat := 341983593021422334070409

theorem tailTrace_1498524 : CollatzResearch.WordTrace tailWord_1498524 prefixEnd_1498524 341983593021422334070409 := by
  unfold tailWord_1498524
  simp only [CollatzResearch.WordTrace]
  refine ⟨27327830211555475184439313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36437106948740633579252417 27327830211555475184439313)
  ·
    refine ⟨20495872658666606388329485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27327830211555475184439313 20495872658666606388329485)
    ·
      refine ⟨7685952246999977395623557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20495872658666606388329485 7685952246999977395623557)
      ·
        refine ⟨1441116046312495761679417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7685952246999977395623557 1441116046312495761679417)
        ·
          refine ⟨1080837034734371821259563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1441116046312495761679417 1080837034734371821259563)
          ·
            refine ⟨1621255552101557731889345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1080837034734371821259563 1621255552101557731889345)
            ·
              refine ⟨1215941664076168298917009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1621255552101557731889345 1215941664076168298917009)
              ·
                refine ⟨911956248057126224187757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1215941664076168298917009 911956248057126224187757)
                ·
                  refine ⟨341983593021422334070409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 911956248057126224187757 341983593021422334070409)
                  ·
                    rfl

theorem cell21_1498524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 2, 2, 3].length) (baseStart_1498524 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1498524 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1498524 prefixEnd_1498524 := by exact prefixLift 1498524
  have htrace : WordTrace (prefixWord ++ tailWord_1498524) baseStart_1498524 baseEnd_1498524 := by
    simpa [prefixWord, tailWord_1498524, baseEnd_1498524] using wordTrace_append hprefix tailTrace_1498524
  have hstable : (prefixWord ++ tailWord_1498524).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498524).length < 2 ^ (prefixWord ++ tailWord_1498524).sum := by decide
  have hdescent : baseEnd_1498524 < baseStart_1498524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498580 : List Nat := [2, 4, 1, 2, 3, 2, 1, 2, 4]
def baseStart_1498580 : Nat := 118140960795 + 1498580 * 2 ^ 59
def prefixEnd_1498580 : Nat := 4983230072969 + 3 ^ 40 * 1498580 * 2
def baseEnd_1498580 : Nat := 341996372984378681136961

theorem tailTrace_1498580 : CollatzResearch.WordTrace tailWord_1498580 prefixEnd_1498580 341996372984378681136961 := by
  unfold tailWord_1498580
  simp only [CollatzResearch.WordTrace]
  refine ⟨27328851455454035966458597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36438468607272047955278129 27328851455454035966458597)
  ·
    refine ⟨5124159647897631743710987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27328851455454035966458597 5124159647897631743710987)
    ·
      refine ⟨7686239471846447615566481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5124159647897631743710987 7686239471846447615566481)
      ·
        refine ⟨5764679603884835711674861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7686239471846447615566481 5764679603884835711674861)
        ·
          refine ⟨2161754851456813391878073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5764679603884835711674861 2161754851456813391878073)
          ·
            refine ⟨1621316138592610043908555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2161754851456813391878073 1621316138592610043908555)
            ·
              refine ⟨2431974207888915065862833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1621316138592610043908555 2431974207888915065862833)
              ·
                refine ⟨1823980655916686299397125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2431974207888915065862833 1823980655916686299397125)
                ·
                  refine ⟨341996372984378681136961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1823980655916686299397125 341996372984378681136961)
                  ·
                    rfl

theorem cell21_1498580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_1498580 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1498580 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1498580 prefixEnd_1498580 := by exact prefixLift 1498580
  have htrace : WordTrace (prefixWord ++ tailWord_1498580) baseStart_1498580 baseEnd_1498580 := by
    simpa [prefixWord, tailWord_1498580, baseEnd_1498580] using wordTrace_append hprefix tailTrace_1498580
  have hstable : (prefixWord ++ tailWord_1498580).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498580).length < 2 ^ (prefixWord ++ tailWord_1498580).sum := by decide
  have hdescent : baseEnd_1498580 < baseStart_1498580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498591 : List Nat := [1, 1, 2, 3, 3, 1, 4, 1, 5]
def baseStart_1498591 : Nat := 118140960795 + 1498591 * 2 ^ 59
def prefixEnd_1498591 : Nat := 4983230072969 + 3 ^ 40 * 1498591 * 2
def baseEnd_1498591 : Nat := 341998883334245106453605

theorem tailTrace_1498591 : CollatzResearch.WordTrace tailWord_1498591 prefixEnd_1498591 341998883334245106453605 := by
  unfold tailWord_1498591
  simp only [CollatzResearch.WordTrace]
  refine ⟨54658104113868220811567627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36438736075912147207711751 54658104113868220811567627)
  ·
    refine ⟨81987156170802331217351441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54658104113868220811567627 81987156170802331217351441)
    ·
      refine ⟨61490367128101748413013581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81987156170802331217351441 61490367128101748413013581)
      ·
        refine ⟨23058887673038155654880093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61490367128101748413013581 23058887673038155654880093)
        ·
          refine ⟨8647082877389308370580035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23058887673038155654880093 8647082877389308370580035)
          ·
            refine ⟨12970624316083962555870053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8647082877389308370580035 12970624316083962555870053)
            ·
              refine ⟨2431992059265742979225635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12970624316083962555870053 2431992059265742979225635)
              ·
                refine ⟨3647988088898614468838453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2431992059265742979225635 3647988088898614468838453)
                ·
                  refine ⟨341998883334245106453605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3647988088898614468838453 341998883334245106453605)
                  ·
                    rfl

theorem cell21_1498591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 1, 5].length) (baseStart_1498591 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1498591 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1498591 prefixEnd_1498591 := by exact prefixLift 1498591
  have htrace : WordTrace (prefixWord ++ tailWord_1498591) baseStart_1498591 baseEnd_1498591 := by
    simpa [prefixWord, tailWord_1498591, baseEnd_1498591] using wordTrace_append hprefix tailTrace_1498591
  have hstable : (prefixWord ++ tailWord_1498591).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498591).length < 2 ^ (prefixWord ++ tailWord_1498591).sum := by decide
  have hdescent : baseEnd_1498591 < baseStart_1498591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498619 : List Nat := [1, 1, 1, 1, 1, 3, 2, 11]
def baseStart_1498619 : Nat := 118140960795 + 1498619 * 2 ^ 59
def prefixEnd_1498619 : Nat := 4983230072969 + 3 ^ 40 * 1498619 * 2
def baseEnd_1498619 : Nat := 114001757771907759995627

theorem tailTrace_1498619 : CollatzResearch.WordTrace tailWord_1498619 prefixEnd_1498619 114001757771907759995627 := by
  unfold tailWord_1498619
  simp only [CollatzResearch.WordTrace]
  refine ⟨54659125357766781593586911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36439416905177854395724607 54659125357766781593586911)
  ·
    refine ⟨81988688036650172390380367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54659125357766781593586911 81988688036650172390380367)
    ·
      refine ⟨122983032054975258585570551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81988688036650172390380367 122983032054975258585570551)
      ·
        refine ⟨184474548082462887878355827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122983032054975258585570551 184474548082462887878355827)
        ·
          refine ⟨276711822123694331817533741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184474548082462887878355827 276711822123694331817533741)
          ·
            refine ⟨103766933296385374431575153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 276711822123694331817533741 103766933296385374431575153)
            ·
              refine ⟨77825199972289030823681365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103766933296385374431575153 77825199972289030823681365)
              ·
                refine ⟨114001757771907759995627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 77825199972289030823681365 114001757771907759995627)
                ·
                  rfl

theorem cell21_1498619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 11].length) (baseStart_1498619 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1498619 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1498619 prefixEnd_1498619 := by exact prefixLift 1498619
  have htrace : WordTrace (prefixWord ++ tailWord_1498619) baseStart_1498619 baseEnd_1498619 := by
    simpa [prefixWord, tailWord_1498619, baseEnd_1498619] using wordTrace_append hprefix tailTrace_1498619
  have hstable : (prefixWord ++ tailWord_1498619).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498619).length < 2 ^ (prefixWord ++ tailWord_1498619).sum := by decide
  have hdescent : baseEnd_1498619 < baseStart_1498619 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498656 : List Nat := [2, 1, 1, 6, 1, 3, 2, 1, 4]
def baseStart_1498656 : Nat := 118140960795 + 1498656 * 2 ^ 59
def prefixEnd_1498656 : Nat := 4983230072969 + 3 ^ 40 * 1498656 * 2
def baseEnd_1498656 : Nat := 342013717219819437870139

theorem tailTrace_1498656 : CollatzResearch.WordTrace tailWord_1498656 prefixEnd_1498656 342013717219819437870139 := by
  unfold tailWord_1498656
  simp only [CollatzResearch.WordTrace]
  refine ⟨27330237429316368456341911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36440316572421824608455881 27330237429316368456341911)
  ·
    refine ⟨40995356143974552684512867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27330237429316368456341911 40995356143974552684512867)
    ·
      refine ⟨61493034215961829026769301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40995356143974552684512867 61493034215961829026769301)
      ·
        refine ⟨2882485978873210735629811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 61493034215961829026769301 2882485978873210735629811)
        ·
          refine ⟨4323728968309816103444717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2882485978873210735629811 4323728968309816103444717)
          ·
            refine ⟨1621398363116181038791769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4323728968309816103444717 1621398363116181038791769)
            ·
              refine ⟨1216048772337135779093827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1621398363116181038791769 1216048772337135779093827)
              ·
                refine ⟨1824073158505703668640741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1216048772337135779093827 1824073158505703668640741)
                ·
                  refine ⟨342013717219819437870139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1824073158505703668640741 342013717219819437870139)
                  ·
                    rfl

theorem cell21_1498656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 2, 1, 4].length) (baseStart_1498656 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1498656 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1498656 prefixEnd_1498656 := by exact prefixLift 1498656
  have htrace : WordTrace (prefixWord ++ tailWord_1498656) baseStart_1498656 baseEnd_1498656 := by
    simpa [prefixWord, tailWord_1498656, baseEnd_1498656] using wordTrace_append hprefix tailTrace_1498656
  have hstable : (prefixWord ++ tailWord_1498656).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498656).length < 2 ^ (prefixWord ++ tailWord_1498656).sum := by decide
  have hdescent : baseEnd_1498656 < baseStart_1498656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498695 : List Nat := [1, 1, 4, 1, 14]
def baseStart_1498695 : Nat := 118140960795 + 1498695 * 2 ^ 59
def prefixEnd_1498695 : Nat := 4983230072969 + 3 ^ 40 * 1498695 * 2
def baseEnd_1498695 : Nat := 4222501451248938724939

theorem tailTrace_1498695 : CollatzResearch.WordTrace tailWord_1498695 prefixEnd_1498695 4222501451248938724939 := by
  unfold tailWord_1498695
  simp only [CollatzResearch.WordTrace]
  refine ⟨54661897305491446573353539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36441264870327631048902359 54661897305491446573353539)
  ·
    refine ⟨81992845958237169860030309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54661897305491446573353539 81992845958237169860030309)
    ·
      refine ⟨15373658617169469348755683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81992845958237169860030309 15373658617169469348755683)
      ·
        refine ⟨23060487925754204023133525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15373658617169469348755683 23060487925754204023133525)
        ·
          refine ⟨4222501451248938724939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 23060487925754204023133525 4222501451248938724939)
          ·
            rfl

theorem cell21_1498695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 14].length) (baseStart_1498695 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1498695 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1498695 prefixEnd_1498695 := by exact prefixLift 1498695
  have htrace : WordTrace (prefixWord ++ tailWord_1498695) baseStart_1498695 baseEnd_1498695 := by
    simpa [prefixWord, tailWord_1498695, baseEnd_1498695] using wordTrace_append hprefix tailTrace_1498695
  have hstable : (prefixWord ++ tailWord_1498695).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498695).length < 2 ^ (prefixWord ++ tailWord_1498695).sum := by decide
  have hdescent : baseEnd_1498695 < baseStart_1498695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498698 : List Nat := [3, 1, 2, 1, 1, 3, 4, 2, 4]
def baseStart_1498698 : Nat := 118140960795 + 1498698 * 2 ^ 59
def prefixEnd_1498698 : Nat := 4983230072969 + 3 ^ 40 * 1498698 * 2
def baseEnd_1498698 : Nat := 342023302192036698170053

theorem tailTrace_1498698 : CollatzResearch.WordTrace tailWord_1498698 prefixEnd_1498698 342023302192036698170053 := by
  unfold tailWord_1498698
  simp only [CollatzResearch.WordTrace]
  refine ⟨13665501681120144521428187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36441337816320385390475165 13665501681120144521428187)
  ·
    refine ⟨20498252521680216782142281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13665501681120144521428187 20498252521680216782142281)
    ·
      refine ⟨15373689391260162586606711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20498252521680216782142281 15373689391260162586606711)
      ·
        refine ⟨23060534086890243879910067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15373689391260162586606711 23060534086890243879910067)
        ·
          refine ⟨34590801130335365819865101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23060534086890243879910067 34590801130335365819865101)
          ·
            refine ⟨12971550423875762182449413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34590801130335365819865101 12971550423875762182449413)
            ·
              refine ⟨2432165704476705409209265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12971550423875762182449413 2432165704476705409209265)
              ·
                refine ⟨1824124278357529056906949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2432165704476705409209265 1824124278357529056906949)
                ·
                  refine ⟨342023302192036698170053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1824124278357529056906949 342023302192036698170053)
                  ·
                    rfl

theorem cell21_1498698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 2, 4].length) (baseStart_1498698 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1498698 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1498698 prefixEnd_1498698 := by exact prefixLift 1498698
  have htrace : WordTrace (prefixWord ++ tailWord_1498698) baseStart_1498698 baseEnd_1498698 := by
    simpa [prefixWord, tailWord_1498698, baseEnd_1498698] using wordTrace_append hprefix tailTrace_1498698
  have hstable : (prefixWord ++ tailWord_1498698).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498698).length < 2 ^ (prefixWord ++ tailWord_1498698).sum := by decide
  have hdescent : baseEnd_1498698 < baseStart_1498698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498757 : List Nat := [1, 3, 1, 1, 4, 1, 3, 1, 6]
def baseStart_1498757 : Nat := 118140960795 + 1498757 * 2 ^ 59
def prefixEnd_1498757 : Nat := 4983230072969 + 3 ^ 40 * 1498757 * 2
def baseEnd_1498757 : Nat := 342036766795865706686599

theorem tailTrace_1498757 : CollatzResearch.WordTrace tailWord_1498757 prefixEnd_1498757 342036766795865706686599 := by
  unfold tailWord_1498757
  simp only [CollatzResearch.WordTrace]
  refine ⟨54664158631266831162110525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36442772420844554108073683 54664158631266831162110525)
  ·
    refine ⟨20499059486725061685791447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54664158631266831162110525 20499059486725061685791447)
    ·
      refine ⟨30748589230087592528687171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20499059486725061685791447 30748589230087592528687171)
      ·
        refine ⟨46122883845131388793030757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30748589230087592528687171 46122883845131388793030757)
        ·
          refine ⟨8648040720962135398693267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46122883845131388793030757 8648040720962135398693267)
          ·
            refine ⟨12972061081443203098039901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8648040720962135398693267 12972061081443203098039901)
            ·
              refine ⟨4864522905541201161764963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12972061081443203098039901 4864522905541201161764963)
              ·
                refine ⟨7296784358311801742647445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4864522905541201161764963 7296784358311801742647445)
                ·
                  refine ⟨342036766795865706686599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7296784358311801742647445 342036766795865706686599)
                  ·
                    rfl

theorem cell21_1498757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 1, 6].length) (baseStart_1498757 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1498757 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1498757 prefixEnd_1498757 := by exact prefixLift 1498757
  have htrace : WordTrace (prefixWord ++ tailWord_1498757) baseStart_1498757 baseEnd_1498757 := by
    simpa [prefixWord, tailWord_1498757, baseEnd_1498757] using wordTrace_append hprefix tailTrace_1498757
  have hstable : (prefixWord ++ tailWord_1498757).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498757).length < 2 ^ (prefixWord ++ tailWord_1498757).sum := by decide
  have hdescent : baseEnd_1498757 < baseStart_1498757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498788 : List Nat := [2, 3, 1, 2, 2, 3, 1, 7]
def baseStart_1498788 : Nat := 118140960795 + 1498788 * 2 ^ 59
def prefixEnd_1498788 : Nat := 4983230072969 + 3 ^ 40 * 1498788 * 2
def baseEnd_1498788 : Nat := 114014613806072180556623

theorem tailTrace_1498788 : CollatzResearch.WordTrace tailWord_1498788 prefixEnd_1498788 114014613806072180556623 := by
  unfold tailWord_1498788
  simp only [CollatzResearch.WordTrace]
  refine ⟨27332644647077261728244509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36443526196103015637659345 27332644647077261728244509)
  ·
    refine ⟨10249741742653973148091691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27332644647077261728244509 10249741742653973148091691)
    ·
      refine ⟨15374612613980959722137537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10249741742653973148091691 15374612613980959722137537)
      ·
        refine ⟨11530959460485719791603153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15374612613980959722137537 11530959460485719791603153)
        ·
          refine ⟨8648219595364289843702365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11530959460485719791603153 8648219595364289843702365)
          ·
            refine ⟨3243082348261608691388387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8648219595364289843702365 3243082348261608691388387)
            ·
              refine ⟨4864623522392413037082581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3243082348261608691388387 4864623522392413037082581)
              ·
                refine ⟨114014613806072180556623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4864623522392413037082581 114014613806072180556623)
                ·
                  rfl

theorem cell21_1498788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 7].length) (baseStart_1498788 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1498788 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1498788 prefixEnd_1498788 := by exact prefixLift 1498788
  have htrace : WordTrace (prefixWord ++ tailWord_1498788) baseStart_1498788 baseEnd_1498788 := by
    simpa [prefixWord, tailWord_1498788, baseEnd_1498788] using wordTrace_append hprefix tailTrace_1498788
  have hstable : (prefixWord ++ tailWord_1498788).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498788).length < 2 ^ (prefixWord ++ tailWord_1498788).sum := by decide
  have hdescent : baseEnd_1498788 < baseStart_1498788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498802 : List Nat := [3, 2, 1, 1, 1, 2, 2, 2, 7]
def baseStart_1498802 : Nat := 118140960795 + 1498802 * 2 ^ 59
def prefixEnd_1498802 : Nat := 4983230072969 + 3 ^ 40 * 1498802 * 2
def baseEnd_1498802 : Nat := 342047036408955628436507

theorem tailTrace_1498802 : CollatzResearch.WordTrace tailWord_1498802 prefixEnd_1498802 342047036408955628436507 := by
  unfold tailWord_1498802
  simp only [CollatzResearch.WordTrace]
  refine ⟨13666449979025950961874665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36443866610735869231665773 13666449979025950961874665)
  ·
    refine ⟨10249837484269463221405999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13666449979025950961874665 10249837484269463221405999)
    ·
      refine ⟨15374756226404194832108999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10249837484269463221405999 15374756226404194832108999)
      ·
        refine ⟨23062134339606292248163499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15374756226404194832108999 23062134339606292248163499)
        ·
          refine ⟨34593201509409438372245249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23062134339606292248163499 34593201509409438372245249)
          ·
            refine ⟨25944901132057078779183937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34593201509409438372245249 25944901132057078779183937)
            ·
              refine ⟨19458675849042809084387953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25944901132057078779183937 19458675849042809084387953)
              ·
                refine ⟨14594006886782106813290965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19458675849042809084387953 14594006886782106813290965)
                ·
                  refine ⟨342047036408955628436507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14594006886782106813290965 342047036408955628436507)
                  ·
                    rfl

theorem cell21_1498802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 7].length) (baseStart_1498802 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1498802 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1498802 prefixEnd_1498802 := by exact prefixLift 1498802
  have htrace : WordTrace (prefixWord ++ tailWord_1498802) baseStart_1498802 baseEnd_1498802 := by
    simpa [prefixWord, tailWord_1498802, baseEnd_1498802] using wordTrace_append hprefix tailTrace_1498802
  have hstable : (prefixWord ++ tailWord_1498802).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498802).length < 2 ^ (prefixWord ++ tailWord_1498802).sum := by decide
  have hdescent : baseEnd_1498802 < baseStart_1498802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498805 : List Nat := [1, 3, 3, 3, 2, 2, 7]
def baseStart_1498805 : Nat := 118140960795 + 1498805 * 2 ^ 59
def prefixEnd_1498805 : Nat := 4983230072969 + 3 ^ 40 * 1498805 * 2
def baseEnd_1498805 : Nat := 38005302338869809987389

theorem tailTrace_1498805 : CollatzResearch.WordTrace tailWord_1498805 prefixEnd_1498805 38005302338869809987389 := by
  unfold tailWord_1498805
  simp only [CollatzResearch.WordTrace]
  refine ⟨54665909335092935359857869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36443939556728623573238579 54665909335092935359857869)
  ·
    refine ⟨20499716000659850759946701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54665909335092935359857869 20499716000659850759946701)
    ·
      refine ⟨7687393500247444034980013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20499716000659850759946701 7687393500247444034980013)
      ·
        refine ⟨2882772562592791513117505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7687393500247444034980013 2882772562592791513117505)
        ·
          refine ⟨2162079421944593634838129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2882772562592791513117505 2162079421944593634838129)
          ·
            refine ⟨1621559566458445226128597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2162079421944593634838129 1621559566458445226128597)
            ·
              refine ⟨38005302338869809987389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1621559566458445226128597 38005302338869809987389)
              ·
                rfl

theorem cell21_1498805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 7].length) (baseStart_1498805 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1498805 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1498805 prefixEnd_1498805 := by exact prefixLift 1498805
  have htrace : WordTrace (prefixWord ++ tailWord_1498805) baseStart_1498805 baseEnd_1498805 := by
    simpa [prefixWord, tailWord_1498805, baseEnd_1498805] using wordTrace_append hprefix tailTrace_1498805
  have hstable : (prefixWord ++ tailWord_1498805).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498805).length < 2 ^ (prefixWord ++ tailWord_1498805).sum := by decide
  have hdescent : baseEnd_1498805 < baseStart_1498805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498822 : List Nat := [6, 1, 2, 1, 1, 1, 1, 8]
def baseStart_1498822 : Nat := 118140960795 + 1498822 * 2 ^ 59
def prefixEnd_1498822 : Nat := 4983230072969 + 3 ^ 40 * 1498822 * 2
def baseEnd_1498822 : Nat := 114017200227146679367711

theorem tailTrace_1498822 : CollatzResearch.WordTrace tailWord_1498822 prefixEnd_1498822 114017200227146679367711 := by
  unfold tailWord_1498822
  simp only [CollatzResearch.WordTrace]
  refine ⟨1708329043000979601975835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 36444352917354231508817813 1708329043000979601975835)
  ·
    refine ⟨2562493564501469402963753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1708329043000979601975835 2562493564501469402963753)
    ·
      refine ⟨1921870173376102052222815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2562493564501469402963753 1921870173376102052222815)
      ·
        refine ⟨2882805260064153078334223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1921870173376102052222815 2882805260064153078334223)
        ·
          refine ⟨4324207890096229617501335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2882805260064153078334223 4324207890096229617501335)
          ·
            refine ⟨6486311835144344426252003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4324207890096229617501335 6486311835144344426252003)
            ·
              refine ⟨9729467752716516639378005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6486311835144344426252003 9729467752716516639378005)
              ·
                refine ⟨114017200227146679367711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9729467752716516639378005 114017200227146679367711)
                ·
                  rfl

theorem cell21_1498822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_1498822 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1498822 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1498822 prefixEnd_1498822 := by exact prefixLift 1498822
  have htrace : WordTrace (prefixWord ++ tailWord_1498822) baseStart_1498822 baseEnd_1498822 := by
    simpa [prefixWord, tailWord_1498822, baseEnd_1498822] using wordTrace_append hprefix tailTrace_1498822
  have hstable : (prefixWord ++ tailWord_1498822).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498822).length < 2 ^ (prefixWord ++ tailWord_1498822).sum := by decide
  have hdescent : baseEnd_1498822 < baseStart_1498822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498847 : List Nat := [1, 1, 2, 3, 2, 2, 1, 9]
def baseStart_1498847 : Nat := 118140960795 + 1498847 * 2 ^ 59
def prefixEnd_1498847 : Nat := 4983230072969 + 3 ^ 40 * 1498847 * 2
def baseEnd_1498847 : Nat := 114019102007348516728805

theorem tailTrace_1498847 : CollatzResearch.WordTrace tailWord_1498847 prefixEnd_1498847 114019102007348516728805 := by
  unfold tailWord_1498847
  simp only [CollatzResearch.WordTrace]
  refine ⟨54667441200940776532886795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36444960800627184355257863 54667441200940776532886795)
  ·
    refine ⟨82001161801411164799330193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54667441200940776532886795 82001161801411164799330193)
    ·
      refine ⟨61500871351058373599497645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82001161801411164799330193 61500871351058373599497645)
      ·
        refine ⟨23062826756646890099811617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61500871351058373599497645 23062826756646890099811617)
        ·
          refine ⟨17297120067485167574858713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23062826756646890099811617 17297120067485167574858713)
          ·
            refine ⟨12972840050613875681144035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17297120067485167574858713 12972840050613875681144035)
            ·
              refine ⟨19459260075920813521716053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12972840050613875681144035 19459260075920813521716053)
              ·
                refine ⟨114019102007348516728805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19459260075920813521716053 114019102007348516728805)
                ·
                  rfl

theorem cell21_1498847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 9].length) (baseStart_1498847 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1498847 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1498847 prefixEnd_1498847 := by exact prefixLift 1498847
  have htrace : WordTrace (prefixWord ++ tailWord_1498847) baseStart_1498847 baseEnd_1498847 := by
    simpa [prefixWord, tailWord_1498847, baseEnd_1498847] using wordTrace_append hprefix tailTrace_1498847
  have hstable : (prefixWord ++ tailWord_1498847).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498847).length < 2 ^ (prefixWord ++ tailWord_1498847).sum := by decide
  have hdescent : baseEnd_1498847 < baseStart_1498847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498870 : List Nat := [5, 1, 1, 1, 1, 5, 2, 2, 3]
def baseStart_1498870 : Nat := 118140960795 + 1498870 * 2 ^ 59
def prefixEnd_1498870 : Nat := 4983230072969 + 3 ^ 40 * 1498870 * 2
def baseEnd_1498870 : Nat := 342062554935402621303035

theorem tailTrace_1498870 : CollatzResearch.WordTrace tailWord_1498870 prefixEnd_1498870 342062554935402621303035 := by
  unfold tailWord_1498870
  simp only [CollatzResearch.WordTrace]
  refine ⟨3416767504991090716310879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36445520053238300973982709 3416767504991090716310879)
  ·
    refine ⟨5125151257486636074466319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3416767504991090716310879 5125151257486636074466319)
    ·
      refine ⟨7687726886229954111699479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5125151257486636074466319 7687726886229954111699479)
      ·
        refine ⟨11531590329344931167549219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7687726886229954111699479 11531590329344931167549219)
        ·
          refine ⟨17297385494017396751323829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11531590329344931167549219 17297385494017396751323829)
          ·
            refine ⟨1621629890064130945436609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17297385494017396751323829 1621629890064130945436609)
            ·
              refine ⟨1216222417548098209077457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1621629890064130945436609 1216222417548098209077457)
              ·
                refine ⟨912166813161073656808093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1216222417548098209077457 912166813161073656808093)
                ·
                  refine ⟨342062554935402621303035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 912166813161073656808093 342062554935402621303035)
                  ·
                    rfl

theorem cell21_1498870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 2, 2, 3].length) (baseStart_1498870 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1498870 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1498870 prefixEnd_1498870 := by exact prefixLift 1498870
  have htrace : WordTrace (prefixWord ++ tailWord_1498870) baseStart_1498870 baseEnd_1498870 := by
    simpa [prefixWord, tailWord_1498870, baseEnd_1498870] using wordTrace_append hprefix tailTrace_1498870
  have hstable : (prefixWord ++ tailWord_1498870).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498870).length < 2 ^ (prefixWord ++ tailWord_1498870).sum := by decide
  have hdescent : baseEnd_1498870 < baseStart_1498870 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498898 : List Nat := [3, 2, 4, 1, 1, 2, 3, 5]
def baseStart_1498898 : Nat := 118140960795 + 1498898 * 2 ^ 59
def prefixEnd_1498898 : Nat := 4983230072969 + 3 ^ 40 * 1498898 * 2
def baseEnd_1498898 : Nat := 114022981638960264945437

theorem tailTrace_1498898 : CollatzResearch.WordTrace tailWord_1498898 prefixEnd_1498898 114022981638960264945437 := by
  unfold tailWord_1498898
  simp only [CollatzResearch.WordTrace]
  refine ⟨13667325330939003060748337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36446200882504008161995565 13667325330939003060748337)
  ·
    refine ⟨10250493998204252295561253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13667325330939003060748337 10250493998204252295561253)
    ·
      refine ⟨1921967624663297305417735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10250493998204252295561253 1921967624663297305417735)
      ·
        refine ⟨2882951436994945958126603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1921967624663297305417735 2882951436994945958126603)
        ·
          refine ⟨4324427155492418937189905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2882951436994945958126603 4324427155492418937189905)
          ·
            refine ⟨3243320366619314202892429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4324427155492418937189905 3243320366619314202892429)
            ·
              refine ⟨1216245137482242826084661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3243320366619314202892429 1216245137482242826084661)
              ·
                refine ⟨114022981638960264945437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1216245137482242826084661 114022981638960264945437)
                ·
                  rfl

theorem cell21_1498898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 3, 5].length) (baseStart_1498898 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1498898 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1498898 prefixEnd_1498898 := by exact prefixLift 1498898
  have htrace : WordTrace (prefixWord ++ tailWord_1498898) baseStart_1498898 baseEnd_1498898 := by
    simpa [prefixWord, tailWord_1498898, baseEnd_1498898] using wordTrace_append hprefix tailTrace_1498898
  have hstable : (prefixWord ++ tailWord_1498898).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498898).length < 2 ^ (prefixWord ++ tailWord_1498898).sum := by decide
  have hdescent : baseEnd_1498898 < baseStart_1498898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498912 : List Nat := [2, 1, 1, 5, 1, 1, 4, 3, 3]
def baseStart_1498912 : Nat := 118140960795 + 1498912 * 2 ^ 59
def prefixEnd_1498912 : Nat := 4983230072969 + 3 ^ 40 * 1498912 * 2
def baseEnd_1498912 : Nat := 342072139907619881602949

theorem tailTrace_1498912 : CollatzResearch.WordTrace tailWord_1498912 prefixEnd_1498912 342072139907619881602949 := by
  unfold tailWord_1498912
  simp only [CollatzResearch.WordTrace]
  refine ⟨27334905972852646317001495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36446541297136861756001993 27334905972852646317001495)
  ·
    refine ⟨41002358959278969475502243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27334905972852646317001495 41002358959278969475502243)
    ·
      refine ⟨61503538438918454213253365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41002358959278969475502243 61503538438918454213253365)
      ·
        refine ⟨5765956728648605082492503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61503538438918454213253365 5765956728648605082492503)
        ·
          refine ⟨8648935092972907623738755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5765956728648605082492503 8648935092972907623738755)
          ·
            refine ⟨12973402639459361435608133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8648935092972907623738755 12973402639459361435608133)
            ·
              refine ⟨2432512994898630269176525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12973402639459361435608133 2432512994898630269176525)
              ·
                refine ⟨912192373086986350941197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2432512994898630269176525 912192373086986350941197)
                ·
                  refine ⟨342072139907619881602949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 912192373086986350941197 342072139907619881602949)
                  ·
                    rfl

theorem cell21_1498912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 3, 3].length) (baseStart_1498912 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1498912 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1498912 prefixEnd_1498912 := by exact prefixLift 1498912
  have htrace : WordTrace (prefixWord ++ tailWord_1498912) baseStart_1498912 baseEnd_1498912 := by
    simpa [prefixWord, tailWord_1498912, baseEnd_1498912] using wordTrace_append hprefix tailTrace_1498912
  have hstable : (prefixWord ++ tailWord_1498912).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498912).length < 2 ^ (prefixWord ++ tailWord_1498912).sum := by decide
  have hdescent : baseEnd_1498912 < baseStart_1498912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498943 : List Nat := [1, 1, 2, 2, 6, 1, 3, 1, 4]
def baseStart_1498943 : Nat := 118140960795 + 1498943 * 2 ^ 59
def prefixEnd_1498943 : Nat := 4983230072969 + 3 ^ 40 * 1498943 * 2
def baseEnd_1498943 : Nat := 342079214529970716586219

theorem tailTrace_1498943 : CollatzResearch.WordTrace tailWord_1498943 prefixEnd_1498943 342079214529970716586219 := by
  unfold tailWord_1498943
  simp only [CollatzResearch.WordTrace]
  refine ⟨54670942608592984928381483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36447295072395323285587655 54670942608592984928381483)
  ·
    refine ⟨82006413912889477392572225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54670942608592984928381483 82006413912889477392572225)
    ·
      refine ⟨61504810434667108044429169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82006413912889477392572225 61504810434667108044429169)
      ·
        refine ⟨46128607826000331033321877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61504810434667108044429169 46128607826000331033321877)
        ·
          refine ⟨2162278491843765517186963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 46128607826000331033321877 2162278491843765517186963)
          ·
            refine ⟨3243417737765648275780445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2162278491843765517186963 3243417737765648275780445)
            ·
              refine ⟨1216281651662118103417667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3243417737765648275780445 1216281651662118103417667)
              ·
                refine ⟨1824422477493177155126501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1216281651662118103417667 1824422477493177155126501)
                ·
                  refine ⟨342079214529970716586219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1824422477493177155126501 342079214529970716586219)
                  ·
                    rfl

theorem cell21_1498943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 3, 1, 4].length) (baseStart_1498943 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1498943 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1498943 prefixEnd_1498943 := by exact prefixLift 1498943
  have htrace : WordTrace (prefixWord ++ tailWord_1498943) baseStart_1498943 baseEnd_1498943 := by
    simpa [prefixWord, tailWord_1498943, baseEnd_1498943] using wordTrace_append hprefix tailTrace_1498943
  have hstable : (prefixWord ++ tailWord_1498943).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498943).length < 2 ^ (prefixWord ++ tailWord_1498943).sum := by decide
  have hdescent : baseEnd_1498943 < baseStart_1498943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498954 : List Nat := [3, 1, 2, 1, 1, 1, 3, 4, 5]
def baseStart_1498954 : Nat := 118140960795 + 1498954 * 2 ^ 59
def prefixEnd_1498954 : Nat := 4983230072969 + 3 ^ 40 * 1498954 * 2
def baseEnd_1498954 : Nat := 342081724879837141902863

theorem tailTrace_1498954 : CollatzResearch.WordTrace tailWord_1498954 prefixEnd_1498954 342081724879837141902863 := by
  unfold tailWord_1498954
  simp only [CollatzResearch.WordTrace]
  refine ⟨13667835952888283451757979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36447562541035422538021277 13667835952888283451757979)
  ·
    refine ⟨20501753929332425177636969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13667835952888283451757979 20501753929332425177636969)
    ·
      refine ⟨15376315446999318883227727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20501753929332425177636969 15376315446999318883227727)
      ·
        refine ⟨23064473170498978324841591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15376315446999318883227727 23064473170498978324841591)
        ·
          refine ⟨34596709755748467487262387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23064473170498978324841591 34596709755748467487262387)
          ·
            refine ⟨51895064633622701230893581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34596709755748467487262387 51895064633622701230893581)
            ·
              refine ⟨19460649237608512961585093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51895064633622701230893581 19460649237608512961585093)
              ·
                refine ⟨3648871732051596180297205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19460649237608512961585093 3648871732051596180297205)
                ·
                  refine ⟨342081724879837141902863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3648871732051596180297205 342081724879837141902863)
                  ·
                    rfl

theorem cell21_1498954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 4, 5].length) (baseStart_1498954 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1498954 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1498954 prefixEnd_1498954 := by exact prefixLift 1498954
  have htrace : WordTrace (prefixWord ++ tailWord_1498954) baseStart_1498954 baseEnd_1498954 := by
    simpa [prefixWord, tailWord_1498954, baseEnd_1498954] using wordTrace_append hprefix tailTrace_1498954
  have hstable : (prefixWord ++ tailWord_1498954).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498954).length < 2 ^ (prefixWord ++ tailWord_1498954).sum := by decide
  have hdescent : baseEnd_1498954 < baseStart_1498954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498957 : List Nat := [1, 6, 1, 2, 1, 2, 1, 7]
def baseStart_1498957 : Nat := 118140960795 + 1498957 * 2 ^ 59
def prefixEnd_1498957 : Nat := 4983230072969 + 3 ^ 40 * 1498957 * 2
def baseEnd_1498957 : Nat := 114027469840236601117619

theorem tailTrace_1498957 : CollatzResearch.WordTrace tailWord_1498957 prefixEnd_1498957 114027469840236601117619 := by
  unfold tailWord_1498957
  simp only [CollatzResearch.WordTrace]
  refine ⟨54671453230542265319391125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36447635487028176879594083 54671453230542265319391125)
  ·
    refine ⟨2562724370181668686846459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 54671453230542265319391125 2562724370181668686846459)
    ·
      refine ⟨3844086555272503030269689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2562724370181668686846459 3844086555272503030269689)
      ·
        refine ⟨2883064916454377272702267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3844086555272503030269689 2883064916454377272702267)
        ·
          refine ⟨4324597374681565909053401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2883064916454377272702267 4324597374681565909053401)
          ·
            refine ⟨3243448031011174431790051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4324597374681565909053401 3243448031011174431790051)
            ·
              refine ⟨4865172046516761647685077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3243448031011174431790051 4865172046516761647685077)
              ·
                refine ⟨114027469840236601117619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4865172046516761647685077 114027469840236601117619)
                ·
                  rfl

theorem cell21_1498957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 7].length) (baseStart_1498957 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1498957 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1498957 prefixEnd_1498957 := by exact prefixLift 1498957
  have htrace : WordTrace (prefixWord ++ tailWord_1498957) baseStart_1498957 baseEnd_1498957 := by
    simpa [prefixWord, tailWord_1498957, baseEnd_1498957] using wordTrace_append hprefix tailTrace_1498957
  have hstable : (prefixWord ++ tailWord_1498957).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498957).length < 2 ^ (prefixWord ++ tailWord_1498957).sum := by decide
  have hdescent : baseEnd_1498957 < baseStart_1498957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499002 : List Nat := [3, 1, 1, 1, 1, 1, 8, 1, 4]
def baseStart_1499002 : Nat := 118140960795 + 1499002 * 2 ^ 59
def prefixEnd_1499002 : Nat := 4983230072969 + 3 ^ 40 * 1499002 * 2
def baseEnd_1499002 : Nat := 342092679133799725102765

theorem tailTrace_1499002 : CollatzResearch.WordTrace tailWord_1499002 prefixEnd_1499002 342092679133799725102765 := by
  unfold tailWord_1499002
  simp only [CollatzResearch.WordTrace]
  refine ⟨13668273628844809501194815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36448729676919492003186173 13668273628844809501194815)
  ·
    refine ⟨20502410443267214251792223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13668273628844809501194815 20502410443267214251792223)
    ·
      refine ⟨30753615664900821377688335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20502410443267214251792223 30753615664900821377688335)
      ·
        refine ⟨46130423497351232066532503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30753615664900821377688335 46130423497351232066532503)
        ·
          refine ⟨69195635246026848099798755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46130423497351232066532503 69195635246026848099798755)
          ·
            refine ⟨103793452869040272149698133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69195635246026848099798755 103793452869040272149698133)
            ·
              refine ⟨1216329525809065689254275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 103793452869040272149698133 1216329525809065689254275)
              ·
                refine ⟨1824494288713598533881413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1216329525809065689254275 1824494288713598533881413)
                ·
                  refine ⟨342092679133799725102765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1824494288713598533881413 342092679133799725102765)
                  ·
                    rfl

theorem cell21_1499002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 8, 1, 4].length) (baseStart_1499002 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1499002 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1499002 prefixEnd_1499002 := by exact prefixLift 1499002
  have htrace : WordTrace (prefixWord ++ tailWord_1499002) baseStart_1499002 baseEnd_1499002 := by
    simpa [prefixWord, tailWord_1499002, baseEnd_1499002] using wordTrace_append hprefix tailTrace_1499002
  have hstable : (prefixWord ++ tailWord_1499002).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499002).length < 2 ^ (prefixWord ++ tailWord_1499002).sum := by decide
  have hdescent : baseEnd_1499002 < baseStart_1499002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499126 : List Nat := [5, 1, 1, 1, 4, 2, 2, 5]
def baseStart_1499126 : Nat := 118140960795 + 1499126 * 2 ^ 59
def prefixEnd_1499126 : Nat := 4983230072969 + 3 ^ 40 * 1499126 * 2
def baseEnd_1499126 : Nat := 114040325874401021678615

theorem tailTrace_1499126 : CollatzResearch.WordTrace tailWord_1499126 prefixEnd_1499126 114040325874401021678615 := by
  unfold tailWord_1499126
  simp only [CollatzResearch.WordTrace]
  refine ⟨3417351072933125448893327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36451744777953338121528821 3417351072933125448893327)
  ·
    refine ⟨5126026609399688173339991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3417351072933125448893327 5126026609399688173339991)
    ·
      refine ⟨7689039914099532260009987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5126026609399688173339991 7689039914099532260009987)
      ·
        refine ⟨11533559871149298390014981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7689039914099532260009987 11533559871149298390014981)
        ·
          refine ⟨2162542475840493448127809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11533559871149298390014981 2162542475840493448127809)
          ·
            refine ⟨1621906856880370086095857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2162542475840493448127809 1621906856880370086095857)
            ·
              refine ⟨1216430142660277564571893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1621906856880370086095857 1216430142660277564571893)
              ·
                refine ⟨114040325874401021678615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1216430142660277564571893 114040325874401021678615)
                ·
                  rfl

theorem cell21_1499126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 2, 5].length) (baseStart_1499126 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1499126 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1499126 prefixEnd_1499126 := by exact prefixLift 1499126
  have htrace : WordTrace (prefixWord ++ tailWord_1499126) baseStart_1499126 baseEnd_1499126 := by
    simpa [prefixWord, tailWord_1499126, baseEnd_1499126] using wordTrace_append hprefix tailTrace_1499126
  have hstable : (prefixWord ++ tailWord_1499126).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499126).length < 2 ^ (prefixWord ++ tailWord_1499126).sum := by decide
  have hdescent : baseEnd_1499126 < baseStart_1499126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499157 : List Nat := [1, 3, 2, 1, 5, 1, 3, 2, 3]
def baseStart_1499157 : Nat := 118140960795 + 1499157 * 2 ^ 59
def prefixEnd_1499157 : Nat := 4983230072969 + 3 ^ 40 * 1499157 * 2
def baseEnd_1499157 : Nat := 342128052245553900019115

theorem tailTrace_1499157 : CollatzResearch.WordTrace tailWord_1499157 prefixEnd_1499157 342128052245553900019115 := by
  unfold tailWord_1499157
  simp only [CollatzResearch.WordTrace]
  refine ⟨54678747829817699476671725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36452498553211799651114483 54678747829817699476671725)
  ·
    refine ⟨20504530436181637303751897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54678747829817699476671725 20504530436181637303751897)
    ·
      refine ⟨15378397827136227977813923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20504530436181637303751897 15378397827136227977813923)
      ·
        refine ⟨23067596740704341966720885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15378397827136227977813923 23067596740704341966720885)
        ·
          refine ⟨2162587194441032059380083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23067596740704341966720885 2162587194441032059380083)
          ·
            refine ⟨3243880791661548089070125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2162587194441032059380083 3243880791661548089070125)
            ·
              refine ⟨1216455296873080533401297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3243880791661548089070125 1216455296873080533401297)
              ·
                refine ⟨912341472654810400050973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1216455296873080533401297 912341472654810400050973)
                ·
                  refine ⟨342128052245553900019115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 912341472654810400050973 342128052245553900019115)
                  ·
                    rfl

theorem cell21_1499157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 3, 2, 3].length) (baseStart_1499157 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1499157 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1499157 prefixEnd_1499157 := by exact prefixLift 1499157
  have htrace : WordTrace (prefixWord ++ tailWord_1499157) baseStart_1499157 baseEnd_1499157 := by
    simpa [prefixWord, tailWord_1499157, baseEnd_1499157] using wordTrace_append hprefix tailTrace_1499157
  have hstable : (prefixWord ++ tailWord_1499157).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499157).length < 2 ^ (prefixWord ++ tailWord_1499157).sum := by decide
  have hdescent : baseEnd_1499157 < baseStart_1499157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499244 : List Nat := [2, 2, 1, 1, 3, 4, 3, 5]
def baseStart_1499244 : Nat := 118140960795 + 1499244 * 2 ^ 59
def prefixEnd_1499244 : Nat := 4983230072969 + 3 ^ 40 * 1499244 * 2
def baseEnd_1499244 : Nat := 114049302276953694022979

theorem tailTrace_1499244 : CollatzResearch.WordTrace tailWord_1499244 prefixEnd_1499244 114049302276953694022979 := by
  unfold tailWord_1499244
  simp only [CollatzResearch.WordTrace]
  refine ⟨27340960490251256667544393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36454613987001675556725857 27340960490251256667544393)
  ·
    refine ⟨20505720367688442500658295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27340960490251256667544393 20505720367688442500658295)
    ·
      refine ⟨30758580551532663750987443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20505720367688442500658295 30758580551532663750987443)
      ·
        refine ⟨46137870827298995626481165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30758580551532663750987443 46137870827298995626481165)
        ·
          refine ⟨17301701560237123359930437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46137870827298995626481165 17301701560237123359930437)
          ·
            refine ⟨3244069042544460629986957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17301701560237123359930437 3244069042544460629986957)
            ·
              refine ⟨1216525890954172736245109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3244069042544460629986957 1216525890954172736245109)
              ·
                refine ⟨114049302276953694022979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1216525890954172736245109 114049302276953694022979)
                ·
                  rfl

theorem cell21_1499244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 3, 5].length) (baseStart_1499244 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1499244 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1499244 prefixEnd_1499244 := by exact prefixLift 1499244
  have htrace : WordTrace (prefixWord ++ tailWord_1499244) baseStart_1499244 baseEnd_1499244 := by
    simpa [prefixWord, tailWord_1499244, baseEnd_1499244] using wordTrace_append hprefix tailTrace_1499244
  have hstable : (prefixWord ++ tailWord_1499244).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499244).length < 2 ^ (prefixWord ++ tailWord_1499244).sum := by decide
  have hdescent : baseEnd_1499244 < baseStart_1499244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499309 : List Nat := [1, 5, 2, 1, 2, 3, 1, 3, 3]
def baseStart_1499309 : Nat := 118140960795 + 1499309 * 2 ^ 59
def prefixEnd_1499309 : Nat := 4983230072969 + 3 ^ 40 * 1499309 * 2
def baseEnd_1499309 : Nat := 342162740716435413485471

theorem tailTrace_1499309 : CollatzResearch.WordTrace tailWord_1499309 prefixEnd_1499309 342162740716435413485471 := by
  unfold tailWord_1499309
  simp only [CollatzResearch.WordTrace]
  refine ⟨54684291725267029436204981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36456194483511352957469987 54684291725267029436204981)
  ·
    refine ⟨5126652349243784009644217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54684291725267029436204981 5126652349243784009644217)
    ·
      refine ⟨3844989261932838007233163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5126652349243784009644217 3844989261932838007233163)
      ·
        refine ⟨5767483892899257010849745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3844989261932838007233163 5767483892899257010849745)
        ·
          refine ⟨4325612919674442758137309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5767483892899257010849745 4325612919674442758137309)
          ·
            refine ⟨1622104844877916034301491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4325612919674442758137309 1622104844877916034301491)
            ·
              refine ⟨2433157267316874051452237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1622104844877916034301491 2433157267316874051452237)
              ·
                refine ⟨912433975243827769294589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2433157267316874051452237 912433975243827769294589)
                ·
                  refine ⟨342162740716435413485471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 912433975243827769294589 342162740716435413485471)
                  ·
                    rfl

theorem cell21_1499309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 3, 3].length) (baseStart_1499309 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1499309 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1499309 prefixEnd_1499309 := by exact prefixLift 1499309
  have htrace : WordTrace (prefixWord ++ tailWord_1499309) baseStart_1499309 baseEnd_1499309 := by
    simpa [prefixWord, tailWord_1499309, baseEnd_1499309] using wordTrace_append hprefix tailTrace_1499309
  have hstable : (prefixWord ++ tailWord_1499309).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499309).length < 2 ^ (prefixWord ++ tailWord_1499309).sum := by decide
  have hdescent : baseEnd_1499309 < baseStart_1499309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499340 : List Nat := [2, 2, 1, 6, 1, 2, 2, 1, 4]
def baseStart_1499340 : Nat := 118140960795 + 1499340 * 2 ^ 59
def prefixEnd_1499340 : Nat := 4983230072969 + 3 ^ 40 * 1499340 * 2
def baseEnd_1499340 : Nat := 342169815338786248468741

theorem tailTrace_1499340 : CollatzResearch.WordTrace tailWord_1499340 prefixEnd_1499340 342169815338786248468741 := by
  unfold tailWord_1499340
  simp only [CollatzResearch.WordTrace]
  refine ⟨27342711194077360865291737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36456948258769814487055649 27342711194077360865291737)
  ·
    refine ⟨20507033395558020648968803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27342711194077360865291737 20507033395558020648968803)
    ·
      refine ⟨30760550093337030973453205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20507033395558020648968803 30760550093337030973453205)
      ·
        refine ⟨1441900785625173326880619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 30760550093337030973453205 1441900785625173326880619)
        ·
          refine ⟨2162851178437759990320929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1441900785625173326880619 2162851178437759990320929)
          ·
            refine ⟨1622138383828319992740697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2162851178437759990320929 1622138383828319992740697)
            ·
              refine ⟨1216603787871239994555523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1622138383828319992740697 1216603787871239994555523)
              ·
                refine ⟨1824905681806859991833285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1216603787871239994555523 1824905681806859991833285)
                ·
                  refine ⟨342169815338786248468741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1824905681806859991833285 342169815338786248468741)
                  ·
                    rfl

theorem cell21_1499340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 2, 1, 4].length) (baseStart_1499340 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1499340 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1499340 prefixEnd_1499340 := by exact prefixLift 1499340
  have htrace : WordTrace (prefixWord ++ tailWord_1499340) baseStart_1499340 baseEnd_1499340 := by
    simpa [prefixWord, tailWord_1499340, baseEnd_1499340] using wordTrace_append hprefix tailTrace_1499340
  have hstable : (prefixWord ++ tailWord_1499340).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499340).length < 2 ^ (prefixWord ++ tailWord_1499340).sum := by decide
  have hdescent : baseEnd_1499340 < baseStart_1499340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499427 : List Nat := [1, 1, 1, 4, 2, 2, 4, 3, 3]
def baseStart_1499427 : Nat := 118140960795 + 1499427 * 2 ^ 59
def prefixEnd_1499427 : Nat := 4983230072969 + 3 ^ 40 * 1499427 * 2
def baseEnd_1499427 : Nat := 342189669924093430518563

theorem tailTrace_1499427 : CollatzResearch.WordTrace tailWord_1499427 prefixEnd_1499427 342189669924093430518563 := by
  unfold tailWord_1499427
  simp only [CollatzResearch.WordTrace]
  refine ⟨54688595538839535589000535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36459063692559690392667023 54688595538839535589000535)
  ·
    refine ⟨82032893308259303383500803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54688595538839535589000535 82032893308259303383500803)
    ·
      refine ⟨123049339962388955075251205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82032893308259303383500803 123049339962388955075251205)
      ·
        refine ⟨23071751242947929076609601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123049339962388955075251205 23071751242947929076609601)
        ·
          refine ⟨17303813432210946807457201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23071751242947929076609601 17303813432210946807457201)
          ·
            refine ⟨12977860074158210105592901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17303813432210946807457201 12977860074158210105592901)
            ·
              refine ⟨2433348763904664394798669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12977860074158210105592901 2433348763904664394798669)
              ·
                refine ⟨912505786464249148049501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2433348763904664394798669 912505786464249148049501)
                ·
                  refine ⟨342189669924093430518563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 912505786464249148049501 342189669924093430518563)
                  ·
                    rfl

theorem cell21_1499427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 3, 3].length) (baseStart_1499427 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1499427 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1499427 prefixEnd_1499427 := by exact prefixLift 1499427
  have htrace : WordTrace (prefixWord ++ tailWord_1499427) baseStart_1499427 baseEnd_1499427 := by
    simpa [prefixWord, tailWord_1499427, baseEnd_1499427] using wordTrace_append hprefix tailTrace_1499427
  have hstable : (prefixWord ++ tailWord_1499427).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499427).length < 2 ^ (prefixWord ++ tailWord_1499427).sum := by decide
  have hdescent : baseEnd_1499427 < baseStart_1499427 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499441 : List Nat := [1, 2, 2, 3, 4, 1, 1, 1, 6]
def baseStart_1499441 : Nat := 118140960795 + 1499441 * 2 ^ 59
def prefixEnd_1499441 : Nat := 4983230072969 + 3 ^ 40 * 1499441 * 2
def baseEnd_1499441 : Nat := 342192864914832517285201

theorem tailTrace_1499441 : CollatzResearch.WordTrace tailWord_1499441 prefixEnd_1499441 342192864914832517285201 := by
  unfold tailWord_1499441
  simp only [CollatzResearch.WordTrace]
  refine ⟨54689106160788815980010177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36459404107192543986673451 54689106160788815980010177)
  ·
    refine ⟨41016829620591611985007633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54689106160788815980010177 41016829620591611985007633)
    ·
      refine ⟨30762622215443708988755725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41016829620591611985007633 30762622215443708988755725)
      ·
        refine ⟨11535983330791390870783397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30762622215443708988755725 11535983330791390870783397)
        ·
          refine ⟨2162996874523385788271887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11535983330791390870783397 2162996874523385788271887)
          ·
            refine ⟨3244495311785078682407831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2162996874523385788271887 3244495311785078682407831)
            ·
              refine ⟨4866742967677618023611747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3244495311785078682407831 4866742967677618023611747)
              ·
                refine ⟨7300114451516427035417621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4866742967677618023611747 7300114451516427035417621)
                ·
                  refine ⟨342192864914832517285201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7300114451516427035417621 342192864914832517285201)
                  ·
                    rfl

theorem cell21_1499441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 1, 6].length) (baseStart_1499441 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1499441 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1499441 prefixEnd_1499441 := by exact prefixLift 1499441
  have htrace : WordTrace (prefixWord ++ tailWord_1499441) baseStart_1499441 baseEnd_1499441 := by
    simpa [prefixWord, tailWord_1499441, baseEnd_1499441] using wordTrace_append hprefix tailTrace_1499441
  have hstable : (prefixWord ++ tailWord_1499441).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499441).length < 2 ^ (prefixWord ++ tailWord_1499441).sum := by decide
  have hdescent : baseEnd_1499441 < baseStart_1499441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499444 : List Nat := [2, 5, 1, 1, 1, 2, 2, 4, 3]
def baseStart_1499444 : Nat := 118140960795 + 1499444 * 2 ^ 59
def prefixEnd_1499444 : Nat := 4983230072969 + 3 ^ 40 * 1499444 * 2
def baseEnd_1499444 : Nat := 342193549555705178735195

theorem tailTrace_1499444 : CollatzResearch.WordTrace tailWord_1499444 prefixEnd_1499444 342193549555705178735195 := by
  unfold tailWord_1499444
  simp only [CollatzResearch.WordTrace]
  refine ⟨27344607789888973746184693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36459477053185298328246257 27344607789888973746184693)
  ·
    refine ⟨2563556980302091288704815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27344607789888973746184693 2563556980302091288704815)
    ·
      refine ⟨3845335470453136933057223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2563556980302091288704815 3845335470453136933057223)
      ·
        refine ⟨5768003205679705399585835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3845335470453136933057223 5768003205679705399585835)
        ·
          refine ⟨8652004808519558099378753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5768003205679705399585835 8652004808519558099378753)
          ·
            refine ⟨6489003606389668574534065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8652004808519558099378753 6489003606389668574534065)
            ·
              refine ⟨4866752704792251430900549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6489003606389668574534065 4866752704792251430900549)
              ·
                refine ⟨912516132148547143293853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4866752704792251430900549 912516132148547143293853)
                ·
                  refine ⟨342193549555705178735195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 912516132148547143293853 342193549555705178735195)
                  ·
                    rfl

theorem cell21_1499444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_1499444 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1499444 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1499444 prefixEnd_1499444 := by exact prefixLift 1499444
  have htrace : WordTrace (prefixWord ++ tailWord_1499444) baseStart_1499444 baseEnd_1499444 := by
    simpa [prefixWord, tailWord_1499444, baseEnd_1499444] using wordTrace_append hprefix tailTrace_1499444
  have hstable : (prefixWord ++ tailWord_1499444).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499444).length < 2 ^ (prefixWord ++ tailWord_1499444).sum := by decide
  have hdescent : baseEnd_1499444 < baseStart_1499444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499472 : List Nat := [2, 1, 1, 1, 1, 8, 2, 5]
def baseStart_1499472 : Nat := 118140960795 + 1499472 * 2 ^ 59
def prefixEnd_1499472 : Nat := 4983230072969 + 3 ^ 40 * 1499472 * 2
def baseEnd_1499472 : Nat := 114066646512394450756157

theorem tailTrace_1499472 : CollatzResearch.WordTrace tailWord_1499472 prefixEnd_1499472 114066646512394450756157 := by
  unfold tailWord_1499472
  simp only [CollatzResearch.WordTrace]
  refine ⟨27345118411838254137194335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36460157882451005516259113 27345118411838254137194335)
  ·
    refine ⟨41017677617757381205791503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27345118411838254137194335 41017677617757381205791503)
    ·
      refine ⟨61526516426636071808687255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41017677617757381205791503 61526516426636071808687255)
      ·
        refine ⟨92289774639954107713030883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61526516426636071808687255 92289774639954107713030883)
        ·
          refine ⟨138434661959931161569546325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92289774639954107713030883 138434661959931161569546325)
          ·
            refine ⟨1622281194842943299643121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 138434661959931161569546325 1622281194842943299643121)
            ·
              refine ⟨1216710896132207474732341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1622281194842943299643121 1216710896132207474732341)
              ·
                refine ⟨114066646512394450756157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1216710896132207474732341 114066646512394450756157)
                ·
                  rfl

theorem cell21_1499472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 2, 5].length) (baseStart_1499472 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1499472 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1499472 prefixEnd_1499472 := by exact prefixLift 1499472
  have htrace : WordTrace (prefixWord ++ tailWord_1499472) baseStart_1499472 baseEnd_1499472 := by
    simpa [prefixWord, tailWord_1499472, baseEnd_1499472] using wordTrace_append hprefix tailTrace_1499472
  have hstable : (prefixWord ++ tailWord_1499472).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499472).length < 2 ^ (prefixWord ++ tailWord_1499472).sum := by decide
  have hdescent : baseEnd_1499472 < baseStart_1499472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499517 : List Nat := [1, 4, 1, 1, 2, 4, 1, 3, 4]
def baseStart_1499517 : Nat := 118140960795 + 1499517 * 2 ^ 59
def prefixEnd_1499517 : Nat := 4983230072969 + 3 ^ 40 * 1499517 * 2
def baseEnd_1499517 : Nat := 342210209150273274018379

theorem tailTrace_1499517 : CollatzResearch.WordTrace tailWord_1499517 prefixEnd_1499517 342210209150273274018379 := by
  unfold tailWord_1499517
  simp only [CollatzResearch.WordTrace]
  refine ⟨54691878108513480959776805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36461252072342320639851203 54691878108513480959776805)
  ·
    refine ⟨10254727145346277679958151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54691878108513480959776805 10254727145346277679958151)
    ·
      refine ⟨15382090718019416519937227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10254727145346277679958151 15382090718019416519937227)
      ·
        refine ⟨23073136077029124779905841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15382090718019416519937227 23073136077029124779905841)
        ·
          refine ⟨17304852057771843584929381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23073136077029124779905841 17304852057771843584929381)
          ·
            refine ⟨3244659760832220672174259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17304852057771843584929381 3244659760832220672174259)
            ·
              refine ⟨4866989641248331008261389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3244659760832220672174259 4866989641248331008261389)
              ·
                refine ⟨1825121115468124128098021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4866989641248331008261389 1825121115468124128098021)
                ·
                  refine ⟨342210209150273274018379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1825121115468124128098021 342210209150273274018379)
                  ·
                    rfl

theorem cell21_1499517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 3, 4].length) (baseStart_1499517 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1499517 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1499517 prefixEnd_1499517 := by exact prefixLift 1499517
  have htrace : WordTrace (prefixWord ++ tailWord_1499517) baseStart_1499517 baseEnd_1499517 := by
    simpa [prefixWord, tailWord_1499517, baseEnd_1499517] using wordTrace_append hprefix tailTrace_1499517
  have hstable : (prefixWord ++ tailWord_1499517).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499517).length < 2 ^ (prefixWord ++ tailWord_1499517).sum := by decide
  have hdescent : baseEnd_1499517 < baseStart_1499517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499565 : List Nat := [1, 5, 2, 2, 2, 2, 1, 6]
def baseStart_1499565 : Nat := 118140960795 + 1499565 * 2 ^ 59
def prefixEnd_1499565 : Nat := 4983230072969 + 3 ^ 40 * 1499565 * 2
def baseEnd_1499565 : Nat := 114073721134745285739427

theorem tailTrace_1499565 : CollatzResearch.WordTrace tailWord_1499565 prefixEnd_1499565 114073721134745285739427 := by
  unfold tailWord_1499565
  simp only [CollatzResearch.WordTrace]
  refine ⟨54693628812339585157524149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36462419208226390105016099 54693628812339585157524149)
  ·
    refine ⟨5127527701156836108517889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54693628812339585157524149 5127527701156836108517889)
    ·
      refine ⟨3845645775867627081388417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5127527701156836108517889 3845645775867627081388417)
      ·
        refine ⟨2884234331900720311041313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3845645775867627081388417 2884234331900720311041313)
        ·
          refine ⟨2163175748925540233280985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2884234331900720311041313 2163175748925540233280985)
          ·
            refine ⟨1622381811694155174960739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2163175748925540233280985 1622381811694155174960739)
            ·
              refine ⟨2433572717541232762441109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1622381811694155174960739 2433572717541232762441109)
              ·
                refine ⟨114073721134745285739427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2433572717541232762441109 114073721134745285739427)
                ·
                  rfl

theorem cell21_1499565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 6].length) (baseStart_1499565 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1499565 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1499565 prefixEnd_1499565 := by exact prefixLift 1499565
  have htrace : WordTrace (prefixWord ++ tailWord_1499565) baseStart_1499565 baseEnd_1499565 := by
    simpa [prefixWord, tailWord_1499565, baseEnd_1499565] using wordTrace_append hprefix tailTrace_1499565
  have hstable : (prefixWord ++ tailWord_1499565).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499565).length < 2 ^ (prefixWord ++ tailWord_1499565).sum := by decide
  have hdescent : baseEnd_1499565 < baseStart_1499565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499596 : List Nat := [2, 2, 1, 4, 3, 1, 2, 3, 3]
def baseStart_1499596 : Nat := 118140960795 + 1499596 * 2 ^ 59
def prefixEnd_1499596 : Nat := 4983230072969 + 3 ^ 40 * 1499596 * 2
def baseEnd_1499596 : Nat := 342228238026586692201551

theorem tailTrace_1499596 : CollatzResearch.WordTrace tailWord_1499596 prefixEnd_1499596 342228238026586692201551 := by
  unfold tailWord_1499596
  simp only [CollatzResearch.WordTrace]
  refine ⟨27347379737613638725951321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36463172983484851634601761 27347379737613638725951321)
  ·
    refine ⟨20510534803210229044463491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27347379737613638725951321 20510534803210229044463491)
    ·
      refine ⟨30765802204815343566695237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20510534803210229044463491 30765802204815343566695237)
      ·
        refine ⟨5768587913402876918755357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30765802204815343566695237 5768587913402876918755357)
        ·
          refine ⟨2163220467526078844533259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5768587913402876918755357 2163220467526078844533259)
          ·
            refine ⟨3244830701289118266799889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2163220467526078844533259 3244830701289118266799889)
            ·
              refine ⟨2433623025966838700099917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3244830701289118266799889 2433623025966838700099917)
              ·
                refine ⟨912608634737564512537469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2433623025966838700099917 912608634737564512537469)
                ·
                  refine ⟨342228238026586692201551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 912608634737564512537469 342228238026586692201551)
                  ·
                    rfl

theorem cell21_1499596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 3, 3].length) (baseStart_1499596 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1499596 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1499596 prefixEnd_1499596 := by exact prefixLift 1499596
  have htrace : WordTrace (prefixWord ++ tailWord_1499596) baseStart_1499596 baseEnd_1499596 := by
    simpa [prefixWord, tailWord_1499596, baseEnd_1499596] using wordTrace_append hprefix tailTrace_1499596
  have hstable : (prefixWord ++ tailWord_1499596).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499596).length < 2 ^ (prefixWord ++ tailWord_1499596).sum := by decide
  have hdescent : baseEnd_1499596 < baseStart_1499596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499638 : List Nat := [5, 1, 1, 1, 2, 1, 1, 4, 5]
def baseStart_1499638 : Nat := 118140960795 + 1499638 * 2 ^ 59
def prefixEnd_1499638 : Nat := 4983230072969 + 3 ^ 40 * 1499638 * 2
def baseEnd_1499638 : Nat := 342237822998803952501465

theorem tailTrace_1499638 : CollatzResearch.WordTrace tailWord_1499638 prefixEnd_1499638 342237822998803952501465 := by
  unfold tailWord_1499638
  simp only [CollatzResearch.WordTrace]
  refine ⟨3418518208817194914058223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36464194227383412416621045 3418518208817194914058223)
  ·
    refine ⟨5127777313225792371087335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3418518208817194914058223 5127777313225792371087335)
    ·
      refine ⟨7691665969838688556631003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5127777313225792371087335 7691665969838688556631003)
      ·
        refine ⟨11537498954758032834946505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7691665969838688556631003 11537498954758032834946505)
        ·
          refine ⟨8653124216068524626209879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11537498954758032834946505 8653124216068524626209879)
          ·
            refine ⟨12979686324102786939314819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8653124216068524626209879 12979686324102786939314819)
            ·
              refine ⟨19469529486154180408972229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12979686324102786939314819 19469529486154180408972229)
              ·
                refine ⟨3650536778653908826682293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19469529486154180408972229 3650536778653908826682293)
                ·
                  refine ⟨342237822998803952501465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3650536778653908826682293 342237822998803952501465)
                  ·
                    rfl

theorem cell21_1499638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_1499638 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1499638 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1499638 prefixEnd_1499638 := by exact prefixLift 1499638
  have htrace : WordTrace (prefixWord ++ tailWord_1499638) baseStart_1499638 baseEnd_1499638 := by
    simpa [prefixWord, tailWord_1499638, baseEnd_1499638] using wordTrace_append hprefix tailTrace_1499638
  have hstable : (prefixWord ++ tailWord_1499638).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499638).length < 2 ^ (prefixWord ++ tailWord_1499638).sum := by decide
  have hdescent : baseEnd_1499638 < baseStart_1499638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499672 : List Nat := [2, 1, 2, 3, 3, 2, 3, 2, 3]
def baseStart_1499672 : Nat := 118140960795 + 1499672 * 2 ^ 59
def prefixEnd_1499672 : Nat := 4983230072969 + 3 ^ 40 * 1499672 * 2
def baseEnd_1499672 : Nat := 342245582262027448934729

theorem tailTrace_1499672 : CollatzResearch.WordTrace tailWord_1499672 prefixEnd_1499672 342245582262027448934729 := by
  unfold tailWord_1499672
  simp only [CollatzResearch.WordTrace]
  refine ⟨27348765711475971215834635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36465020948634628287779513 27348765711475971215834635)
  ·
    refine ⟨41023148567213956823751953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27348765711475971215834635 41023148567213956823751953)
    ·
      refine ⟨30767361425410467617813965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41023148567213956823751953 30767361425410467617813965)
      ·
        refine ⟨11537760534528925356680237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30767361425410467617813965 11537760534528925356680237)
        ·
          refine ⟨4326660200448347008755089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11537760534528925356680237 4326660200448347008755089)
          ·
            refine ⟨3244995150336260256566317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4326660200448347008755089 3244995150336260256566317)
            ·
              refine ⟨1216873181376097596212369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3244995150336260256566317 1216873181376097596212369)
              ·
                refine ⟨912654886032073197159277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1216873181376097596212369 912654886032073197159277)
                ·
                  refine ⟨342245582262027448934729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 912654886032073197159277 342245582262027448934729)
                  ·
                    rfl

theorem cell21_1499672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 3, 2, 3].length) (baseStart_1499672 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1499672 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1499672 prefixEnd_1499672 := by exact prefixLift 1499672
  have htrace : WordTrace (prefixWord ++ tailWord_1499672) baseStart_1499672 baseEnd_1499672 := by
    simpa [prefixWord, tailWord_1499672, baseEnd_1499672] using wordTrace_append hprefix tailTrace_1499672
  have hstable : (prefixWord ++ tailWord_1499672).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499672).length < 2 ^ (prefixWord ++ tailWord_1499672).sum := by decide
  have hdescent : baseEnd_1499672 < baseStart_1499672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499683 : List Nat := [1, 1, 1, 4, 4, 2, 2, 6]
def baseStart_1499683 : Nat := 118140960795 + 1499683 * 2 ^ 59
def prefixEnd_1499683 : Nat := 4983230072969 + 3 ^ 40 * 1499683 * 2
def baseEnd_1499683 : Nat := 114082697537297958083791

theorem tailTrace_1499683 : CollatzResearch.WordTrace tailWord_1499683 prefixEnd_1499683 114082697537297958083791 := by
  unfold tailWord_1499683
  simp only [CollatzResearch.WordTrace]
  refine ⟨54697932625912091310319703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36465288417274727540213135 54697932625912091310319703)
  ·
    refine ⟨82046898938868136965479555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54697932625912091310319703 82046898938868136965479555)
    ·
      refine ⟨123070348408302205448219333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82046898938868136965479555 123070348408302205448219333)
      ·
        refine ⟨23075690326556663521541125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123070348408302205448219333 23075690326556663521541125)
        ·
          refine ⟨4326691936229374410288961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23075690326556663521541125 4326691936229374410288961)
          ·
            refine ⟨3245018952172030807716721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4326691936229374410288961 3245018952172030807716721)
            ·
              refine ⟨2433764214129023105787541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3245018952172030807716721 2433764214129023105787541)
              ·
                refine ⟨114082697537297958083791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2433764214129023105787541 114082697537297958083791)
                ·
                  rfl

theorem cell21_1499683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 6].length) (baseStart_1499683 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1499683 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1499683 prefixEnd_1499683 := by exact prefixLift 1499683
  have htrace : WordTrace (prefixWord ++ tailWord_1499683) baseStart_1499683 baseEnd_1499683 := by
    simpa [prefixWord, tailWord_1499683, baseEnd_1499683] using wordTrace_append hprefix tailTrace_1499683
  have hstable : (prefixWord ++ tailWord_1499683).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499683).length < 2 ^ (prefixWord ++ tailWord_1499683).sum := by decide
  have hdescent : baseEnd_1499683 < baseStart_1499683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499697 : List Nat := [1, 2, 2, 3, 1, 1, 2, 4, 5]
def baseStart_1499697 : Nat := 118140960795 + 1499697 * 2 ^ 59
def prefixEnd_1499697 : Nat := 4983230072969 + 3 ^ 40 * 1499697 * 2
def baseEnd_1499697 : Nat := 342251287602632961018011

theorem tailTrace_1499697 : CollatzResearch.WordTrace tailWord_1499697 prefixEnd_1499697 342251287602632961018011 := by
  unfold tailWord_1499697
  simp only [CollatzResearch.WordTrace]
  refine ⟨54698443247861371701329345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36465628831907581134219563 54698443247861371701329345)
  ·
    refine ⟨41023832435896028775997009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54698443247861371701329345 41023832435896028775997009)
    ·
      refine ⟨30767874326922021581997757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41023832435896028775997009 30767874326922021581997757)
      ·
        refine ⟨11537952872595758093249159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30767874326922021581997757 11537952872595758093249159)
        ·
          refine ⟨17306929308893637139873739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11537952872595758093249159 17306929308893637139873739)
          ·
            refine ⟨25960393963340455709810609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17306929308893637139873739 25960393963340455709810609)
            ·
              refine ⟨19470295472505341782357957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25960393963340455709810609 19470295472505341782357957)
              ·
                refine ⟨3650680401094751584192117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19470295472505341782357957 3650680401094751584192117)
                ·
                  refine ⟨342251287602632961018011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3650680401094751584192117 342251287602632961018011)
                  ·
                    rfl

theorem cell21_1499697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 4, 5].length) (baseStart_1499697 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1499697 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1499697 prefixEnd_1499697 := by exact prefixLift 1499697
  have htrace : WordTrace (prefixWord ++ tailWord_1499697) baseStart_1499697 baseEnd_1499697 := by
    simpa [prefixWord, tailWord_1499697, baseEnd_1499697] using wordTrace_append hprefix tailTrace_1499697
  have hstable : (prefixWord ++ tailWord_1499697).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499697).length < 2 ^ (prefixWord ++ tailWord_1499697).sum := by decide
  have hdescent : baseEnd_1499697 < baseStart_1499697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499790 : List Nat := [4, 1, 1, 3, 1, 1, 4, 1, 5]
def baseStart_1499790 : Nat := 118140960795 + 1499790 * 2 ^ 59
def prefixEnd_1499790 : Nat := 4983230072969 + 3 ^ 40 * 1499790 * 2
def baseEnd_1499790 : Nat := 342272511469685465967821

theorem tailTrace_1499790 : CollatzResearch.WordTrace tailWord_1499790 prefixEnd_1499790 342272511469685465967821 := by
  unfold tailWord_1499790
  simp only [CollatzResearch.WordTrace]
  refine ⟨6837729404565556073058103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36467890157682965722976549 6837729404565556073058103)
  ·
    refine ⟨10256594106848334109587155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6837729404565556073058103 10256594106848334109587155)
    ·
      refine ⟨15384891160272501164380733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10256594106848334109587155 15384891160272501164380733)
      ·
        refine ⟨5769334185102187936642775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15384891160272501164380733 5769334185102187936642775)
        ·
          refine ⟨8654001277653281904964163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5769334185102187936642775 8654001277653281904964163)
          ·
            refine ⟨12981001916479922857446245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8654001277653281904964163 12981001916479922857446245)
            ·
              refine ⟨2433937859339985535771171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12981001916479922857446245 2433937859339985535771171)
              ·
                refine ⟨3650906789009978303656757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2433937859339985535771171 3650906789009978303656757)
                ·
                  refine ⟨342272511469685465967821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3650906789009978303656757 342272511469685465967821)
                  ·
                    rfl

theorem cell21_1499790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 1, 5].length) (baseStart_1499790 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1499790 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1499790 prefixEnd_1499790 := by exact prefixLift 1499790
  have htrace : WordTrace (prefixWord ++ tailWord_1499790) baseStart_1499790 baseEnd_1499790 := by
    simpa [prefixWord, tailWord_1499790, baseEnd_1499790] using wordTrace_append hprefix tailTrace_1499790
  have hstable : (prefixWord ++ tailWord_1499790).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499790).length < 2 ^ (prefixWord ++ tailWord_1499790).sum := by decide
  have hdescent : baseEnd_1499790 < baseStart_1499790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499841 : List Nat := [1, 2, 6, 2, 2, 1, 1, 1, 5]
def baseStart_1499841 : Nat := 118140960795 + 1499841 * 2 ^ 59
def prefixEnd_1499841 : Nat := 4983230072969 + 3 ^ 40 * 1499841 * 2
def baseEnd_1499841 : Nat := 342284150364520710617717

theorem tailTrace_1499841 : CollatzResearch.WordTrace tailWord_1499841 prefixEnd_1499841 342284150364520710617717 := by
  unfold tailWord_1499841
  simp only [CollatzResearch.WordTrace]
  refine ⟨54703695359339684294571377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36469130239559789529714251 54703695359339684294571377)
  ·
    refine ⟨41027771519504763220928533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54703695359339684294571377 41027771519504763220928533)
    ·
      refine ⟨1923176789976785775981025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 41027771519504763220928533 1923176789976785775981025)
      ·
        refine ⟨1442382592482589331985769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1923176789976785775981025 1442382592482589331985769)
        ·
          refine ⟨1081786944361941998989327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1442382592482589331985769 1081786944361941998989327)
          ·
            refine ⟨1622680416542912998483991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1081786944361941998989327 1622680416542912998483991)
            ·
              refine ⟨2434020624814369497725987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1622680416542912998483991 2434020624814369497725987)
              ·
                refine ⟨3651030937221554246588981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2434020624814369497725987 3651030937221554246588981)
                ·
                  refine ⟨342284150364520710617717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3651030937221554246588981 342284150364520710617717)
                  ·
                    rfl

theorem cell21_1499841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 1, 5].length) (baseStart_1499841 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1499841 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1499841 prefixEnd_1499841 := by exact prefixLift 1499841
  have htrace : WordTrace (prefixWord ++ tailWord_1499841) baseStart_1499841 baseEnd_1499841 := by
    simpa [prefixWord, tailWord_1499841, baseEnd_1499841] using wordTrace_append hprefix tailTrace_1499841
  have hstable : (prefixWord ++ tailWord_1499841).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499841).length < 2 ^ (prefixWord ++ tailWord_1499841).sum := by decide
  have hdescent : baseEnd_1499841 < baseStart_1499841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499900 : List Nat := [2, 2, 2, 1, 3, 4, 2, 2, 3]
def baseStart_1499900 : Nat := 118140960795 + 1499900 * 2 ^ 59
def prefixEnd_1499900 : Nat := 4983230072969 + 3 ^ 40 * 1499900 * 2
def baseEnd_1499900 : Nat := 342297614968349719134263

theorem tailTrace_1499900 : CollatzResearch.WordTrace tailWord_1499900 prefixEnd_1499900 342297614968349719134263 := by
  unfold tailWord_1499900
  simp only [CollatzResearch.WordTrace]
  refine ⟨27352923633062968685484577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36470564844083958247312769 27352923633062968685484577)
  ·
    refine ⟨20514692724797226514113433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27352923633062968685484577 20514692724797226514113433)
    ·
      refine ⟨15386019543597919885585075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20514692724797226514113433 15386019543597919885585075)
      ·
        refine ⟨23079029315396879828377613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15386019543597919885585075 23079029315396879828377613)
        ·
          refine ⟨8654635993273829935641605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23079029315396879828377613 8654635993273829935641605)
          ·
            refine ⟨1622744248738843112932801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8654635993273829935641605 1622744248738843112932801)
            ·
              refine ⟨1217058186554132334699601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1622744248738843112932801 1217058186554132334699601)
              ·
                refine ⟨912793639915599251024701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1217058186554132334699601 912793639915599251024701)
                ·
                  refine ⟨342297614968349719134263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 912793639915599251024701 342297614968349719134263)
                  ·
                    rfl

theorem cell21_1499900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 2, 2, 3].length) (baseStart_1499900 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1499900 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1499900 prefixEnd_1499900 := by exact prefixLift 1499900
  have htrace : WordTrace (prefixWord ++ tailWord_1499900) baseStart_1499900 baseEnd_1499900 := by
    simpa [prefixWord, tailWord_1499900, baseEnd_1499900] using wordTrace_append hprefix tailTrace_1499900
  have hstable : (prefixWord ++ tailWord_1499900).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499900).length < 2 ^ (prefixWord ++ tailWord_1499900).sum := by decide
  have hdescent : baseEnd_1499900 < baseStart_1499900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499911 : List Nat := [1, 1, 4, 4, 1, 1, 3, 6]
def baseStart_1499911 : Nat := 118140960795 + 1499911 * 2 ^ 59
def prefixEnd_1499911 : Nat := 4983230072969 + 3 ^ 40 * 1499911 * 2
def baseEnd_1499911 : Nat := 114100041772738714816969

theorem tailTrace_1499911 : CollatzResearch.WordTrace tailWord_1499911 prefixEnd_1499911 114100041772738714816969 := by
  unfold tailWord_1499911
  simp only [CollatzResearch.WordTrace]
  refine ⟨54706248469086086249619587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36470832312724057499746391 54706248469086086249619587)
  ·
    refine ⟨82059372703629129374429381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54706248469086086249619587 82059372703629129374429381)
    ·
      refine ⟨15386132381930461757705509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82059372703629129374429381 15386132381930461757705509)
      ·
        refine ⟨2884899821611961579569783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15386132381930461757705509 2884899821611961579569783)
        ·
          refine ⟨4327349732417942369354675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2884899821611961579569783 4327349732417942369354675)
          ·
            refine ⟨6491024598626913554032013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4327349732417942369354675 6491024598626913554032013)
            ·
              refine ⟨2434134224485092582762005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6491024598626913554032013 2434134224485092582762005)
              ·
                refine ⟨114100041772738714816969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2434134224485092582762005 114100041772738714816969)
                ·
                  rfl

theorem cell21_1499911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 6].length) (baseStart_1499911 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1499911 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1499911 prefixEnd_1499911 := by exact prefixLift 1499911
  have htrace : WordTrace (prefixWord ++ tailWord_1499911) baseStart_1499911 baseEnd_1499911 := by
    simpa [prefixWord, tailWord_1499911, baseEnd_1499911] using wordTrace_append hprefix tailTrace_1499911
  have hstable : (prefixWord ++ tailWord_1499911).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499911).length < 2 ^ (prefixWord ++ tailWord_1499911).sum := by decide
  have hdescent : baseEnd_1499911 < baseStart_1499911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499925 : List Nat := [1, 3, 2, 1, 2, 2, 3, 2, 5]
def baseStart_1499925 : Nat := 118140960795 + 1499925 * 2 ^ 59
def prefixEnd_1499925 : Nat := 4983230072969 + 3 ^ 40 * 1499925 * 2
def baseEnd_1499925 : Nat := 342303320308955231217545

theorem tailTrace_1499925 : CollatzResearch.WordTrace tailWord_1499925 prefixEnd_1499925 342303320308955231217545 := by
  unfold tailWord_1499925
  simp only [CollatzResearch.WordTrace]
  refine ⟨54706759091035366640629229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36471172727356911093752819 54706759091035366640629229)
  ·
    refine ⟨20515034659138262490235961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54706759091035366640629229 20515034659138262490235961)
    ·
      refine ⟨15386275994353696867676971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20515034659138262490235961 15386275994353696867676971)
      ·
        refine ⟨23079413991530545301515457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15386275994353696867676971 23079413991530545301515457)
        ·
          refine ⟨17309560493647908976136593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23079413991530545301515457 17309560493647908976136593)
          ·
            refine ⟨12982170370235931732102445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17309560493647908976136593 12982170370235931732102445)
            ·
              refine ⟨4868313888838474399538417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12982170370235931732102445 4868313888838474399538417)
              ·
                refine ⟨3651235416628855799653813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4868313888838474399538417 3651235416628855799653813)
                ·
                  refine ⟨342303320308955231217545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3651235416628855799653813 342303320308955231217545)
                  ·
                    rfl

theorem cell21_1499925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 2, 5].length) (baseStart_1499925 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1499925 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1499925 prefixEnd_1499925 := by exact prefixLift 1499925
  have htrace : WordTrace (prefixWord ++ tailWord_1499925) baseStart_1499925 baseEnd_1499925 := by
    simpa [prefixWord, tailWord_1499925, baseEnd_1499925] using wordTrace_append hprefix tailTrace_1499925
  have hstable : (prefixWord ++ tailWord_1499925).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499925).length < 2 ^ (prefixWord ++ tailWord_1499925).sum := by decide
  have hdescent : baseEnd_1499925 < baseStart_1499925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499939 : List Nat := [1, 1, 1, 4, 2, 1, 1, 4, 6]
def baseStart_1499939 : Nat := 118140960795 + 1499939 * 2 ^ 59
def prefixEnd_1499939 : Nat := 4983230072969 + 3 ^ 40 * 1499939 * 2
def baseEnd_1499939 : Nat := 342306515299694317984183

theorem tailTrace_1499939 : CollatzResearch.WordTrace tailWord_1499939 prefixEnd_1499939 342306515299694317984183 := by
  unfold tailWord_1499939
  simp only [CollatzResearch.WordTrace]
  refine ⟨54707269712984647031638871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36471513141989764687759247 54707269712984647031638871)
  ·
    refine ⟨82060904569476970547458307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54707269712984647031638871 82060904569476970547458307)
    ·
      refine ⟨123091356854215455821187461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82060904569476970547458307 123091356854215455821187461)
      ·
        refine ⟨23079629410165397966472649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123091356854215455821187461 23079629410165397966472649)
        ·
          refine ⟨17309722057624048474854487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23079629410165397966472649 17309722057624048474854487)
          ·
            refine ⟨25964583086436072712281731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17309722057624048474854487 25964583086436072712281731)
            ·
              refine ⟨38946874629654109068422597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25964583086436072712281731 38946874629654109068422597)
              ·
                refine ⟨7302538993060145450329237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38946874629654109068422597 7302538993060145450329237)
                ·
                  refine ⟨342306515299694317984183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7302538993060145450329237 342306515299694317984183)
                  ·
                    rfl

theorem cell21_1499939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 4, 6].length) (baseStart_1499939 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1499939 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1499939 prefixEnd_1499939 := by exact prefixLift 1499939
  have htrace : WordTrace (prefixWord ++ tailWord_1499939) baseStart_1499939 baseEnd_1499939 := by
    simpa [prefixWord, tailWord_1499939, baseEnd_1499939] using wordTrace_append hprefix tailTrace_1499939
  have hstable : (prefixWord ++ tailWord_1499939).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499939).length < 2 ^ (prefixWord ++ tailWord_1499939).sum := by decide
  have hdescent : baseEnd_1499939 < baseStart_1499939 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500018 : List Nat := [3, 2, 1, 2, 1, 1, 2, 6, 3]
def baseStart_1500018 : Nat := 118140960795 + 1500018 * 2 ^ 59
def prefixEnd_1500018 : Nat := 4983230072969 + 3 ^ 40 * 1500018 * 2
def baseEnd_1500018 : Nat := 342324544176007736167355

theorem tailTrace_1500018 : CollatzResearch.WordTrace tailWord_1500018 prefixEnd_1500018 342324544176007736167355 := by
  unfold tailWord_1500018
  simp only [CollatzResearch.WordTrace]
  refine ⟨13677537769924610880941177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36473434053132295682509805 13677537769924610880941177)
  ·
    refine ⟨10258153327443458160705883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13677537769924610880941177 10258153327443458160705883)
    ·
      refine ⟨15387229991165187241058825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10258153327443458160705883 15387229991165187241058825)
      ·
        refine ⟨11540422493373890430794119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15387229991165187241058825 11540422493373890430794119)
        ·
          refine ⟨17310633740060835646191179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11540422493373890430794119 17310633740060835646191179)
          ·
            refine ⟨25965950610091253469286769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17310633740060835646191179 25965950610091253469286769)
            ·
              refine ⟨19474462957568440101965077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25965950610091253469286769 19474462957568440101965077)
              ·
                refine ⟨912865451136020629779613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19474462957568440101965077 912865451136020629779613)
                ·
                  refine ⟨342324544176007736167355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 912865451136020629779613 342324544176007736167355)
                  ·
                    rfl

theorem cell21_1500018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 6, 3].length) (baseStart_1500018 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1500018 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1500018 prefixEnd_1500018 := by exact prefixLift 1500018
  have htrace : WordTrace (prefixWord ++ tailWord_1500018) baseStart_1500018 baseEnd_1500018 := by
    simpa [prefixWord, tailWord_1500018, baseEnd_1500018] using wordTrace_append hprefix tailTrace_1500018
  have hstable : (prefixWord ++ tailWord_1500018).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500018).length < 2 ^ (prefixWord ++ tailWord_1500018).sum := by decide
  have hdescent : baseEnd_1500018 < baseStart_1500018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500122 : List Nat := [3, 1, 1, 2, 4, 2, 8]
def baseStart_1500122 : Nat := 118140960795 + 1500122 * 2 ^ 59
def prefixEnd_1500122 : Nat := 4983230072969 + 3 ^ 40 * 1500122 * 2
def baseEnd_1500122 : Nat := 38038697599214074048201

theorem tailTrace_1500122 : CollatzResearch.WordTrace tailWord_1500122 prefixEnd_1500122 38038697599214074048201 := by
  unfold tailWord_1500122
  simp only [CollatzResearch.WordTrace]
  refine ⟨13678486067830417321387655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36475962847547779523700413 13678486067830417321387655)
  ·
    refine ⟨20517729101745625982081483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13678486067830417321387655 20517729101745625982081483)
    ·
      refine ⟨30776593652618438973122225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20517729101745625982081483 30776593652618438973122225)
      ·
        refine ⟨23082445239463829229841669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30776593652618438973122225 23082445239463829229841669)
        ·
          refine ⟨4327958482399467980595313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23082445239463829229841669 4327958482399467980595313)
          ·
            refine ⟨3245968861799600985446485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4327958482399467980595313 3245968861799600985446485)
            ·
              refine ⟨38038697599214074048201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3245968861799600985446485 38038697599214074048201)
              ·
                rfl

theorem cell21_1500122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 8].length) (baseStart_1500122 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1500122 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1500122 prefixEnd_1500122 := by exact prefixLift 1500122
  have htrace : WordTrace (prefixWord ++ tailWord_1500122) baseStart_1500122 baseEnd_1500122 := by
    simpa [prefixWord, tailWord_1500122, baseEnd_1500122] using wordTrace_append hprefix tailTrace_1500122
  have hstable : (prefixWord ++ tailWord_1500122).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500122).length < 2 ^ (prefixWord ++ tailWord_1500122).sum := by decide
  have hdescent : baseEnd_1500122 < baseStart_1500122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500125 : List Nat := [1, 4, 3, 1, 2, 1, 3, 2, 4]
def baseStart_1500125 : Nat := 118140960795 + 1500125 * 2 ^ 59
def prefixEnd_1500125 : Nat := 4983230072969 + 3 ^ 40 * 1500125 * 2
def baseEnd_1500125 : Nat := 342348963033799327883803

theorem tailTrace_1500125 : CollatzResearch.WordTrace tailWord_1500125 prefixEnd_1500125 342348963033799327883803 := by
  unfold tailWord_1500125
  simp only [CollatzResearch.WordTrace]
  refine ⟨54714053690310800797909829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36476035793540533865273219 54714053690310800797909829)
  ·
    refine ⟨10258885066933275149608093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54714053690310800797909829 10258885066933275149608093)
    ·
      refine ⟨3847081900099978181103035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10258885066933275149608093 3847081900099978181103035)
      ·
        refine ⟨5770622850149967271654553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3847081900099978181103035 5770622850149967271654553)
        ·
          refine ⟨4327967137612475453740915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5770622850149967271654553 4327967137612475453740915)
          ·
            refine ⟨6491950706418713180611373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4327967137612475453740915 6491950706418713180611373)
            ·
              refine ⟨2434481514907017442729265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6491950706418713180611373 2434481514907017442729265)
              ·
                refine ⟨1825861136180263082046949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2434481514907017442729265 1825861136180263082046949)
                ·
                  refine ⟨342348963033799327883803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1825861136180263082046949 342348963033799327883803)
                  ·
                    rfl

theorem cell21_1500125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 2, 4].length) (baseStart_1500125 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1500125 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1500125 prefixEnd_1500125 := by exact prefixLift 1500125
  have htrace : WordTrace (prefixWord ++ tailWord_1500125) baseStart_1500125 baseEnd_1500125 := by
    simpa [prefixWord, tailWord_1500125, baseEnd_1500125] using wordTrace_append hprefix tailTrace_1500125
  have hstable : (prefixWord ++ tailWord_1500125).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500125).length < 2 ^ (prefixWord ++ tailWord_1500125).sum := by decide
  have hdescent : baseEnd_1500125 < baseStart_1500125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500142 : List Nat := [4, 1, 2, 1, 4, 1, 3, 1, 4]
def baseStart_1500142 : Nat := 118140960795 + 1500142 * 2 ^ 59
def prefixEnd_1500142 : Nat := 4983230072969 + 3 ^ 40 * 1500142 * 2
def baseEnd_1500142 : Nat := 342352842665411076100435

theorem tailTrace_1500142 : CollatzResearch.WordTrace tailWord_1500142 prefixEnd_1500142 342352842665411076100435 := by
  unfold tailWord_1500142
  simp only [CollatzResearch.WordTrace]
  refine ⟨6839334216406151587659835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36476449154166141800852453 6839334216406151587659835)
  ·
    refine ⟨10259001324609227381489753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6839334216406151587659835 10259001324609227381489753)
    ·
      refine ⟨7694250993456920536117315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10259001324609227381489753 7694250993456920536117315)
      ·
        refine ⟨11541376490185380804175973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7694250993456920536117315 11541376490185380804175973)
        ·
          refine ⟨2164008091909758900782995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11541376490185380804175973 2164008091909758900782995)
          ·
            refine ⟨3246012137864638351174493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2164008091909758900782995 3246012137864638351174493)
            ·
              refine ⟨1217254551699239381690435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3246012137864638351174493 1217254551699239381690435)
              ·
                refine ⟨1825881827548859072535653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1217254551699239381690435 1825881827548859072535653)
                ·
                  refine ⟨342352842665411076100435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1825881827548859072535653 342352842665411076100435)
                  ·
                    rfl

theorem cell21_1500142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 3, 1, 4].length) (baseStart_1500142 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1500142 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1500142 prefixEnd_1500142 := by exact prefixLift 1500142
  have htrace : WordTrace (prefixWord ++ tailWord_1500142) baseStart_1500142 baseEnd_1500142 := by
    simpa [prefixWord, tailWord_1500142, baseEnd_1500142] using wordTrace_append hprefix tailTrace_1500142
  have hstable : (prefixWord ++ tailWord_1500142).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500142).length < 2 ^ (prefixWord ++ tailWord_1500142).sum := by decide
  have hdescent : baseEnd_1500142 < baseStart_1500142 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500148 : List Nat := [2, 6, 2, 1, 2, 1, 2, 5]
def baseStart_1500148 : Nat := 118140960795 + 1500148 * 2 ^ 59
def prefixEnd_1500148 : Nat := 4983230072969 + 3 ^ 40 * 1500148 * 2
def baseEnd_1500148 : Nat := 114118070649052133000141

theorem tailTrace_1500148 : CollatzResearch.WordTrace tailWord_1500148 prefixEnd_1500148 114118070649052133000141 := by
  unfold tailWord_1500148
  simp only [CollatzResearch.WordTrace]
  refine ⟨27357446284613737862998549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36476595046151650483998065 27357446284613737862998549)
  ·
    refine ⟨1282380294591268962328057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 27357446284613737862998549 1282380294591268962328057)
    ·
      refine ⟨961785220943451721746043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1282380294591268962328057 961785220943451721746043)
      ·
        refine ⟨1442677831415177582619065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 961785220943451721746043 1442677831415177582619065)
        ·
          refine ⟨1082008373561383186964299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1442677831415177582619065 1082008373561383186964299)
          ·
            refine ⟨1623012560342074780446449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1082008373561383186964299 1623012560342074780446449)
            ·
              refine ⟨1217259420256556085334837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1623012560342074780446449 1217259420256556085334837)
              ·
                refine ⟨114118070649052133000141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1217259420256556085334837 114118070649052133000141)
                ·
                  rfl

theorem cell21_1500148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 2, 5].length) (baseStart_1500148 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1500148 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1500148 prefixEnd_1500148 := by exact prefixLift 1500148
  have htrace : WordTrace (prefixWord ++ tailWord_1500148) baseStart_1500148 baseEnd_1500148 := by
    simpa [prefixWord, tailWord_1500148, baseEnd_1500148] using wordTrace_append hprefix tailTrace_1500148
  have hstable : (prefixWord ++ tailWord_1500148).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500148).length < 2 ^ (prefixWord ++ tailWord_1500148).sum := by decide
  have hdescent : baseEnd_1500148 < baseStart_1500148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500162 : List Nat := [3, 4, 1, 3, 2, 1, 1, 3, 3]
def baseStart_1500162 : Nat := 118140960795 + 1500162 * 2 ^ 59
def prefixEnd_1500162 : Nat := 4983230072969 + 3 ^ 40 * 1500162 * 2
def baseEnd_1500162 : Nat := 342357406937895485767061

theorem tailTrace_1500162 : CollatzResearch.WordTrace tailWord_1500162 prefixEnd_1500162 342357406937895485767061 := by
  unfold tailWord_1500162
  simp only [CollatzResearch.WordTrace]
  refine ⟨13678850797794189029251685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36476935460784504078004493 13678850797794189029251685)
  ·
    refine ⟨2564784524586410442984691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13678850797794189029251685 2564784524586410442984691)
    ·
      refine ⟨3847176786879615664477037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2564784524586410442984691 3847176786879615664477037)
      ·
        refine ⟨1442691295079855874178889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3847176786879615664477037 1442691295079855874178889)
        ·
          refine ⟨1082018471309891905634167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1442691295079855874178889 1082018471309891905634167)
          ·
            refine ⟨1623027706964837858451251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1082018471309891905634167 1623027706964837858451251)
            ·
              refine ⟨2434541560447256787676877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1623027706964837858451251 2434541560447256787676877)
              ·
                refine ⟨912953085167721295378829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2434541560447256787676877 912953085167721295378829)
                ·
                  refine ⟨342357406937895485767061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 912953085167721295378829 342357406937895485767061)
                  ·
                    rfl

theorem cell21_1500162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_1500162 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1500162 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1500162 prefixEnd_1500162 := by exact prefixLift 1500162
  have htrace : WordTrace (prefixWord ++ tailWord_1500162) baseStart_1500162 baseEnd_1500162 := by
    simpa [prefixWord, tailWord_1500162, baseEnd_1500162] using wordTrace_append hprefix tailTrace_1500162
  have hstable : (prefixWord ++ tailWord_1500162).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500162).length < 2 ^ (prefixWord ++ tailWord_1500162).sum := by decide
  have hdescent : baseEnd_1500162 < baseStart_1500162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500167 : List Nat := [1, 1, 4, 3, 1, 1, 1, 1, 8]
def baseStart_1500167 : Nat := 118140960795 + 1500167 * 2 ^ 59
def prefixEnd_1500167 : Nat := 4983230072969 + 3 ^ 40 * 1500167 * 2
def baseEnd_1500167 : Nat := 342358548006016588183717

theorem tailTrace_1500167 : CollatzResearch.WordTrace tailWord_1500167 prefixEnd_1500167 342358548006016588183717 := by
  unfold tailWord_1500167
  simp only [CollatzResearch.WordTrace]
  refine ⟨54715585556158641970938755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36477057037439094647292503 54715585556158641970938755)
  ·
    refine ⟨82073378334237962956408133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54715585556158641970938755 82073378334237962956408133)
    ·
      refine ⟨15388758437669618054326525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82073378334237962956408133 15388758437669618054326525)
      ·
        refine ⟨5770784414126106770372447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15388758437669618054326525 5770784414126106770372447)
        ·
          refine ⟨8656176621189160155558671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5770784414126106770372447 8656176621189160155558671)
          ·
            refine ⟨12984264931783740233338007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8656176621189160155558671 12984264931783740233338007)
            ·
              refine ⟨19476397397675610350007011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12984264931783740233338007 19476397397675610350007011)
              ·
                refine ⟨29214596096513415525010517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19476397397675610350007011 29214596096513415525010517)
                ·
                  refine ⟨342358548006016588183717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29214596096513415525010517 342358548006016588183717)
                  ·
                    rfl

theorem cell21_1500167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 8].length) (baseStart_1500167 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1500167 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1500167 prefixEnd_1500167 := by exact prefixLift 1500167
  have htrace : WordTrace (prefixWord ++ tailWord_1500167) baseStart_1500167 baseEnd_1500167 := by
    simpa [prefixWord, tailWord_1500167, baseEnd_1500167] using wordTrace_append hprefix tailTrace_1500167
  have hstable : (prefixWord ++ tailWord_1500167).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500167).length < 2 ^ (prefixWord ++ tailWord_1500167).sum := by decide
  have hdescent : baseEnd_1500167 < baseStart_1500167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500243 : List Nat := [1, 1, 1, 2, 1, 1, 2, 8, 4]
def baseStart_1500243 : Nat := 118140960795 + 1500243 * 2 ^ 59
def prefixEnd_1500243 : Nat := 4983230072969 + 3 ^ 40 * 1500243 * 2
def baseEnd_1500243 : Nat := 342375892241457344916895

theorem tailTrace_1500243 : CollatzResearch.WordTrace tailWord_1500243 prefixEnd_1500243 342375892241457344916895 := by
  unfold tailWord_1500243
  simp only [CollatzResearch.WordTrace]
  refine ⟨54718357503883306950705383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36478905002588871300470255 54718357503883306950705383)
  ·
    refine ⟨82077536255824960426058075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54718357503883306950705383 82077536255824960426058075)
    ·
      refine ⟨123116304383737440639087113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82077536255824960426058075 123116304383737440639087113)
      ·
        refine ⟨92337228287803080479315335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123116304383737440639087113 92337228287803080479315335)
        ·
          refine ⟨138505842431704620718973003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92337228287803080479315335 138505842431704620718973003)
          ·
            refine ⟨207758763647556931078459505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138505842431704620718973003 207758763647556931078459505)
            ·
              refine ⟨155819072735667698308844629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 207758763647556931078459505 155819072735667698308844629)
              ·
                refine ⟨1826004758621105839556773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 155819072735667698308844629 1826004758621105839556773)
                ·
                  refine ⟨342375892241457344916895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1826004758621105839556773 342375892241457344916895)
                  ·
                    rfl

theorem cell21_1500243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 8, 4].length) (baseStart_1500243 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1500243 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1500243 prefixEnd_1500243 := by exact prefixLift 1500243
  have htrace : WordTrace (prefixWord ++ tailWord_1500243) baseStart_1500243 baseEnd_1500243 := by
    simpa [prefixWord, tailWord_1500243, baseEnd_1500243] using wordTrace_append hprefix tailTrace_1500243
  have hstable : (prefixWord ++ tailWord_1500243).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500243).length < 2 ^ (prefixWord ++ tailWord_1500243).sum := by decide
  have hdescent : baseEnd_1500243 < baseStart_1500243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500350 : List Nat := [4, 2, 1, 1, 3, 1, 9]
def baseStart_1500350 : Nat := 118140960795 + 1500350 * 2 ^ 59
def prefixEnd_1500350 : Nat := 4983230072969 + 3 ^ 40 * 1500350 * 2
def baseEnd_1500350 : Nat := 38044479011027659625927

theorem tailTrace_1500350 : CollatzResearch.WordTrace tailWord_1500350 prefixEnd_1500350 38044479011027659625927 := by
  unfold tailWord_1500350
  simp only [CollatzResearch.WordTrace]
  refine ⟨6840282514311958028106313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36481506742997109483233669 6840282514311958028106313)
  ·
    refine ⟨5130211885733968521079735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6840282514311958028106313 5130211885733968521079735)
    ·
      refine ⟨7695317828600952781619603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5130211885733968521079735 7695317828600952781619603)
      ·
        refine ⟨11542976742901429172429405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7695317828600952781619603 11542976742901429172429405)
        ·
          refine ⟨4328616278588035939661027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11542976742901429172429405 4328616278588035939661027)
          ·
            refine ⟨6492924417882053909491541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4328616278588035939661027 6492924417882053909491541)
            ·
              refine ⟨38044479011027659625927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6492924417882053909491541 38044479011027659625927)
              ·
                rfl

theorem cell21_1500350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 9].length) (baseStart_1500350 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1500350 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1500350 prefixEnd_1500350 := by exact prefixLift 1500350
  have htrace : WordTrace (prefixWord ++ tailWord_1500350) baseStart_1500350 baseEnd_1500350 := by
    simpa [prefixWord, tailWord_1500350, baseEnd_1500350] using wordTrace_append hprefix tailTrace_1500350
  have hstable : (prefixWord ++ tailWord_1500350).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500350).length < 2 ^ (prefixWord ++ tailWord_1500350).sum := by decide
  have hdescent : baseEnd_1500350 < baseStart_1500350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500356 : List Nat := [2, 3, 3, 1, 3, 1, 3, 2, 3]
def baseStart_1500356 : Nat := 118140960795 + 1500356 * 2 ^ 59
def prefixEnd_1500356 : Nat := 4983230072969 + 3 ^ 40 * 1500356 * 2
def baseEnd_1500356 : Nat := 342401680380994259533331

theorem tailTrace_1500356 : CollatzResearch.WordTrace tailWord_1500356 prefixEnd_1500356 342401680380994259533331 := by
  unfold tailWord_1500356
  simp only [CollatzResearch.WordTrace]
  refine ⟨27361239476236963624784461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36481652634982618166379281 27361239476236963624784461)
  ·
    refine ⟨10260464803588861359294173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27361239476236963624784461 10260464803588861359294173)
    ·
      refine ⟨3847674301345823009735315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10260464803588861359294173 3847674301345823009735315)
      ·
        refine ⟨5771511452018734514602973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3847674301345823009735315 5771511452018734514602973)
        ·
          refine ⟨2164316794507025442976115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5771511452018734514602973 2164316794507025442976115)
          ·
            refine ⟨3246475191760538164464173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2164316794507025442976115 3246475191760538164464173)
            ·
              refine ⟨1217428196910201811674065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3246475191760538164464173 1217428196910201811674065)
              ·
                refine ⟨913071147682651358755549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1217428196910201811674065 913071147682651358755549)
                ·
                  refine ⟨342401680380994259533331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 913071147682651358755549 342401680380994259533331)
                  ·
                    rfl

theorem cell21_1500356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 3, 2, 3].length) (baseStart_1500356 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1500356 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1500356 prefixEnd_1500356 := by exact prefixLift 1500356
  have htrace : WordTrace (prefixWord ++ tailWord_1500356) baseStart_1500356 baseEnd_1500356 := by
    simpa [prefixWord, tailWord_1500356, baseEnd_1500356] using wordTrace_append hprefix tailTrace_1500356
  have hstable : (prefixWord ++ tailWord_1500356).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500356).length < 2 ^ (prefixWord ++ tailWord_1500356).sum := by decide
  have hdescent : baseEnd_1500356 < baseStart_1500356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500415 : List Nat := [1, 1, 2, 2, 1, 7, 2, 2, 3]
def baseStart_1500415 : Nat := 118140960795 + 1500415 * 2 ^ 59
def prefixEnd_1500415 : Nat := 4983230072969 + 3 ^ 40 * 1500415 * 2
def baseEnd_1500415 : Nat := 342415144984823268049877

theorem tailTrace_1500415 : CollatzResearch.WordTrace tailWord_1500415 prefixEnd_1500415 342415144984823268049877 := by
  unfold tailWord_1500415
  simp only [CollatzResearch.WordTrace]
  refine ⟨54724630859260180325966699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36483087239506786883977799 54724630859260180325966699)
  ·
    refine ⟨82086946288890270488950049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54724630859260180325966699 82086946288890270488950049)
    ·
      refine ⟨61565209716667702866712537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82086946288890270488950049 61565209716667702866712537)
      ·
        refine ⟨46173907287500777150034403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61565209716667702866712537 46173907287500777150034403)
        ·
          refine ⟨69260860931251165725051605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46173907287500777150034403 69260860931251165725051605)
          ·
            refine ⟨1623301428076199196680897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 69260860931251165725051605 1623301428076199196680897)
            ·
              refine ⟨1217476071057149397510673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1623301428076199196680897 1217476071057149397510673)
              ·
                refine ⟨913107053292862048133005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1217476071057149397510673 913107053292862048133005)
                ·
                  refine ⟨342415144984823268049877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 913107053292862048133005 342415144984823268049877)
                  ·
                    rfl

theorem cell21_1500415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 2, 2, 3].length) (baseStart_1500415 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1500415 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1500415 prefixEnd_1500415 := by exact prefixLift 1500415
  have htrace : WordTrace (prefixWord ++ tailWord_1500415) baseStart_1500415 baseEnd_1500415 := by
    simpa [prefixWord, tailWord_1500415, baseEnd_1500415] using wordTrace_append hprefix tailTrace_1500415
  have hstable : (prefixWord ++ tailWord_1500415).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500415).length < 2 ^ (prefixWord ++ tailWord_1500415).sum := by decide
  have hdescent : baseEnd_1500415 < baseStart_1500415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500440 : List Nat := [2, 1, 2, 3, 1, 3, 1, 1, 7]
def baseStart_1500440 : Nat := 118140960795 + 1500440 * 2 ^ 59
def prefixEnd_1500440 : Nat := 4983230072969 + 3 ^ 40 * 1500440 * 2
def baseEnd_1500440 : Nat := 342420850325428780133159

theorem tailTrace_1500440 : CollatzResearch.WordTrace tailWord_1500440 prefixEnd_1500440 342420850325428780133159 := by
  unfold tailWord_1500440
  simp only [CollatzResearch.WordTrace]
  refine ⟨27362771342084804797813387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36483695122779739730417849 27362771342084804797813387)
  ·
    refine ⟨41044157013127207196720081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27362771342084804797813387 41044157013127207196720081)
    ·
      refine ⟨30783117759845405397540061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41044157013127207196720081 30783117759845405397540061)
      ·
        refine ⟨11543669159942027024077523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30783117759845405397540061 11543669159942027024077523)
        ·
          refine ⟨17315503739913040536116285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11543669159942027024077523 17315503739913040536116285)
          ·
            refine ⟨6493313902467390201043607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17315503739913040536116285 6493313902467390201043607)
            ·
              refine ⟨9739970853701085301565411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6493313902467390201043607 9739970853701085301565411)
              ·
                refine ⟨14609956280551627952348117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9739970853701085301565411 14609956280551627952348117)
                ·
                  refine ⟨342420850325428780133159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14609956280551627952348117 342420850325428780133159)
                  ·
                    rfl

theorem cell21_1500440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 7].length) (baseStart_1500440 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1500440 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1500440 prefixEnd_1500440 := by exact prefixLift 1500440
  have htrace : WordTrace (prefixWord ++ tailWord_1500440) baseStart_1500440 baseEnd_1500440 := by
    simpa [prefixWord, tailWord_1500440, baseEnd_1500440] using wordTrace_append hprefix tailTrace_1500440
  have hstable : (prefixWord ++ tailWord_1500440).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500440).length < 2 ^ (prefixWord ++ tailWord_1500440).sum := by decide
  have hdescent : baseEnd_1500440 < baseStart_1500440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500519 : List Nat := [1, 1, 5, 1, 5, 1, 7]
def baseStart_1500519 : Nat := 118140960795 + 1500519 * 2 ^ 59
def prefixEnd_1500519 : Nat := 4983230072969 + 3 ^ 40 * 1500519 * 2
def baseEnd_1500519 : Nat := 38048764355749133146259

theorem tailTrace_1500519 : CollatzResearch.WordTrace tailWord_1500519 prefixEnd_1500519 38048764355749133146259 := by
  unfold tailWord_1500519
  simp only [CollatzResearch.WordTrace]
  refine ⟨54728424050883406087752611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36485616033922270725168407 54728424050883406087752611)
  ·
    refine ⟨82092636076325109131628917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54728424050883406087752611 82092636076325109131628917)
    ·
      refine ⟨7696184632155478981090211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 82092636076325109131628917 7696184632155478981090211)
      ·
        refine ⟨11544276948233218471635317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7696184632155478981090211 11544276948233218471635317)
        ·
          refine ⟨1082275963896864231715811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11544276948233218471635317 1082275963896864231715811)
          ·
            refine ⟨1623413945845296347573717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1082275963896864231715811 1623413945845296347573717)
            ·
              refine ⟨38048764355749133146259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1623413945845296347573717 38048764355749133146259)
              ·
                rfl

theorem cell21_1500519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 7].length) (baseStart_1500519 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1500519 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1500519 prefixEnd_1500519 := by exact prefixLift 1500519
  have htrace : WordTrace (prefixWord ++ tailWord_1500519) baseStart_1500519 baseEnd_1500519 := by
    simpa [prefixWord, tailWord_1500519, baseEnd_1500519] using wordTrace_append hprefix tailTrace_1500519
  have hstable : (prefixWord ++ tailWord_1500519).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500519).length < 2 ^ (prefixWord ++ tailWord_1500519).sum := by decide
  have hdescent : baseEnd_1500519 < baseStart_1500519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500668 : List Nat := [2, 2, 2, 1, 2, 1, 4, 2, 5]
def baseStart_1500668 : Nat := 118140960795 + 1500668 * 2 ^ 59
def prefixEnd_1500668 : Nat := 4983230072969 + 3 ^ 40 * 1500668 * 2
def baseEnd_1500668 : Nat := 342472883031751050332693

theorem tailTrace_1500668 : CollatzResearch.WordTrace tailWord_1500668 prefixEnd_1500668 342472883031751050332693 := by
  unfold tailWord_1500668
  simp only [CollatzResearch.WordTrace]
  refine ⟨27366929263671802267463329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36489239018229069689951105 27366929263671802267463329)
  ·
    refine ⟨20525196947753851700597497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27366929263671802267463329 20525196947753851700597497)
    ·
      refine ⟨15393897710815388775448123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20525196947753851700597497 15393897710815388775448123)
      ·
        refine ⟨23090846566223083163172185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15393897710815388775448123 23090846566223083163172185)
        ·
          refine ⟨17318134924667312372379139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23090846566223083163172185 17318134924667312372379139)
          ·
            refine ⟨25977202387000968558568709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17318134924667312372379139 25977202387000968558568709)
            ·
              refine ⟨4870725447562681604731633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25977202387000968558568709 4870725447562681604731633)
              ·
                refine ⟨3653044085672011203548725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4870725447562681604731633 3653044085672011203548725)
                ·
                  refine ⟨342472883031751050332693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3653044085672011203548725 342472883031751050332693)
                  ·
                    rfl

theorem cell21_1500668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 2, 5].length) (baseStart_1500668 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1500668 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1500668 prefixEnd_1500668 := by exact prefixLift 1500668
  have htrace : WordTrace (prefixWord ++ tailWord_1500668) baseStart_1500668 baseEnd_1500668 := by
    simpa [prefixWord, tailWord_1500668, baseEnd_1500668] using wordTrace_append hprefix tailTrace_1500668
  have hstable : (prefixWord ++ tailWord_1500668).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500668).length < 2 ^ (prefixWord ++ tailWord_1500668).sum := by decide
  have hdescent : baseEnd_1500668 < baseStart_1500668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500775 : List Nat := [1, 1, 5, 1, 1, 1, 4, 3, 4]
def baseStart_1500775 : Nat := 118140960795 + 1500775 * 2 ^ 59
def prefixEnd_1500775 : Nat := 4983230072969 + 3 ^ 40 * 1500775 * 2
def baseEnd_1500775 : Nat := 342497301889542642049141

theorem tailTrace_1500775 : CollatzResearch.WordTrace tailWord_1500775 prefixEnd_1500775 342497301889542642049141 := by
  unfold tailWord_1500775
  simp only [CollatzResearch.WordTrace]
  refine ⟨54737761137955961809071779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36491840758637307872714519 54737761137955961809071779)
  ·
    refine ⟨82106641706933942713607669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54737761137955961809071779 82106641706933942713607669)
    ·
      refine ⟨7697497660025057129400719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 82106641706933942713607669 7697497660025057129400719)
      ·
        refine ⟨11546246490037585694101079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7697497660025057129400719 11546246490037585694101079)
        ·
          refine ⟨17319369735056378541151619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11546246490037585694101079 17319369735056378541151619)
          ·
            refine ⟨25979054602584567811727429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17319369735056378541151619 25979054602584567811727429)
            ·
              refine ⟨4871072737984606464698893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25979054602584567811727429 4871072737984606464698893)
              ·
                refine ⟨1826652276744227424262085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4871072737984606464698893 1826652276744227424262085)
                ·
                  refine ⟨342497301889542642049141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1826652276744227424262085 342497301889542642049141)
                  ·
                    rfl

theorem cell21_1500775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 3, 4].length) (baseStart_1500775 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1500775 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1500775 prefixEnd_1500775 := by exact prefixLift 1500775
  have htrace : WordTrace (prefixWord ++ tailWord_1500775) baseStart_1500775 baseEnd_1500775 := by
    simpa [prefixWord, tailWord_1500775, baseEnd_1500775] using wordTrace_append hprefix tailTrace_1500775
  have hstable : (prefixWord ++ tailWord_1500775).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500775).length < 2 ^ (prefixWord ++ tailWord_1500775).sum := by decide
  have hdescent : baseEnd_1500775 < baseStart_1500775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500803 : List Nat := [1, 1, 1, 3, 3, 1, 1, 1, 9]
def baseStart_1500803 : Nat := 118140960795 + 1500803 * 2 ^ 59
def prefixEnd_1500803 : Nat := 4983230072969 + 3 ^ 40 * 1500803 * 2
def baseEnd_1500803 : Nat := 342503691871020815582417

theorem tailTrace_1500803 : CollatzResearch.WordTrace tailWord_1500803 prefixEnd_1500803 342503691871020815582417 := by
  unfold tailWord_1500803
  simp only [CollatzResearch.WordTrace]
  refine ⟨54738782381854522591091063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36492521587903015060727375 54738782381854522591091063)
  ·
    refine ⟨82108173572781783886636595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54738782381854522591091063 82108173572781783886636595)
    ·
      refine ⟨123162260359172675829954893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82108173572781783886636595 123162260359172675829954893)
      ·
        refine ⟨46185847634689753436233085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123162260359172675829954893 46185847634689753436233085)
        ·
          refine ⟨17319692863008657538587407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46185847634689753436233085 17319692863008657538587407)
          ·
            refine ⟨25979539294512986307881111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17319692863008657538587407 25979539294512986307881111)
            ·
              refine ⟨38969308941769479461821667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25979539294512986307881111 38969308941769479461821667)
              ·
                refine ⟨58453963412654219192732501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38969308941769479461821667 58453963412654219192732501)
                ·
                  refine ⟨342503691871020815582417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 58453963412654219192732501 342503691871020815582417)
                  ·
                    rfl

theorem cell21_1500803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 9].length) (baseStart_1500803 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1500803 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1500803 prefixEnd_1500803 := by exact prefixLift 1500803
  have htrace : WordTrace (prefixWord ++ tailWord_1500803) baseStart_1500803 baseEnd_1500803 := by
    simpa [prefixWord, tailWord_1500803, baseEnd_1500803] using wordTrace_append hprefix tailTrace_1500803
  have hstable : (prefixWord ++ tailWord_1500803).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500803).length < 2 ^ (prefixWord ++ tailWord_1500803).sum := by decide
  have hdescent : baseEnd_1500803 < baseStart_1500803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500840 : List Nat := [2, 1, 7, 1, 1, 1, 1, 7]
def baseStart_1500840 : Nat := 118140960795 + 1500840 * 2 ^ 59
def prefixEnd_1500840 : Nat := 4983230072969 + 3 ^ 40 * 1500840 * 2
def baseEnd_1500840 : Nat := 114170711925038991155225

theorem tailTrace_1500840 : CollatzResearch.WordTrace tailWord_1500840 prefixEnd_1500840 114170711925038991155225 := by
  unfold tailWord_1500840
  simp only [CollatzResearch.WordTrace]
  refine ⟨27370065941360238955093987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36493421255146985273458649 27370065941360238955093987)
  ·
    refine ⟨41055098912040358432640981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27370065941360238955093987 41055098912040358432640981)
    ·
      refine ⟨962228880750945900765023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 41055098912040358432640981 962228880750945900765023)
      ·
        refine ⟨1443343321126418851147535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 962228880750945900765023 1443343321126418851147535)
        ·
          refine ⟨2165014981689628276721303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1443343321126418851147535 2165014981689628276721303)
          ·
            refine ⟨3247522472534442415081955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2165014981689628276721303 3247522472534442415081955)
            ·
              refine ⟨4871283708801663622622933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3247522472534442415081955 4871283708801663622622933)
              ·
                refine ⟨114170711925038991155225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4871283708801663622622933 114170711925038991155225)
                ·
                  rfl

theorem cell21_1500840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 7].length) (baseStart_1500840 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1500840 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1500840 prefixEnd_1500840 := by exact prefixLift 1500840
  have htrace : WordTrace (prefixWord ++ tailWord_1500840) baseStart_1500840 baseEnd_1500840 := by
    simpa [prefixWord, tailWord_1500840, baseEnd_1500840] using wordTrace_append hprefix tailTrace_1500840
  have hstable : (prefixWord ++ tailWord_1500840).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500840).length < 2 ^ (prefixWord ++ tailWord_1500840).sum := by decide
  have hdescent : baseEnd_1500840 < baseStart_1500840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500882 : List Nat := [3, 2, 2, 2, 2, 2, 2, 6]
def baseStart_1500882 : Nat := 118140960795 + 1500882 * 2 ^ 59
def prefixEnd_1500882 : Nat := 4983230072969 + 3 ^ 40 * 1500882 * 2
def baseEnd_1500882 : Nat := 114173906915778077921863

theorem tailTrace_1500882 : CollatzResearch.WordTrace tailWord_1500882 prefixEnd_1500882 114173906915778077921863 := by
  unfold tailWord_1500882
  simp only [CollatzResearch.WordTrace]
  refine ⟨13685415937142079770804225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36494442499045546055477933 13685415937142079770804225)
  ·
    refine ⟨10264061952856559828103169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13685415937142079770804225 10264061952856559828103169)
    ·
      refine ⟨7698046464642419871077377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10264061952856559828103169 7698046464642419871077377)
      ·
        refine ⟨5773534848481814903308033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7698046464642419871077377 5773534848481814903308033)
        ·
          refine ⟨4330151136361361177481025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5773534848481814903308033 4330151136361361177481025)
          ·
            refine ⟨3247613352271020883110769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4330151136361361177481025 3247613352271020883110769)
            ·
              refine ⟨2435710014203265662333077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3247613352271020883110769 2435710014203265662333077)
              ·
                refine ⟨114173906915778077921863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2435710014203265662333077 114173906915778077921863)
                ·
                  rfl

theorem cell21_1500882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 6].length) (baseStart_1500882 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1500882 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1500882 prefixEnd_1500882 := by exact prefixLift 1500882
  have htrace : WordTrace (prefixWord ++ tailWord_1500882) baseStart_1500882 baseEnd_1500882 := by
    simpa [prefixWord, tailWord_1500882, baseEnd_1500882] using wordTrace_append hprefix tailTrace_1500882
  have hstable : (prefixWord ++ tailWord_1500882).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500882).length < 2 ^ (prefixWord ++ tailWord_1500882).sum := by decide
  have hdescent : baseEnd_1500882 < baseStart_1500882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500930 : List Nat := [3, 4, 1, 1, 1, 1, 3, 4, 3]
def baseStart_1500930 : Nat := 118140960795 + 1500930 * 2 ^ 59
def prefixEnd_1500930 : Nat := 4983230072969 + 3 ^ 40 * 1500930 * 2
def baseEnd_1500930 : Nat := 342532675001296816965491

theorem tailTrace_1500930 : CollatzResearch.WordTrace tailWord_1500930 prefixEnd_1500930 342532675001296816965491 := by
  unfold tailWord_1500930
  simp only [CollatzResearch.WordTrace]
  refine ⟨13685853613098605820241061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36495609634929615520642829 13685853613098605820241061)
  ·
    refine ⟨2566097552455988591295199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13685853613098605820241061 2566097552455988591295199)
    ·
      refine ⟨3849146328683982886942799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2566097552455988591295199 3849146328683982886942799)
      ·
        refine ⟨5773719493025974330414199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3849146328683982886942799 5773719493025974330414199)
        ·
          refine ⟨8660579239538961495621299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5773719493025974330414199 8660579239538961495621299)
          ·
            refine ⟨12990868859308442243431949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8660579239538961495621299 12990868859308442243431949)
            ·
              refine ⟨4871575822240665841286981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12990868859308442243431949 4871575822240665841286981)
              ·
                refine ⟨913420466670124845241309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4871575822240665841286981 913420466670124845241309)
                ·
                  refine ⟨342532675001296816965491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 913420466670124845241309 342532675001296816965491)
                  ·
                    rfl

theorem cell21_1500930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_1500930 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1500930 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1500930 prefixEnd_1500930 := by exact prefixLift 1500930
  have htrace : WordTrace (prefixWord ++ tailWord_1500930) baseStart_1500930 baseEnd_1500930 := by
    simpa [prefixWord, tailWord_1500930, baseEnd_1500930] using wordTrace_append hprefix tailTrace_1500930
  have hstable : (prefixWord ++ tailWord_1500930).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500930).length < 2 ^ (prefixWord ++ tailWord_1500930).sum := by decide
  have hdescent : baseEnd_1500930 < baseStart_1500930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500955 : List Nat := [1, 1, 1, 1, 1, 1, 4, 6, 5]
def baseStart_1500955 : Nat := 118140960795 + 1500955 * 2 ^ 59
def prefixEnd_1500955 : Nat := 4983230072969 + 3 ^ 40 * 1500955 * 2
def baseEnd_1500955 : Nat := 342538380341902329048773

theorem tailTrace_1500955 : CollatzResearch.WordTrace tailWord_1500955 prefixEnd_1500955 342538380341902329048773 := by
  unfold tailWord_1500955
  simp only [CollatzResearch.WordTrace]
  refine ⟨54744326277303852550624319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36496217518202568367082879 54744326277303852550624319)
  ·
    refine ⟨82116489415955778825936479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54744326277303852550624319 82116489415955778825936479)
    ·
      refine ⟨123174734123933668238904719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82116489415955778825936479 123174734123933668238904719)
      ·
        refine ⟨184762101185900502358357079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123174734123933668238904719 184762101185900502358357079)
        ·
          refine ⟨277143151778850753537535619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184762101185900502358357079 277143151778850753537535619)
          ·
            refine ⟨415714727668276130306303429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277143151778850753537535619 415714727668276130306303429)
            ·
              refine ⟨77946511437801774432431893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 415714727668276130306303429 77946511437801774432431893)
              ·
                refine ⟨3653742723646958176520245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 77946511437801774432431893 3653742723646958176520245)
                ·
                  refine ⟨342538380341902329048773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3653742723646958176520245 342538380341902329048773)
                  ·
                    rfl

theorem cell21_1500955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6, 5].length) (baseStart_1500955 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1500955 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1500955 prefixEnd_1500955 := by exact prefixLift 1500955
  have htrace : WordTrace (prefixWord ++ tailWord_1500955) baseStart_1500955 baseEnd_1500955 := by
    simpa [prefixWord, tailWord_1500955, baseEnd_1500955] using wordTrace_append hprefix tailTrace_1500955
  have hstable : (prefixWord ++ tailWord_1500955).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500955).length < 2 ^ (prefixWord ++ tailWord_1500955).sum := by decide
  have hdescent : baseEnd_1500955 < baseStart_1500955 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500989 : List Nat := [1, 4, 1, 4, 1, 2, 2, 1, 5]
def baseStart_1500989 : Nat := 118140960795 + 1500989 * 2 ^ 59
def prefixEnd_1500989 : Nat := 4983230072969 + 3 ^ 40 * 1500989 * 2
def baseEnd_1500989 : Nat := 342546139605125825482037

theorem tailTrace_1500989 : CollatzResearch.WordTrace tailWord_1500989 prefixEnd_1500989 342546139605125825482037 := by
  unfold tailWord_1500989
  simp only [CollatzResearch.WordTrace]
  refine ⟨54745566359180676357362021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36497044239453784238241347 54745566359180676357362021)
  ·
    refine ⟨10264793692346376817005379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54745566359180676357362021 10264793692346376817005379)
    ·
      refine ⟨15397190538519565225508069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10264793692346376817005379 15397190538519565225508069)
      ·
        refine ⟨2886973225972418479782763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15397190538519565225508069 2886973225972418479782763)
        ·
          refine ⟨4330459838958627719674145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2886973225972418479782763 4330459838958627719674145)
          ·
            refine ⟨3247844879218970789755609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4330459838958627719674145 3247844879218970789755609)
            ·
              refine ⟨2435883659414228092316707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3247844879218970789755609 2435883659414228092316707)
              ·
                refine ⟨3653825489121342138475061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2435883659414228092316707 3653825489121342138475061)
                ·
                  refine ⟨342546139605125825482037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3653825489121342138475061 342546139605125825482037)
                  ·
                    rfl

theorem cell21_1500989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 1, 5].length) (baseStart_1500989 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1500989 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1500989 prefixEnd_1500989 := by exact prefixLift 1500989
  have htrace : WordTrace (prefixWord ++ tailWord_1500989) baseStart_1500989 baseEnd_1500989 := by
    simpa [prefixWord, tailWord_1500989, baseEnd_1500989] using wordTrace_append hprefix tailTrace_1500989
  have hstable : (prefixWord ++ tailWord_1500989).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500989).length < 2 ^ (prefixWord ++ tailWord_1500989).sum := by decide
  have hdescent : baseEnd_1500989 < baseStart_1500989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501054 : List Nat := [4, 2, 3, 1, 1, 3, 2, 1, 4]
def baseStart_1501054 : Nat := 118140960795 + 1501054 * 2 ^ 59
def prefixEnd_1501054 : Nat := 4983230072969 + 3 ^ 40 * 1501054 * 2
def baseEnd_1501054 : Nat := 342560973490700156898571

theorem tailTrace_1501054 : CollatzResearch.WordTrace tailWord_1501054 prefixEnd_1501054 342560973490700156898571 := by
  unfold tailWord_1501054
  simp only [CollatzResearch.WordTrace]
  refine ⟨6843492137993149057309777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36498624735963461638985477 6843492137993149057309777)
  ·
    refine ⟨5132619103494861792982333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6843492137993149057309777 5132619103494861792982333)
    ·
      refine ⟨1924732163810573172368375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5132619103494861792982333 1924732163810573172368375)
      ·
        refine ⟨2887098245715859758552563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1924732163810573172368375 2887098245715859758552563)
        ·
          refine ⟨4330647368573789637828845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2887098245715859758552563 4330647368573789637828845)
          ·
            refine ⟨1623992763215171114185817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4330647368573789637828845 1623992763215171114185817)
            ·
              refine ⟨1217994572411378335639363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1623992763215171114185817 1217994572411378335639363)
              ·
                refine ⟨1826991858617067503459045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1217994572411378335639363 1826991858617067503459045)
                ·
                  refine ⟨342560973490700156898571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1826991858617067503459045 342560973490700156898571)
                  ·
                    rfl

theorem cell21_1501054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_1501054 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1501054 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1501054 prefixEnd_1501054 := by exact prefixLift 1501054
  have htrace : WordTrace (prefixWord ++ tailWord_1501054) baseStart_1501054 baseEnd_1501054 := by
    simpa [prefixWord, tailWord_1501054, baseEnd_1501054] using wordTrace_append hprefix tailTrace_1501054
  have hstable : (prefixWord ++ tailWord_1501054).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501054).length < 2 ^ (prefixWord ++ tailWord_1501054).sum := by decide
  have hdescent : baseEnd_1501054 < baseStart_1501054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501107 : List Nat := [1, 1, 1, 2, 3, 1, 4, 3, 5]
def baseStart_1501107 : Nat := 118140960795 + 1501107 * 2 ^ 59
def prefixEnd_1501107 : Nat := 4983230072969 + 3 ^ 40 * 1501107 * 2
def baseEnd_1501107 : Nat := 342573068812783842515129

theorem tailTrace_1501107 : CollatzResearch.WordTrace tailWord_1501107 prefixEnd_1501107 342573068812783842515129 := by
  unfold tailWord_1501107
  simp only [CollatzResearch.WordTrace]
  refine ⟨54749870172753182510157575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36499913448502121673438383 54749870172753182510157575)
  ·
    refine ⟨82124805259129773765236363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54749870172753182510157575 82124805259129773765236363)
    ·
      refine ⟨123187207888694660647854545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82124805259129773765236363 123187207888694660647854545)
      ·
        refine ⟨92390405916520995485890909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123187207888694660647854545 92390405916520995485890909)
        ·
          refine ⟨34646402218695373307209091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92390405916520995485890909 34646402218695373307209091)
          ·
            refine ⟨51969603328043059960813637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34646402218695373307209091 51969603328043059960813637)
            ·
              refine ⟨9744300624008073742652557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51969603328043059960813637 9744300624008073742652557)
              ·
                refine ⟨3654112734003027653494709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9744300624008073742652557 3654112734003027653494709)
                ·
                  refine ⟨342573068812783842515129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3654112734003027653494709 342573068812783842515129)
                  ·
                    rfl

theorem cell21_1501107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 3, 5].length) (baseStart_1501107 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1501107 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1501107 prefixEnd_1501107 := by exact prefixLift 1501107
  have htrace : WordTrace (prefixWord ++ tailWord_1501107) baseStart_1501107 baseEnd_1501107 := by
    simpa [prefixWord, tailWord_1501107, baseEnd_1501107] using wordTrace_append hprefix tailTrace_1501107
  have hstable : (prefixWord ++ tailWord_1501107).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501107).length < 2 ^ (prefixWord ++ tailWord_1501107).sum := by decide
  have hdescent : baseEnd_1501107 < baseStart_1501107 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501141 : List Nat := [1, 3, 2, 3, 2, 1, 1, 5, 3]
def baseStart_1501141 : Nat := 118140960795 + 1501141 * 2 ^ 59
def prefixEnd_1501141 : Nat := 4983230072969 + 3 ^ 40 * 1501141 * 2
def baseEnd_1501141 : Nat := 342580828076007338948393

theorem tailTrace_1501141 : CollatzResearch.WordTrace tailWord_1501141 prefixEnd_1501141 342580828076007338948393 := by
  unfold tailWord_1501141
  simp only [CollatzResearch.WordTrace]
  refine ⟨54751110254630006316895277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36500740169753337544596851 54751110254630006316895277)
  ·
    refine ⟨20531666345486252368835729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54751110254630006316895277 20531666345486252368835729)
    ·
      refine ⟨15398749759114689276626797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20531666345486252368835729 15398749759114689276626797)
      ·
        refine ⟨5774531159668008478735049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15398749759114689276626797 5774531159668008478735049)
        ·
          refine ⟨4330898369751006359051287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5774531159668008478735049 4330898369751006359051287)
          ·
            refine ⟨6496347554626509538576931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4330898369751006359051287 6496347554626509538576931)
            ·
              refine ⟨9744521331939764307865397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6496347554626509538576931 9744521331939764307865397)
              ·
                refine ⟨913548874869352903862381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9744521331939764307865397 913548874869352903862381)
                ·
                  refine ⟨342580828076007338948393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 913548874869352903862381 342580828076007338948393)
                  ·
                    rfl

theorem cell21_1501141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 5, 3].length) (baseStart_1501141 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1501141 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1501141 prefixEnd_1501141 := by exact prefixLift 1501141
  have htrace : WordTrace (prefixWord ++ tailWord_1501141) baseStart_1501141 baseEnd_1501141 := by
    simpa [prefixWord, tailWord_1501141, baseEnd_1501141] using wordTrace_append hprefix tailTrace_1501141
  have hstable : (prefixWord ++ tailWord_1501141).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501141).length < 2 ^ (prefixWord ++ tailWord_1501141).sum := by decide
  have hdescent : baseEnd_1501141 < baseStart_1501141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501155 : List Nat := [1, 1, 1, 6, 1, 2, 3, 2, 4]
def baseStart_1501155 : Nat := 118140960795 + 1501155 * 2 ^ 59
def prefixEnd_1501155 : Nat := 4983230072969 + 3 ^ 40 * 1501155 * 2
def baseEnd_1501155 : Nat := 342584023066746425715031

theorem tailTrace_1501155 : CollatzResearch.WordTrace tailWord_1501155 prefixEnd_1501155 342584023066746425715031 := by
  unfold tailWord_1501155
  simp only [CollatzResearch.WordTrace]
  refine ⟨54751620876579286707904919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36501080584386191138603279 54751620876579286707904919)
  ·
    refine ⟨82127431314868930061857379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54751620876579286707904919 82127431314868930061857379)
    ·
      refine ⟨123191146972303395092786069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82127431314868930061857379 123191146972303395092786069)
      ·
        refine ⟨5774585014326721644974347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 123191146972303395092786069 5774585014326721644974347)
        ·
          refine ⟨8661877521490082467461521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5774585014326721644974347 8661877521490082467461521)
          ·
            refine ⟨6496408141117561850596141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8661877521490082467461521 6496408141117561850596141)
            ·
              refine ⟨2436153052919085693973553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6496408141117561850596141 2436153052919085693973553)
              ·
                refine ⟨1827114789689314270480165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2436153052919085693973553 1827114789689314270480165)
                ·
                  refine ⟨342584023066746425715031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1827114789689314270480165 342584023066746425715031)
                  ·
                    rfl

theorem cell21_1501155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 2, 4].length) (baseStart_1501155 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1501155 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1501155 prefixEnd_1501155 := by exact prefixLift 1501155
  have htrace : WordTrace (prefixWord ++ tailWord_1501155) baseStart_1501155 baseEnd_1501155 := by
    simpa [prefixWord, tailWord_1501155, baseEnd_1501155] using wordTrace_append hprefix tailTrace_1501155
  have hstable : (prefixWord ++ tailWord_1501155).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501155).length < 2 ^ (prefixWord ++ tailWord_1501155).sum := by decide
  have hdescent : baseEnd_1501155 < baseStart_1501155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501217 : List Nat := [1, 2, 3, 2, 4, 2, 1, 1, 5]
def baseStart_1501217 : Nat := 118140960795 + 1501217 * 2 ^ 59
def prefixEnd_1501217 : Nat := 4983230072969 + 3 ^ 40 * 1501217 * 2
def baseEnd_1501217 : Nat := 342598172311448095681571

theorem tailTrace_1501217 : CollatzResearch.WordTrace tailWord_1501217 prefixEnd_1501217 342598172311448095681571 := by
  unfold tailWord_1501217
  simp only [CollatzResearch.WordTrace]
  refine ⟨54753882202354671296661905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36502588134903114197774603 54753882202354671296661905)
  ·
    refine ⟨41065411651766003472496429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54753882202354671296661905 41065411651766003472496429)
    ·
      refine ⟨15399529369412251302186161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41065411651766003472496429 15399529369412251302186161)
      ·
        refine ⟨11549647027059188476639621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15399529369412251302186161 11549647027059188476639621)
        ·
          refine ⟨2165558817573597839369929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11549647027059188476639621 2165558817573597839369929)
          ·
            refine ⟨1624169113180198379527447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2165558817573597839369929 1624169113180198379527447)
            ·
              refine ⟨2436253669770297569291171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1624169113180198379527447 2436253669770297569291171)
              ·
                refine ⟨3654380504655446353936757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2436253669770297569291171 3654380504655446353936757)
                ·
                  refine ⟨342598172311448095681571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3654380504655446353936757 342598172311448095681571)
                  ·
                    rfl

theorem cell21_1501217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 1, 5].length) (baseStart_1501217 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1501217 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1501217 prefixEnd_1501217 := by exact prefixLift 1501217
  have htrace : WordTrace (prefixWord ++ tailWord_1501217) baseStart_1501217 baseEnd_1501217 := by
    simpa [prefixWord, tailWord_1501217, baseEnd_1501217] using wordTrace_append hprefix tailTrace_1501217
  have hstable : (prefixWord ++ tailWord_1501217).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501217).length < 2 ^ (prefixWord ++ tailWord_1501217).sum := by decide
  have hdescent : baseEnd_1501217 < baseStart_1501217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501400 : List Nat := [2, 1, 2, 2, 4, 3, 2, 1, 4]
def baseStart_1501400 : Nat := 118140960795 + 1501400 * 2 ^ 59
def prefixEnd_1501400 : Nat := 4983230072969 + 3 ^ 40 * 1501400 * 2
def baseEnd_1501400 : Nat := 342639935404680444131197

theorem tailTrace_1501400 : CollatzResearch.WordTrace tailWord_1501400 prefixEnd_1501400 342639935404680444131197 := by
  unfold tailWord_1501400
  simp only [CollatzResearch.WordTrace]
  refine ⟨27380278380345846775286827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36507037840461129033715769 27380278380345846775286827)
  ·
    refine ⟨41070417570518770162930241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27380278380345846775286827 41070417570518770162930241)
    ·
      refine ⟨30802813177889077622197681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41070417570518770162930241 30802813177889077622197681)
      ·
        refine ⟨23102109883416808216648261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30802813177889077622197681 23102109883416808216648261)
        ·
          refine ⟨4331645603140651540621549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23102109883416808216648261 4331645603140651540621549)
          ·
            refine ⟨1624367101177744327733081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4331645603140651540621549 1624367101177744327733081)
            ·
              refine ⟨1218275325883308245799811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1624367101177744327733081 1218275325883308245799811)
              ·
                refine ⟨1827412988824962368699717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1218275325883308245799811 1827412988824962368699717)
                ·
                  refine ⟨342639935404680444131197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1827412988824962368699717 342639935404680444131197)
                  ·
                    rfl

theorem cell21_1501400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 2, 1, 4].length) (baseStart_1501400 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1501400 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1501400 prefixEnd_1501400 := by exact prefixLift 1501400
  have htrace : WordTrace (prefixWord ++ tailWord_1501400) baseStart_1501400 baseEnd_1501400 := by
    simpa [prefixWord, tailWord_1501400, baseEnd_1501400] using wordTrace_append hprefix tailTrace_1501400
  have hstable : (prefixWord ++ tailWord_1501400).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501400).length < 2 ^ (prefixWord ++ tailWord_1501400).sum := by decide
  have hdescent : baseEnd_1501400 < baseStart_1501400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501425 : List Nat := [1, 2, 2, 2, 2, 1, 2, 1, 8]
def baseStart_1501425 : Nat := 118140960795 + 1501425 * 2 ^ 59
def prefixEnd_1501425 : Nat := 4983230072969 + 3 ^ 40 * 1501425 * 2
def baseEnd_1501425 : Nat := 342645640745285956214479

theorem tailTrace_1501425 : CollatzResearch.WordTrace tailWord_1501425 prefixEnd_1501425 342645640745285956214479 := by
  unfold tailWord_1501425
  simp only [CollatzResearch.WordTrace]
  refine ⟨54761468585601122820233729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36507645723734081880155819 54761468585601122820233729)
  ·
    refine ⟨41071101439200842115175297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54761468585601122820233729 41071101439200842115175297)
    ·
      refine ⟨30803326079400631586381473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41071101439200842115175297 30803326079400631586381473)
      ·
        refine ⟨23102494559550473689786105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30803326079400631586381473 23102494559550473689786105)
        ·
          refine ⟨17326870919662855267339579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23102494559550473689786105 17326870919662855267339579)
          ·
            refine ⟨25990306379494282901009369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17326870919662855267339579 25990306379494282901009369)
            ·
              refine ⟨19492729784620712175757027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25990306379494282901009369 19492729784620712175757027)
              ·
                refine ⟨29239094676931068263635541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19492729784620712175757027 29239094676931068263635541)
                ·
                  refine ⟨342645640745285956214479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29239094676931068263635541 342645640745285956214479)
                  ·
                    rfl

theorem cell21_1501425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 8].length) (baseStart_1501425 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1501425 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1501425 prefixEnd_1501425 := by exact prefixLift 1501425
  have htrace : WordTrace (prefixWord ++ tailWord_1501425) baseStart_1501425 baseEnd_1501425 := by
    simpa [prefixWord, tailWord_1501425, baseEnd_1501425] using wordTrace_append hprefix tailTrace_1501425
  have hstable : (prefixWord ++ tailWord_1501425).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501425).length < 2 ^ (prefixWord ++ tailWord_1501425).sum := by decide
  have hdescent : baseEnd_1501425 < baseStart_1501425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501538 : List Nat := [3, 3, 2, 1, 1, 4, 1, 3, 3]
def baseStart_1501538 : Nat := 118140960795 + 1501538 * 2 ^ 59
def prefixEnd_1501538 : Nat := 4983230072969 + 3 ^ 40 * 1501538 * 2
def baseEnd_1501538 : Nat := 342671428884822870830915

theorem tailTrace_1501538 : CollatzResearch.WordTrace tailWord_1501538 prefixEnd_1501538 342671428884822870830915 := by
  unfold tailWord_1501538
  simp only [CollatzResearch.WordTrace]
  refine ⟨13691397508547935779774317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36510393356127828746064845 13691397508547935779774317)
  ·
    refine ⟨5134274065705475917415369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13691397508547935779774317 5134274065705475917415369)
    ·
      refine ⟨3850705549279106938061527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5134274065705475917415369 3850705549279106938061527)
      ·
        refine ⟨5776058323918660407092291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3850705549279106938061527 5776058323918660407092291)
        ·
          refine ⟨8664087485877990610638437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5776058323918660407092291 8664087485877990610638437)
          ·
            refine ⟨1624516403602123239494707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8664087485877990610638437 1624516403602123239494707)
            ·
              refine ⟨2436774605403184859242061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1624516403602123239494707 2436774605403184859242061)
              ·
                refine ⟨913790477026194322215773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2436774605403184859242061 913790477026194322215773)
                ·
                  refine ⟨342671428884822870830915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 913790477026194322215773 342671428884822870830915)
                  ·
                    rfl

theorem cell21_1501538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 3, 3].length) (baseStart_1501538 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1501538 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1501538 prefixEnd_1501538 := by exact prefixLift 1501538
  have htrace : WordTrace (prefixWord ++ tailWord_1501538) baseStart_1501538 baseEnd_1501538 := by
    simpa [prefixWord, tailWord_1501538, baseEnd_1501538] using wordTrace_append hprefix tailTrace_1501538
  have hstable : (prefixWord ++ tailWord_1501538).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501538).length < 2 ^ (prefixWord ++ tailWord_1501538).sum := by decide
  have hdescent : baseEnd_1501538 < baseStart_1501538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501563 : List Nat := [1, 1, 1, 1, 1, 7, 3, 1, 5]
def baseStart_1501563 : Nat := 118140960795 + 1501563 * 2 ^ 59
def prefixEnd_1501563 : Nat := 4983230072969 + 3 ^ 40 * 1501563 * 2
def baseEnd_1501563 : Nat := 342677134225428382914197

theorem tailTrace_1501563 : CollatzResearch.WordTrace tailWord_1501563 prefixEnd_1501563 342677134225428382914197 := by
  unfold tailWord_1501563
  simp only [CollatzResearch.WordTrace]
  refine ⟨54766501859101172388757343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36511001239400781592504895 54766501859101172388757343)
  ·
    refine ⟨82149752788651758583136015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54766501859101172388757343 82149752788651758583136015)
    ·
      refine ⟨123224629182977637874704023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82149752788651758583136015 123224629182977637874704023)
      ·
        refine ⟨184836943774466456812056035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123224629182977637874704023 184836943774466456812056035)
        ·
          refine ⟨277255415661699685218084053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184836943774466456812056035 277255415661699685218084053)
          ·
            refine ⟨6498173804571086372298845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 277255415661699685218084053 6498173804571086372298845)
            ·
              refine ⟨2436815176714157389612067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6498173804571086372298845 2436815176714157389612067)
              ·
                refine ⟨3655222765071236084418101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2436815176714157389612067 3655222765071236084418101)
                ·
                  refine ⟨342677134225428382914197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3655222765071236084418101 342677134225428382914197)
                  ·
                    rfl

theorem cell21_1501563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 1, 5].length) (baseStart_1501563 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1501563 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1501563 prefixEnd_1501563 := by exact prefixLift 1501563
  have htrace : WordTrace (prefixWord ++ tailWord_1501563) baseStart_1501563 baseEnd_1501563 := by
    simpa [prefixWord, tailWord_1501563, baseEnd_1501563] using wordTrace_append hprefix tailTrace_1501563
  have hstable : (prefixWord ++ tailWord_1501563).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501563).length < 2 ^ (prefixWord ++ tailWord_1501563).sum := by decide
  have hdescent : baseEnd_1501563 < baseStart_1501563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501625 : List Nat := [1, 2, 1, 4, 3, 3, 1, 6]
def baseStart_1501625 : Nat := 118140960795 + 1501625 * 2 ^ 59
def prefixEnd_1501625 : Nat := 4983230072969 + 3 ^ 40 * 1501625 * 2
def baseEnd_1501625 : Nat := 114230427823376684293579

theorem tailTrace_1501625 : CollatzResearch.WordTrace tailWord_1501625 prefixEnd_1501625 114230427823376684293579 := by
  unfold tailWord_1501625
  simp only [CollatzResearch.WordTrace]
  refine ⟨54768763184876556977514329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36512508789917704651676219 54768763184876556977514329)
  ·
    refine ⟨41076572388657417733135747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54768763184876556977514329 41076572388657417733135747)
    ·
      refine ⟨61614858582986126599703621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41076572388657417733135747 61614858582986126599703621)
      ·
        refine ⟨11552785984309898737444429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61614858582986126599703621 11552785984309898737444429)
        ·
          refine ⟨4332294744116212026541661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11552785984309898737444429 4332294744116212026541661)
          ·
            refine ⟨1624610529043579509953123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4332294744116212026541661 1624610529043579509953123)
            ·
              refine ⟨2436915793565369264929685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1624610529043579509953123 2436915793565369264929685)
              ·
                refine ⟨114230427823376684293579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2436915793565369264929685 114230427823376684293579)
                ·
                  rfl

theorem cell21_1501625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 6].length) (baseStart_1501625 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1501625 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1501625 prefixEnd_1501625 := by exact prefixLift 1501625
  have htrace : WordTrace (prefixWord ++ tailWord_1501625) baseStart_1501625 baseEnd_1501625 := by
    simpa [prefixWord, tailWord_1501625, baseEnd_1501625] using wordTrace_append hprefix tailTrace_1501625
  have hstable : (prefixWord ++ tailWord_1501625).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501625).length < 2 ^ (prefixWord ++ tailWord_1501625).sum := by decide
  have hdescent : baseEnd_1501625 < baseStart_1501625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501639 : List Nat := [1, 1, 4, 1, 1, 5, 1, 2, 5]
def baseStart_1501639 : Nat := 118140960795 + 1501639 * 2 ^ 59
def prefixEnd_1501639 : Nat := 4983230072969 + 3 ^ 40 * 1501639 * 2
def baseEnd_1501639 : Nat := 342694478460869139647375

theorem tailTrace_1501639 : CollatzResearch.WordTrace tailWord_1501639 prefixEnd_1501639 342694478460869139647375 := by
  unfold tailWord_1501639
  simp only [CollatzResearch.WordTrace]
  refine ⟨54769273806825837368523971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36512849204550558245682647 54769273806825837368523971)
  ·
    refine ⟨82153910710238756052785957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54769273806825837368523971 82153910710238756052785957)
    ·
      refine ⟨15403858258169766759897367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82153910710238756052785957 15403858258169766759897367)
      ·
        refine ⟨23105787387254650139846051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15403858258169766759897367 23105787387254650139846051)
        ·
          refine ⟨34658681080881975209769077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23105787387254650139846051 34658681080881975209769077)
          ·
            refine ⟨3249251351332685175915851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34658681080881975209769077 3249251351332685175915851)
            ·
              refine ⟨4873877026999027763873777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3249251351332685175915851 4873877026999027763873777)
              ·
                refine ⟨3655407770249270822905333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4873877026999027763873777 3655407770249270822905333)
                ·
                  refine ⟨342694478460869139647375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3655407770249270822905333 342694478460869139647375)
                  ·
                    rfl

theorem cell21_1501639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 2, 5].length) (baseStart_1501639 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1501639 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1501639 prefixEnd_1501639 := by exact prefixLift 1501639
  have htrace : WordTrace (prefixWord ++ tailWord_1501639) baseStart_1501639 baseEnd_1501639 := by
    simpa [prefixWord, tailWord_1501639, baseEnd_1501639] using wordTrace_append hprefix tailTrace_1501639
  have hstable : (prefixWord ++ tailWord_1501639).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501639).length < 2 ^ (prefixWord ++ tailWord_1501639).sum := by decide
  have hdescent : baseEnd_1501639 < baseStart_1501639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501729 : List Nat := [1, 2, 3, 2, 2, 1, 1, 3, 6]
def baseStart_1501729 : Nat := 118140960795 + 1501729 * 2 ^ 59
def prefixEnd_1501729 : Nat := 4983230072969 + 3 ^ 40 * 1501729 * 2
def baseEnd_1501729 : Nat := 342715017687048983147191

theorem tailTrace_1501729 : CollatzResearch.WordTrace tailWord_1501729 prefixEnd_1501729 342715017687048983147191 := by
  unfold tailWord_1501729
  simp only [CollatzResearch.WordTrace]
  refine ⟨54772556376499782739300241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36515037584333188492866827 54772556376499782739300241)
  ·
    refine ⟨41079417282374837054475181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54772556376499782739300241 41079417282374837054475181)
    ·
      refine ⟨15404781480890563895428193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41079417282374837054475181 15404781480890563895428193)
      ·
        refine ⟨11553586110667922921571145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15404781480890563895428193 11553586110667922921571145)
        ·
          refine ⟨8665189583000942191178359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11553586110667922921571145 8665189583000942191178359)
          ·
            refine ⟨12997784374501413286767539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8665189583000942191178359 12997784374501413286767539)
            ·
              refine ⟨19496676561752119930151309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12997784374501413286767539 19496676561752119930151309)
              ·
                refine ⟨7311253710657044973806741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19496676561752119930151309 7311253710657044973806741)
                ·
                  refine ⟨342715017687048983147191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7311253710657044973806741 342715017687048983147191)
                  ·
                    rfl

theorem cell21_1501729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 3, 6].length) (baseStart_1501729 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1501729 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1501729 prefixEnd_1501729 := by exact prefixLift 1501729
  have htrace : WordTrace (prefixWord ++ tailWord_1501729) baseStart_1501729 baseEnd_1501729 := by
    simpa [prefixWord, tailWord_1501729, baseEnd_1501729] using wordTrace_append hprefix tailTrace_1501729
  have hstable : (prefixWord ++ tailWord_1501729).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501729).length < 2 ^ (prefixWord ++ tailWord_1501729).sum := by decide
  have hdescent : baseEnd_1501729 < baseStart_1501729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501870 : List Nat := [4, 1, 4, 1, 1, 1, 4, 5]
def baseStart_1501870 : Nat := 118140960795 + 1501870 * 2 ^ 59
def prefixEnd_1501870 : Nat := 4983230072969 + 3 ^ 40 * 1501870 * 2
def baseEnd_1501870 : Nat := 114249065269354690432301

theorem tailTrace_1501870 : CollatzResearch.WordTrace tailWord_1501870 prefixEnd_1501870 114249065269354690432301 := by
  unfold tailWord_1501870
  simp only [CollatzResearch.WordTrace]
  refine ⟨6847212383623620477522883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36518466045992642546788709 6847212383623620477522883)
  ·
    refine ⟨10270818575435430716284325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6847212383623620477522883 10270818575435430716284325)
    ·
      refine ⟨1925778482894143259303311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10270818575435430716284325 1925778482894143259303311)
      ·
        refine ⟨2888667724341214888954967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1925778482894143259303311 2888667724341214888954967)
        ·
          refine ⟨4333001586511822333432451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2888667724341214888954967 4333001586511822333432451)
          ·
            refine ⟨6499502379767733500148677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4333001586511822333432451 6499502379767733500148677)
            ·
              refine ⟨1218656696206450031277877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6499502379767733500148677 1218656696206450031277877)
              ·
                refine ⟨114249065269354690432301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1218656696206450031277877 114249065269354690432301)
                ·
                  rfl

theorem cell21_1501870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 4, 5].length) (baseStart_1501870 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1501870 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1501870 prefixEnd_1501870 := by exact prefixLift 1501870
  have htrace : WordTrace (prefixWord ++ tailWord_1501870) baseStart_1501870 baseEnd_1501870 := by
    simpa [prefixWord, tailWord_1501870, baseEnd_1501870] using wordTrace_append hprefix tailTrace_1501870
  have hstable : (prefixWord ++ tailWord_1501870).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501870).length < 2 ^ (prefixWord ++ tailWord_1501870).sum := by decide
  have hdescent : baseEnd_1501870 < baseStart_1501870 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501912 : List Nat := [2, 1, 2, 2, 3, 3, 2, 6]
def baseStart_1501912 : Nat := 118140960795 + 1501912 * 2 ^ 59
def prefixEnd_1501912 : Nat := 4983230072969 + 3 ^ 40 * 1501912 * 2
def baseEnd_1501912 : Nat := 114252260260093777198939

theorem tailTrace_1501912 : CollatzResearch.WordTrace tailWord_1501912 prefixEnd_1501912 114252260260093777198939 := by
  unfold tailWord_1501912
  simp only [CollatzResearch.WordTrace]
  refine ⟨27389615467418402496605995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36519487289891203328807993 27389615467418402496605995)
  ·
    refine ⟨41084423201127603744908993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27389615467418402496605995 41084423201127603744908993)
    ·
      refine ⟨30813317400845702808681745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41084423201127603744908993 30813317400845702808681745)
      ·
        refine ⟨23109988050634277106511309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30813317400845702808681745 23109988050634277106511309)
        ·
          refine ⟨8666245518987853914941741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23109988050634277106511309 8666245518987853914941741)
          ·
            refine ⟨3249842069620445218103153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8666245518987853914941741 3249842069620445218103153)
            ·
              refine ⟨2437381552215333913577365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3249842069620445218103153 2437381552215333913577365)
              ·
                refine ⟨114252260260093777198939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2437381552215333913577365 114252260260093777198939)
                ·
                  rfl

theorem cell21_1501912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 6].length) (baseStart_1501912 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1501912 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1501912 prefixEnd_1501912 := by exact prefixLift 1501912
  have htrace : WordTrace (prefixWord ++ tailWord_1501912) baseStart_1501912 baseEnd_1501912 := by
    simpa [prefixWord, tailWord_1501912, baseEnd_1501912] using wordTrace_append hprefix tailTrace_1501912
  have hstable : (prefixWord ++ tailWord_1501912).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501912).length < 2 ^ (prefixWord ++ tailWord_1501912).sum := by decide
  have hdescent : baseEnd_1501912 < baseStart_1501912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501943 : List Nat := [1, 1, 3, 1, 1, 1, 3, 7, 3]
def baseStart_1501943 : Nat := 118140960795 + 1501943 * 2 ^ 59
def prefixEnd_1501943 : Nat := 4983230072969 + 3 ^ 40 * 1501943 * 2
def baseEnd_1501943 : Nat := 342763855402632166580087

theorem tailTrace_1501943 : CollatzResearch.WordTrace tailWord_1501943 prefixEnd_1501943 342763855402632166580087 := by
  unfold tailWord_1501943
  simp only [CollatzResearch.WordTrace]
  refine ⟨54780361597724497287590483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36520241065149664858393655 54780361597724497287590483)
  ·
    refine ⟨82170542396586745931385725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54780361597724497287590483 82170542396586745931385725)
    ·
      refine ⟨30813953398720029724269647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82170542396586745931385725 30813953398720029724269647)
      ·
        refine ⟨46220930098080044586404471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30813953398720029724269647 46220930098080044586404471)
        ·
          refine ⟨69331395147120066879606707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46220930098080044586404471 69331395147120066879606707)
          ·
            refine ⟨103997092720680100319410061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69331395147120066879606707 103997092720680100319410061)
            ·
              refine ⟨38998909770255037619778773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103997092720680100319410061 38998909770255037619778773)
              ·
                refine ⟨914036947740352444213565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 38998909770255037619778773 914036947740352444213565)
                ·
                  refine ⟨342763855402632166580087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 914036947740352444213565 342763855402632166580087)
                  ·
                    rfl

theorem cell21_1501943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 7, 3].length) (baseStart_1501943 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1501943 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1501943 prefixEnd_1501943 := by exact prefixLift 1501943
  have htrace : WordTrace (prefixWord ++ tailWord_1501943) baseStart_1501943 baseEnd_1501943 := by
    simpa [prefixWord, tailWord_1501943, baseEnd_1501943] using wordTrace_append hprefix tailTrace_1501943
  have hstable : (prefixWord ++ tailWord_1501943).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501943).length < 2 ^ (prefixWord ++ tailWord_1501943).sum := by decide
  have hdescent : baseEnd_1501943 < baseStart_1501943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501960 : List Nat := [2, 1, 3, 2, 2, 3, 1, 4, 3]
def baseStart_1501960 : Nat := 118140960795 + 1501960 * 2 ^ 59
def prefixEnd_1501960 : Nat := 4983230072969 + 3 ^ 40 * 1501960 * 2
def baseEnd_1501960 : Nat := 342767735034243914796719

theorem tailTrace_1501960 : CollatzResearch.WordTrace tailWord_1501960 prefixEnd_1501960 342767735034243914796719 := by
  unfold tailWord_1501960
  simp only [CollatzResearch.WordTrace]
  refine ⟨27390490819331454595479667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36520654425775272793972889 27390490819331454595479667)
  ·
    refine ⟨41085736228997181893219501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27390490819331454595479667 41085736228997181893219501)
    ·
      refine ⟨15407151085873943209957313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41085736228997181893219501 15407151085873943209957313)
      ·
        refine ⟨11555363314405457407467985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15407151085873943209957313 11555363314405457407467985)
        ·
          refine ⟨8666522485804093055600989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11555363314405457407467985 8666522485804093055600989)
          ·
            refine ⟨3249945932176534895850371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8666522485804093055600989 3249945932176534895850371)
            ·
              refine ⟨4874918898264802343775557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3249945932176534895850371 4874918898264802343775557)
              ·
                refine ⟨914047293424650439457917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4874918898264802343775557 914047293424650439457917)
                ·
                  refine ⟨342767735034243914796719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 914047293424650439457917 342767735034243914796719)
                  ·
                    rfl

theorem cell21_1501960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 4, 3].length) (baseStart_1501960 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1501960 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1501960 prefixEnd_1501960 := by exact prefixLift 1501960
  have htrace : WordTrace (prefixWord ++ tailWord_1501960) baseStart_1501960 baseEnd_1501960 := by
    simpa [prefixWord, tailWord_1501960, baseEnd_1501960] using wordTrace_append hprefix tailTrace_1501960
  have hstable : (prefixWord ++ tailWord_1501960).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501960).length < 2 ^ (prefixWord ++ tailWord_1501960).sum := by decide
  have hdescent : baseEnd_1501960 < baseStart_1501960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501994 : List Nat := [3, 1, 4, 3, 1, 1, 2, 3, 3]
def baseStart_1501994 : Nat := 118140960795 + 1501994 * 2 ^ 59
def prefixEnd_1501994 : Nat := 4983230072969 + 3 ^ 40 * 1501994 * 2
def baseEnd_1501994 : Nat := 342775494297467411229983

theorem tailTrace_1501994 : CollatzResearch.WordTrace tailWord_1501994 prefixEnd_1501994 342775494297467411229983 := by
  unfold tailWord_1501994
  simp only [CollatzResearch.WordTrace]
  refine ⟨13695555430134933249424259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36521481147026488665131357 13695555430134933249424259)
  ·
    refine ⟨20543333145202399874136389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13695555430134933249424259 20543333145202399874136389)
    ·
      refine ⟨3851874964725449976400573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20543333145202399874136389 3851874964725449976400573)
      ·
        refine ⟨1444453111772043741150215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3851874964725449976400573 1444453111772043741150215)
        ·
          refine ⟨2166679667658065611725323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1444453111772043741150215 2166679667658065611725323)
          ·
            refine ⟨3250019501487098417587985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2166679667658065611725323 3250019501487098417587985)
            ·
              refine ⟨2437514626115323813190989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3250019501487098417587985 2437514626115323813190989)
              ·
                refine ⟨914067984793246429946621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2437514626115323813190989 914067984793246429946621)
                ·
                  refine ⟨342775494297467411229983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 914067984793246429946621 342775494297467411229983)
                  ·
                    rfl

theorem cell21_1501994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 3, 3].length) (baseStart_1501994 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1501994 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1501994 prefixEnd_1501994 := by exact prefixLift 1501994
  have htrace : WordTrace (prefixWord ++ tailWord_1501994) baseStart_1501994 baseEnd_1501994 := by
    simpa [prefixWord, tailWord_1501994, baseEnd_1501994] using wordTrace_append hprefix tailTrace_1501994
  have hstable : (prefixWord ++ tailWord_1501994).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501994).length < 2 ^ (prefixWord ++ tailWord_1501994).sum := by decide
  have hdescent : baseEnd_1501994 < baseStart_1501994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502002 : List Nat := [3, 2, 1, 1, 3, 1, 1, 2, 7]
def baseStart_1502002 : Nat := 118140960795 + 1502002 * 2 ^ 59
def prefixEnd_1502002 : Nat := 4983230072969 + 3 ^ 40 * 1502002 * 2
def baseEnd_1502002 : Nat := 342777320006461175096633

theorem tailTrace_1502002 : CollatzResearch.WordTrace tailWord_1502002 prefixEnd_1502002 342777320006461175096633 := by
  unfold tailWord_1502002
  simp only [CollatzResearch.WordTrace]
  refine ⟨13695628376127687590997065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36521675669673833575992173 13695628376127687590997065)
  ·
    refine ⟨10271721282095765693247799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13695628376127687590997065 10271721282095765693247799)
    ·
      refine ⟨15407581923143648539871699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10271721282095765693247799 15407581923143648539871699)
      ·
        refine ⟨23111372884715472809807549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15407581923143648539871699 23111372884715472809807549)
        ·
          refine ⟨8666764831768302303677831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23111372884715472809807549 8666764831768302303677831)
          ·
            refine ⟨13000147247652453455516747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8666764831768302303677831 13000147247652453455516747)
            ·
              refine ⟨19500220871478680183275121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13000147247652453455516747 19500220871478680183275121)
              ·
                refine ⟨14625165653609010137456341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19500220871478680183275121 14625165653609010137456341)
                ·
                  refine ⟨342777320006461175096633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14625165653609010137456341 342777320006461175096633)
                  ·
                    rfl

theorem cell21_1502002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 7].length) (baseStart_1502002 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1502002 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1502002 prefixEnd_1502002 := by exact prefixLift 1502002
  have htrace : WordTrace (prefixWord ++ tailWord_1502002) baseStart_1502002 baseEnd_1502002 := by
    simpa [prefixWord, tailWord_1502002, baseEnd_1502002] using wordTrace_append hprefix tailTrace_1502002
  have hstable : (prefixWord ++ tailWord_1502002).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502002).length < 2 ^ (prefixWord ++ tailWord_1502002).sum := by decide
  have hdescent : baseEnd_1502002 < baseStart_1502002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502019 : List Nat := [1, 1, 1, 3, 1, 4, 1, 6, 3]
def baseStart_1502019 : Nat := 118140960795 + 1502019 * 2 ^ 59
def prefixEnd_1502019 : Nat := 4983230072969 + 3 ^ 40 * 1502019 * 2
def baseEnd_1502019 : Nat := 342781199638072923313265

theorem tailTrace_1502019 : CollatzResearch.WordTrace tailWord_1502019 prefixEnd_1502019 342781199638072923313265 := by
  unfold tailWord_1502019
  simp only [CollatzResearch.WordTrace]
  refine ⟨54783133545449162267357111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36522089030299441511571407 54783133545449162267357111)
  ·
    refine ⟨82174700318173743401035667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54783133545449162267357111 82174700318173743401035667)
    ·
      refine ⟨123262050477260615101553501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82174700318173743401035667 123262050477260615101553501)
      ·
        refine ⟨46223268928972730663082563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123262050477260615101553501 46223268928972730663082563)
        ·
          refine ⟨69334903393459095994623845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46223268928972730663082563 69334903393459095994623845)
          ·
            refine ⟨13000294386273580498991971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69334903393459095994623845 13000294386273580498991971)
            ·
              refine ⟨19500441579410370748487957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13000294386273580498991971 19500441579410370748487957)
              ·
                refine ⟨914083199034861128835373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19500441579410370748487957 914083199034861128835373)
                ·
                  refine ⟨342781199638072923313265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 914083199034861128835373 342781199638072923313265)
                  ·
                    rfl

theorem cell21_1502019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 6, 3].length) (baseStart_1502019 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1502019 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1502019 prefixEnd_1502019 := by exact prefixLift 1502019
  have htrace : WordTrace (prefixWord ++ tailWord_1502019) baseStart_1502019 baseEnd_1502019 := by
    simpa [prefixWord, tailWord_1502019, baseEnd_1502019] using wordTrace_append hprefix tailTrace_1502019
  have hstable : (prefixWord ++ tailWord_1502019).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502019).length < 2 ^ (prefixWord ++ tailWord_1502019).sum := by decide
  have hdescent : baseEnd_1502019 < baseStart_1502019 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502047 : List Nat := [1, 1, 2, 3, 1, 3, 3, 7]
def baseStart_1502047 : Nat := 118140960795 + 1502047 * 2 ^ 59
def prefixEnd_1502047 : Nat := 4983230072969 + 3 ^ 40 * 1502047 * 2
def baseEnd_1502047 : Nat := 114262529873183698948847

theorem tailTrace_1502047 : CollatzResearch.WordTrace tailWord_1502047 prefixEnd_1502047 114262529873183698948847 := by
  unfold tailWord_1502047
  simp only [CollatzResearch.WordTrace]
  refine ⟨54784154789347723049376395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36522769859565148699584263 54784154789347723049376395)
  ·
    refine ⟨82176232184021584574064593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54784154789347723049376395 82176232184021584574064593)
    ·
      refine ⟨61632174138016188430548445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82176232184021584574064593 61632174138016188430548445)
      ·
        refine ⟨23112065301756070661455667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61632174138016188430548445 23112065301756070661455667)
        ·
          refine ⟨34668097952634105992183501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23112065301756070661455667 34668097952634105992183501)
          ·
            refine ⟨13000536732237789747068813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34668097952634105992183501 13000536732237789747068813)
            ·
              refine ⟨4875201274589171155150805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13000536732237789747068813 4875201274589171155150805)
              ·
                refine ⟨114262529873183698948847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4875201274589171155150805 114262529873183698948847)
                ·
                  rfl

theorem cell21_1502047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 7].length) (baseStart_1502047 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1502047 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1502047 prefixEnd_1502047 := by exact prefixLift 1502047
  have htrace : WordTrace (prefixWord ++ tailWord_1502047) baseStart_1502047 baseEnd_1502047 := by
    simpa [prefixWord, tailWord_1502047, baseEnd_1502047] using wordTrace_append hprefix tailTrace_1502047
  have hstable : (prefixWord ++ tailWord_1502047).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502047).length < 2 ^ (prefixWord ++ tailWord_1502047).sum := by decide
  have hdescent : baseEnd_1502047 < baseStart_1502047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502070 : List Nat := [5, 1, 1, 3, 1, 2, 3, 2, 3]
def baseStart_1502070 : Nat := 118140960795 + 1502070 * 2 ^ 59
def prefixEnd_1502070 : Nat := 4983230072969 + 3 ^ 40 * 1502070 * 2
def baseEnd_1502070 : Nat := 342792838532908167963161

theorem tailTrace_1502070 : CollatzResearch.WordTrace tailWord_1502070 prefixEnd_1502070 342792838532908167963161 := by
  unfold tailWord_1502070
  simp only [CollatzResearch.WordTrace]
  refine ⟨3424062104266524873591479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36523329112176265318309109 3424062104266524873591479)
  ·
    refine ⟨5136093156399787310387219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3424062104266524873591479 5136093156399787310387219)
    ·
      refine ⟨7704139734599680965580829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5136093156399787310387219 7704139734599680965580829)
      ·
        refine ⟨2889052400474880362092811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7704139734599680965580829 2889052400474880362092811)
        ·
          refine ⟨4333578600712320543139217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2889052400474880362092811 4333578600712320543139217)
          ·
            refine ⟨3250183950534240407354413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4333578600712320543139217 3250183950534240407354413)
            ·
              refine ⟨1218818981450340152757905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3250183950534240407354413 1218818981450340152757905)
              ·
                refine ⟨914114236087755114568429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1218818981450340152757905 914114236087755114568429)
                ·
                  refine ⟨342792838532908167963161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 914114236087755114568429 342792838532908167963161)
                  ·
                    rfl

theorem cell21_1502070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 3, 2, 3].length) (baseStart_1502070 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1502070 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1502070 prefixEnd_1502070 := by exact prefixLift 1502070
  have htrace : WordTrace (prefixWord ++ tailWord_1502070) baseStart_1502070 baseEnd_1502070 := by
    simpa [prefixWord, tailWord_1502070, baseEnd_1502070] using wordTrace_append hprefix tailTrace_1502070
  have hstable : (prefixWord ++ tailWord_1502070).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502070).length < 2 ^ (prefixWord ++ tailWord_1502070).sum := by decide
  have hdescent : baseEnd_1502070 < baseStart_1502070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502216 : List Nat := [2, 1, 3, 2, 1, 3, 4, 5]
def baseStart_1502216 : Nat := 118140960795 + 1502216 * 2 ^ 59
def prefixEnd_1502216 : Nat := 4983230072969 + 3 ^ 40 * 1502216 * 2
def baseEnd_1502216 : Nat := 114275385907348119509843

theorem tailTrace_1502216 : CollatzResearch.WordTrace tailWord_1502216 prefixEnd_1502216 114275385907348119509843 := by
  unfold tailWord_1502216
  simp only [CollatzResearch.WordTrace]
  refine ⟨27395159362867732456139251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36526879150490309941519001 27395159362867732456139251)
  ·
    refine ⟨41092739044301598684208877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27395159362867732456139251 41092739044301598684208877)
    ·
      refine ⟨15409777141613099506578329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41092739044301598684208877 15409777141613099506578329)
      ·
        refine ⟨11557332856209824629933747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15409777141613099506578329 11557332856209824629933747)
        ·
          refine ⟨17335999284314736944900621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11557332856209824629933747 17335999284314736944900621)
          ·
            refine ⟨6500999731618026354337733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17335999284314736944900621 6500999731618026354337733)
            ·
              refine ⟨1218937449678379941438325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6500999731618026354337733 1218937449678379941438325)
              ·
                refine ⟨114275385907348119509843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1218937449678379941438325 114275385907348119509843)
                ·
                  rfl

theorem cell21_1502216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 4, 5].length) (baseStart_1502216 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1502216 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1502216 prefixEnd_1502216 := by exact prefixLift 1502216
  have htrace : WordTrace (prefixWord ++ tailWord_1502216) baseStart_1502216 baseEnd_1502216 := by
    simpa [prefixWord, tailWord_1502216, baseEnd_1502216] using wordTrace_append hprefix tailTrace_1502216
  have hstable : (prefixWord ++ tailWord_1502216).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502216).length < 2 ^ (prefixWord ++ tailWord_1502216).sum := by decide
  have hdescent : baseEnd_1502216 < baseStart_1502216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502340 : List Nat := [2, 3, 2, 1, 2, 3, 2, 3, 3]
def baseStart_1502340 : Nat := 118140960795 + 1502340 * 2 ^ 59
def prefixEnd_1502340 : Nat := 4983230072969 + 3 ^ 40 * 1502340 * 2
def baseEnd_1502340 : Nat := 342854456211447698462609

theorem tailTrace_1502340 : CollatzResearch.WordTrace tailWord_1502340 prefixEnd_1502340 342854456211447698462609 := by
  unfold tailWord_1502340
  simp only [CollatzResearch.WordTrace]
  refine ⟨27397420688643117044896237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36529894251524156059861649 27397420688643117044896237)
  ·
    refine ⟨10274032758241168891836089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27397420688643117044896237 10274032758241168891836089)
    ·
      refine ⟨7705524568680876668877067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10274032758241168891836089 7705524568680876668877067)
      ·
        refine ⟨11558286853021315003315601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7705524568680876668877067 11558286853021315003315601)
        ·
          refine ⟨8668715139765986252486701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11558286853021315003315601 8668715139765986252486701)
          ·
            refine ⟨3250768177412244844682513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8668715139765986252486701 3250768177412244844682513)
            ·
              refine ⟨2438076133059183633511885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3250768177412244844682513 2438076133059183633511885)
              ·
                refine ⟨914278549897193862566957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2438076133059183633511885 914278549897193862566957)
                ·
                  refine ⟨342854456211447698462609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 914278549897193862566957 342854456211447698462609)
                  ·
                    rfl

theorem cell21_1502340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 3, 3].length) (baseStart_1502340 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1502340 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1502340 prefixEnd_1502340 := by exact prefixLift 1502340
  have htrace : WordTrace (prefixWord ++ tailWord_1502340) baseStart_1502340 baseEnd_1502340 := by
    simpa [prefixWord, tailWord_1502340, baseEnd_1502340] using wordTrace_append hprefix tailTrace_1502340
  have hstable : (prefixWord ++ tailWord_1502340).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502340).length < 2 ^ (prefixWord ++ tailWord_1502340).sum := by decide
  have hdescent : baseEnd_1502340 < baseStart_1502340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502354 : List Nat := [3, 2, 3, 1, 1, 2, 3, 2, 4]
def baseStart_1502354 : Nat := 118140960795 + 1502354 * 2 ^ 59
def prefixEnd_1502354 : Nat := 4983230072969 + 3 ^ 40 * 1502354 * 2
def baseEnd_1502354 : Nat := 342857651202186785229247

theorem tailTrace_1502354 : CollatzResearch.WordTrace tailWord_1502354 prefixEnd_1502354 342857651202186785229247 := by
  unfold tailWord_1502354
  simp only [CollatzResearch.WordTrace]
  refine ⟨13698837999808878620200529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36530234666157009653868077 13698837999808878620200529)
  ·
    refine ⟨10274128499856658965150397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13698837999808878620200529 10274128499856658965150397)
    ·
      refine ⟨3852798187446247111931399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10274128499856658965150397 3852798187446247111931399)
      ·
        refine ⟨5779197281169370667897099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3852798187446247111931399 5779197281169370667897099)
        ·
          refine ⟨8668795921754056001845649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5779197281169370667897099 8668795921754056001845649)
          ·
            refine ⟨6501596941315542001384237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8668795921754056001845649 6501596941315542001384237)
            ·
              refine ⟨2438098852993328250519089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6501596941315542001384237 2438098852993328250519089)
              ·
                refine ⟨1828574139744996187889317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2438098852993328250519089 1828574139744996187889317)
                ·
                  refine ⟨342857651202186785229247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1828574139744996187889317 342857651202186785229247)
                  ·
                    rfl

theorem cell21_1502354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 2, 4].length) (baseStart_1502354 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1502354 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1502354 prefixEnd_1502354 := by exact prefixLift 1502354
  have htrace : WordTrace (prefixWord ++ tailWord_1502354) baseStart_1502354 baseEnd_1502354 := by
    simpa [prefixWord, tailWord_1502354, baseEnd_1502354] using wordTrace_append hprefix tailTrace_1502354
  have hstable : (prefixWord ++ tailWord_1502354).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502354).length < 2 ^ (prefixWord ++ tailWord_1502354).sum := by decide
  have hdescent : baseEnd_1502354 < baseStart_1502354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502385 : List Nat := [1, 2, 2, 5, 1, 3, 2, 5]
def baseStart_1502385 : Nat := 118140960795 + 1502385 * 2 ^ 59
def prefixEnd_1502385 : Nat := 4983230072969 + 3 ^ 40 * 1502385 * 2
def baseEnd_1502385 : Nat := 114288241941512540070839

theorem tailTrace_1502385 : CollatzResearch.WordTrace tailWord_1502385 prefixEnd_1502385 114288241941512540070839 := by
  unfold tailWord_1502385
  simp only [CollatzResearch.WordTrace]
  refine ⟨54796482662123206775180609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36530988441415471183453739 54796482662123206775180609)
  ·
    refine ⟨41097361996592405081385457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54796482662123206775180609 41097361996592405081385457)
    ·
      refine ⟨30823021497444303811039093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41097361996592405081385457 30823021497444303811039093)
      ·
        refine ⟨2889658265385403482284915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30823021497444303811039093 2889658265385403482284915)
        ·
          refine ⟨4334487398078105223427373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2889658265385403482284915 4334487398078105223427373)
          ·
            refine ⟨1625432774279289458785265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4334487398078105223427373 1625432774279289458785265)
            ·
              refine ⟨1219074580709467094088949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1625432774279289458785265 1219074580709467094088949)
              ·
                refine ⟨114288241941512540070839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1219074580709467094088949 114288241941512540070839)
                ·
                  rfl

theorem cell21_1502385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 2, 5].length) (baseStart_1502385 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1502385 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1502385 prefixEnd_1502385 := by exact prefixLift 1502385
  have htrace : WordTrace (prefixWord ++ tailWord_1502385) baseStart_1502385 baseEnd_1502385 := by
    simpa [prefixWord, tailWord_1502385, baseEnd_1502385] using wordTrace_append hprefix tailTrace_1502385
  have hstable : (prefixWord ++ tailWord_1502385).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502385).length < 2 ^ (prefixWord ++ tailWord_1502385).sum := by decide
  have hdescent : baseEnd_1502385 < baseStart_1502385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502399 : List Nat := [1, 1, 2, 2, 2, 2, 5, 3, 3]
def baseStart_1502399 : Nat := 118140960795 + 1502399 * 2 ^ 59
def prefixEnd_1502399 : Nat := 4983230072969 + 3 ^ 40 * 1502399 * 2
def baseEnd_1502399 : Nat := 342867920815276706979155

theorem tailTrace_1502399 : CollatzResearch.WordTrace tailWord_1502399 prefixEnd_1502399 342867920815276706979155 := by
  unfold tailWord_1502399
  simp only [CollatzResearch.WordTrace]
  refine ⟨54796993284072487166190251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36531328856048324777460167 54796993284072487166190251)
  ·
    refine ⟨82195489926108730749285377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54796993284072487166190251 82195489926108730749285377)
    ·
      refine ⟨61646617444581548061964033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82195489926108730749285377 61646617444581548061964033)
      ·
        refine ⟨46234963083436161046473025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61646617444581548061964033 46234963083436161046473025)
        ·
          refine ⟨34676222312577120784854769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46234963083436161046473025 34676222312577120784854769)
          ·
            refine ⟨26007166734432840588641077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34676222312577120784854769 26007166734432840588641077)
            ·
              refine ⟨2438171881353078805185101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26007166734432840588641077 2438171881353078805185101)
              ·
                refine ⟨914314455507404551944413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2438171881353078805185101 914314455507404551944413)
                ·
                  refine ⟨342867920815276706979155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 914314455507404551944413 342867920815276706979155)
                  ·
                    rfl

theorem cell21_1502399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 3, 3].length) (baseStart_1502399 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1502399 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1502399 prefixEnd_1502399 := by exact prefixLift 1502399
  have htrace : WordTrace (prefixWord ++ tailWord_1502399) baseStart_1502399 baseEnd_1502399 := by
    simpa [prefixWord, tailWord_1502399, baseEnd_1502399] using wordTrace_append hprefix tailTrace_1502399
  have hstable : (prefixWord ++ tailWord_1502399).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502399).length < 2 ^ (prefixWord ++ tailWord_1502399).sum := by decide
  have hdescent : baseEnd_1502399 < baseStart_1502399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502402 : List Nat := [3, 5, 1, 1, 2, 2, 7]
def baseStart_1502402 : Nat := 118140960795 + 1502402 * 2 ^ 59
def prefixEnd_1502402 : Nat := 4983230072969 + 3 ^ 40 * 1502402 * 2
def baseEnd_1502402 : Nat := 38096511717349929825461

theorem tailTrace_1502402 : CollatzResearch.WordTrace tailWord_1502402 prefixEnd_1502402 38096511717349929825461 := by
  unfold tailWord_1502402
  simp only [CollatzResearch.WordTrace]
  refine ⟨13699275675765404669637365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36531401802041079119032973 13699275675765404669637365)
  ·
    refine ⟨1284307094603006687778503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13699275675765404669637365 1284307094603006687778503)
    ·
      refine ⟨1926460641904510031667755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1284307094603006687778503 1926460641904510031667755)
      ·
        refine ⟨2889690962856765047501633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1926460641904510031667755 2889690962856765047501633)
        ·
          refine ⟨2167268222142573785626225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2889690962856765047501633 2167268222142573785626225)
          ·
            refine ⟨1625451166606930339219669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2167268222142573785626225 1625451166606930339219669)
            ·
              refine ⟨38096511717349929825461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1625451166606930339219669 38096511717349929825461)
              ·
                rfl

theorem cell21_1502402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 7].length) (baseStart_1502402 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1502402 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1502402 prefixEnd_1502402 := by exact prefixLift 1502402
  have htrace : WordTrace (prefixWord ++ tailWord_1502402) baseStart_1502402 baseEnd_1502402 := by
    simpa [prefixWord, tailWord_1502402, baseEnd_1502402] using wordTrace_append hprefix tailTrace_1502402
  have hstable : (prefixWord ++ tailWord_1502402).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502402).length < 2 ^ (prefixWord ++ tailWord_1502402).sum := by decide
  have hdescent : baseEnd_1502402 < baseStart_1502402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502475 : List Nat := [1, 1, 1, 1, 5, 4, 1, 4, 3]
def baseStart_1502475 : Nat := 118140960795 + 1502475 * 2 ^ 59
def prefixEnd_1502475 : Nat := 4983230072969 + 3 ^ 40 * 1502475 * 2
def baseEnd_1502475 : Nat := 342885265050717463712333

theorem tailTrace_1502475 : CollatzResearch.WordTrace tailWord_1502475 prefixEnd_1502475 342885265050717463712333 := by
  unfold tailWord_1502475
  simp only [CollatzResearch.WordTrace]
  refine ⟨54799765231797152145956879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36533176821198101430637919 54799765231797152145956879)
  ·
    refine ⟨82199647847695728218935319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54799765231797152145956879 82199647847695728218935319)
    ·
      refine ⟨123299471771543592328402979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82199647847695728218935319 123299471771543592328402979)
      ·
        refine ⟨184949207657315388492604469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123299471771543592328402979 184949207657315388492604469)
        ·
          refine ⟨17338988217873317671181669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 184949207657315388492604469 17338988217873317671181669)
          ·
            refine ⟨3251060290851247063346563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17338988217873317671181669 3251060290851247063346563)
            ·
              refine ⟨4876590436276870595019845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3251060290851247063346563 4876590436276870595019845)
              ·
                refine ⟨914360706801913236566221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4876590436276870595019845 914360706801913236566221)
                ·
                  refine ⟨342885265050717463712333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 914360706801913236566221 342885265050717463712333)
                  ·
                    rfl

theorem cell21_1502475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 4, 3].length) (baseStart_1502475 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1502475 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1502475 prefixEnd_1502475 := by exact prefixLift 1502475
  have htrace : WordTrace (prefixWord ++ tailWord_1502475) baseStart_1502475 baseEnd_1502475 := by
    simpa [prefixWord, tailWord_1502475, baseEnd_1502475] using wordTrace_append hprefix tailTrace_1502475
  have hstable : (prefixWord ++ tailWord_1502475).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502475).length < 2 ^ (prefixWord ++ tailWord_1502475).sum := by decide
  have hdescent : baseEnd_1502475 < baseStart_1502475 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502509 : List Nat := [1, 5, 3, 1, 1, 2, 2, 3, 3]
def baseStart_1502509 : Nat := 118140960795 + 1502509 * 2 ^ 59
def prefixEnd_1502509 : Nat := 4983230072969 + 3 ^ 40 * 1502509 * 2
def baseEnd_1502509 : Nat := 342893024313940960145597

theorem tailTrace_1502509 : CollatzResearch.WordTrace tailWord_1502509 prefixEnd_1502509 342893024313940960145597 := by
  unfold tailWord_1502509
  simp only [CollatzResearch.WordTrace]
  refine ⟨54801005313673975952694581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36534003542449317301796387 54801005313673975952694581)
  ·
    refine ⟨5137594248156935245565117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54801005313673975952694581 5137594248156935245565117)
    ·
      refine ⟨1926597843058850717086919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5137594248156935245565117 1926597843058850717086919)
      ·
        refine ⟨2889896764588276075630379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1926597843058850717086919 2889896764588276075630379)
        ·
          refine ⟨4334845146882414113445569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2889896764588276075630379 4334845146882414113445569)
          ·
            refine ⟨3251133860161810585084177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4334845146882414113445569 3251133860161810585084177)
            ·
              refine ⟨2438350395121357938813133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3251133860161810585084177 2438350395121357938813133)
              ·
                refine ⟨914381398170509227054925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2438350395121357938813133 914381398170509227054925)
                ·
                  refine ⟨342893024313940960145597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 914381398170509227054925 342893024313940960145597)
                  ·
                    rfl

theorem cell21_1502509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 3, 3].length) (baseStart_1502509 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1502509 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1502509 prefixEnd_1502509 := by exact prefixLift 1502509
  have htrace : WordTrace (prefixWord ++ tailWord_1502509) baseStart_1502509 baseEnd_1502509 := by
    simpa [prefixWord, tailWord_1502509, baseEnd_1502509] using wordTrace_append hprefix tailTrace_1502509
  have hstable : (prefixWord ++ tailWord_1502509).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502509).length < 2 ^ (prefixWord ++ tailWord_1502509).sum := by decide
  have hdescent : baseEnd_1502509 < baseStart_1502509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502638 : List Nat := [4, 1, 16]
def baseStart_1502638 : Nat := 118140960795 + 1502638 * 2 ^ 59
def prefixEnd_1502638 : Nat := 4983230072969 + 3 ^ 40 * 1502638 * 2
def baseEnd_1502638 : Nat := 470401185008868864877

theorem tailTrace_1502638 : CollatzResearch.WordTrace tailWord_1502638 prefixEnd_1502638 470401185008868864877 := by
  unfold tailWord_1502638
  simp only [CollatzResearch.WordTrace]
  refine ⟨6850713791275828873017571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36537140220137753989427045 6850713791275828873017571)
  ·
    refine ⟨10276070686913743309526357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6850713791275828873017571 10276070686913743309526357)
    ·
      refine ⟨470401185008868864877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 16 10276070686913743309526357 470401185008868864877)
      ·
        rfl

theorem cell21_1502638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 16].length) (baseStart_1502638 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1502638 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1502638 prefixEnd_1502638 := by exact prefixLift 1502638
  have htrace : WordTrace (prefixWord ++ tailWord_1502638) baseStart_1502638 baseEnd_1502638 := by
    simpa [prefixWord, tailWord_1502638, baseEnd_1502638] using wordTrace_append hprefix tailTrace_1502638
  have hstable : (prefixWord ++ tailWord_1502638).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502638).length < 2 ^ (prefixWord ++ tailWord_1502638).sum := by decide
  have hdescent : baseEnd_1502638 < baseStart_1502638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502641 : List Nat := [1, 2, 2, 4, 1, 1, 4, 2, 4]
def baseStart_1502641 : Nat := 118140960795 + 1502641 * 2 ^ 59
def prefixEnd_1502641 : Nat := 4983230072969 + 3 ^ 40 * 1502641 * 2
def baseEnd_1502641 : Nat := 342923148512338063945327

theorem tailTrace_1502641 : CollatzResearch.WordTrace tailWord_1502641 prefixEnd_1502641 342923148512338063945327 := by
  unfold tailWord_1502641
  simp only [CollatzResearch.WordTrace]
  refine ⟨54805819749195762496499777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36537213166130508330999851 54805819749195762496499777)
  ·
    refine ⟨41104364811896821872374833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54805819749195762496499777 41104364811896821872374833)
    ·
      refine ⟨30828273608922616404281125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41104364811896821872374833 30828273608922616404281125)
      ·
        refine ⟨5780301301672990575802711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30828273608922616404281125 5780301301672990575802711)
        ·
          refine ⟨8670451952509485863704067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5780301301672990575802711 8670451952509485863704067)
          ·
            refine ⟨13005677928764228795556101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8670451952509485863704067 13005677928764228795556101)
            ·
              refine ⟨2438564611643292899166769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13005677928764228795556101 2438564611643292899166769)
              ·
                refine ⟨1828923458732469674375077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2438564611643292899166769 1828923458732469674375077)
                ·
                  refine ⟨342923148512338063945327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1828923458732469674375077 342923148512338063945327)
                  ·
                    rfl

theorem cell21_1502641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 2, 4].length) (baseStart_1502641 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1502641 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1502641 prefixEnd_1502641 := by exact prefixLift 1502641
  have htrace : WordTrace (prefixWord ++ tailWord_1502641) baseStart_1502641 baseEnd_1502641 := by
    simpa [prefixWord, tailWord_1502641, baseEnd_1502641] using wordTrace_append hprefix tailTrace_1502641
  have hstable : (prefixWord ++ tailWord_1502641).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502641).length < 2 ^ (prefixWord ++ tailWord_1502641).sum := by decide
  have hdescent : baseEnd_1502641 < baseStart_1502641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502683 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 12]
def baseStart_1502683 : Nat := 118140960795 + 1502683 * 2 ^ 59
def prefixEnd_1502683 : Nat := 4983230072969 + 3 ^ 40 * 1502683 * 2
def baseEnd_1502683 : Nat := 342932733484555324245241

theorem tailTrace_1502683 : CollatzResearch.WordTrace tailWord_1502683 prefixEnd_1502683 342932733484555324245241 := by
  unfold tailWord_1502683
  simp only [CollatzResearch.WordTrace]
  refine ⟨54807351615043603669528703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36538234410029069113019135 54807351615043603669528703)
  ·
    refine ⟨82211027422565405504293055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54807351615043603669528703 82211027422565405504293055)
    ·
      refine ⟨123316541133848108256439583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82211027422565405504293055 123316541133848108256439583)
      ·
        refine ⟨184974811700772162384659375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123316541133848108256439583 184974811700772162384659375)
        ·
          refine ⟨277462217551158243576989063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184974811700772162384659375 277462217551158243576989063)
          ·
            refine ⟨416193326326737365365483595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277462217551158243576989063 416193326326737365365483595)
            ·
              refine ⟨624289989490106048048225393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 416193326326737365365483595 624289989490106048048225393)
              ·
                refine ⟨468217492117579536036169045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 624289989490106048048225393 468217492117579536036169045)
                ·
                  refine ⟨342932733484555324245241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 468217492117579536036169045 342932733484555324245241)
                  ·
                    rfl

theorem cell21_1502683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 12].length) (baseStart_1502683 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1502683 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1502683 prefixEnd_1502683 := by exact prefixLift 1502683
  have htrace : WordTrace (prefixWord ++ tailWord_1502683) baseStart_1502683 baseEnd_1502683 := by
    simpa [prefixWord, tailWord_1502683, baseEnd_1502683] using wordTrace_append hprefix tailTrace_1502683
  have hstable : (prefixWord ++ tailWord_1502683).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502683).length < 2 ^ (prefixWord ++ tailWord_1502683).sum := by decide
  have hdescent : baseEnd_1502683 < baseStart_1502683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502700 : List Nat := [2, 2, 1, 1, 2, 1, 2, 6, 4]
def baseStart_1502700 : Nat := 118140960795 + 1502700 * 2 ^ 59
def prefixEnd_1502700 : Nat := 4983230072969 + 3 ^ 40 * 1502700 * 2
def baseEnd_1502700 : Nat := 342936613116167072461873

theorem tailTrace_1502700 : CollatzResearch.WordTrace tailWord_1502700 prefixEnd_1502700 342936613116167072461873 := by
  unfold tailWord_1502700
  simp only [CollatzResearch.WordTrace]
  refine ⟨27403985827991007786448777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36538647770654677048598369 27403985827991007786448777)
  ·
    refine ⟨20552989370993255839836583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27403985827991007786448777 20552989370993255839836583)
    ·
      refine ⟨30829484056489883759754875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20552989370993255839836583 30829484056489883759754875)
      ·
        refine ⟨46244226084734825639632313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30829484056489883759754875 46244226084734825639632313)
        ·
          refine ⟨34683169563551119229724235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46244226084734825639632313 34683169563551119229724235)
          ·
            refine ⟨52024754345326678844586353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34683169563551119229724235 52024754345326678844586353)
            ·
              refine ⟨39018565758995009133439765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52024754345326678844586353 39018565758995009133439765)
              ·
                refine ⟨1828995269952891053129989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 39018565758995009133439765 1828995269952891053129989)
                ·
                  refine ⟨342936613116167072461873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1828995269952891053129989 342936613116167072461873)
                  ·
                    rfl

theorem cell21_1502700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 4].length) (baseStart_1502700 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1502700 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1502700 prefixEnd_1502700 := by exact prefixLift 1502700
  have htrace : WordTrace (prefixWord ++ tailWord_1502700) baseStart_1502700 baseEnd_1502700 := by
    simpa [prefixWord, tailWord_1502700, baseEnd_1502700] using wordTrace_append hprefix tailTrace_1502700
  have hstable : (prefixWord ++ tailWord_1502700).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502700).length < 2 ^ (prefixWord ++ tailWord_1502700).sum := by decide
  have hdescent : baseEnd_1502700 < baseStart_1502700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502714 : List Nat := [3, 1, 1, 1, 1, 2, 4, 8]
def baseStart_1502714 : Nat := 118140960795 + 1502714 * 2 ^ 59
def prefixEnd_1502714 : Nat := 4983230072969 + 3 ^ 40 * 1502714 * 2
def baseEnd_1502714 : Nat := 114313269368968719742837

theorem tailTrace_1502714 : CollatzResearch.WordTrace tailWord_1502714 prefixEnd_1502714 114313269368968719742837 := by
  unfold tailWord_1502714
  simp only [CollatzResearch.WordTrace]
  refine ⟨13702120569482823990976799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36538988185287530642604797 13702120569482823990976799)
  ·
    refine ⟨20553180854224235986465199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13702120569482823990976799 20553180854224235986465199)
    ·
      refine ⟨30829771281336353979697799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20553180854224235986465199 30829771281336353979697799)
      ·
        refine ⟨46244656922004530969546699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30829771281336353979697799 46244656922004530969546699)
        ·
          refine ⟨69366985383006796454320049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46244656922004530969546699 69366985383006796454320049)
          ·
            refine ⟨52025239037255097340740037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69366985383006796454320049 52025239037255097340740037)
            ·
              refine ⟨9754732319485330751388757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52025239037255097340740037 9754732319485330751388757)
              ·
                refine ⟨114313269368968719742837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9754732319485330751388757 114313269368968719742837)
                ·
                  rfl

theorem cell21_1502714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 8].length) (baseStart_1502714 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1502714 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1502714 prefixEnd_1502714 := by exact prefixLift 1502714
  have htrace : WordTrace (prefixWord ++ tailWord_1502714) baseStart_1502714 baseEnd_1502714 := by
    simpa [prefixWord, tailWord_1502714, baseEnd_1502714] using wordTrace_append hprefix tailTrace_1502714
  have hstable : (prefixWord ++ tailWord_1502714).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502714).length < 2 ^ (prefixWord ++ tailWord_1502714).sum := by decide
  have hdescent : baseEnd_1502714 < baseStart_1502714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502731 : List Nat := [1, 1, 1, 1, 8, 1, 1, 7]
def baseStart_1502731 : Nat := 118140960795 + 1502731 * 2 ^ 59
def prefixEnd_1502731 : Nat := 4983230072969 + 3 ^ 40 * 1502731 * 2
def baseEnd_1502731 : Nat := 114314562579505969148381

theorem tailTrace_1502731 : CollatzResearch.WordTrace tailWord_1502731 prefixEnd_1502731 114314562579505969148381 := by
  unfold tailWord_1502731
  simp only [CollatzResearch.WordTrace]
  refine ⟨54809102318869707867276047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36539401545913138578184031 54809102318869707867276047)
  ·
    refine ⟨82213653478304561800914071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54809102318869707867276047 82213653478304561800914071)
    ·
      refine ⟨123320480217456842701371107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82213653478304561800914071 123320480217456842701371107)
      ·
        refine ⟨184980720326185264052056661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123320480217456842701371107 184980720326185264052056661)
        ·
          refine ⟨2167742816322483563110039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 184980720326185264052056661 2167742816322483563110039)
          ·
            refine ⟨3251614224483725344665059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2167742816322483563110039 3251614224483725344665059)
            ·
              refine ⟨4877421336725588016997589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3251614224483725344665059 4877421336725588016997589)
              ·
                refine ⟨114314562579505969148381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4877421336725588016997589 114314562579505969148381)
                ·
                  rfl

theorem cell21_1502731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 7].length) (baseStart_1502731 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1502731 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1502731 prefixEnd_1502731 := by exact prefixLift 1502731
  have htrace : WordTrace (prefixWord ++ tailWord_1502731) baseStart_1502731 baseEnd_1502731 := by
    simpa [prefixWord, tailWord_1502731, baseEnd_1502731] using wordTrace_append hprefix tailTrace_1502731
  have hstable : (prefixWord ++ tailWord_1502731).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502731).length < 2 ^ (prefixWord ++ tailWord_1502731).sum := by decide
  have hdescent : baseEnd_1502731 < baseStart_1502731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502813 : List Nat := [1, 4, 4, 2, 1, 1, 1, 4, 3]
def baseStart_1502813 : Nat := 118140960795 + 1502813 * 2 ^ 59
def prefixEnd_1502813 : Nat := 4983230072969 + 3 ^ 40 * 1502813 * 2
def baseEnd_1502813 : Nat := 342962401255703987078309

theorem tailTrace_1502813 : CollatzResearch.WordTrace tailWord_1502813 prefixEnd_1502813 342962401255703987078309 := by
  unfold tailWord_1502813
  simp only [CollatzResearch.WordTrace]
  refine ⟨54812093104572635871761093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36541395403048423914507395 54812093104572635871761093)
  ·
    refine ⟨10277267457107369225955205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54812093104572635871761093 10277267457107369225955205)
    ·
      refine ⟨1926987648207631729866601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10277267457107369225955205 1926987648207631729866601)
      ·
        refine ⟨1445240736155723797399951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1926987648207631729866601 1445240736155723797399951)
        ·
          refine ⟨2167861104233585696099927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1445240736155723797399951 2167861104233585696099927)
          ·
            refine ⟨3251791656350378544149891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2167861104233585696099927 3251791656350378544149891)
            ·
              refine ⟨4877687484525567816224837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3251791656350378544149891 4877687484525567816224837)
              ·
                refine ⟨914566403348543965542157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4877687484525567816224837 914566403348543965542157)
                ·
                  refine ⟨342962401255703987078309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 914566403348543965542157 342962401255703987078309)
                  ·
                    rfl

theorem cell21_1502813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 4, 3].length) (baseStart_1502813 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1502813 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1502813 prefixEnd_1502813 := by exact prefixLift 1502813
  have htrace : WordTrace (prefixWord ++ tailWord_1502813) baseStart_1502813 baseEnd_1502813 := by
    simpa [prefixWord, tailWord_1502813, baseEnd_1502813] using wordTrace_append hprefix tailTrace_1502813
  have hstable : (prefixWord ++ tailWord_1502813).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502813).length < 2 ^ (prefixWord ++ tailWord_1502813).sum := by decide
  have hdescent : baseEnd_1502813 < baseStart_1502813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502824 : List Nat := [2, 1, 4, 3, 1, 3, 1, 6]
def baseStart_1502824 : Nat := 118140960795 + 1502824 * 2 ^ 59
def prefixEnd_1502824 : Nat := 4983230072969 + 3 ^ 40 * 1502824 * 2
def baseEnd_1502824 : Nat := 114321637201856804131651

theorem tailTrace_1502824 : CollatzResearch.WordTrace tailWord_1502824 prefixEnd_1502824 114321637201856804131651 := by
  unfold tailWord_1502824
  simp only [CollatzResearch.WordTrace]
  refine ⟨27406247153766392375205763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36541662871688523166941017 27406247153766392375205763)
  ·
    refine ⟨41109370730649588562808645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27406247153766392375205763 41109370730649588562808645)
    ·
      refine ⟨7708007011996797855526621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41109370730649588562808645 7708007011996797855526621)
      ·
        refine ⟨2890502629498799195822483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7708007011996797855526621 2890502629498799195822483)
        ·
          refine ⟨4335753944248198793733725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2890502629498799195822483 4335753944248198793733725)
          ·
            refine ⟨1625907729093074547650147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4335753944248198793733725 1625907729093074547650147)
            ·
              refine ⟨2438861593639611821475221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1625907729093074547650147 2438861593639611821475221)
              ·
                refine ⟨114321637201856804131651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2438861593639611821475221 114321637201856804131651)
                ·
                  rfl

theorem cell21_1502824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 6].length) (baseStart_1502824 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1502824 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1502824 prefixEnd_1502824 := by exact prefixLift 1502824
  have htrace : WordTrace (prefixWord ++ tailWord_1502824) baseStart_1502824 baseEnd_1502824 := by
    simpa [prefixWord, tailWord_1502824, baseEnd_1502824] using wordTrace_append hprefix tailTrace_1502824
  have hstable : (prefixWord ++ tailWord_1502824).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502824).length < 2 ^ (prefixWord ++ tailWord_1502824).sum := by decide
  have hdescent : baseEnd_1502824 < baseStart_1502824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502838 : List Nat := [5, 1, 1, 2, 2, 1, 1, 1, 7]
def baseStart_1502838 : Nat := 118140960795 + 1502838 * 2 ^ 59
def prefixEnd_1502838 : Nat := 4983230072969 + 3 ^ 40 * 1502838 * 2
def baseEnd_1502838 : Nat := 342968106596309499161591

theorem tailTrace_1502838 : CollatzResearch.WordTrace tailWord_1502838 prefixEnd_1502838 342968106596309499161591 := by
  unfold tailWord_1502838
  simp only [CollatzResearch.WordTrace]
  refine ⟨3425812808092629071338823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36542003286321376760947445 3425812808092629071338823)
  ·
    refine ⟨5138719212138943607008235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3425812808092629071338823 5138719212138943607008235)
    ·
      refine ⟨7708078818208415410512353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5138719212138943607008235 7708078818208415410512353)
      ·
        refine ⟨5781059113656311557884265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7708078818208415410512353 5781059113656311557884265)
        ·
          refine ⟨4335794335242233668413199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5781059113656311557884265 4335794335242233668413199)
          ·
            refine ⟨6503691502863350502619799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4335794335242233668413199 6503691502863350502619799)
            ·
              refine ⟨9755537254295025753929699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6503691502863350502619799 9755537254295025753929699)
              ·
                refine ⟨14633305881442538630894549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9755537254295025753929699 14633305881442538630894549)
                ·
                  refine ⟨342968106596309499161591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14633305881442538630894549 342968106596309499161591)
                  ·
                    rfl

theorem cell21_1502838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_1502838 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1502838 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1502838 prefixEnd_1502838 := by exact prefixLift 1502838
  have htrace : WordTrace (prefixWord ++ tailWord_1502838) baseStart_1502838 baseEnd_1502838 := by
    simpa [prefixWord, tailWord_1502838, baseEnd_1502838] using wordTrace_append hprefix tailTrace_1502838
  have hstable : (prefixWord ++ tailWord_1502838).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502838).length < 2 ^ (prefixWord ++ tailWord_1502838).sum := by decide
  have hdescent : baseEnd_1502838 < baseStart_1502838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502855 : List Nat := [1, 1, 4, 2, 1, 4, 2, 3, 3]
def baseStart_1502855 : Nat := 118140960795 + 1502855 * 2 ^ 59
def prefixEnd_1502855 : Nat := 4983230072969 + 3 ^ 40 * 1502855 * 2
def baseEnd_1502855 : Nat := 342971986227921247378223

theorem tailTrace_1502855 : CollatzResearch.WordTrace tailWord_1502855 prefixEnd_1502855 342971986227921247378223 := by
  unfold tailWord_1502855
  simp only [CollatzResearch.WordTrace]
  refine ⟨54813624970420477044790019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36542416646946984696526679 54813624970420477044790019)
  ·
    refine ⟨82220437455630715567185029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54813624970420477044790019 82220437455630715567185029)
    ·
      refine ⟨15416332022930759168847193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82220437455630715567185029 15416332022930759168847193)
      ·
        refine ⟨11562249017198069376635395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15416332022930759168847193 11562249017198069376635395)
        ·
          refine ⟨17343373525797104064953093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11562249017198069376635395 17343373525797104064953093)
          ·
            refine ⟨3251882536086957012178705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17343373525797104064953093 3251882536086957012178705)
            ·
              refine ⟨2438911902065217759134029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3251882536086957012178705 2438911902065217759134029)
              ·
                refine ⟨914591963274456659675261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2438911902065217759134029 914591963274456659675261)
                ·
                  refine ⟨342971986227921247378223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 914591963274456659675261 342971986227921247378223)
                  ·
                    rfl

theorem cell21_1502855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 3, 3].length) (baseStart_1502855 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1502855 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1502855 prefixEnd_1502855 := by exact prefixLift 1502855
  have htrace : WordTrace (prefixWord ++ tailWord_1502855) baseStart_1502855 baseEnd_1502855 := by
    simpa [prefixWord, tailWord_1502855, baseEnd_1502855] using wordTrace_append hprefix tailTrace_1502855
  have hstable : (prefixWord ++ tailWord_1502855).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502855).length < 2 ^ (prefixWord ++ tailWord_1502855).sum := by decide
  have hdescent : baseEnd_1502855 < baseStart_1502855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502911 : List Nat := [1, 1, 2, 2, 2, 3, 1, 1, 8]
def baseStart_1502911 : Nat := 118140960795 + 1502911 * 2 ^ 59
def prefixEnd_1502911 : Nat := 4983230072969 + 3 ^ 40 * 1502911 * 2
def baseEnd_1502911 : Nat := 342984766190877594444775

theorem tailTrace_1502911 : CollatzResearch.WordTrace tailWord_1502911 prefixEnd_1502911 342984766190877594444775 := by
  unfold tailWord_1502911
  simp only [CollatzResearch.WordTrace]
  refine ⟨54815667458217598608828587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36543778305478399072552391 54815667458217598608828587)
  ·
    refine ⟨82223501187326397913242881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54815667458217598608828587 82223501187326397913242881)
    ·
      refine ⟨61667625890494798434932161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82223501187326397913242881 61667625890494798434932161)
      ·
        refine ⟨46250719417871098826199121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61667625890494798434932161 46250719417871098826199121)
        ·
          refine ⟨34688039563403324119649341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46250719417871098826199121 34688039563403324119649341)
          ·
            refine ⟨13008014836276246544868503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34688039563403324119649341 13008014836276246544868503)
            ·
              refine ⟨19512022254414369817302755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13008014836276246544868503 19512022254414369817302755)
              ·
                refine ⟨29268033381621554725954133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19512022254414369817302755 29268033381621554725954133)
                ·
                  refine ⟨342984766190877594444775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29268033381621554725954133 342984766190877594444775)
                  ·
                    rfl

theorem cell21_1502911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 8].length) (baseStart_1502911 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1502911 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1502911 prefixEnd_1502911 := by exact prefixLift 1502911
  have htrace : WordTrace (prefixWord ++ tailWord_1502911) baseStart_1502911 baseEnd_1502911 := by
    simpa [prefixWord, tailWord_1502911, baseEnd_1502911] using wordTrace_append hprefix tailTrace_1502911
  have hstable : (prefixWord ++ tailWord_1502911).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502911).length < 2 ^ (prefixWord ++ tailWord_1502911).sum := by decide
  have hdescent : baseEnd_1502911 < baseStart_1502911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502945 : List Nat := [1, 2, 3, 1, 5, 1, 1, 3, 4]
def baseStart_1502945 : Nat := 118140960795 + 1502945 * 2 ^ 59
def prefixEnd_1502945 : Nat := 4983230072969 + 3 ^ 40 * 1502945 * 2
def baseEnd_1502945 : Nat := 342992525454101090878039

theorem tailTrace_1502945 : CollatzResearch.WordTrace tailWord_1502945 prefixEnd_1502945 342992525454101090878039 := by
  unfold tailWord_1502945
  simp only [CollatzResearch.WordTrace]
  refine ⟨54816907540094422415566289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36544605026729614943710859 54816907540094422415566289)
  ·
    refine ⟨41112680655070816811674717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54816907540094422415566289 41112680655070816811674717)
    ·
      refine ⟨15417255245651556304378019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41112680655070816811674717 15417255245651556304378019)
      ·
        refine ⟨23125882868477334456567029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15417255245651556304378019 23125882868477334456567029)
        ·
          refine ⟨2168051518919750105303159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23125882868477334456567029 2168051518919750105303159)
          ·
            refine ⟨3252077278379625157954739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2168051518919750105303159 3252077278379625157954739)
            ·
              refine ⟨4878115917569437736932109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3252077278379625157954739 4878115917569437736932109)
              ·
                refine ⟨1829293469088539151349541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4878115917569437736932109 1829293469088539151349541)
                ·
                  refine ⟨342992525454101090878039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1829293469088539151349541 342992525454101090878039)
                  ·
                    rfl

theorem cell21_1502945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 3, 4].length) (baseStart_1502945 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1502945 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1502945 prefixEnd_1502945 := by exact prefixLift 1502945
  have htrace : WordTrace (prefixWord ++ tailWord_1502945) baseStart_1502945 baseEnd_1502945 := by
    simpa [prefixWord, tailWord_1502945, baseEnd_1502945] using wordTrace_append hprefix tailTrace_1502945
  have hstable : (prefixWord ++ tailWord_1502945).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502945).length < 2 ^ (prefixWord ++ tailWord_1502945).sum := by decide
  have hdescent : baseEnd_1502945 < baseStart_1502945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502987 : List Nat := [1, 1, 1, 1, 5, 1, 2, 3, 6]
def baseStart_1502987 : Nat := 118140960795 + 1502987 * 2 ^ 59
def prefixEnd_1502987 : Nat := 4983230072969 + 3 ^ 40 * 1502987 * 2
def baseEnd_1502987 : Nat := 343002110426318351177953

theorem tailTrace_1502987 : CollatzResearch.WordTrace tailWord_1502987 prefixEnd_1502987 343002110426318351177953 := by
  unfold tailWord_1502987
  simp only [CollatzResearch.WordTrace]
  refine ⟨54818439405942263588595215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36545626270628175725730143 54818439405942263588595215)
  ·
    refine ⟨82227659108913395382892823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54818439405942263588595215 82227659108913395382892823)
    ·
      refine ⟨123341488663370093074339235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82227659108913395382892823 123341488663370093074339235)
      ·
        refine ⟨185012232995055139611508853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123341488663370093074339235 185012232995055139611508853)
        ·
          refine ⟨17344896843286419338578955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 185012232995055139611508853 17344896843286419338578955)
          ·
            refine ⟨26017345264929629007868433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17344896843286419338578955 26017345264929629007868433)
            ·
              refine ⟨19513008948697221755901325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26017345264929629007868433 19513008948697221755901325)
              ·
                refine ⟨7317378355761458158462997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19513008948697221755901325 7317378355761458158462997)
                ·
                  refine ⟨343002110426318351177953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7317378355761458158462997 343002110426318351177953)
                  ·
                    rfl

theorem cell21_1502987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 3, 6].length) (baseStart_1502987 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1502987 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1502987 prefixEnd_1502987 := by exact prefixLift 1502987
  have htrace : WordTrace (prefixWord ++ tailWord_1502987) baseStart_1502987 baseEnd_1502987 := by
    simpa [prefixWord, tailWord_1502987, baseEnd_1502987] using wordTrace_append hprefix tailTrace_1502987
  have hstable : (prefixWord ++ tailWord_1502987).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502987).length < 2 ^ (prefixWord ++ tailWord_1502987).sum := by decide
  have hdescent : baseEnd_1502987 < baseStart_1502987 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503004 : List Nat := [2, 2, 3, 1, 1, 2, 1, 5, 4]
def baseStart_1503004 : Nat := 118140960795 + 1503004 * 2 ^ 59
def prefixEnd_1503004 : Nat := 4983230072969 + 3 ^ 40 * 1503004 * 2
def baseEnd_1503004 : Nat := 343005990057930099394585

theorem tailTrace_1503004 : CollatzResearch.WordTrace tailWord_1503004 prefixEnd_1503004 343005990057930099394585 := by
  unfold tailWord_1503004
  simp only [CollatzResearch.WordTrace]
  refine ⟨27409529723440337745982033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36546039631253783661309377 27409529723440337745982033)
  ·
    refine ⟨20557147292580253309486525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27409529723440337745982033 20557147292580253309486525)
    ·
      refine ⟨7708930234717594991057447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20557147292580253309486525 7708930234717594991057447)
      ·
        refine ⟨11563395352076392486586171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7708930234717594991057447 11563395352076392486586171)
        ·
          refine ⟨17345093028114588729879257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11563395352076392486586171 17345093028114588729879257)
          ·
            refine ⟨13008819771085941547409443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17345093028114588729879257 13008819771085941547409443)
            ·
              refine ⟨19513229656628912321114165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13008819771085941547409443 19513229656628912321114165)
              ·
                refine ⟨1829365280308960530104453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19513229656628912321114165 1829365280308960530104453)
                ·
                  refine ⟨343005990057930099394585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1829365280308960530104453 343005990057930099394585)
                  ·
                    rfl

theorem cell21_1503004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 5, 4].length) (baseStart_1503004 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1503004 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1503004 prefixEnd_1503004 := by exact prefixLift 1503004
  have htrace : WordTrace (prefixWord ++ tailWord_1503004) baseStart_1503004 baseEnd_1503004 := by
    simpa [prefixWord, tailWord_1503004, baseEnd_1503004] using wordTrace_append hprefix tailTrace_1503004
  have hstable : (prefixWord ++ tailWord_1503004).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503004).length < 2 ^ (prefixWord ++ tailWord_1503004).sum := by decide
  have hdescent : baseEnd_1503004 < baseStart_1503004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503038 : List Nat := [4, 2, 1, 2, 2, 3, 1, 2, 4]
def baseStart_1503038 : Nat := 118140960795 + 1503038 * 2 ^ 59
def prefixEnd_1503038 : Nat := 4983230072969 + 3 ^ 40 * 1503038 * 2
def baseEnd_1503038 : Nat := 343013749321153595827849

theorem tailTrace_1503038 : CollatzResearch.WordTrace tailWord_1503038 prefixEnd_1503038 343013749321153595827849 := by
  unfold tailWord_1503038
  simp only [CollatzResearch.WordTrace]
  refine ⟨6852537441094687412337721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36546866352504999532467845 6852537441094687412337721)
  ·
    refine ⟨5139403080821015559253291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6852537441094687412337721 5139403080821015559253291)
    ·
      refine ⟨7709104621231523338879937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5139403080821015559253291 7709104621231523338879937)
      ·
        refine ⟨5781828465923642504159953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7709104621231523338879937 5781828465923642504159953)
        ·
          refine ⟨4336371349442731878119965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5781828465923642504159953 4336371349442731878119965)
          ·
            refine ⟨1626139256041024454294987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4336371349442731878119965 1626139256041024454294987)
            ·
              refine ⟨2439208884061536681442481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1626139256041024454294987 2439208884061536681442481)
              ·
                refine ⟨1829406663046152511081861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2439208884061536681442481 1829406663046152511081861)
                ·
                  refine ⟨343013749321153595827849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1829406663046152511081861 343013749321153595827849)
                  ·
                    rfl

theorem cell21_1503038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_1503038 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1503038 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1503038 prefixEnd_1503038 := by exact prefixLift 1503038
  have htrace : WordTrace (prefixWord ++ tailWord_1503038) baseStart_1503038 baseEnd_1503038 := by
    simpa [prefixWord, tailWord_1503038, baseEnd_1503038] using wordTrace_append hprefix tailTrace_1503038
  have hstable : (prefixWord ++ tailWord_1503038).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503038).length < 2 ^ (prefixWord ++ tailWord_1503038).sum := by decide
  have hdescent : baseEnd_1503038 < baseStart_1503038 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503049 : List Nat := [1, 2, 1, 1, 2, 4, 4, 1, 5]
def baseStart_1503049 : Nat := 118140960795 + 1503049 * 2 ^ 59
def prefixEnd_1503049 : Nat := 4983230072969 + 3 ^ 40 * 1503049 * 2
def baseEnd_1503049 : Nat := 343016259671020021144493

theorem tailTrace_1503049 : CollatzResearch.WordTrace tailWord_1503049 prefixEnd_1503049 343016259671020021144493 := by
  unfold tailWord_1503049
  simp only [CollatzResearch.WordTrace]
  refine ⟨54820700731717648177352201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36547133821145098784901467 54820700731717648177352201)
  ·
    refine ⟨41115525548788236133014151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54820700731717648177352201 41115525548788236133014151)
    ·
      refine ⟨61673288323182354199521227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41115525548788236133014151 61673288323182354199521227)
      ·
        refine ⟨92509932484773531299281841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61673288323182354199521227 92509932484773531299281841)
        ·
          refine ⟨69382449363580148474461381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92509932484773531299281841 69382449363580148474461381)
          ·
            refine ⟨13009209255671277838961509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69382449363580148474461381 13009209255671277838961509)
            ·
              refine ⟨2439226735438364594805283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13009209255671277838961509 2439226735438364594805283)
              ·
                refine ⟨3658840103157546892207925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2439226735438364594805283 3658840103157546892207925)
                ·
                  refine ⟨343016259671020021144493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3658840103157546892207925 343016259671020021144493)
                  ·
                    rfl

theorem cell21_1503049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 1, 5].length) (baseStart_1503049 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1503049 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1503049 prefixEnd_1503049 := by exact prefixLift 1503049
  have htrace : WordTrace (prefixWord ++ tailWord_1503049) baseStart_1503049 baseEnd_1503049 := by
    simpa [prefixWord, tailWord_1503049, baseEnd_1503049] using wordTrace_append hprefix tailTrace_1503049
  have hstable : (prefixWord ++ tailWord_1503049).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503049).length < 2 ^ (prefixWord ++ tailWord_1503049).sum := by decide
  have hdescent : baseEnd_1503049 < baseStart_1503049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503111 : List Nat := [1, 1, 4, 2, 4, 1, 2, 6]
def baseStart_1503111 : Nat := 118140960795 + 1503111 * 2 ^ 59
def prefixEnd_1503111 : Nat := 4983230072969 + 3 ^ 40 * 1503111 * 2
def baseEnd_1503111 : Nat := 114343469638573897037011

theorem tailTrace_1503111 : CollatzResearch.WordTrace tailWord_1503111 prefixEnd_1503111 114343469638573897037011 := by
  unfold tailWord_1503111
  simp only [CollatzResearch.WordTrace]
  refine ⟨54822962057493032766109187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36548641371662021844072791 54822962057493032766109187)
  ·
    refine ⟨82234443086239549149163781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54822962057493032766109187 82234443086239549149163781)
    ·
      refine ⟨15418958078669915465468209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82234443086239549149163781 15418958078669915465468209)
      ·
        refine ⟨11564218559002436599101157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15418958078669915465468209 11564218559002436599101157)
        ·
          refine ⟨2168290979812956862331467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11564218559002436599101157 2168290979812956862331467)
          ·
            refine ⟨3252436469719435293497201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2168290979812956862331467 3252436469719435293497201)
            ·
              refine ⟨2439327352289576470122901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3252436469719435293497201 2439327352289576470122901)
              ·
                refine ⟨114343469638573897037011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2439327352289576470122901 114343469638573897037011)
                ·
                  rfl

theorem cell21_1503111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 6].length) (baseStart_1503111 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1503111 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1503111 prefixEnd_1503111 := by exact prefixLift 1503111
  have htrace : WordTrace (prefixWord ++ tailWord_1503111) baseStart_1503111 baseEnd_1503111 := by
    simpa [prefixWord, tailWord_1503111, baseEnd_1503111] using wordTrace_append hprefix tailTrace_1503111
  have hstable : (prefixWord ++ tailWord_1503111).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503111).length < 2 ^ (prefixWord ++ tailWord_1503111).sum := by decide
  have hdescent : baseEnd_1503111 < baseStart_1503111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503184 : List Nat := [2, 1, 1, 1, 1, 2, 5, 1, 7]
def baseStart_1503184 : Nat := 118140960795 + 1503184 * 2 ^ 59
def prefixEnd_1503184 : Nat := 4983230072969 + 3 ^ 40 * 1503184 * 2
def baseEnd_1503184 : Nat := 343047068510289786394217

theorem tailTrace_1503184 : CollatzResearch.WordTrace tailWord_1503184 prefixEnd_1503184 343047068510289786394217 := by
  unfold tailWord_1503184
  simp only [CollatzResearch.WordTrace]
  refine ⟨27412812293114283116758303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36550416390819044155677737 27412812293114283116758303)
  ·
    refine ⟨41119218439671424675137455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27412812293114283116758303 41119218439671424675137455)
    ·
      refine ⟨61678827659507137012706183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41119218439671424675137455 61678827659507137012706183)
      ·
        refine ⟨92518241489260705519059275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61678827659507137012706183 92518241489260705519059275)
        ·
          refine ⟨138777362233891058278588913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92518241489260705519059275 138777362233891058278588913)
          ·
            refine ⟨104083021675418293708941685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138777362233891058278588913 104083021675418293708941685)
            ·
              refine ⟨9757783282070465035213283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 104083021675418293708941685 9757783282070465035213283)
              ·
                refine ⟨14636674923105697552819925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9757783282070465035213283 14636674923105697552819925)
                ·
                  refine ⟨343047068510289786394217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14636674923105697552819925 343047068510289786394217)
                  ·
                    rfl

theorem cell21_1503184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 7].length) (baseStart_1503184 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1503184 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1503184 prefixEnd_1503184 := by exact prefixLift 1503184
  have htrace : WordTrace (prefixWord ++ tailWord_1503184) baseStart_1503184 baseEnd_1503184 := by
    simpa [prefixWord, tailWord_1503184, baseEnd_1503184] using wordTrace_append hprefix tailTrace_1503184
  have hstable : (prefixWord ++ tailWord_1503184).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503184).length < 2 ^ (prefixWord ++ tailWord_1503184).sum := by decide
  have hdescent : baseEnd_1503184 < baseStart_1503184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503215 : List Nat := [1, 1, 2, 1, 4, 2, 3, 1, 6]
def baseStart_1503215 : Nat := 118140960795 + 1503215 * 2 ^ 59
def prefixEnd_1503215 : Nat := 4983230072969 + 3 ^ 40 * 1503215 * 2
def baseEnd_1503215 : Nat := 343054143132640621377487

theorem tailTrace_1503215 : CollatzResearch.WordTrace tailWord_1503215 prefixEnd_1503215 343054143132640621377487 := by
  unfold tailWord_1503215
  simp only [CollatzResearch.WordTrace]
  refine ⟨54826755249116258527895099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36551170166077505685263399 54826755249116258527895099)
  ·
    refine ⟨82240132873674387791842649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54826755249116258527895099 82240132873674387791842649)
    ·
      refine ⟨61680099655255790843881987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82240132873674387791842649 61680099655255790843881987)
      ·
        refine ⟨92520149482883686265822981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61680099655255790843881987 92520149482883686265822981)
        ·
          refine ⟨17347528028040691174841809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92520149482883686265822981 17347528028040691174841809)
          ·
            refine ⟨13010646021030518381131357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17347528028040691174841809 13010646021030518381131357)
            ·
              refine ⟨4878992257886444392924259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13010646021030518381131357 4878992257886444392924259)
              ·
                refine ⟨7318488386829666589386389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4878992257886444392924259 7318488386829666589386389)
                ·
                  refine ⟨343054143132640621377487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7318488386829666589386389 343054143132640621377487)
                  ·
                    rfl

theorem cell21_1503215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 1, 6].length) (baseStart_1503215 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1503215 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1503215 prefixEnd_1503215 := by exact prefixLift 1503215
  have htrace : WordTrace (prefixWord ++ tailWord_1503215) baseStart_1503215 baseEnd_1503215 := by
    simpa [prefixWord, tailWord_1503215, baseEnd_1503215] using wordTrace_append hprefix tailTrace_1503215
  have hstable : (prefixWord ++ tailWord_1503215).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503215).length < 2 ^ (prefixWord ++ tailWord_1503215).sum := by decide
  have hdescent : baseEnd_1503215 < baseStart_1503215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503238 : List Nat := [6, 2, 1, 2, 1, 1, 1, 7]
def baseStart_1503238 : Nat := 118140960795 + 1503238 * 2 ^ 59
def prefixEnd_1503238 : Nat := 4983230072969 + 3 ^ 40 * 1503238 * 2
def baseEnd_1503238 : Nat := 114353130681999230831369

theorem tailTrace_1503238 : CollatzResearch.WordTrace tailWord_1503238 prefixEnd_1503238 114353130681999230831369 := by
  unfold tailWord_1503238
  simp only [CollatzResearch.WordTrace]
  refine ⟨1713362316501029170499449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 36551729418688622303988245 1713362316501029170499449)
  ·
    refine ⟨1285021737375771877874587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1713362316501029170499449 1285021737375771877874587)
    ·
      refine ⟨1927532606063657816811881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1285021737375771877874587 1927532606063657816811881)
      ·
        refine ⟨1445649454547743362608911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1927532606063657816811881 1445649454547743362608911)
        ·
          refine ⟨2168474181821615043913367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1445649454547743362608911 2168474181821615043913367)
          ·
            refine ⟨3252711272732422565870051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2168474181821615043913367 3252711272732422565870051)
            ·
              refine ⟨4879066909098633848805077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3252711272732422565870051 4879066909098633848805077)
              ·
                refine ⟨114353130681999230831369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4879066909098633848805077 114353130681999230831369)
                ·
                  rfl

theorem cell21_1503238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_1503238 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1503238 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1503238 prefixEnd_1503238 := by exact prefixLift 1503238
  have htrace : WordTrace (prefixWord ++ tailWord_1503238) baseStart_1503238 baseEnd_1503238 := by
    simpa [prefixWord, tailWord_1503238, baseEnd_1503238] using wordTrace_append hprefix tailTrace_1503238
  have hstable : (prefixWord ++ tailWord_1503238).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503238).length < 2 ^ (prefixWord ++ tailWord_1503238).sum := by decide
  have hdescent : baseEnd_1503238 < baseStart_1503238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503246 : List Nat := [4, 1, 1, 2, 2, 1, 3, 7]
def baseStart_1503246 : Nat := 118140960795 + 1503246 * 2 ^ 59
def prefixEnd_1503246 : Nat := 4983230072969 + 3 ^ 40 * 1503246 * 2
def baseEnd_1503246 : Nat := 114353739251663818786919

theorem tailTrace_1503246 : CollatzResearch.WordTrace tailWord_1503246 prefixEnd_1503246 114353739251663818786919 := by
  unfold tailWord_1503246
  simp only [CollatzResearch.WordTrace]
  refine ⟨6853485739000493852784199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36551923941335967214849061 6853485739000493852784199)
  ·
    refine ⟨10280228608500740779176299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6853485739000493852784199 10280228608500740779176299)
    ·
      refine ⟨15420342912751111168764449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10280228608500740779176299 15420342912751111168764449)
      ·
        refine ⟨11565257184563333376573337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15420342912751111168764449 11565257184563333376573337)
        ·
          refine ⟨8673942888422500032430003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11565257184563333376573337 8673942888422500032430003)
          ·
            refine ⟨13010914332633750048645005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8673942888422500032430003 13010914332633750048645005)
            ·
              refine ⟨4879092874737656268241877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13010914332633750048645005 4879092874737656268241877)
              ·
                refine ⟨114353739251663818786919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4879092874737656268241877 114353739251663818786919)
                ·
                  rfl

theorem cell21_1503246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 7].length) (baseStart_1503246 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1503246 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1503246 prefixEnd_1503246 := by exact prefixLift 1503246
  have htrace : WordTrace (prefixWord ++ tailWord_1503246) baseStart_1503246 baseEnd_1503246 := by
    simpa [prefixWord, tailWord_1503246, baseEnd_1503246] using wordTrace_append hprefix tailTrace_1503246
  have hstable : (prefixWord ++ tailWord_1503246).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503246).length < 2 ^ (prefixWord ++ tailWord_1503246).sum := by decide
  have hdescent : baseEnd_1503246 < baseStart_1503246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503291 : List Nat := [1, 1, 1, 1, 1, 2, 1, 9, 4]
def baseStart_1503291 : Nat := 118140960795 + 1503291 * 2 ^ 59
def prefixEnd_1503291 : Nat := 4983230072969 + 3 ^ 40 * 1503291 * 2
def baseEnd_1503291 : Nat := 343071487368081378110665

theorem tailTrace_1503291 : CollatzResearch.WordTrace tailWord_1503291 prefixEnd_1503291 343071487368081378110665 := by
  unfold tailWord_1503291
  simp only [CollatzResearch.WordTrace]
  refine ⟨54829527196840923507661727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36553018131227282338441151 54829527196840923507661727)
  ·
    refine ⟨82244290795261385261492591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54829527196840923507661727 82244290795261385261492591)
    ·
      refine ⟨123366436192892077892238887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82244290795261385261492591 123366436192892077892238887)
      ·
        refine ⟨185049654289338116838358331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123366436192892077892238887 185049654289338116838358331)
        ·
          refine ⟨277574481434007175257537497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185049654289338116838358331 277574481434007175257537497)
          ·
            refine ⟨208180861075505381443153123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 277574481434007175257537497 208180861075505381443153123)
            ·
              refine ⟨312271291613258072164729685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208180861075505381443153123 312271291613258072164729685)
              ·
                refine ⟨1829714599296434016590213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 312271291613258072164729685 1829714599296434016590213)
                ·
                  refine ⟨343071487368081378110665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1829714599296434016590213 343071487368081378110665)
                  ·
                    rfl

theorem cell21_1503291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 9, 4].length) (baseStart_1503291 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1503291 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1503291 prefixEnd_1503291 := by exact prefixLift 1503291
  have htrace : WordTrace (prefixWord ++ tailWord_1503291) baseStart_1503291 baseEnd_1503291 := by
    simpa [prefixWord, tailWord_1503291, baseEnd_1503291] using wordTrace_append hprefix tailTrace_1503291
  have hstable : (prefixWord ++ tailWord_1503291).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503291).length < 2 ^ (prefixWord ++ tailWord_1503291).sum := by decide
  have hdescent : baseEnd_1503291 < baseStart_1503291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503305 : List Nat := [1, 2, 1, 1, 2, 2, 3, 9]
def baseStart_1503305 : Nat := 118140960795 + 1503305 * 2 ^ 59
def prefixEnd_1503305 : Nat := 4983230072969 + 3 ^ 40 * 1503305 * 2
def baseEnd_1503305 : Nat := 114358227452940154959101

theorem tailTrace_1503305 : CollatzResearch.WordTrace tailWord_1503305 prefixEnd_1503305 114358227452940154959101 := by
  unfold tailWord_1503305
  simp only [CollatzResearch.WordTrace]
  refine ⟨54830037818790203898671369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36553358545860135932447579 54830037818790203898671369)
  ·
    refine ⟨41122528364092652924003527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54830037818790203898671369 41122528364092652924003527)
    ·
      refine ⟨61683792546138979386005291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41122528364092652924003527 61683792546138979386005291)
      ·
        refine ⟨92525688819208469079007937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61683792546138979386005291 92525688819208469079007937)
        ·
          refine ⟨69394266614406351809255953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92525688819208469079007937 69394266614406351809255953)
          ·
            refine ⟨52045699960804763856941965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69394266614406351809255953 52045699960804763856941965)
            ·
              refine ⟨19517137485301786446353237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52045699960804763856941965 19517137485301786446353237)
              ·
                refine ⟨114358227452940154959101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19517137485301786446353237 114358227452940154959101)
                ·
                  rfl

theorem cell21_1503305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 9].length) (baseStart_1503305 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1503305 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1503305 prefixEnd_1503305 := by exact prefixLift 1503305
  have htrace : WordTrace (prefixWord ++ tailWord_1503305) baseStart_1503305 baseEnd_1503305 := by
    simpa [prefixWord, tailWord_1503305, baseEnd_1503305] using wordTrace_append hprefix tailTrace_1503305
  have hstable : (prefixWord ++ tailWord_1503305).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503305).length < 2 ^ (prefixWord ++ tailWord_1503305).sum := by decide
  have hdescent : baseEnd_1503305 < baseStart_1503305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503325 : List Nat := [1, 4, 4, 1, 1, 1, 1, 4, 4]
def baseStart_1503325 : Nat := 118140960795 + 1503325 * 2 ^ 59
def prefixEnd_1503325 : Nat := 4983230072969 + 3 ^ 40 * 1503325 * 2
def baseEnd_1503325 : Nat := 343079246631304874543929

theorem tailTrace_1503325 : CollatzResearch.WordTrace tailWord_1503325 prefixEnd_1503325 343079246631304874543929 := by
  unfold tailWord_1503325
  simp only [CollatzResearch.WordTrace]
  refine ⟨54830767278717747314399429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36553844852478498209599619 54830767278717747314399429)
  ·
    refine ⟨10280768864759577621449893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54830767278717747314399429 10280768864759577621449893)
    ·
      refine ⟨1927644162142420804021855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10280768864759577621449893 1927644162142420804021855)
      ·
        refine ⟨2891466243213631206032783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1927644162142420804021855 2891466243213631206032783)
        ·
          refine ⟨4337199364820446809049175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2891466243213631206032783 4337199364820446809049175)
          ·
            refine ⟨6505799047230670213573763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4337199364820446809049175 6505799047230670213573763)
            ·
              refine ⟨9758698570846005320360645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6505799047230670213573763 9758698570846005320360645)
              ·
                refine ⟨1829755982033625997567621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9758698570846005320360645 1829755982033625997567621)
                ·
                  refine ⟨343079246631304874543929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1829755982033625997567621 343079246631304874543929)
                  ·
                    rfl

theorem cell21_1503325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 4, 4].length) (baseStart_1503325 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1503325 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1503325 prefixEnd_1503325 := by exact prefixLift 1503325
  have htrace : WordTrace (prefixWord ++ tailWord_1503325) baseStart_1503325 baseEnd_1503325 := by
    simpa [prefixWord, tailWord_1503325, baseEnd_1503325] using wordTrace_append hprefix tailTrace_1503325
  have hstable : (prefixWord ++ tailWord_1503325).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503325).length < 2 ^ (prefixWord ++ tailWord_1503325).sum := by decide
  have hdescent : baseEnd_1503325 < baseStart_1503325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503353 : List Nat := [1, 2, 1, 3, 4, 2, 1, 2, 5]
def baseStart_1503353 : Nat := 118140960795 + 1503353 * 2 ^ 59
def prefixEnd_1503353 : Nat := 4983230072969 + 3 ^ 40 * 1503353 * 2
def baseEnd_1503353 : Nat := 343085636612783048077205

theorem tailTrace_1503353 : CollatzResearch.WordTrace tailWord_1503353 prefixEnd_1503353 343085636612783048077205 := by
  unfold tailWord_1503353
  simp only [CollatzResearch.WordTrace]
  refine ⟨54831788522616308096418713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36554525681744205397612475 54831788522616308096418713)
  ·
    refine ⟨41123841391962231072314035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54831788522616308096418713 41123841391962231072314035)
    ·
      refine ⟨61685762087943346608471053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41123841391962231072314035 61685762087943346608471053)
      ·
        refine ⟨23132160782978754978176645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61685762087943346608471053 23132160782978754978176645)
        ·
          refine ⟨4337280146808516558408121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23132160782978754978176645 4337280146808516558408121)
          ·
            refine ⟨3252960110106387418806091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4337280146808516558408121 3252960110106387418806091)
            ·
              refine ⟨4879440165159581128209137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3252960110106387418806091 4879440165159581128209137)
              ·
                refine ⟨3659580123869685846156853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4879440165159581128209137 3659580123869685846156853)
                ·
                  refine ⟨343085636612783048077205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3659580123869685846156853 343085636612783048077205)
                  ·
                    rfl

theorem cell21_1503353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 2, 5].length) (baseStart_1503353 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1503353 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1503353 prefixEnd_1503353 := by exact prefixLift 1503353
  have htrace : WordTrace (prefixWord ++ tailWord_1503353) baseStart_1503353 baseEnd_1503353 := by
    simpa [prefixWord, tailWord_1503353, baseEnd_1503353] using wordTrace_append hprefix tailTrace_1503353
  have hstable : (prefixWord ++ tailWord_1503353).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503353).length < 2 ^ (prefixWord ++ tailWord_1503353).sum := by decide
  have hdescent : baseEnd_1503353 < baseStart_1503353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503370 : List Nat := [3, 1, 2, 3, 1, 2, 1, 5, 3]
def baseStart_1503370 : Nat := 118140960795 + 1503370 * 2 ^ 59
def prefixEnd_1503370 : Nat := 4983230072969 + 3 ^ 40 * 1503370 * 2
def baseEnd_1503370 : Nat := 343089516244394796293837

theorem tailTrace_1503370 : CollatzResearch.WordTrace tailWord_1503370 prefixEnd_1503370 343089516244394796293837 := by
  unfold tailWord_1503370
  simp only [CollatzResearch.WordTrace]
  refine ⟨13708102140888679999946891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36554939042369813333191709 13708102140888679999946891)
  ·
    refine ⟨20562153211333019999920337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13708102140888679999946891 20562153211333019999920337)
    ·
      refine ⟨15421614908499764999940253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20562153211333019999920337 15421614908499764999940253)
      ·
        refine ⟨5783105590687411874977595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15421614908499764999940253 5783105590687411874977595)
        ·
          refine ⟨8674658386031117812466393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5783105590687411874977595 8674658386031117812466393)
          ·
            refine ⟨6505993789523338359349795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8674658386031117812466393 6505993789523338359349795)
            ·
              refine ⟨9758990684285007539024693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6505993789523338359349795 9758990684285007539024693)
              ·
                refine ⟨914905376651719456783565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9758990684285007539024693 914905376651719456783565)
                ·
                  refine ⟨343089516244394796293837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 914905376651719456783565 343089516244394796293837)
                  ·
                    rfl

theorem cell21_1503370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 5, 3].length) (baseStart_1503370 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1503370 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1503370 prefixEnd_1503370 := by exact prefixLift 1503370
  have htrace : WordTrace (prefixWord ++ tailWord_1503370) baseStart_1503370 baseEnd_1503370 := by
    simpa [prefixWord, tailWord_1503370, baseEnd_1503370] using wordTrace_append hprefix tailTrace_1503370
  have hstable : (prefixWord ++ tailWord_1503370).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503370).length < 2 ^ (prefixWord ++ tailWord_1503370).sum := by decide
  have hdescent : baseEnd_1503370 < baseStart_1503370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503381 : List Nat := [1, 3, 2, 1, 1, 1, 12]
def baseStart_1503381 : Nat := 118140960795 + 1503381 * 2 ^ 59
def prefixEnd_1503381 : Nat := 4983230072969 + 3 ^ 40 * 1503381 * 2
def baseEnd_1503381 : Nat := 38121336288251246845609

theorem tailTrace_1503381 : CollatzResearch.WordTrace tailWord_1503381 prefixEnd_1503381 38121336288251246845609 := by
  unfold tailWord_1503381
  simp only [CollatzResearch.WordTrace]
  refine ⟨54832809766514868878437997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36555206511009912585625331 54832809766514868878437997)
  ·
    refine ⟨20562303662443075829414249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54832809766514868878437997 20562303662443075829414249)
    ·
      refine ⟨15421727746832306872060687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20562303662443075829414249 15421727746832306872060687)
      ·
        refine ⟨23132591620248460308091031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15421727746832306872060687 23132591620248460308091031)
        ·
          refine ⟨34698887430372690462136547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23132591620248460308091031 34698887430372690462136547)
          ·
            refine ⟨52048331145559035693204821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34698887430372690462136547 52048331145559035693204821)
            ·
              refine ⟨38121336288251246845609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 52048331145559035693204821 38121336288251246845609)
              ·
                rfl

theorem cell21_1503381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 12].length) (baseStart_1503381 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1503381 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1503381 prefixEnd_1503381 := by exact prefixLift 1503381
  have htrace : WordTrace (prefixWord ++ tailWord_1503381) baseStart_1503381 baseEnd_1503381 := by
    simpa [prefixWord, tailWord_1503381, baseEnd_1503381] using wordTrace_append hprefix tailTrace_1503381
  have hstable : (prefixWord ++ tailWord_1503381).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503381).length < 2 ^ (prefixWord ++ tailWord_1503381).sum := by decide
  have hdescent : baseEnd_1503381 < baseStart_1503381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503384 : List Nat := [2, 1, 2, 4, 3, 1, 1, 1, 6]
def baseStart_1503384 : Nat := 118140960795 + 1503384 * 2 ^ 59
def prefixEnd_1503384 : Nat := 4983230072969 + 3 ^ 40 * 1503384 * 2
def baseEnd_1503384 : Nat := 343092711235133883060475

theorem tailTrace_1503384 : CollatzResearch.WordTrace tailWord_1503384 prefixEnd_1503384 343092711235133883060475 := by
  unfold tailWord_1503384
  simp only [CollatzResearch.WordTrace]
  refine ⟨27416459592752000195398603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36555279457002666927198137 27416459592752000195398603)
  ·
    refine ⟨41124689389128000293097905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27416459592752000195398603 41124689389128000293097905)
    ·
      refine ⟨30843517041846000219823429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41124689389128000293097905 30843517041846000219823429)
      ·
        refine ⟨5783159445346125041216893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30843517041846000219823429 5783159445346125041216893)
        ·
          refine ⟨2168684792004796890456335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5783159445346125041216893 2168684792004796890456335)
          ·
            refine ⟨3253027188007195335684503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2168684792004796890456335 3253027188007195335684503)
            ·
              refine ⟨4879540782010793003526755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3253027188007195335684503 4879540782010793003526755)
              ·
                refine ⟨7319311173016189505290133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4879540782010793003526755 7319311173016189505290133)
                ·
                  refine ⟨343092711235133883060475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7319311173016189505290133 343092711235133883060475)
                  ·
                    rfl

theorem cell21_1503384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 1, 6].length) (baseStart_1503384 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1503384 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1503384 prefixEnd_1503384 := by exact prefixLift 1503384
  have htrace : WordTrace (prefixWord ++ tailWord_1503384) baseStart_1503384 baseEnd_1503384 := by
    simpa [prefixWord, tailWord_1503384, baseEnd_1503384] using wordTrace_append hprefix tailTrace_1503384
  have hstable : (prefixWord ++ tailWord_1503384).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503384).length < 2 ^ (prefixWord ++ tailWord_1503384).sum := by decide
  have hdescent : baseEnd_1503384 < baseStart_1503384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503415 : List Nat := [1, 1, 3, 1, 4, 4, 2, 5]
def baseStart_1503415 : Nat := 118140960795 + 1503415 * 2 ^ 59
def prefixEnd_1503415 : Nat := 4983230072969 + 3 ^ 40 * 1503415 * 2
def baseEnd_1503415 : Nat := 114366595285828239347915

theorem tailTrace_1503415 : CollatzResearch.WordTrace tailWord_1503415 prefixEnd_1503415 114366595285828239347915 := by
  unfold tailWord_1503415
  simp only [CollatzResearch.WordTrace]
  refine ⟨54834049848391692685175699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36556033232261128456783799 54834049848391692685175699)
  ·
    refine ⟨82251074772587539027763549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54834049848391692685175699 82251074772587539027763549)
    ·
      refine ⟨30844153039720327135411331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82251074772587539027763549 30844153039720327135411331)
      ·
        refine ⟨46266229559580490703116997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30844153039720327135411331 46266229559580490703116997)
        ·
          refine ⟨8674918042421342006834437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46266229559580490703116997 8674918042421342006834437)
          ·
            refine ⟨1626547132954001626281457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8674918042421342006834437 1626547132954001626281457)
            ·
              refine ⟨1219910349715501219711093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1626547132954001626281457 1219910349715501219711093)
              ·
                refine ⟨114366595285828239347915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1219910349715501219711093 114366595285828239347915)
                ·
                  rfl

theorem cell21_1503415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 2, 5].length) (baseStart_1503415 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1503415 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1503415 prefixEnd_1503415 := by exact prefixLift 1503415
  have htrace : WordTrace (prefixWord ++ tailWord_1503415) baseStart_1503415 baseEnd_1503415 := by
    simpa [prefixWord, tailWord_1503415, baseEnd_1503415] using wordTrace_append hprefix tailTrace_1503415
  have hstable : (prefixWord ++ tailWord_1503415).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503415).length < 2 ^ (prefixWord ++ tailWord_1503415).sum := by decide
  have hdescent : baseEnd_1503415 < baseStart_1503415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503452 : List Nat := [2, 2, 5, 2, 2, 1, 2, 1, 4]
def baseStart_1503452 : Nat := 118140960795 + 1503452 * 2 ^ 59
def prefixEnd_1503452 : Nat := 4983230072969 + 3 ^ 40 * 1503452 * 2
def baseEnd_1503452 : Nat := 343108229761580875927003

theorem tailTrace_1503452 : CollatzResearch.WordTrace tailWord_1503452 prefixEnd_1503452 343108229761580875927003 := by
  unfold tailWord_1503452
  simp only [CollatzResearch.WordTrace]
  refine ⟨27417699674628824002136305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36556932899505098669515073 27417699674628824002136305)
  ·
    refine ⟨20563274755971618001602229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27417699674628824002136305 20563274755971618001602229)
    ·
      refine ⟨1927807008372339187650209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20563274755971618001602229 1927807008372339187650209)
      ·
        refine ⟨1445855256279254390737657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1927807008372339187650209 1445855256279254390737657)
        ·
          refine ⟨1084391442209440793053243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1445855256279254390737657 1084391442209440793053243)
          ·
            refine ⟨1626587163314161189579865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1084391442209440793053243 1626587163314161189579865)
            ·
              refine ⟨1219940372485620892184899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1626587163314161189579865 1219940372485620892184899)
              ·
                refine ⟨1829910558728431338277349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1219940372485620892184899 1829910558728431338277349)
                ·
                  refine ⟨343108229761580875927003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1829910558728431338277349 343108229761580875927003)
                  ·
                    rfl

theorem cell21_1503452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 2, 1, 4].length) (baseStart_1503452 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1503452 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1503452 prefixEnd_1503452 := by exact prefixLift 1503452
  have htrace : WordTrace (prefixWord ++ tailWord_1503452) baseStart_1503452 baseEnd_1503452 := by
    simpa [prefixWord, tailWord_1503452, baseEnd_1503452] using wordTrace_append hprefix tailTrace_1503452
  have hstable : (prefixWord ++ tailWord_1503452).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503452).length < 2 ^ (prefixWord ++ tailWord_1503452).sum := by decide
  have hdescent : baseEnd_1503452 < baseStart_1503452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503474 : List Nat := [3, 2, 1, 3, 2, 1, 2, 7]
def baseStart_1503474 : Nat := 118140960795 + 1503474 * 2 ^ 59
def prefixEnd_1503474 : Nat := 4983230072969 + 3 ^ 40 * 1503474 * 2
def baseEnd_1503474 : Nat := 114371083487104575520097

theorem tailTrace_1503474 : CollatzResearch.WordTrace tailWord_1503474 prefixEnd_1503474 114371083487104575520097 := by
  unfold tailWord_1503474
  simp only [CollatzResearch.WordTrace]
  refine ⟨13709050438794486440393369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36557467836785297174382317 13709050438794486440393369)
  ·
    refine ⟨10281787829095864830295027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13709050438794486440393369 10281787829095864830295027)
    ·
      refine ⟨15422681743643797245442541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10281787829095864830295027 15422681743643797245442541)
      ·
        refine ⟨5783505653866423967040953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15422681743643797245442541 5783505653866423967040953)
        ·
          refine ⟨4337629240399817975280715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5783505653866423967040953 4337629240399817975280715)
          ·
            refine ⟨6506443860599726962921073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4337629240399817975280715 6506443860599726962921073)
            ·
              refine ⟨4879832895449795222190805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6506443860599726962921073 4879832895449795222190805)
              ·
                refine ⟨114371083487104575520097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4879832895449795222190805 114371083487104575520097)
                ·
                  rfl

theorem cell21_1503474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 7].length) (baseStart_1503474 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1503474 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1503474 prefixEnd_1503474 := by exact prefixLift 1503474
  have htrace : WordTrace (prefixWord ++ tailWord_1503474) baseStart_1503474 baseEnd_1503474 := by
    simpa [prefixWord, tailWord_1503474, baseEnd_1503474] using wordTrace_append hprefix tailTrace_1503474
  have hstable : (prefixWord ++ tailWord_1503474).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503474).length < 2 ^ (prefixWord ++ tailWord_1503474).sum := by decide
  have hdescent : baseEnd_1503474 < baseStart_1503474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503550 : List Nat := [4, 2, 1, 2, 1, 3, 8]
def baseStart_1503550 : Nat := 118140960795 + 1503550 * 2 ^ 59
def prefixEnd_1503550 : Nat := 4983230072969 + 3 ^ 40 * 1503550 * 2
def baseEnd_1503550 : Nat := 38125621632972720365941

theorem tailTrace_1503550 : CollatzResearch.WordTrace tailWord_1503550 prefixEnd_1503550 38125621632972720365941 := by
  unfold tailWord_1503550
  simp only [CollatzResearch.WordTrace]
  refine ⟨6854871712862826342667513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36559315801935073827560069 6854871712862826342667513)
  ·
    refine ⟨5141153784647119757000635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6854871712862826342667513 5141153784647119757000635)
    ·
      refine ⟨7711730676970679635500953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5141153784647119757000635 7711730676970679635500953)
      ·
        refine ⟨5783798007728009726625715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7711730676970679635500953 5783798007728009726625715)
        ·
          refine ⟨8675697011592014589938573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5783798007728009726625715 8675697011592014589938573)
          ·
            refine ⟨3253386379347005471226965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8675697011592014589938573 3253386379347005471226965)
            ·
              refine ⟨38125621632972720365941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3253386379347005471226965 38125621632972720365941)
              ·
                rfl

theorem cell21_1503550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 8].length) (baseStart_1503550 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1503550 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1503550 prefixEnd_1503550 := by exact prefixLift 1503550
  have htrace : WordTrace (prefixWord ++ tailWord_1503550) baseStart_1503550 baseEnd_1503550 := by
    simpa [prefixWord, tailWord_1503550, baseEnd_1503550] using wordTrace_append hprefix tailTrace_1503550
  have hstable : (prefixWord ++ tailWord_1503550).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503550).length < 2 ^ (prefixWord ++ tailWord_1503550).sum := by decide
  have hdescent : baseEnd_1503550 < baseStart_1503550 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503584 : List Nat := [2, 1, 1, 3, 6, 1, 2, 5]
def baseStart_1503584 : Nat := 118140960795 + 1503584 * 2 ^ 59
def prefixEnd_1503584 : Nat := 4983230072969 + 3 ^ 40 * 1503584 * 2
def baseEnd_1503584 : Nat := 114379451319992659908911

theorem tailTrace_1503584 : CollatzResearch.WordTrace tailWord_1503584 prefixEnd_1503584 114379451319992659908911 := by
  unfold tailWord_1503584
  simp only [CollatzResearch.WordTrace]
  refine ⟨27420106892389717274038903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36560142523186289698718537 27420106892389717274038903)
  ·
    refine ⟨41130160338584575911058355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27420106892389717274038903 41130160338584575911058355)
    ·
      refine ⟨61695240507876863866587533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41130160338584575911058355 61695240507876863866587533)
      ·
        refine ⟨23135715190453823949970325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61695240507876863866587533 23135715190453823949970325)
        ·
          refine ⟨1084486649552522997654859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 23135715190453823949970325 1084486649552522997654859)
          ·
            refine ⟨1626729974328784496482289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1084486649552522997654859 1626729974328784496482289)
            ·
              refine ⟨1220047480746588372361717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1626729974328784496482289 1220047480746588372361717)
              ·
                refine ⟨114379451319992659908911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1220047480746588372361717 114379451319992659908911)
                ·
                  rfl

theorem cell21_1503584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 2, 5].length) (baseStart_1503584 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1503584 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1503584 prefixEnd_1503584 := by exact prefixLift 1503584
  have htrace : WordTrace (prefixWord ++ tailWord_1503584) baseStart_1503584 baseEnd_1503584 := by
    simpa [prefixWord, tailWord_1503584, baseEnd_1503584] using wordTrace_append hprefix tailTrace_1503584
  have hstable : (prefixWord ++ tailWord_1503584).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503584).length < 2 ^ (prefixWord ++ tailWord_1503584).sum := by decide
  have hdescent : baseEnd_1503584 < baseStart_1503584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503671 : List Nat := [1, 1, 3, 1, 3, 3, 1, 4, 4]
def baseStart_1503671 : Nat := 118140960795 + 1503671 * 2 ^ 59
def prefixEnd_1503671 : Nat := 4983230072969 + 3 ^ 40 * 1503671 * 2
def baseEnd_1503671 : Nat := 343158208545285161776555

theorem tailTrace_1503671 : CollatzResearch.WordTrace tailWord_1503671 prefixEnd_1503671 343158208545285161776555 := by
  unfold tailWord_1503671
  simp only [CollatzResearch.WordTrace]
  refine ⟨54843386935464248406494867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36562257956976165604329911 54843386935464248406494867)
  ·
    refine ⟨82265080403196372609742301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54843386935464248406494867 82265080403196372609742301)
    ·
      refine ⟨30849405151198639728653363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82265080403196372609742301 30849405151198639728653363)
      ·
        refine ⟨46274107726797959592980045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30849405151198639728653363 46274107726797959592980045)
        ·
          refine ⟨17352790397549234847367517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46274107726797959592980045 17352790397549234847367517)
          ·
            refine ⟨6507296399080963067762819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17352790397549234847367517 6507296399080963067762819)
            ·
              refine ⟨9760944598621444601644229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6507296399080963067762819 9760944598621444601644229)
              ·
                refine ⟨1830177112241520862808293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9760944598621444601644229 1830177112241520862808293)
                ·
                  refine ⟨343158208545285161776555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1830177112241520862808293 343158208545285161776555)
                  ·
                    rfl

theorem cell21_1503671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 4, 4].length) (baseStart_1503671 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1503671 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1503671 prefixEnd_1503671 := by exact prefixLift 1503671
  have htrace : WordTrace (prefixWord ++ tailWord_1503671) baseStart_1503671 baseEnd_1503671 := by
    simpa [prefixWord, tailWord_1503671, baseEnd_1503671] using wordTrace_append hprefix tailTrace_1503671
  have hstable : (prefixWord ++ tailWord_1503671).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503671).length < 2 ^ (prefixWord ++ tailWord_1503671).sum := by decide
  have hdescent : baseEnd_1503671 < baseStart_1503671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503764 : List Nat := [2, 4, 3, 1, 1, 1, 1, 2, 6]
def baseStart_1503764 : Nat := 118140960795 + 1503764 * 2 ^ 59
def prefixEnd_1503764 : Nat := 4983230072969 + 3 ^ 40 * 1503764 * 2
def baseEnd_1503764 : Nat := 343179432412337666726365

theorem tailTrace_1503764 : CollatzResearch.WordTrace tailWord_1503764 prefixEnd_1503764 343179432412337666726365 := by
  unfold tailWord_1503764
  simp only [CollatzResearch.WordTrace]
  refine ⟨27423389462063662644815173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36564519282751550193086897 27423389462063662644815173)
  ·
    refine ⟨5141885524136936745902845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27423389462063662644815173 5141885524136936745902845)
    ·
      refine ⟨1928207071551351279713567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5141885524136936745902845 1928207071551351279713567)
      ·
        refine ⟨2892310607327026919570351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1928207071551351279713567 2892310607327026919570351)
        ·
          refine ⟨4338465910990540379355527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2892310607327026919570351 4338465910990540379355527)
          ·
            refine ⟨6507698866485810569033291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4338465910990540379355527 6507698866485810569033291)
            ·
              refine ⟨9761548299728715853549937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6507698866485810569033291 9761548299728715853549937)
              ·
                refine ⟨7321161224796536890162453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9761548299728715853549937 7321161224796536890162453)
                ·
                  refine ⟨343179432412337666726365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7321161224796536890162453 343179432412337666726365)
                  ·
                    rfl

theorem cell21_1503764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_1503764 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1503764 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1503764 prefixEnd_1503764 := by exact prefixLift 1503764
  have htrace : WordTrace (prefixWord ++ tailWord_1503764) baseStart_1503764 baseEnd_1503764 := by
    simpa [prefixWord, tailWord_1503764, baseEnd_1503764] using wordTrace_append hprefix tailTrace_1503764
  have hstable : (prefixWord ++ tailWord_1503764).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503764).length < 2 ^ (prefixWord ++ tailWord_1503764).sum := by decide
  have hdescent : baseEnd_1503764 < baseStart_1503764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503792 : List Nat := [2, 1, 1, 1, 2, 3, 5, 1, 5]
def baseStart_1503792 : Nat := 118140960795 + 1503792 * 2 ^ 59
def prefixEnd_1503792 : Nat := 4983230072969 + 3 ^ 40 * 1503792 * 2
def baseEnd_1503792 : Nat := 343185822393815840259641

theorem tailTrace_1503792 : CollatzResearch.WordTrace tailWord_1503792 prefixEnd_1503792 343185822393815840259641 := by
  unfold tailWord_1503792
  simp only [CollatzResearch.WordTrace]
  refine ⟨27423900084012943035824815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36565200112017257381099753 27423900084012943035824815)
  ·
    refine ⟨41135850126019414553737223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27423900084012943035824815 41135850126019414553737223)
    ·
      refine ⟨61703775189029121830605835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41135850126019414553737223 61703775189029121830605835)
      ·
        refine ⟨92555662783543682745908753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61703775189029121830605835 92555662783543682745908753)
        ·
          refine ⟨69416747087657762059431565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92555662783543682745908753 69416747087657762059431565)
          ·
            refine ⟨26031280157871660772286837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69416747087657762059431565 26031280157871660772286837)
            ·
              refine ⟨2440432514800468197401891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26031280157871660772286837 2440432514800468197401891)
              ·
                refine ⟨3660648772200702296102837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2440432514800468197401891 3660648772200702296102837)
                ·
                  refine ⟨343185822393815840259641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3660648772200702296102837 343185822393815840259641)
                  ·
                    rfl

theorem cell21_1503792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 1, 5].length) (baseStart_1503792 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1503792 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1503792 prefixEnd_1503792 := by exact prefixLift 1503792
  have htrace : WordTrace (prefixWord ++ tailWord_1503792) baseStart_1503792 baseEnd_1503792 := by
    simpa [prefixWord, tailWord_1503792, baseEnd_1503792] using wordTrace_append hprefix tailTrace_1503792
  have hstable : (prefixWord ++ tailWord_1503792).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503792).length < 2 ^ (prefixWord ++ tailWord_1503792).sum := by decide
  have hdescent : baseEnd_1503792 < baseStart_1503792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503798 : List Nat := [5, 1, 2, 1, 2, 3, 2, 1, 4]
def baseStart_1503798 : Nat := 118140960795 + 1503798 * 2 ^ 59
def prefixEnd_1503798 : Nat := 4983230072969 + 3 ^ 40 * 1503798 * 2
def baseEnd_1503798 : Nat := 343187191675561163159629

theorem tailTrace_1503798 : CollatzResearch.WordTrace tailWord_1503798 prefixEnd_1503798 343187191675561163159629 := by
  unfold tailWord_1503798
  simp only [CollatzResearch.WordTrace]
  refine ⟨3428001187875259318523003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36565346004002766064245365 3428001187875259318523003)
  ·
    refine ⟨5142001781812888977784505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3428001187875259318523003 5142001781812888977784505)
    ·
      refine ⟨3856501336359666733338379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5142001781812888977784505 3856501336359666733338379)
      ·
        refine ⟨5784752004539500100007569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3856501336359666733338379 5784752004539500100007569)
        ·
          refine ⟨4338564003404625075005677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5784752004539500100007569 4338564003404625075005677)
          ·
            refine ⟨1626961501276734403127129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4338564003404625075005677 1626961501276734403127129)
            ·
              refine ⟨1220221125957550802345347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1626961501276734403127129 1220221125957550802345347)
              ·
                refine ⟨1830331688936326203518021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1220221125957550802345347 1830331688936326203518021)
                ·
                  refine ⟨343187191675561163159629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1830331688936326203518021 343187191675561163159629)
                  ·
                    rfl

theorem cell21_1503798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_1503798 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1503798 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1503798 prefixEnd_1503798 := by exact prefixLift 1503798
  have htrace : WordTrace (prefixWord ++ tailWord_1503798) baseStart_1503798 baseEnd_1503798 := by
    simpa [prefixWord, tailWord_1503798, baseEnd_1503798] using wordTrace_append hprefix tailTrace_1503798
  have hstable : (prefixWord ++ tailWord_1503798).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503798).length < 2 ^ (prefixWord ++ tailWord_1503798).sum := by decide
  have hdescent : baseEnd_1503798 < baseStart_1503798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503837 : List Nat := [1, 4, 4, 12]
def baseStart_1503837 : Nat := 118140960795 + 1503837 * 2 ^ 59
def prefixEnd_1503837 : Nat := 4983230072969 + 3 ^ 40 * 1503837 * 2
def baseEnd_1503837 : Nat := 1412329596736237703743

theorem tailTrace_1503837 : CollatzResearch.WordTrace tailWord_1503837 prefixEnd_1503837 1412329596736237703743 := by
  unfold tailWord_1503837
  simp only [CollatzResearch.WordTrace]
  refine ⟨54849441452862858757037765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36566294301908572504691843 54849441452862858757037765)
  ·
    refine ⟨10284270272411786016944581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54849441452862858757037765 10284270272411786016944581)
    ·
      refine ⟨1928300676077209878177109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10284270272411786016944581 1928300676077209878177109)
      ·
        refine ⟨1412329596736237703743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 1928300676077209878177109 1412329596736237703743)
        ·
          rfl

theorem cell21_1503837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 12].length) (baseStart_1503837 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1503837 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1503837 prefixEnd_1503837 := by exact prefixLift 1503837
  have htrace : WordTrace (prefixWord ++ tailWord_1503837) baseStart_1503837 baseEnd_1503837 := by
    simpa [prefixWord, tailWord_1503837, baseEnd_1503837] using wordTrace_append hprefix tailTrace_1503837
  have hstable : (prefixWord ++ tailWord_1503837).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503837).length < 2 ^ (prefixWord ++ tailWord_1503837).sum := by decide
  have hdescent : baseEnd_1503837 < baseStart_1503837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503854 : List Nat := [4, 1, 2, 2, 2, 1, 3, 6]
def baseStart_1503854 : Nat := 118140960795 + 1503854 * 2 ^ 59
def prefixEnd_1503854 : Nat := 4983230072969 + 3 ^ 40 * 1503854 * 2
def baseEnd_1503854 : Nat := 114399990546172503408727

theorem tailTrace_1503854 : CollatzResearch.WordTrace tailWord_1503854 prefixEnd_1503854 114399990546172503408727 := by
  unfold tailWord_1503854
  simp only [CollatzResearch.WordTrace]
  refine ⟨6856257686725158832550827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36566707662534180440271077 6856257686725158832550827)
  ·
    refine ⟨10284386530087738248826241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6856257686725158832550827 10284386530087738248826241)
    ·
      refine ⟨7713289897565803686619681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10284386530087738248826241 7713289897565803686619681)
      ·
        refine ⟨5784967423174352764964761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7713289897565803686619681 5784967423174352764964761)
        ·
          refine ⟨4338725567380764573723571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5784967423174352764964761 4338725567380764573723571)
          ·
            refine ⟨6508088351071146860585357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4338725567380764573723571 6508088351071146860585357)
            ·
              refine ⟨2440533131651680072719509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6508088351071146860585357 2440533131651680072719509)
              ·
                refine ⟨114399990546172503408727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2440533131651680072719509 114399990546172503408727)
                ·
                  rfl

theorem cell21_1503854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 6].length) (baseStart_1503854 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1503854 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1503854 prefixEnd_1503854 := by exact prefixLift 1503854
  have htrace : WordTrace (prefixWord ++ tailWord_1503854) baseStart_1503854 baseEnd_1503854 := by
    simpa [prefixWord, tailWord_1503854, baseEnd_1503854] using wordTrace_append hprefix tailTrace_1503854
  have hstable : (prefixWord ++ tailWord_1503854).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503854).length < 2 ^ (prefixWord ++ tailWord_1503854).sum := by decide
  have hdescent : baseEnd_1503854 < baseStart_1503854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503902 : List Nat := [4, 3, 1, 1, 1, 1, 1, 6, 3]
def baseStart_1503902 : Nat := 118140960795 + 1503902 * 2 ^ 59
def prefixEnd_1503902 : Nat := 4983230072969 + 3 ^ 40 * 1503902 * 2
def baseEnd_1503902 : Nat := 343210925892480093426083

theorem tailTrace_1503902 : CollatzResearch.WordTrace tailWord_1503902 prefixEnd_1503902 343210925892480093426083 := by
  unfold tailWord_1503902
  simp only [CollatzResearch.WordTrace]
  refine ⟨6856476524703421857269245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36567874798418249905435973 6856476524703421857269245)
  ·
    refine ⟨2571178696763783196475967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6856476524703421857269245 2571178696763783196475967)
    ·
      refine ⟨3856768045145674794713951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2571178696763783196475967 3856768045145674794713951)
      ·
        refine ⟨5785152067718512192070927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3856768045145674794713951 5785152067718512192070927)
        ·
          refine ⟨8677728101577768288106391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5785152067718512192070927 8677728101577768288106391)
          ·
            refine ⟨13016592152366652432159587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8677728101577768288106391 13016592152366652432159587)
            ·
              refine ⟨19524888228549978648239381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13016592152366652432159587 19524888228549978648239381)
              ·
                refine ⟨915229135713280249136221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19524888228549978648239381 915229135713280249136221)
                ·
                  refine ⟨343210925892480093426083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 915229135713280249136221 343210925892480093426083)
                  ·
                    rfl

theorem cell21_1503902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_1503902 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1503902 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1503902 prefixEnd_1503902 := by exact prefixLift 1503902
  have htrace : WordTrace (prefixWord ++ tailWord_1503902) baseStart_1503902 baseEnd_1503902 := by
    simpa [prefixWord, tailWord_1503902, baseEnd_1503902] using wordTrace_append hprefix tailTrace_1503902
  have hstable : (prefixWord ++ tailWord_1503902).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503902).length < 2 ^ (prefixWord ++ tailWord_1503902).sum := by decide
  have hdescent : baseEnd_1503902 < baseStart_1503902 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504023 : List Nat := [1, 1, 3, 4, 4, 1, 1, 6]
def baseStart_1504023 : Nat := 118140960795 + 1504023 * 2 ^ 59
def prefixEnd_1504023 : Nat := 4983230072969 + 3 ^ 40 * 1504023 * 2
def baseEnd_1504023 : Nat := 114412846580336923969723

theorem tailTrace_1504023 : CollatzResearch.WordTrace tailWord_1504023 prefixEnd_1504023 114412846580336923969723 := by
  unfold tailWord_1504023
  simp only [CollatzResearch.WordTrace]
  refine ⟨54856225430189012523308723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36570816953459341682205815 54856225430189012523308723)
  ·
    refine ⟨82284338145283518784963085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54856225430189012523308723 82284338145283518784963085)
    ·
      refine ⟨30856626804481319544361157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82284338145283518784963085 30856626804481319544361157)
      ·
        refine ⟨5785617525840247414567717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30856626804481319544361157 5785617525840247414567717)
        ·
          refine ⟨1084803286095046390231447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5785617525840247414567717 1084803286095046390231447)
          ·
            refine ⟨1627204929142569585347171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1084803286095046390231447 1627204929142569585347171)
            ·
              refine ⟨2440807393713854378020757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1627204929142569585347171 2440807393713854378020757)
              ·
                refine ⟨114412846580336923969723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2440807393713854378020757 114412846580336923969723)
                ·
                  rfl

theorem cell21_1504023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 6].length) (baseStart_1504023 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1504023 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1504023 prefixEnd_1504023 := by exact prefixLift 1504023
  have htrace : WordTrace (prefixWord ++ tailWord_1504023) baseStart_1504023 baseEnd_1504023 := by
    simpa [prefixWord, tailWord_1504023, baseEnd_1504023] using wordTrace_append hprefix tailTrace_1504023
  have hstable : (prefixWord ++ tailWord_1504023).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504023).length < 2 ^ (prefixWord ++ tailWord_1504023).sum := by decide
  have hdescent : baseEnd_1504023 < baseStart_1504023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504048 : List Nat := [2, 1, 1, 1, 2, 2, 1, 11]
def baseStart_1504048 : Nat := 118140960795 + 1504048 * 2 ^ 59
def prefixEnd_1504048 : Nat := 4983230072969 + 3 ^ 40 * 1504048 * 2
def baseEnd_1504048 : Nat := 114414748360538761330817

theorem tailTrace_1504048 : CollatzResearch.WordTrace tailWord_1504048 prefixEnd_1504048 114414748360538761330817 := by
  unfold tailWord_1504048
  simp only [CollatzResearch.WordTrace]
  refine ⟨27428568627549220896484399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36571424836732294528645865 27428568627549220896484399)
  ·
    refine ⟨41142852941323831344726599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27428568627549220896484399 41142852941323831344726599)
    ·
      refine ⟨61714279411985747017089899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41142852941323831344726599 61714279411985747017089899)
      ·
        refine ⟨92571419117978620525634849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61714279411985747017089899 92571419117978620525634849)
        ·
          refine ⟨69428564338483965394226137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92571419117978620525634849 69428564338483965394226137)
          ·
            refine ⟨52071423253862974045669603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69428564338483965394226137 52071423253862974045669603)
            ·
              refine ⟨78107134880794461068504405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52071423253862974045669603 78107134880794461068504405)
              ·
                refine ⟨114414748360538761330817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 78107134880794461068504405 114414748360538761330817)
                ·
                  rfl

theorem cell21_1504048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 11].length) (baseStart_1504048 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1504048 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1504048 prefixEnd_1504048 := by exact prefixLift 1504048
  have htrace : WordTrace (prefixWord ++ tailWord_1504048) baseStart_1504048 baseEnd_1504048 := by
    simpa [prefixWord, tailWord_1504048, baseEnd_1504048] using wordTrace_append hprefix tailTrace_1504048
  have hstable : (prefixWord ++ tailWord_1504048).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504048).length < 2 ^ (prefixWord ++ tailWord_1504048).sum := by decide
  have hdescent : baseEnd_1504048 < baseStart_1504048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504113 : List Nat := [1, 2, 2, 2, 1, 4, 3, 3, 3]
def baseStart_1504113 : Nat := 118140960795 + 1504113 * 2 ^ 59
def prefixEnd_1504113 : Nat := 4983230072969 + 3 ^ 40 * 1504113 * 2
def baseEnd_1504113 : Nat := 343259078967190615408985

theorem tailTrace_1504113 : CollatzResearch.WordTrace tailWord_1504113 prefixEnd_1504113 343259078967190615408985 := by
  unfold tailWord_1504113
  simp only [CollatzResearch.WordTrace]
  refine ⟨54859507999862957894084993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36573005333241971929389995 54859507999862957894084993)
  ·
    refine ⟨41144630999897218420563745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54859507999862957894084993 41144630999897218420563745)
    ·
      refine ⟨30858473249922913815422809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41144630999897218420563745 30858473249922913815422809)
      ·
        refine ⟨23143854937442185361567107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30858473249922913815422809 23143854937442185361567107)
        ·
          refine ⟨34715782406163278042350661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23143854937442185361567107 34715782406163278042350661)
          ·
            refine ⟨6509209201155614632940749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34715782406163278042350661 6509209201155614632940749)
            ·
              refine ⟨2440953450433355487352781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6509209201155614632940749 2440953450433355487352781)
              ·
                refine ⟨915357543912508307757293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2440953450433355487352781 915357543912508307757293)
                ·
                  refine ⟨343259078967190615408985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 915357543912508307757293 343259078967190615408985)
                  ·
                    rfl

theorem cell21_1504113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 3, 3].length) (baseStart_1504113 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1504113 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1504113 prefixEnd_1504113 := by exact prefixLift 1504113
  have htrace : WordTrace (prefixWord ++ tailWord_1504113) baseStart_1504113 baseEnd_1504113 := by
    simpa [prefixWord, tailWord_1504113, baseEnd_1504113] using wordTrace_append hprefix tailTrace_1504113
  have hstable : (prefixWord ++ tailWord_1504113).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504113).length < 2 ^ (prefixWord ++ tailWord_1504113).sum := by decide
  have hdescent : baseEnd_1504113 < baseStart_1504113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504310 : List Nat := [5, 1, 2, 1, 1, 3, 2, 6]
def baseStart_1504310 : Nat := 118140960795 + 1504310 * 2 ^ 59
def prefixEnd_1504310 : Nat := 4983230072969 + 3 ^ 40 * 1504310 * 2
def baseEnd_1504310 : Nat := 114434679017054016875083

theorem tailTrace_1504310 : CollatzResearch.WordTrace tailWord_1504310 prefixEnd_1504310 114434679017054016875083 := by
  unfold tailWord_1504310
  simp only [CollatzResearch.WordTrace]
  refine ⟨3429168323759328783687899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36577795453432840359337589 3429168323759328783687899)
  ·
    refine ⟨5143752485638993175531849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3429168323759328783687899 5143752485638993175531849)
    ·
      refine ⟨3857814364229244881648887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5143752485638993175531849 3857814364229244881648887)
      ·
        refine ⟨5786721546343867322473331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3857814364229244881648887 5786721546343867322473331)
        ·
          refine ⟨8680082319515800983709997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5786721546343867322473331 8680082319515800983709997)
          ·
            refine ⟨3255030869818425368891249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8680082319515800983709997 3255030869818425368891249)
            ·
              refine ⟨2441273152363819026668437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3255030869818425368891249 2441273152363819026668437)
              ·
                refine ⟨114434679017054016875083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2441273152363819026668437 114434679017054016875083)
                ·
                  rfl

theorem cell21_1504310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 6].length) (baseStart_1504310 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1504310 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1504310 prefixEnd_1504310 := by exact prefixLift 1504310
  have htrace : WordTrace (prefixWord ++ tailWord_1504310) baseStart_1504310 baseEnd_1504310 := by
    simpa [prefixWord, tailWord_1504310, baseEnd_1504310] using wordTrace_append hprefix tailTrace_1504310
  have hstable : (prefixWord ++ tailWord_1504310).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504310).length < 2 ^ (prefixWord ++ tailWord_1504310).sum := by decide
  have hdescent : baseEnd_1504310 < baseStart_1504310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504445 : List Nat := [1, 4, 1, 2, 1, 1, 6, 5]
def baseStart_1504445 : Nat := 118140960795 + 1504445 * 2 ^ 59
def prefixEnd_1504445 : Nat := 4983230072969 + 3 ^ 40 * 1504445 * 2
def baseEnd_1504445 : Nat := 114444948630143938624991

theorem tailTrace_1504445 : CollatzResearch.WordTrace tailWord_1504445 prefixEnd_1504445 114444948630143938624991 := by
  unfold tailWord_1504445
  simp only [CollatzResearch.WordTrace]
  refine ⟨54871617034660178595170789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36581078023106785730113859 54871617034660178595170789)
  ·
    refine ⟨10288428193998783486594523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54871617034660178595170789 10288428193998783486594523)
    ·
      refine ⟨15432642290998175229891785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10288428193998783486594523 15432642290998175229891785)
      ·
        refine ⟨11574481718248631422418839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15432642290998175229891785 11574481718248631422418839)
        ·
          refine ⟨17361722577372947133628259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11574481718248631422418839 17361722577372947133628259)
          ·
            refine ⟨26042583866059420700442389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17361722577372947133628259 26042583866059420700442389)
            ·
              refine ⟨1220746118721535345333237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 26042583866059420700442389 1220746118721535345333237)
              ·
                refine ⟨114444948630143938624991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1220746118721535345333237 114444948630143938624991)
                ·
                  rfl

theorem cell21_1504445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 6, 5].length) (baseStart_1504445 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1504445 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1504445 prefixEnd_1504445 := by exact prefixLift 1504445
  have htrace : WordTrace (prefixWord ++ tailWord_1504445) baseStart_1504445 baseEnd_1504445 := by
    simpa [prefixWord, tailWord_1504445, baseEnd_1504445] using wordTrace_append hprefix tailTrace_1504445
  have hstable : (prefixWord ++ tailWord_1504445).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504445).length < 2 ^ (prefixWord ++ tailWord_1504445).sum := by decide
  have hdescent : baseEnd_1504445 < baseStart_1504445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504462 : List Nat := [4, 1, 1, 1, 6, 1, 7]
def baseStart_1504462 : Nat := 118140960795 + 1504462 * 2 ^ 59
def prefixEnd_1504462 : Nat := 4983230072969 + 3 ^ 40 * 1504462 * 2
def baseEnd_1504462 : Nat := 38148747280227062676845

theorem tailTrace_1504462 : CollatzResearch.WordTrace tailWord_1504462 prefixEnd_1504462 38148747280227062676845 := by
  unfold tailWord_1504462
  simp only [CollatzResearch.WordTrace]
  refine ⟨6859029634449823812317455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36581491383732393665693093 6859029634449823812317455)
  ·
    refine ⟨10288544451674735718476183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6859029634449823812317455 10288544451674735718476183)
    ·
      refine ⟨15432816677512103577714275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10288544451674735718476183 15432816677512103577714275)
      ·
        refine ⟨23149225016268155366571413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15432816677512103577714275 23149225016268155366571413)
        ·
          refine ⟨1085119922637569782808035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 23149225016268155366571413 1085119922637569782808035)
          ·
            refine ⟨1627679883956354674212053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1085119922637569782808035 1627679883956354674212053)
            ·
              refine ⟨38148747280227062676845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1627679883956354674212053 38148747280227062676845)
              ·
                rfl

theorem cell21_1504462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 7].length) (baseStart_1504462 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1504462 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1504462 prefixEnd_1504462 := by exact prefixLift 1504462
  have htrace : WordTrace (prefixWord ++ tailWord_1504462) baseStart_1504462 baseEnd_1504462 := by
    simpa [prefixWord, tailWord_1504462, baseEnd_1504462] using wordTrace_append hprefix tailTrace_1504462
  have hstable : (prefixWord ++ tailWord_1504462).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504462).length < 2 ^ (prefixWord ++ tailWord_1504462).sum := by decide
  have hdescent : baseEnd_1504462 < baseStart_1504462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504535 : List Nat := [1, 1, 3, 4, 1, 1, 2, 3, 5]
def baseStart_1504535 : Nat := 118140960795 + 1504535 * 2 ^ 59
def prefixEnd_1504535 : Nat := 4983230072969 + 3 ^ 40 * 1504535 * 2
def baseEnd_1504535 : Nat := 343355385116611659374789

theorem tailTrace_1504535 : CollatzResearch.WordTrace tailWord_1504535 prefixEnd_1504535 343355385116611659374789 := by
  unfold tailWord_1504535
  simp only [CollatzResearch.WordTrace]
  refine ⟨54874899604334123965947059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36583266402889415977298039 54874899604334123965947059)
  ·
    refine ⟨82312349406501185948920589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54874899604334123965947059 82312349406501185948920589)
    ·
      refine ⟨30867131027437944730845221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82312349406501185948920589 30867131027437944730845221)
      ·
        refine ⟨5787587067644614637033479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30867131027437944730845221 5787587067644614637033479)
        ·
          refine ⟨8681380601466921955550219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5787587067644614637033479 8681380601466921955550219)
          ·
            refine ⟨13022070902200382933325329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8681380601466921955550219 13022070902200382933325329)
            ·
              refine ⟨9766553176650287199993997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13022070902200382933325329 9766553176650287199993997)
              ·
                refine ⟨3662457441243857699997749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9766553176650287199993997 3662457441243857699997749)
                ·
                  refine ⟨343355385116611659374789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3662457441243857699997749 343355385116611659374789)
                  ·
                    rfl

theorem cell21_1504535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 3, 5].length) (baseStart_1504535 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1504535 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1504535 prefixEnd_1504535 := by exact prefixLift 1504535
  have htrace : WordTrace (prefixWord ++ tailWord_1504535) baseStart_1504535 baseEnd_1504535 := by
    simpa [prefixWord, tailWord_1504535, baseEnd_1504535] using wordTrace_append hprefix tailTrace_1504535
  have hstable : (prefixWord ++ tailWord_1504535).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504535).length < 2 ^ (prefixWord ++ tailWord_1504535).sum := by decide
  have hdescent : baseEnd_1504535 < baseStart_1504535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504552 : List Nat := [2, 1, 5, 1, 2, 2, 1, 2, 5]
def baseStart_1504552 : Nat := 118140960795 + 1504552 * 2 ^ 59
def prefixEnd_1504552 : Nat := 4983230072969 + 3 ^ 40 * 1504552 * 2
def baseEnd_1504552 : Nat := 343359264748223407591421

theorem tailTrace_1504552 : CollatzResearch.WordTrace tailWord_1504552 prefixEnd_1504552 343359264748223407591421 := by
  unfold tailWord_1504552
  simp only [CollatzResearch.WordTrace]
  refine ⟨27437759822636267934657955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36583679763515023912877273 27437759822636267934657955)
  ·
    refine ⟨41156639733954401901986933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27437759822636267934657955 41156639733954401901986933)
    ·
      refine ⟨3858434975058225178311275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41156639733954401901986933 3858434975058225178311275)
      ·
        refine ⟨5787652462587337767466913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3858434975058225178311275 5787652462587337767466913)
        ·
          refine ⟨4340739346940503325600185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5787652462587337767466913 4340739346940503325600185)
          ·
            refine ⟨3255554510205377494200139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4340739346940503325600185 3255554510205377494200139)
            ·
              refine ⟨4883331765308066241300209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3255554510205377494200139 4883331765308066241300209)
              ·
                refine ⟨3662498823981049680975157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4883331765308066241300209 3662498823981049680975157)
                ·
                  refine ⟨343359264748223407591421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3662498823981049680975157 343359264748223407591421)
                  ·
                    rfl

theorem cell21_1504552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 2, 5].length) (baseStart_1504552 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1504552 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1504552 prefixEnd_1504552 := by exact prefixLift 1504552
  have htrace : WordTrace (prefixWord ++ tailWord_1504552) baseStart_1504552 baseEnd_1504552 := by
    simpa [prefixWord, tailWord_1504552, baseEnd_1504552] using wordTrace_append hprefix tailTrace_1504552
  have hstable : (prefixWord ++ tailWord_1504552).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504552).length < 2 ^ (prefixWord ++ tailWord_1504552).sum := by decide
  have hdescent : baseEnd_1504552 < baseStart_1504552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504583 : List Nat := [1, 1, 4, 1, 2, 5, 1, 2, 4]
def baseStart_1504583 : Nat := 118140960795 + 1504583 * 2 ^ 59
def prefixEnd_1504583 : Nat := 4983230072969 + 3 ^ 40 * 1504583 * 2
def baseEnd_1504583 : Nat := 343366339370574242574691

theorem tailTrace_1504583 : CollatzResearch.WordTrace tailWord_1504583 prefixEnd_1504583 343366339370574242574691 := by
  unfold tailWord_1504583
  simp only [CollatzResearch.WordTrace]
  refine ⟨54876650308160228163694403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36584433538773485442462935 54876650308160228163694403)
  ·
    refine ⟨82314975462240342245541605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54876650308160228163694403 82314975462240342245541605)
    ·
      refine ⟨15434057899170064171039051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82314975462240342245541605 15434057899170064171039051)
      ·
        refine ⟨23151086848755096256558577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15434057899170064171039051 23151086848755096256558577)
        ·
          refine ⟨17363315136566322192418933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23151086848755096256558577 17363315136566322192418933)
          ·
            refine ⟨1627810794053092705539275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17363315136566322192418933 1627810794053092705539275)
            ·
              refine ⟨2441716191079639058308913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1627810794053092705539275 2441716191079639058308913)
              ·
                refine ⟨1831287143309729293731685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2441716191079639058308913 1831287143309729293731685)
                ·
                  refine ⟨343366339370574242574691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1831287143309729293731685 343366339370574242574691)
                  ·
                    rfl

theorem cell21_1504583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 2, 4].length) (baseStart_1504583 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1504583 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1504583 prefixEnd_1504583 := by exact prefixLift 1504583
  have htrace : WordTrace (prefixWord ++ tailWord_1504583) baseStart_1504583 baseEnd_1504583 := by
    simpa [prefixWord, tailWord_1504583, baseEnd_1504583] using wordTrace_append hprefix tailTrace_1504583
  have hstable : (prefixWord ++ tailWord_1504583).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504583).length < 2 ^ (prefixWord ++ tailWord_1504583).sum := by decide
  have hdescent : baseEnd_1504583 < baseStart_1504583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504611 : List Nat := [1, 1, 1, 5, 2, 2, 2, 2, 5]
def baseStart_1504611 : Nat := 118140960795 + 1504611 * 2 ^ 59
def prefixEnd_1504611 : Nat := 4983230072969 + 3 ^ 40 * 1504611 * 2
def baseEnd_1504611 : Nat := 343372729352052416107967

theorem tailTrace_1504611 : CollatzResearch.WordTrace tailWord_1504611 prefixEnd_1504611 343372729352052416107967 := by
  unfold tailWord_1504611
  simp only [CollatzResearch.WordTrace]
  refine ⟨54877671552058788945713687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36585114368039192630475791 54877671552058788945713687)
  ·
    refine ⟨82316507328088183418570531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54877671552058788945713687 82316507328088183418570531)
    ·
      refine ⟨123474760992132275127855797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82316507328088183418570531 123474760992132275127855797)
      ·
        refine ⟨11575758843012400793236481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 123474760992132275127855797 11575758843012400793236481)
        ·
          refine ⟨8681819132259300594927361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11575758843012400793236481 8681819132259300594927361)
          ·
            refine ⟨6511364349194475446195521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8681819132259300594927361 6511364349194475446195521)
            ·
              refine ⟨4883523261895856584646641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6511364349194475446195521 4883523261895856584646641)
              ·
                refine ⟨3662642446421892438484981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4883523261895856584646641 3662642446421892438484981)
                ·
                  refine ⟨343372729352052416107967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3662642446421892438484981 343372729352052416107967)
                  ·
                    rfl

theorem cell21_1504611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 2, 5].length) (baseStart_1504611 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1504611 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1504611 prefixEnd_1504611 := by exact prefixLift 1504611
  have htrace : WordTrace (prefixWord ++ tailWord_1504611) baseStart_1504611 baseEnd_1504611 := by
    simpa [prefixWord, tailWord_1504611, baseEnd_1504611] using wordTrace_append hprefix tailTrace_1504611
  have hstable : (prefixWord ++ tailWord_1504611).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504611).length < 2 ^ (prefixWord ++ tailWord_1504611).sum := by decide
  have hdescent : baseEnd_1504611 < baseStart_1504611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504625 : List Nat := [1, 2, 2, 2, 1, 2, 3, 2, 6]
def baseStart_1504625 : Nat := 118140960795 + 1504625 * 2 ^ 59
def prefixEnd_1504625 : Nat := 4983230072969 + 3 ^ 40 * 1504625 * 2
def baseEnd_1504625 : Nat := 343375924342791502874605

theorem tailTrace_1504625 : CollatzResearch.WordTrace tailWord_1504625 prefixEnd_1504625 343375924342791502874605 := by
  unfold tailWord_1504625
  simp only [CollatzResearch.WordTrace]
  refine ⟨54878182174008069336723329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36585454782672046224482219 54878182174008069336723329)
  ·
    refine ⟨41158636630506052002542497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54878182174008069336723329 41158636630506052002542497)
    ·
      refine ⟨30868977472879539001906873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41158636630506052002542497 30868977472879539001906873)
      ·
        refine ⟨23151733104659654251430155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30868977472879539001906873 23151733104659654251430155)
        ·
          refine ⟨34727599656989481377145233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23151733104659654251430155 34727599656989481377145233)
          ·
            refine ⟨26045699742742111032858925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34727599656989481377145233 26045699742742111032858925)
            ·
              refine ⟨9767137403528291637322097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26045699742742111032858925 9767137403528291637322097)
              ·
                refine ⟨7325353052646218727991573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9767137403528291637322097 7325353052646218727991573)
                ·
                  refine ⟨343375924342791502874605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7325353052646218727991573 343375924342791502874605)
                  ·
                    rfl

theorem cell21_1504625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 2, 6].length) (baseStart_1504625 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1504625 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1504625 prefixEnd_1504625 := by exact prefixLift 1504625
  have htrace : WordTrace (prefixWord ++ tailWord_1504625) baseStart_1504625 baseEnd_1504625 := by
    simpa [prefixWord, tailWord_1504625, baseEnd_1504625] using wordTrace_append hprefix tailTrace_1504625
  have hstable : (prefixWord ++ tailWord_1504625).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504625).length < 2 ^ (prefixWord ++ tailWord_1504625).sum := by decide
  have hdescent : baseEnd_1504625 < baseStart_1504625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504718 : List Nat := [4, 1, 1, 1, 2, 1, 4, 3, 4]
def baseStart_1504718 : Nat := 118140960795 + 1504718 * 2 ^ 59
def prefixEnd_1504718 : Nat := 4983230072969 + 3 ^ 40 * 1504718 * 2
def baseEnd_1504718 : Nat := 343397148209844007824415

theorem tailTrace_1504718 : CollatzResearch.WordTrace tailWord_1504718 prefixEnd_1504718 343397148209844007824415 := by
  unfold tailWord_1504718
  simp only [CollatzResearch.WordTrace]
  refine ⟨6860196770333893277482351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36587716108447430813239205 6860196770333893277482351)
  ·
    refine ⟨10290295155500839916223527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6860196770333893277482351 10290295155500839916223527)
    ·
      refine ⟨15435442733251259874335291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10290295155500839916223527 15435442733251259874335291)
      ·
        refine ⟨23153164099876889811502937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15435442733251259874335291 23153164099876889811502937)
        ·
          refine ⟨17364873074907667358627203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23153164099876889811502937 17364873074907667358627203)
          ·
            refine ⟨26047309612361501037940805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17364873074907667358627203 26047309612361501037940805)
            ·
              refine ⟨4883870552317781444613901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26047309612361501037940805 4883870552317781444613901)
              ·
                refine ⟨1831451457119168041730213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4883870552317781444613901 1831451457119168041730213)
                ·
                  refine ⟨343397148209844007824415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1831451457119168041730213 343397148209844007824415)
                  ·
                    rfl

theorem cell21_1504718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 3, 4].length) (baseStart_1504718 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1504718 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1504718 prefixEnd_1504718 := by exact prefixLift 1504718
  have htrace : WordTrace (prefixWord ++ tailWord_1504718) baseStart_1504718 baseEnd_1504718 := by
    simpa [prefixWord, tailWord_1504718, baseEnd_1504718] using wordTrace_append hprefix tailTrace_1504718
  have hstable : (prefixWord ++ tailWord_1504718).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504718).length < 2 ^ (prefixWord ++ tailWord_1504718).sum := by decide
  have hdescent : baseEnd_1504718 < baseStart_1504718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504749 : List Nat := [1, 5, 1, 3, 2, 1, 8]
def baseStart_1504749 : Nat := 118140960795 + 1504749 * 2 ^ 59
def prefixEnd_1504749 : Nat := 4983230072969 + 3 ^ 40 * 1504749 * 2
def baseEnd_1504749 : Nat := 38156024759132760311965

theorem tailTrace_1504749 : CollatzResearch.WordTrace tailWord_1504749 prefixEnd_1504749 38156024759132760311965 := by
  unfold tailWord_1504749
  simp only [CollatzResearch.WordTrace]
  refine ⟨54882704825558838514237301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36588469883705892342824867 54882704825558838514237301)
  ·
    refine ⟨5145253577396141110709747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54882704825558838514237301 5145253577396141110709747)
    ·
      refine ⟨7717880366094211666064621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5145253577396141110709747 7717880366094211666064621)
      ·
        refine ⟨2894205137285329374774233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7717880366094211666064621 2894205137285329374774233)
        ·
          refine ⟨2170653852963997031080675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2894205137285329374774233 2170653852963997031080675)
          ·
            refine ⟨3255980779445995546621013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2170653852963997031080675 3255980779445995546621013)
            ·
              refine ⟨38156024759132760311965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3255980779445995546621013 38156024759132760311965)
              ·
                rfl

theorem cell21_1504749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 8].length) (baseStart_1504749 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1504749 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1504749 prefixEnd_1504749 := by exact prefixLift 1504749
  have htrace : WordTrace (prefixWord ++ tailWord_1504749) baseStart_1504749 baseEnd_1504749 := by
    simpa [prefixWord, tailWord_1504749, baseEnd_1504749] using wordTrace_append hprefix tailTrace_1504749
  have hstable : (prefixWord ++ tailWord_1504749).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504749).length < 2 ^ (prefixWord ++ tailWord_1504749).sum := by decide
  have hdescent : baseEnd_1504749 < baseStart_1504749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504814 : List Nat := [4, 1, 3, 1, 2, 2, 3, 2, 3]
def baseStart_1504814 : Nat := 118140960795 + 1504814 * 2 ^ 59
def prefixEnd_1504814 : Nat := 4983230072969 + 3 ^ 40 * 1504814 * 2
def baseEnd_1504814 : Nat := 343419056717769174224219

theorem tailTrace_1504814 : CollatzResearch.WordTrace tailWord_1504814 prefixEnd_1504814 343419056717769174224219 := by
  unfold tailWord_1504814
  simp only [CollatzResearch.WordTrace]
  refine ⟨6860634446290419326919187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36590050380215569743568997 6860634446290419326919187)
  ·
    refine ⟨10290951669435628990378781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6860634446290419326919187 10290951669435628990378781)
    ·
      refine ⟨3859106876038360871392043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10290951669435628990378781 3859106876038360871392043)
      ·
        refine ⟨5788660314057541307088065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3859106876038360871392043 5788660314057541307088065)
        ·
          refine ⟨4341495235543155980316049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5788660314057541307088065 4341495235543155980316049)
          ·
            refine ⟨3256121426657366985237037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4341495235543155980316049 3256121426657366985237037)
            ·
              refine ⟨1221045534996512619463889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3256121426657366985237037 1221045534996512619463889)
              ·
                refine ⟨915784151247384464597917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1221045534996512619463889 915784151247384464597917)
                ·
                  refine ⟨343419056717769174224219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 915784151247384464597917 343419056717769174224219)
                  ·
                    rfl

theorem cell21_1504814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 3, 2, 3].length) (baseStart_1504814 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1504814 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1504814 prefixEnd_1504814 := by exact prefixLift 1504814
  have htrace : WordTrace (prefixWord ++ tailWord_1504814) baseStart_1504814 baseEnd_1504814 := by
    simpa [prefixWord, tailWord_1504814, baseEnd_1504814] using wordTrace_append hprefix tailTrace_1504814
  have hstable : (prefixWord ++ tailWord_1504814).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504814).length < 2 ^ (prefixWord ++ tailWord_1504814).sum := by decide
  have hdescent : baseEnd_1504814 < baseStart_1504814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504828 : List Nat := [2, 2, 2, 2, 4, 2, 2, 1, 4]
def baseStart_1504828 : Nat := 118140960795 + 1504828 * 2 ^ 59
def prefixEnd_1504828 : Nat := 4983230072969 + 3 ^ 40 * 1504828 * 2
def baseEnd_1504828 : Nat := 343422251708508260990857

theorem tailTrace_1504828 : CollatzResearch.WordTrace tailWord_1504828 prefixEnd_1504828 343422251708508260990857 := by
  unfold tailWord_1504828
  simp only [CollatzResearch.WordTrace]
  refine ⟨27442793096136317503181569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36590390794848423337575425 27442793096136317503181569)
  ·
    refine ⟨20582094822102238127386177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27442793096136317503181569 20582094822102238127386177)
    ·
      refine ⟨15436571116576678595539633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20582094822102238127386177 15436571116576678595539633)
      ·
        refine ⟨11577428337432508946654725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15436571116576678595539633 11577428337432508946654725)
        ·
          refine ⟨2170767813268595427497761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11577428337432508946654725 2170767813268595427497761)
          ·
            refine ⟨1628075859951446570623321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2170767813268595427497761 1628075859951446570623321)
            ·
              refine ⟨1221056894963584927967491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1628075859951446570623321 1221056894963584927967491)
              ·
                refine ⟨1831585342445377391951237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1221056894963584927967491 1831585342445377391951237)
                ·
                  refine ⟨343422251708508260990857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1831585342445377391951237 343422251708508260990857)
                  ·
                    rfl

theorem cell21_1504828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 2, 1, 4].length) (baseStart_1504828 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1504828 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1504828 prefixEnd_1504828 := by exact prefixLift 1504828
  have htrace : WordTrace (prefixWord ++ tailWord_1504828) baseStart_1504828 baseEnd_1504828 := by
    simpa [prefixWord, tailWord_1504828, baseEnd_1504828] using wordTrace_append hprefix tailTrace_1504828
  have hstable : (prefixWord ++ tailWord_1504828).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504828).length < 2 ^ (prefixWord ++ tailWord_1504828).sum := by decide
  have hdescent : baseEnd_1504828 < baseStart_1504828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504867 : List Nat := [1, 1, 1, 5, 1, 12]
def baseStart_1504867 : Nat := 118140960795 + 1504867 * 2 ^ 59
def prefixEnd_1504867 : Nat := 4983230072969 + 3 ^ 40 * 1504867 * 2
def baseEnd_1504867 : Nat := 12719672297772328142251

theorem tailTrace_1504867 : CollatzResearch.WordTrace tailWord_1504867 prefixEnd_1504867 12719672297772328142251 := by
  unfold tailWord_1504867
  simp only [CollatzResearch.WordTrace]
  refine ⟨54887008639131344667032855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36591339092754229778021903 54887008639131344667032855)
  ·
    refine ⟨82330512958697017000549283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54887008639131344667032855 82330512958697017000549283)
    ·
      refine ⟨123495769438045525500823925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82330512958697017000549283 123495769438045525500823925)
      ·
        refine ⟨11577728384816768015702243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 123495769438045525500823925 11577728384816768015702243)
        ·
          refine ⟨17366592577225152023553365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11577728384816768015702243 17366592577225152023553365)
          ·
            refine ⟨12719672297772328142251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 17366592577225152023553365 12719672297772328142251)
            ·
              rfl

theorem cell21_1504867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 12].length) (baseStart_1504867 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1504867 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1504867 prefixEnd_1504867 := by exact prefixLift 1504867
  have htrace : WordTrace (prefixWord ++ tailWord_1504867) baseStart_1504867 baseEnd_1504867 := by
    simpa [prefixWord, tailWord_1504867, baseEnd_1504867] using wordTrace_append hprefix tailTrace_1504867
  have hstable : (prefixWord ++ tailWord_1504867).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504867).length < 2 ^ (prefixWord ++ tailWord_1504867).sum := by decide
  have hdescent : baseEnd_1504867 < baseStart_1504867 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504932 : List Nat := [2, 3, 1, 2, 2, 2, 2, 4, 3]
def baseStart_1504932 : Nat := 118140960795 + 1504932 * 2 ^ 59
def prefixEnd_1504932 : Nat := 4983230072969 + 3 ^ 40 * 1504932 * 2
def baseEnd_1504932 : Nat := 343445985925427191257311

theorem tailTrace_1504932 : CollatzResearch.WordTrace tailWord_1504932 prefixEnd_1504932 343445985925427191257311 := by
  unfold tailWord_1504932
  simp only [CollatzResearch.WordTrace]
  refine ⟨27444689691947930384074525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36592919589263907178766033 27444689691947930384074525)
  ·
    refine ⟨10291758634480473894027947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27444689691947930384074525 10291758634480473894027947)
    ·
      refine ⟨15437637951720710841041921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10291758634480473894027947 15437637951720710841041921)
      ·
        refine ⟨11578228463790533130781441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15437637951720710841041921 11578228463790533130781441)
        ·
          refine ⟨8683671347842899848086081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11578228463790533130781441 8683671347842899848086081)
          ·
            refine ⟨6512753510882174886064561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8683671347842899848086081 6512753510882174886064561)
            ·
              refine ⟨4884565133161631164548421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6512753510882174886064561 4884565133161631164548421)
              ·
                refine ⟨915855962467805843352829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4884565133161631164548421 915855962467805843352829)
                ·
                  refine ⟨343445985925427191257311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 915855962467805843352829 343445985925427191257311)
                  ·
                    rfl

theorem cell21_1504932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 4, 3].length) (baseStart_1504932 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1504932 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1504932 prefixEnd_1504932 := by exact prefixLift 1504932
  have htrace : WordTrace (prefixWord ++ tailWord_1504932) baseStart_1504932 baseEnd_1504932 := by
    simpa [prefixWord, tailWord_1504932, baseEnd_1504932] using wordTrace_append hprefix tailTrace_1504932
  have hstable : (prefixWord ++ tailWord_1504932).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504932).length < 2 ^ (prefixWord ++ tailWord_1504932).sum := by decide
  have hdescent : baseEnd_1504932 < baseStart_1504932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504943 : List Nat := [1, 1, 2, 1, 2, 4, 2, 8]
def baseStart_1504943 : Nat := 118140960795 + 1504943 * 2 ^ 59
def prefixEnd_1504943 : Nat := 4983230072969 + 3 ^ 40 * 1504943 * 2
def baseEnd_1504943 : Nat := 114482832091764538857985

theorem tailTrace_1504943 : CollatzResearch.WordTrace tailWord_1504943 prefixEnd_1504943 114482832091764538857985 := by
  unfold tailWord_1504943
  simp only [CollatzResearch.WordTrace]
  refine ⟨54889780586856009646799483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36593187057904006431199655 54889780586856009646799483)
  ·
    refine ⟨82334670880284014470199225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54889780586856009646799483 82334670880284014470199225)
    ·
      refine ⟨61751003160213010852649419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82334670880284014470199225 61751003160213010852649419)
      ·
        refine ⟨92626504740319516278974129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61751003160213010852649419 92626504740319516278974129)
        ·
          refine ⟨69469878555239637209230597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92626504740319516278974129 69469878555239637209230597)
          ·
            refine ⟨13025602229107431976730737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69469878555239637209230597 13025602229107431976730737)
            ·
              refine ⟨9769201671830573982548053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13025602229107431976730737 9769201671830573982548053)
              ·
                refine ⟨114482832091764538857985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9769201671830573982548053 114482832091764538857985)
                ·
                  rfl

theorem cell21_1504943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 8].length) (baseStart_1504943 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1504943 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1504943 prefixEnd_1504943 := by exact prefixLift 1504943
  have htrace : WordTrace (prefixWord ++ tailWord_1504943) baseStart_1504943 baseEnd_1504943 := by
    simpa [prefixWord, tailWord_1504943, baseEnd_1504943] using wordTrace_append hprefix tailTrace_1504943
  have hstable : (prefixWord ++ tailWord_1504943).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504943).length < 2 ^ (prefixWord ++ tailWord_1504943).sum := by decide
  have hdescent : baseEnd_1504943 < baseStart_1504943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505042 : List Nat := [3, 2, 4, 1, 1, 1, 4, 2, 3]
def baseStart_1505042 : Nat := 118140960795 + 1505042 * 2 ^ 59
def prefixEnd_1505042 : Nat := 4983230072969 + 3 ^ 40 * 1505042 * 2
def baseEnd_1505042 : Nat := 343471089424091444423753

theorem tailTrace_1505042 : CollatzResearch.WordTrace tailWord_1505042 prefixEnd_1505042 343471089424091444423753 := by
  unfold tailWord_1505042
  simp only [CollatzResearch.WordTrace]
  refine ⟨13723347853374337388663345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36595594275664899703102253 13723347853374337388663345)
  ·
    refine ⟨10292510890030753041497509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13723347853374337388663345 10292510890030753041497509)
    ·
      refine ⟨1929845791880766195280783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10292510890030753041497509 1929845791880766195280783)
      ·
        refine ⟨2894768687821149292921175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1929845791880766195280783 2894768687821149292921175)
        ·
          refine ⟨4342153031731723939381763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2894768687821149292921175 4342153031731723939381763)
          ·
            refine ⟨6513229547597585909072645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4342153031731723939381763 6513229547597585909072645)
            ·
              refine ⟨1221230540174547357951121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6513229547597585909072645 1221230540174547357951121)
              ·
                refine ⟨915922905130910518463341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1221230540174547357951121 915922905130910518463341)
                ·
                  refine ⟨343471089424091444423753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 915922905130910518463341 343471089424091444423753)
                  ·
                    rfl

theorem cell21_1505042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 4, 2, 3].length) (baseStart_1505042 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1505042 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1505042 prefixEnd_1505042 := by exact prefixLift 1505042
  have htrace : WordTrace (prefixWord ++ tailWord_1505042) baseStart_1505042 baseEnd_1505042 := by
    simpa [prefixWord, tailWord_1505042, baseEnd_1505042] using wordTrace_append hprefix tailTrace_1505042
  have hstable : (prefixWord ++ tailWord_1505042).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505042).length < 2 ^ (prefixWord ++ tailWord_1505042).sum := by decide
  have hdescent : baseEnd_1505042 < baseStart_1505042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505070 : List Nat := [4, 1, 3, 2, 2, 1, 3, 5]
def baseStart_1505070 : Nat := 118140960795 + 1505070 * 2 ^ 59
def prefixEnd_1505070 : Nat := 4983230072969 + 3 ^ 40 * 1505070 * 2
def baseEnd_1505070 : Nat := 114492493135189872652343

theorem tailTrace_1505070 : CollatzResearch.WordTrace tailWord_1505070 prefixEnd_1505070 114492493135189872652343 := by
  unfold tailWord_1505070
  simp only [CollatzResearch.WordTrace]
  refine ⟨6861801582174488792084083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36596275104930606891115109 6861801582174488792084083)
  ·
    refine ⟨10292702373261733188126125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6861801582174488792084083 10292702373261733188126125)
    ·
      refine ⟨3859763389973149945547297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10292702373261733188126125 3859763389973149945547297)
      ·
        refine ⟨2894822542479862459160473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3859763389973149945547297 2894822542479862459160473)
        ·
          refine ⟨2171116906859896844370355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2894822542479862459160473 2171116906859896844370355)
          ·
            refine ⟨3256675360289845266555533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2171116906859896844370355 3256675360289845266555533)
            ·
              refine ⟨1221253260108691974958325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3256675360289845266555533 1221253260108691974958325)
              ·
                refine ⟨114492493135189872652343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1221253260108691974958325 114492493135189872652343)
                ·
                  rfl

theorem cell21_1505070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 3, 5].length) (baseStart_1505070 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1505070 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1505070 prefixEnd_1505070 := by exact prefixLift 1505070
  have htrace : WordTrace (prefixWord ++ tailWord_1505070) baseStart_1505070 baseEnd_1505070 := by
    simpa [prefixWord, tailWord_1505070, baseEnd_1505070] using wordTrace_append hprefix tailTrace_1505070
  have hstable : (prefixWord ++ tailWord_1505070).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505070).length < 2 ^ (prefixWord ++ tailWord_1505070).sum := by decide
  have hdescent : baseEnd_1505070 < baseStart_1505070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505101 : List Nat := [1, 6, 1, 2, 1, 1, 2, 4, 3]
def baseStart_1505101 : Nat := 118140960795 + 1505101 * 2 ^ 59
def prefixEnd_1505101 : Nat := 4983230072969 + 3 ^ 40 * 1505101 * 2
def baseEnd_1505101 : Nat := 343484554027920452940299

theorem tailTrace_1505101 : CollatzResearch.WordTrace tailWord_1505101 prefixEnd_1505101 343484554027920452940299 := by
  unfold tailWord_1505101
  simp only [CollatzResearch.WordTrace]
  refine ⟨54895543320283602631051157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36597028880189068420700771 54895543320283602631051157)
  ·
    refine ⟨2573228593138293873330523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 54895543320283602631051157 2573228593138293873330523)
    ·
      refine ⟨3859842889707440809995785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2573228593138293873330523 3859842889707440809995785)
      ·
        refine ⟨2894882167280580607496839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3859842889707440809995785 2894882167280580607496839)
        ·
          refine ⟨4342323250920870911245259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2894882167280580607496839 4342323250920870911245259)
          ·
            refine ⟨6513484876381306366867889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4342323250920870911245259 6513484876381306366867889)
            ·
              refine ⟨4885113657285979775150917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6513484876381306366867889 4885113657285979775150917)
              ·
                refine ⟨915958810741121207840797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4885113657285979775150917 915958810741121207840797)
                ·
                  refine ⟨343484554027920452940299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 915958810741121207840797 343484554027920452940299)
                  ·
                    rfl

theorem cell21_1505101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_1505101 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1505101 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1505101 prefixEnd_1505101 := by exact prefixLift 1505101
  have htrace : WordTrace (prefixWord ++ tailWord_1505101) baseStart_1505101 baseEnd_1505101 := by
    simpa [prefixWord, tailWord_1505101, baseEnd_1505101] using wordTrace_append hprefix tailTrace_1505101
  have hstable : (prefixWord ++ tailWord_1505101).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505101).length < 2 ^ (prefixWord ++ tailWord_1505101).sum := by decide
  have hdescent : baseEnd_1505101 < baseStart_1505101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505157 : List Nat := [1, 3, 1, 1, 3, 2, 2, 4, 4]
def baseStart_1505157 : Nat := 118140960795 + 1505157 * 2 ^ 59
def prefixEnd_1505157 : Nat := 4983230072969 + 3 ^ 40 * 1505157 * 2
def baseEnd_1505157 : Nat := 343497333990876800006851

theorem tailTrace_1505157 : CollatzResearch.WordTrace tailWord_1505157 prefixEnd_1505157 343497333990876800006851 := by
  unfold tailWord_1505157
  simp only [CollatzResearch.WordTrace]
  refine ⟨54897585808080724195089725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36598390538720482796726483 54897585808080724195089725)
  ·
    refine ⟨20586594678030271573158647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54897585808080724195089725 20586594678030271573158647)
    ·
      refine ⟨30879892017045407359737971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20586594678030271573158647 30879892017045407359737971)
      ·
        refine ⟨46319838025568111039606957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30879892017045407359737971 46319838025568111039606957)
        ·
          refine ⟨17369939259588041639852609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46319838025568111039606957 17369939259588041639852609)
          ·
            refine ⟨13027454444691031229889457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17369939259588041639852609 13027454444691031229889457)
            ·
              refine ⟨9770590833518273422417093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13027454444691031229889457 9770590833518273422417093)
              ·
                refine ⟨1831985781284676266703205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9770590833518273422417093 1831985781284676266703205)
                ·
                  refine ⟨343497333990876800006851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1831985781284676266703205 343497333990876800006851)
                  ·
                    rfl

theorem cell21_1505157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 4, 4].length) (baseStart_1505157 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1505157 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1505157 prefixEnd_1505157 := by exact prefixLift 1505157
  have htrace : WordTrace (prefixWord ++ tailWord_1505157) baseStart_1505157 baseEnd_1505157 := by
    simpa [prefixWord, tailWord_1505157, baseEnd_1505157] using wordTrace_append hprefix tailTrace_1505157
  have hstable : (prefixWord ++ tailWord_1505157).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505157).length < 2 ^ (prefixWord ++ tailWord_1505157).sum := by decide
  have hdescent : baseEnd_1505157 < baseStart_1505157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505160 : List Nat := [2, 1, 3, 3, 3, 2, 1, 1, 5]
def baseStart_1505160 : Nat := 118140960795 + 1505160 * 2 ^ 59
def prefixEnd_1505160 : Nat := 4983230072969 + 3 ^ 40 * 1505160 * 2
def baseEnd_1505160 : Nat := 343498018631749461456845

theorem tailTrace_1505160 : CollatzResearch.WordTrace tailWord_1505160 prefixEnd_1505160 343498018631749461456845 := by
  unfold tailWord_1505160
  simp only [CollatzResearch.WordTrace]
  refine ⟨27448847613534927853724467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36598463484713237138299289 27448847613534927853724467)
  ·
    refine ⟨41173271420302391780586701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27448847613534927853724467 41173271420302391780586701)
    ·
      refine ⟨15439976782613396917720013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41173271420302391780586701 15439976782613396917720013)
      ·
        refine ⟨5789991293480023844145005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15439976782613396917720013 5789991293480023844145005)
        ·
          refine ⟨2171246735055008941554377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5789991293480023844145005 2171246735055008941554377)
          ·
            refine ⟨1628435051291256706165783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2171246735055008941554377 1628435051291256706165783)
            ·
              refine ⟨2442652576936885059248675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1628435051291256706165783 2442652576936885059248675)
              ·
                refine ⟨3663978865405327588873013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2442652576936885059248675 3663978865405327588873013)
                ·
                  refine ⟨343498018631749461456845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3663978865405327588873013 343498018631749461456845)
                  ·
                    rfl

theorem cell21_1505160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 1, 5].length) (baseStart_1505160 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1505160 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1505160 prefixEnd_1505160 := by exact prefixLift 1505160
  have htrace : WordTrace (prefixWord ++ tailWord_1505160) baseStart_1505160 baseEnd_1505160 := by
    simpa [prefixWord, tailWord_1505160, baseEnd_1505160] using wordTrace_append hprefix tailTrace_1505160
  have hstable : (prefixWord ++ tailWord_1505160).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505160).length < 2 ^ (prefixWord ++ tailWord_1505160).sum := by decide
  have hdescent : baseEnd_1505160 < baseStart_1505160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505284 : List Nat := [2, 3, 2, 4, 1, 1, 3, 1, 4]
def baseStart_1505284 : Nat := 118140960795 + 1505284 * 2 ^ 59
def prefixEnd_1505284 : Nat := 4983230072969 + 3 ^ 40 * 1505284 * 2
def baseEnd_1505284 : Nat := 343526317121152801389925

theorem tailTrace_1505284 : CollatzResearch.WordTrace tailWord_1505284 prefixEnd_1505284 343526317121152801389925 := by
  unfold tailWord_1505284
  simp only [CollatzResearch.WordTrace]
  refine ⟨27451108939310312442481453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36601478585747083256641937 27451108939310312442481453)
  ·
    refine ⟨10294165852241367165930545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27451108939310312442481453 10294165852241367165930545)
    ·
      refine ⟨7720624389181025374447909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10294165852241367165930545 7720624389181025374447909)
      ·
        refine ⟨1447617072971442257708983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7720624389181025374447909 1447617072971442257708983)
        ·
          refine ⟨2171425609457163386563475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1447617072971442257708983 2171425609457163386563475)
          ·
            refine ⟨3257138414185745079845213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2171425609457163386563475 3257138414185745079845213)
            ·
              refine ⟨1221426905319654404941955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3257138414185745079845213 1221426905319654404941955)
              ·
                refine ⟨1832140357979481607412933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1221426905319654404941955 1832140357979481607412933)
                ·
                  refine ⟨343526317121152801389925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1832140357979481607412933 343526317121152801389925)
                  ·
                    rfl

theorem cell21_1505284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 3, 1, 4].length) (baseStart_1505284 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1505284 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1505284 prefixEnd_1505284 := by exact prefixLift 1505284
  have htrace : WordTrace (prefixWord ++ tailWord_1505284) baseStart_1505284 baseEnd_1505284 := by
    simpa [prefixWord, tailWord_1505284, baseEnd_1505284] using wordTrace_append hprefix tailTrace_1505284
  have hstable : (prefixWord ++ tailWord_1505284).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505284).length < 2 ^ (prefixWord ++ tailWord_1505284).sum := by decide
  have hdescent : baseEnd_1505284 < baseStart_1505284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505309 : List Nat := [1, 4, 2, 2, 2, 1, 1, 2, 6]
def baseStart_1505309 : Nat := 118140960795 + 1505309 * 2 ^ 59
def prefixEnd_1505309 : Nat := 4983230072969 + 3 ^ 40 * 1505309 * 2
def baseEnd_1505309 : Nat := 343532022461758313473207

theorem tailTrace_1505309 : CollatzResearch.WordTrace tailWord_1505309 prefixEnd_1505309 343532022461758313473207 := by
  unfold tailWord_1505309
  simp only [CollatzResearch.WordTrace]
  refine ⟨54903129703530054154622981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36602086469020036103081987 54903129703530054154622981)
  ·
    refine ⟨10294336819411885153991809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54903129703530054154622981 10294336819411885153991809)
    ·
      refine ⟨7720752614558913865493857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10294336819411885153991809 7720752614558913865493857)
      ·
        refine ⟨5790564460919185399120393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7720752614558913865493857 5790564460919185399120393)
        ·
          refine ⟨4342923345689389049340295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5790564460919185399120393 4342923345689389049340295)
          ·
            refine ⟨6514385018534083574010443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4342923345689389049340295 6514385018534083574010443)
            ·
              refine ⟨9771577527801125361015665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6514385018534083574010443 9771577527801125361015665)
              ·
                refine ⟨7328683145850844020761749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9771577527801125361015665 7328683145850844020761749)
                ·
                  refine ⟨343532022461758313473207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7328683145850844020761749 343532022461758313473207)
                  ·
                    rfl

theorem cell21_1505309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 2, 6].length) (baseStart_1505309 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1505309 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1505309 prefixEnd_1505309 := by exact prefixLift 1505309
  have htrace : WordTrace (prefixWord ++ tailWord_1505309) baseStart_1505309 baseEnd_1505309 := by
    simpa [prefixWord, tailWord_1505309, baseEnd_1505309] using wordTrace_append hprefix tailTrace_1505309
  have hstable : (prefixWord ++ tailWord_1505309).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505309).length < 2 ^ (prefixWord ++ tailWord_1505309).sum := by decide
  have hdescent : baseEnd_1505309 < baseStart_1505309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505374 : List Nat := [4, 4, 1, 1, 3, 8]
def baseStart_1505374 : Nat := 118140960795 + 1505374 * 2 ^ 59
def prefixEnd_1505374 : Nat := 4983230072969 + 3 ^ 40 * 1505374 * 2
def baseEnd_1505374 : Nat := 12723957642493801662583

theorem tailTrace_1505374 : CollatzResearch.WordTrace tailWord_1505374 prefixEnd_1505374 12723957642493801662583 := by
  unfold tailWord_1505374
  simp only [CollatzResearch.WordTrace]
  refine ⟨6863187556036821281967397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36603666965529713503826117 6863187556036821281967397)
  ·
    refine ⟨1286847666756903990368887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6863187556036821281967397 1286847666756903990368887)
    ·
      refine ⟨1930271500135355985553331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1286847666756903990368887 1930271500135355985553331)
      ·
        refine ⟨2895407250203033978329997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1930271500135355985553331 2895407250203033978329997)
        ·
          refine ⟨1085777718826137741873749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2895407250203033978329997 1085777718826137741873749)
          ·
            refine ⟨12723957642493801662583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1085777718826137741873749 12723957642493801662583)
            ·
              rfl

theorem cell21_1505374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 8].length) (baseStart_1505374 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1505374 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1505374 prefixEnd_1505374 := by exact prefixLift 1505374
  have htrace : WordTrace (prefixWord ++ tailWord_1505374) baseStart_1505374 baseEnd_1505374 := by
    simpa [prefixWord, tailWord_1505374, baseEnd_1505374] using wordTrace_append hprefix tailTrace_1505374
  have hstable : (prefixWord ++ tailWord_1505374).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505374).length < 2 ^ (prefixWord ++ tailWord_1505374).sum := by decide
  have hdescent : baseEnd_1505374 < baseStart_1505374 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505385 : List Nat := [1, 2, 1, 1, 1, 5, 4, 2, 4]
def baseStart_1505385 : Nat := 118140960795 + 1505385 * 2 ^ 59
def prefixEnd_1505385 : Nat := 4983230072969 + 3 ^ 40 * 1505385 * 2
def baseEnd_1505385 : Nat := 343549366697199070206385

theorem tailTrace_1505385 : CollatzResearch.WordTrace tailWord_1505385 prefixEnd_1505385 343549366697199070206385 := by
  unfold tailWord_1505385
  simp only [CollatzResearch.WordTrace]
  refine ⟨54905901651254719134389609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36603934434169812756259739 54905901651254719134389609)
  ·
    refine ⟨41179426238441039350792207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54905901651254719134389609 41179426238441039350792207)
    ·
      refine ⟨61769139357661559026188311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41179426238441039350792207 61769139357661559026188311)
      ·
        refine ⟨92653709036492338539282467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61769139357661559026188311 92653709036492338539282467)
        ·
          refine ⟨138980563554738507808923701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92653709036492338539282467 138980563554738507808923701)
          ·
            refine ⟨13029427833256735107086597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 138980563554738507808923701 13029427833256735107086597)
            ·
              refine ⟨2443017718735637832578737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13029427833256735107086597 2443017718735637832578737)
              ·
                refine ⟨1832263289051728374434053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2443017718735637832578737 1832263289051728374434053)
                ·
                  refine ⟨343549366697199070206385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1832263289051728374434053 343549366697199070206385)
                  ·
                    rfl

theorem cell21_1505385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 2, 4].length) (baseStart_1505385 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1505385 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1505385 prefixEnd_1505385 := by exact prefixLift 1505385
  have htrace : WordTrace (prefixWord ++ tailWord_1505385) baseStart_1505385 baseEnd_1505385 := by
    simpa [prefixWord, tailWord_1505385, baseEnd_1505385] using wordTrace_append hprefix tailTrace_1505385
  have hstable : (prefixWord ++ tailWord_1505385).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505385).length < 2 ^ (prefixWord ++ tailWord_1505385).sum := by decide
  have hdescent : baseEnd_1505385 < baseStart_1505385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505388 : List Nat := [2, 2, 1, 1, 3, 3, 4, 2, 3]
def baseStart_1505388 : Nat := 118140960795 + 1505388 * 2 ^ 59
def prefixEnd_1505388 : Nat := 4983230072969 + 3 ^ 40 * 1505388 * 2
def baseEnd_1505388 : Nat := 343550051338071731656379

theorem tailTrace_1505388 : CollatzResearch.WordTrace tailWord_1505388 prefixEnd_1505388 343550051338071731656379 := by
  unfold tailWord_1505388
  simp only [CollatzResearch.WordTrace]
  refine ⟨27453005535121925323374409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36604007380162567097832545 27453005535121925323374409)
  ·
    refine ⟨20589754151341443992530807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27453005535121925323374409 20589754151341443992530807)
    ·
      refine ⟨30884631227012165988796211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20589754151341443992530807 30884631227012165988796211)
      ·
        refine ⟨46326946840518248983194317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30884631227012165988796211 46326946840518248983194317)
        ·
          refine ⟨17372605065194343368697869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46326946840518248983194317 17372605065194343368697869)
          ·
            refine ⟨6514726899447878763261701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17372605065194343368697869 6514726899447878763261701)
            ·
              refine ⟨1221511293646477268111569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6514726899447878763261701 1221511293646477268111569)
              ·
                refine ⟨916133470234857951083677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1221511293646477268111569 916133470234857951083677)
                ·
                  refine ⟨343550051338071731656379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 916133470234857951083677 343550051338071731656379)
                  ·
                    rfl

theorem cell21_1505388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 4, 2, 3].length) (baseStart_1505388 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1505388 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1505388 prefixEnd_1505388 := by exact prefixLift 1505388
  have htrace : WordTrace (prefixWord ++ tailWord_1505388) baseStart_1505388 baseEnd_1505388 := by
    simpa [prefixWord, tailWord_1505388, baseEnd_1505388] using wordTrace_append hprefix tailTrace_1505388
  have hstable : (prefixWord ++ tailWord_1505388).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505388).length < 2 ^ (prefixWord ++ tailWord_1505388).sum := by decide
  have hdescent : baseEnd_1505388 < baseStart_1505388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505399 : List Nat := [1, 1, 3, 1, 1, 5, 3, 6]
def baseStart_1505399 : Nat := 118140960795 + 1505399 * 2 ^ 59
def prefixEnd_1505399 : Nat := 4983230072969 + 3 ^ 40 * 1505399 * 2
def baseEnd_1505399 : Nat := 114517520562646052324341

theorem tailTrace_1505399 : CollatzResearch.WordTrace tailWord_1505399 prefixEnd_1505399 114517520562646052324341 := by
  unfold tailWord_1505399
  simp only [CollatzResearch.WordTrace]
  refine ⟨54906412273203999525399251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36604274848802666350266167 54906412273203999525399251)
  ·
    refine ⟨82359618409805999288098877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54906412273203999525399251 82359618409805999288098877)
    ·
      refine ⟨30884856903677249733037079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82359618409805999288098877 30884856903677249733037079)
      ·
        refine ⟨46327285355515874599555619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30884856903677249733037079 46327285355515874599555619)
        ·
          refine ⟨69490928033273811899333429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46327285355515874599555619 69490928033273811899333429)
          ·
            refine ⟨6514774503119419865562509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 69490928033273811899333429 6514774503119419865562509)
            ·
              refine ⟨2443040438669782449585941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6514774503119419865562509 2443040438669782449585941)
              ·
                refine ⟨114517520562646052324341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2443040438669782449585941 114517520562646052324341)
                ·
                  rfl

theorem cell21_1505399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 6].length) (baseStart_1505399 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1505399 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1505399 prefixEnd_1505399 := by exact prefixLift 1505399
  have htrace : WordTrace (prefixWord ++ tailWord_1505399) baseStart_1505399 baseEnd_1505399 := by
    simpa [prefixWord, tailWord_1505399, baseEnd_1505399] using wordTrace_append hprefix tailTrace_1505399
  have hstable : (prefixWord ++ tailWord_1505399).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505399).length < 2 ^ (prefixWord ++ tailWord_1505399).sum := by decide
  have hdescent : baseEnd_1505399 < baseStart_1505399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505489 : List Nat := [1, 2, 2, 1, 2, 2, 2, 2, 7]
def baseStart_1505489 : Nat := 118140960795 + 1505489 * 2 ^ 59
def prefixEnd_1505489 : Nat := 4983230072969 + 3 ^ 40 * 1505489 * 2
def baseEnd_1505489 : Nat := 343573100914118000472839

theorem tailTrace_1505489 : CollatzResearch.WordTrace tailWord_1505489 prefixEnd_1505489 343573100914118000472839 := by
  unfold tailWord_1505489
  simp only [CollatzResearch.WordTrace]
  refine ⟨54909694842877944896175521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36606463228585296597450347 54909694842877944896175521)
  ·
    refine ⟨41182271132158458672131641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54909694842877944896175521 41182271132158458672131641)
    ·
      refine ⟨30886703349118844004098731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41182271132158458672131641 30886703349118844004098731)
      ·
        refine ⟨46330055023678266006148097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30886703349118844004098731 46330055023678266006148097)
        ·
          refine ⟨34747541267758699504611073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46330055023678266006148097 34747541267758699504611073)
          ·
            refine ⟨26060655950819024628458305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34747541267758699504611073 26060655950819024628458305)
            ·
              refine ⟨19545491963114268471343729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26060655950819024628458305 19545491963114268471343729)
              ·
                refine ⟨14659118972335701353507797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19545491963114268471343729 14659118972335701353507797)
                ·
                  refine ⟨343573100914118000472839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14659118972335701353507797 343573100914118000472839)
                  ·
                    rfl

theorem cell21_1505489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 7].length) (baseStart_1505489 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1505489 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1505489 prefixEnd_1505489 := by exact prefixLift 1505489
  have htrace : WordTrace (prefixWord ++ tailWord_1505489) baseStart_1505489 baseEnd_1505489 := by
    simpa [prefixWord, tailWord_1505489, baseEnd_1505489] using wordTrace_append hprefix tailTrace_1505489
  have hstable : (prefixWord ++ tailWord_1505489).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505489).length < 2 ^ (prefixWord ++ tailWord_1505489).sum := by decide
  have hdescent : baseEnd_1505489 < baseStart_1505489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505568 : List Nat := [2, 1, 1, 5, 2, 3, 1, 6]
def baseStart_1505568 : Nat := 118140960795 + 1505568 * 2 ^ 59
def prefixEnd_1505568 : Nat := 4983230072969 + 3 ^ 40 * 1505568 * 2
def baseEnd_1505568 : Nat := 114530376596810472885337

theorem tailTrace_1505568 : CollatzResearch.WordTrace tailWord_1505568 prefixEnd_1505568 114530376596810472885337 := by
  unfold tailWord_1505568
  simp only [CollatzResearch.WordTrace]
  refine ⟨27456288104795870694150679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36608384139727827592200905 27456288104795870694150679)
  ·
    refine ⟨41184432157193806041226019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27456288104795870694150679 41184432157193806041226019)
    ·
      refine ⟨61776648235790709061839029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41184432157193806041226019 61776648235790709061839029)
      ·
        refine ⟨5791560772105378974547409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61776648235790709061839029 5791560772105378974547409)
        ·
          refine ⟨4343670579079034230910557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5791560772105378974547409 4343670579079034230910557)
          ·
            refine ⟨1628876467154637836591459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4343670579079034230910557 1628876467154637836591459)
            ·
              refine ⟨2443314700731956754887189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1628876467154637836591459 2443314700731956754887189)
              ·
                refine ⟨114530376596810472885337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2443314700731956754887189 114530376596810472885337)
                ·
                  rfl

theorem cell21_1505568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 6].length) (baseStart_1505568 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1505568 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1505568 prefixEnd_1505568 := by exact prefixLift 1505568
  have htrace : WordTrace (prefixWord ++ tailWord_1505568) baseStart_1505568 baseEnd_1505568 := by
    simpa [prefixWord, tailWord_1505568, baseEnd_1505568] using wordTrace_append hprefix tailTrace_1505568
  have hstable : (prefixWord ++ tailWord_1505568).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505568).length < 2 ^ (prefixWord ++ tailWord_1505568).sum := by decide
  have hdescent : baseEnd_1505568 < baseStart_1505568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505596 : List Nat := [2, 2, 2, 2, 1, 2, 2, 2, 6]
def baseStart_1505596 : Nat := 118140960795 + 1505596 * 2 ^ 59
def prefixEnd_1505596 : Nat := 4983230072969 + 3 ^ 40 * 1505596 * 2
def baseEnd_1505596 : Nat := 343597519771909592189287

theorem tailTrace_1505596 : CollatzResearch.WordTrace tailWord_1505596 prefixEnd_1505596 343597519771909592189287 := by
  unfold tailWord_1505596
  simp only [CollatzResearch.WordTrace]
  refine ⟨27456798726745151085160321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36609064968993534780213761 27456798726745151085160321)
  ·
    refine ⟨20592599045058863313870241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27456798726745151085160321 20592599045058863313870241)
    ·
      refine ⟨15444449283794147485402681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20592599045058863313870241 15444449283794147485402681)
      ·
        refine ⟨11583336962845610614052011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15444449283794147485402681 11583336962845610614052011)
        ·
          refine ⟨17375005444268415921078017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11583336962845610614052011 17375005444268415921078017)
          ·
            refine ⟨13031254083201311940808513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17375005444268415921078017 13031254083201311940808513)
            ·
              refine ⟨9773440562400983955606385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13031254083201311940808513 9773440562400983955606385)
              ·
                refine ⟨7330080421800737966704789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9773440562400983955606385 7330080421800737966704789)
                ·
                  refine ⟨343597519771909592189287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7330080421800737966704789 343597519771909592189287)
                  ·
                    rfl

theorem cell21_1505596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 2, 6].length) (baseStart_1505596 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1505596 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1505596 prefixEnd_1505596 := by exact prefixLift 1505596
  have htrace : WordTrace (prefixWord ++ tailWord_1505596) baseStart_1505596 baseEnd_1505596 := by
    simpa [prefixWord, tailWord_1505596, baseEnd_1505596] using wordTrace_append hprefix tailTrace_1505596
  have hstable : (prefixWord ++ tailWord_1505596).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505596).length < 2 ^ (prefixWord ++ tailWord_1505596).sum := by decide
  have hdescent : baseEnd_1505596 < baseStart_1505596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505599 : List Nat := [1, 1, 2, 2, 4, 1, 4, 3, 3]
def baseStart_1505599 : Nat := 118140960795 + 1505599 * 2 ^ 59
def prefixEnd_1505599 : Nat := 4983230072969 + 3 ^ 40 * 1505599 * 2
def baseEnd_1505599 : Nat := 343598204412782253639281

theorem tailTrace_1505599 : CollatzResearch.WordTrace tailWord_1505599 prefixEnd_1505599 343598204412782253639281 := by
  unfold tailWord_1505599
  simp only [CollatzResearch.WordTrace]
  refine ⟨54913706872479433682679851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36609137914986289121786567 54913706872479433682679851)
  ·
    refine ⟨82370560308719150524019777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54913706872479433682679851 82370560308719150524019777)
    ·
      refine ⟨61777920231539362893014833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82370560308719150524019777 61777920231539362893014833)
      ·
        refine ⟨46333440173654522169761125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61777920231539362893014833 46333440173654522169761125)
        ·
          refine ⟨8687520032560222906830211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46333440173654522169761125 8687520032560222906830211)
          ·
            refine ⟨13031280048840334360245317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8687520032560222906830211 13031280048840334360245317)
            ·
              refine ⟨2443365009157562692545997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13031280048840334360245317 2443365009157562692545997)
              ·
                refine ⟨916261878434086009704749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2443365009157562692545997 916261878434086009704749)
                ·
                  refine ⟨343598204412782253639281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 916261878434086009704749 343598204412782253639281)
                  ·
                    rfl

theorem cell21_1505599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 3, 3].length) (baseStart_1505599 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1505599 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1505599 prefixEnd_1505599 := by exact prefixLift 1505599
  have htrace : WordTrace (prefixWord ++ tailWord_1505599) baseStart_1505599 baseEnd_1505599 := by
    simpa [prefixWord, tailWord_1505599, baseEnd_1505599] using wordTrace_append hprefix tailTrace_1505599
  have hstable : (prefixWord ++ tailWord_1505599).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505599).length < 2 ^ (prefixWord ++ tailWord_1505599).sum := by decide
  have hdescent : baseEnd_1505599 < baseStart_1505599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505641 : List Nat := [1, 2, 1, 1, 1, 3, 3, 4, 5]
def baseStart_1505641 : Nat := 118140960795 + 1505641 * 2 ^ 59
def prefixEnd_1505641 : Nat := 4983230072969 + 3 ^ 40 * 1505641 * 2
def baseEnd_1505641 : Nat := 343607789384999513939195

theorem tailTrace_1505641 : CollatzResearch.WordTrace tailWord_1505641 prefixEnd_1505641 343607789384999513939195 := by
  unfold tailWord_1505641
  simp only [CollatzResearch.WordTrace]
  refine ⟨54915238738327274855708777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36610159158884849903805851 54915238738327274855708777)
  ·
    refine ⟨41186429053745456141781583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54915238738327274855708777 41186429053745456141781583)
    ·
      refine ⟨61779643580618184212672375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41186429053745456141781583 61779643580618184212672375)
      ·
        refine ⟨92669465370927276319008563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61779643580618184212672375 92669465370927276319008563)
        ·
          refine ⟨139004198056390914478512845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92669465370927276319008563 139004198056390914478512845)
          ·
            refine ⟨52126574271146592929442317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139004198056390914478512845 52126574271146592929442317)
            ·
              refine ⟨19547465351679972348540869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52126574271146592929442317 19547465351679972348540869)
              ·
                refine ⟨3665149753439994815351413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19547465351679972348540869 3665149753439994815351413)
                ·
                  refine ⟨343607789384999513939195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3665149753439994815351413 343607789384999513939195)
                  ·
                    rfl

theorem cell21_1505641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 4, 5].length) (baseStart_1505641 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1505641 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1505641 prefixEnd_1505641 := by exact prefixLift 1505641
  have htrace : WordTrace (prefixWord ++ tailWord_1505641) baseStart_1505641 baseEnd_1505641 := by
    simpa [prefixWord, tailWord_1505641, baseEnd_1505641] using wordTrace_append hprefix tailTrace_1505641
  have hstable : (prefixWord ++ tailWord_1505641).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505641).length < 2 ^ (prefixWord ++ tailWord_1505641).sum := by decide
  have hdescent : baseEnd_1505641 < baseStart_1505641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505672 : List Nat := [2, 1, 3, 3, 1, 1, 1, 3, 6]
def baseStart_1505672 : Nat := 118140960795 + 1505672 * 2 ^ 59
def prefixEnd_1505672 : Nat := 4983230072969 + 3 ^ 40 * 1505672 * 2
def baseEnd_1505672 : Nat := 343614864007350348922465

theorem tailTrace_1505672 : CollatzResearch.WordTrace tailWord_1505672 prefixEnd_1505672 343614864007350348922465 := by
  unfold tailWord_1505672
  simp only [CollatzResearch.WordTrace]
  refine ⟨27458184700607483575043635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36610912934143311433391513 27458184700607483575043635)
  ·
    refine ⟨41187277050911225362565453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27458184700607483575043635 41187277050911225362565453)
    ·
      refine ⟨15445228894091709510962045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41187277050911225362565453 15445228894091709510962045)
      ·
        refine ⟨5791960835284391066610767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15445228894091709510962045 5791960835284391066610767)
        ·
          refine ⟨8687941252926586599916151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5791960835284391066610767 8687941252926586599916151)
          ·
            refine ⟨13031911879389879899874227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8687941252926586599916151 13031911879389879899874227)
            ·
              refine ⟨19547867819084819849811341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13031911879389879899874227 19547867819084819849811341)
              ·
                refine ⟨7330450432156807443679253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19547867819084819849811341 7330450432156807443679253)
                ·
                  refine ⟨343614864007350348922465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7330450432156807443679253 343614864007350348922465)
                  ·
                    rfl

theorem cell21_1505672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 3, 6].length) (baseStart_1505672 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1505672 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1505672 prefixEnd_1505672 := by exact prefixLift 1505672
  have htrace : WordTrace (prefixWord ++ tailWord_1505672) baseStart_1505672 baseEnd_1505672 := by
    simpa [prefixWord, tailWord_1505672, baseEnd_1505672] using wordTrace_append hprefix tailTrace_1505672
  have hstable : (prefixWord ++ tailWord_1505672).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505672).length < 2 ^ (prefixWord ++ tailWord_1505672).sum := by decide
  have hdescent : baseEnd_1505672 < baseStart_1505672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505703 : List Nat := [1, 1, 6, 1, 1, 2, 2, 7]
def baseStart_1505703 : Nat := 118140960795 + 1505703 * 2 ^ 59
def prefixEnd_1505703 : Nat := 4983230072969 + 3 ^ 40 * 1505703 * 2
def baseEnd_1505703 : Nat := 114540646209900394635245

theorem tailTrace_1505703 : CollatzResearch.WordTrace tailWord_1505703 prefixEnd_1505703 114540646209900394635245 := by
  unfold tailWord_1505703
  simp only [CollatzResearch.WordTrace]
  refine ⟨54917500064102659444465763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36611666709401772962977175 54917500064102659444465763)
  ·
    refine ⟨82376250096153989166698645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54917500064102659444465763 82376250096153989166698645)
    ·
      refine ⟨3861386723257218242188999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 82376250096153989166698645 3861386723257218242188999)
      ·
        refine ⟨5792080084885827363283499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3861386723257218242188999 5792080084885827363283499)
        ·
          refine ⟨8688120127328741044925249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5792080084885827363283499 8688120127328741044925249)
          ·
            refine ⟨6516090095496555783693937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8688120127328741044925249 6516090095496555783693937)
            ·
              refine ⟨4887067571622416837770453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6516090095496555783693937 4887067571622416837770453)
              ·
                refine ⟨114540646209900394635245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4887067571622416837770453 114540646209900394635245)
                ·
                  rfl

theorem cell21_1505703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 7].length) (baseStart_1505703 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1505703 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1505703 prefixEnd_1505703 := by exact prefixLift 1505703
  have htrace : WordTrace (prefixWord ++ tailWord_1505703) baseStart_1505703 baseEnd_1505703 := by
    simpa [prefixWord, tailWord_1505703, baseEnd_1505703] using wordTrace_append hprefix tailTrace_1505703
  have hstable : (prefixWord ++ tailWord_1505703).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505703).length < 2 ^ (prefixWord ++ tailWord_1505703).sum := by decide
  have hdescent : baseEnd_1505703 < baseStart_1505703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505807 : List Nat := [1, 1, 2, 1, 1, 1, 2, 4, 8]
def baseStart_1505807 : Nat := 118140960795 + 1505807 * 2 ^ 59
def prefixEnd_1505807 : Nat := 4983230072969 + 3 ^ 40 * 1505807 * 2
def baseEnd_1505807 : Nat := 343645672846620114172189

theorem tailTrace_1505807 : CollatzResearch.WordTrace tailWord_1505807 prefixEnd_1505807 343645672846620114172189 := by
  unfold tailWord_1505807
  simp only [CollatzResearch.WordTrace]
  refine ⟨54921293255725885206251675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36614195503817256804167783 54921293255725885206251675)
  ·
    refine ⟨82381939883588827809377513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54921293255725885206251675 82381939883588827809377513)
    ·
      refine ⟨61786454912691620857033135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82381939883588827809377513 61786454912691620857033135)
      ·
        refine ⟨92679682369037431285549703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61786454912691620857033135 92679682369037431285549703)
        ·
          refine ⟨139019523553556146928324555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92679682369037431285549703 139019523553556146928324555)
          ·
            refine ⟨208529285330334220392486833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139019523553556146928324555 208529285330334220392486833)
            ·
              refine ⟨156396963997750665294365125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 208529285330334220392486833 156396963997750665294365125)
              ·
                refine ⟨29324430749578249742693461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 156396963997750665294365125 29324430749578249742693461)
                ·
                  refine ⟨343645672846620114172189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29324430749578249742693461 343645672846620114172189)
                  ·
                    rfl

theorem cell21_1505807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 8].length) (baseStart_1505807 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1505807 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1505807 prefixEnd_1505807 := by exact prefixLift 1505807
  have htrace : WordTrace (prefixWord ++ tailWord_1505807) baseStart_1505807 baseEnd_1505807 := by
    simpa [prefixWord, tailWord_1505807, baseEnd_1505807] using wordTrace_append hprefix tailTrace_1505807
  have hstable : (prefixWord ++ tailWord_1505807).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505807).length < 2 ^ (prefixWord ++ tailWord_1505807).sum := by decide
  have hdescent : baseEnd_1505807 < baseStart_1505807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505827 : List Nat := [1, 1, 1, 4, 4, 1, 3, 3, 3]
def baseStart_1505827 : Nat := 118140960795 + 1505827 * 2 ^ 59
def prefixEnd_1505827 : Nat := 4983230072969 + 3 ^ 40 * 1505827 * 2
def baseEnd_1505827 : Nat := 343650237119104523838815

theorem tailTrace_1505827 : CollatzResearch.WordTrace tailWord_1505827 prefixEnd_1505827 343650237119104523838815 := by
  unfold tailWord_1505827
  simp only [CollatzResearch.WordTrace]
  refine ⟨54922022715653428621979735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36614681810435619081319823 54922022715653428621979735)
  ·
    refine ⟨82383034073480142932969603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54922022715653428621979735 82383034073480142932969603)
    ·
      refine ⟨123574551110220214399454405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82383034073480142932969603 123574551110220214399454405)
      ·
        refine ⟨23170228333166290199897701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123574551110220214399454405 23170228333166290199897701)
        ·
          refine ⟨4344417812468679412480819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23170228333166290199897701 4344417812468679412480819)
          ·
            refine ⟨6516626718703019118721229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4344417812468679412480819 6516626718703019118721229)
            ·
              refine ⟨2443735019513632169520461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6516626718703019118721229 2443735019513632169520461)
              ·
                refine ⟨916400632317612063570173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2443735019513632169520461 916400632317612063570173)
                ·
                  refine ⟨343650237119104523838815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 916400632317612063570173 343650237119104523838815)
                  ·
                    rfl

theorem cell21_1505827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 3, 3].length) (baseStart_1505827 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1505827 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1505827 prefixEnd_1505827 := by exact prefixLift 1505827
  have htrace : WordTrace (prefixWord ++ tailWord_1505827) baseStart_1505827 baseEnd_1505827 := by
    simpa [prefixWord, tailWord_1505827, baseEnd_1505827] using wordTrace_append hprefix tailTrace_1505827
  have hstable : (prefixWord ++ tailWord_1505827).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505827).length < 2 ^ (prefixWord ++ tailWord_1505827).sum := by decide
  have hdescent : baseEnd_1505827 < baseStart_1505827 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505900 : List Nat := [2, 2, 1, 1, 3, 1, 3, 4, 4]
def baseStart_1505900 : Nat := 118140960795 + 1505900 * 2 ^ 59
def prefixEnd_1505900 : Nat := 4983230072969 + 3 ^ 40 * 1505900 * 2
def baseEnd_1505900 : Nat := 343666896713672619121999

theorem tailTrace_1505900 : CollatzResearch.WordTrace tailWord_1505900 prefixEnd_1505900 343666896713672619121999 := by
  unfold tailWord_1505900
  simp only [CollatzResearch.WordTrace]
  refine ⟨27462342622194481044693577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36616456829592641392924769 27462342622194481044693577)
  ·
    refine ⟨20596756966645860783520183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27462342622194481044693577 20596756966645860783520183)
    ·
      refine ⟨30895135449968791175280275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20596756966645860783520183 30895135449968791175280275)
      ·
        refine ⟨46342703174953186762920413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30895135449968791175280275 46342703174953186762920413)
        ·
          refine ⟨17378513690607445036095155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46342703174953186762920413 17378513690607445036095155)
          ·
            refine ⟨26067770535911167554142733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17378513690607445036095155 26067770535911167554142733)
            ·
              refine ⟨9775413950966687832803525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26067770535911167554142733 9775413950966687832803525)
              ·
                refine ⟨1832890115806253968650661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9775413950966687832803525 1832890115806253968650661)
                ·
                  refine ⟨343666896713672619121999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1832890115806253968650661 343666896713672619121999)
                  ·
                    rfl

theorem cell21_1505900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 4].length) (baseStart_1505900 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1505900 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1505900 prefixEnd_1505900 := by exact prefixLift 1505900
  have htrace : WordTrace (prefixWord ++ tailWord_1505900) baseStart_1505900 baseEnd_1505900 := by
    simpa [prefixWord, tailWord_1505900, baseEnd_1505900] using wordTrace_append hprefix tailTrace_1505900
  have hstable : (prefixWord ++ tailWord_1505900).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505900).length < 2 ^ (prefixWord ++ tailWord_1505900).sum := by decide
  have hdescent : baseEnd_1505900 < baseStart_1505900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505903 : List Nat := [1, 1, 2, 1, 3, 2, 6, 2, 3]
def baseStart_1505903 : Nat := 118140960795 + 1505903 * 2 ^ 59
def prefixEnd_1505903 : Nat := 4983230072969 + 3 ^ 40 * 1505903 * 2
def baseEnd_1505903 : Nat := 343667581354545280571993

theorem tailTrace_1505903 : CollatzResearch.WordTrace tailWord_1505903 prefixEnd_1505903 343667581354545280571993 := by
  unfold tailWord_1505903
  simp only [CollatzResearch.WordTrace]
  refine ⟨54924794663378093601746363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36616529775585395734497575 54924794663378093601746363)
  ·
    refine ⟨82387191995067140402619545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54924794663378093601746363 82387191995067140402619545)
    ·
      refine ⟨61790393996300355301964659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82387191995067140402619545 61790393996300355301964659)
      ·
        refine ⟨92685590994450532952946989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61790393996300355301964659 92685590994450532952946989)
        ·
          refine ⟨34757096622918949857355121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92685590994450532952946989 34757096622918949857355121)
          ·
            refine ⟨26067822467189212393016341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34757096622918949857355121 26067822467189212393016341)
            ·
              refine ⟨1221929178149494330922641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 26067822467189212393016341 1221929178149494330922641)
              ·
                refine ⟨916446883612120748191981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1221929178149494330922641 916446883612120748191981)
                ·
                  refine ⟨343667581354545280571993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 916446883612120748191981 343667581354545280571993)
                  ·
                    rfl

theorem cell21_1505903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 6, 2, 3].length) (baseStart_1505903 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1505903 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1505903 prefixEnd_1505903 := by exact prefixLift 1505903
  have htrace : WordTrace (prefixWord ++ tailWord_1505903) baseStart_1505903 baseEnd_1505903 := by
    simpa [prefixWord, tailWord_1505903, baseEnd_1505903] using wordTrace_append hprefix tailTrace_1505903
  have hstable : (prefixWord ++ tailWord_1505903).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505903).length < 2 ^ (prefixWord ++ tailWord_1505903).sum := by decide
  have hdescent : baseEnd_1505903 < baseStart_1505903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505996 : List Nat := [2, 2, 1, 5, 1, 3, 1, 3, 3]
def baseStart_1505996 : Nat := 118140960795 + 1505996 * 2 ^ 59
def prefixEnd_1505996 : Nat := 4983230072969 + 3 ^ 40 * 1505996 * 2
def baseEnd_1505996 : Nat := 343688805221597785521803

theorem tailTrace_1505996 : CollatzResearch.WordTrace tailWord_1505996 prefixEnd_1505996 343688805221597785521803 := by
  unfold tailWord_1505996
  simp only [CollatzResearch.WordTrace]
  refine ⟨27464093326020585242440921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36618791101360780323254561 27464093326020585242440921)
  ·
    refine ⟨20598069994515438931830691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27464093326020585242440921 20598069994515438931830691)
    ·
      refine ⟨30897104991773158397746037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20598069994515438931830691 30897104991773158397746037)
      ·
        refine ⟨2896603592978733599788691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30897104991773158397746037 2896603592978733599788691)
        ·
          refine ⟨4344905389468100399683037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2896603592978733599788691 4344905389468100399683037)
          ·
            refine ⟨1629339521050537649881139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4344905389468100399683037 1629339521050537649881139)
            ·
              refine ⟨2444009281575806474821709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1629339521050537649881139 2444009281575806474821709)
              ·
                refine ⟨916503480590927428058141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2444009281575806474821709 916503480590927428058141)
                ·
                  refine ⟨343688805221597785521803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 916503480590927428058141 343688805221597785521803)
                  ·
                    rfl

theorem cell21_1505996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 3, 3].length) (baseStart_1505996 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1505996 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1505996 prefixEnd_1505996 := by exact prefixLift 1505996
  have htrace : WordTrace (prefixWord ++ tailWord_1505996) baseStart_1505996 baseEnd_1505996 := by
    simpa [prefixWord, tailWord_1505996, baseEnd_1505996] using wordTrace_append hprefix tailTrace_1505996
  have hstable : (prefixWord ++ tailWord_1505996).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505996).length < 2 ^ (prefixWord ++ tailWord_1505996).sum := by decide
  have hdescent : baseEnd_1505996 < baseStart_1505996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506097 : List Nat := [1, 2, 2, 3, 2, 1, 3, 2, 5]
def baseStart_1506097 : Nat := 118140960795 + 1506097 * 2 ^ 59
def prefixEnd_1506097 : Nat := 4983230072969 + 3 ^ 40 * 1506097 * 2
def baseEnd_1506097 : Nat := 343711854797644054338263

theorem tailTrace_1506097 : CollatzResearch.WordTrace tailWord_1506097 prefixEnd_1506097 343711854797644054338263 := by
  unfold tailWord_1506097
  simp only [CollatzResearch.WordTrace]
  refine ⟨54931870424675264734308545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36621246949783509822872363 54931870424675264734308545)
  ·
    refine ⟨41198902818506448550731409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54931870424675264734308545 41198902818506448550731409)
    ·
      refine ⟨30899177113879836413048557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41198902818506448550731409 30899177113879836413048557)
      ·
        refine ⟨11587191417704938654893209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30899177113879836413048557 11587191417704938654893209)
        ·
          refine ⟨8690393563278703991169907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11587191417704938654893209 8690393563278703991169907)
          ·
            refine ⟨13035590344918055986754861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8690393563278703991169907 13035590344918055986754861)
            ·
              refine ⟨4888346379344270995033073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13035590344918055986754861 4888346379344270995033073)
              ·
                refine ⟨3666259784508203246274805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4888346379344270995033073 3666259784508203246274805)
                ·
                  refine ⟨343711854797644054338263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3666259784508203246274805 343711854797644054338263)
                  ·
                    rfl

theorem cell21_1506097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 2, 5].length) (baseStart_1506097 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1506097 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1506097 prefixEnd_1506097 := by exact prefixLift 1506097
  have htrace : WordTrace (prefixWord ++ tailWord_1506097) baseStart_1506097 baseEnd_1506097 := by
    simpa [prefixWord, tailWord_1506097, baseEnd_1506097] using wordTrace_append hprefix tailTrace_1506097
  have hstable : (prefixWord ++ tailWord_1506097).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506097).length < 2 ^ (prefixWord ++ tailWord_1506097).sum := by decide
  have hdescent : baseEnd_1506097 < baseStart_1506097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506128 : List Nat := [2, 1, 1, 1, 1, 4, 5, 2, 4]
def baseStart_1506128 : Nat := 118140960795 + 1506128 * 2 ^ 59
def prefixEnd_1506128 : Nat := 4983230072969 + 3 ^ 40 * 1506128 * 2
def baseEnd_1506128 : Nat := 343718929419994889321533

theorem tailTrace_1506128 : CollatzResearch.WordTrace tailWord_1506128 prefixEnd_1506128 343718929419994889321533 := by
  unfold tailWord_1506128
  simp only [CollatzResearch.WordTrace]
  refine ⟨27466500543781478514343519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36622000725041971352458025 27466500543781478514343519)
  ·
    refine ⟨41199750815672217771515279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27466500543781478514343519 41199750815672217771515279)
    ·
      refine ⟨61799626223508326657272919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41199750815672217771515279 61799626223508326657272919)
      ·
        refine ⟨92699439335262489985909379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61799626223508326657272919 92699439335262489985909379)
        ·
          refine ⟨139049159002893734978864069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92699439335262489985909379 139049159002893734978864069)
          ·
            refine ⟨26071717313042575308537013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 139049159002893734978864069 26071717313042575308537013)
            ·
              refine ⟨2444223498097741435175345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26071717313042575308537013 2444223498097741435175345)
              ·
                refine ⟨1833167623573306076381509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2444223498097741435175345 1833167623573306076381509)
                ·
                  refine ⟨343718929419994889321533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1833167623573306076381509 343718929419994889321533)
                  ·
                    rfl

theorem cell21_1506128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 2, 4].length) (baseStart_1506128 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1506128 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1506128 prefixEnd_1506128 := by exact prefixLift 1506128
  have htrace : WordTrace (prefixWord ++ tailWord_1506128) baseStart_1506128 baseEnd_1506128 := by
    simpa [prefixWord, tailWord_1506128, baseEnd_1506128] using wordTrace_append hprefix tailTrace_1506128
  have hstable : (prefixWord ++ tailWord_1506128).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506128).length < 2 ^ (prefixWord ++ tailWord_1506128).sum := by decide
  have hdescent : baseEnd_1506128 < baseStart_1506128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506187 : List Nat := [1, 1, 1, 1, 4, 2, 4, 1, 6]
def baseStart_1506187 : Nat := 118140960795 + 1506187 * 2 ^ 59
def prefixEnd_1506187 : Nat := 4983230072969 + 3 ^ 40 * 1506187 * 2
def baseEnd_1506187 : Nat := 343732394023823897838079

theorem tailTrace_1506187 : CollatzResearch.WordTrace tailWord_1506187 prefixEnd_1506187 343732394023823897838079 := by
  unfold tailWord_1506187
  simp only [CollatzResearch.WordTrace]
  refine ⟨54935152994349210105084815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36623435329566140070056543 54935152994349210105084815)
  ·
    refine ⟨82402729491523815157627223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54935152994349210105084815 82402729491523815157627223)
    ·
      refine ⟨123604094237285722736440835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82402729491523815157627223 123604094237285722736440835)
      ·
        refine ⟨185406141355928584104661253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123604094237285722736440835 185406141355928584104661253)
        ·
          refine ⟨34763651504236609519623985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 185406141355928584104661253 34763651504236609519623985)
          ·
            refine ⟨26072738628177457139717989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34763651504236609519623985 26072738628177457139717989)
            ·
              refine ⟨4888638492783273213697123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26072738628177457139717989 4888638492783273213697123)
              ·
                refine ⟨7332957739174909820545685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4888638492783273213697123 7332957739174909820545685)
                ·
                  refine ⟨343732394023823897838079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7332957739174909820545685 343732394023823897838079)
                  ·
                    rfl

theorem cell21_1506187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 1, 6].length) (baseStart_1506187 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1506187 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1506187 prefixEnd_1506187 := by exact prefixLift 1506187
  have htrace : WordTrace (prefixWord ++ tailWord_1506187) baseStart_1506187 baseEnd_1506187 := by
    simpa [prefixWord, tailWord_1506187, baseEnd_1506187] using wordTrace_append hprefix tailTrace_1506187
  have hstable : (prefixWord ++ tailWord_1506187).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506187).length < 2 ^ (prefixWord ++ tailWord_1506187).sum := by decide
  have hdescent : baseEnd_1506187 < baseStart_1506187 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506325 : List Nat := [1, 3, 2, 1, 4, 1, 2, 2, 5]
def baseStart_1506325 : Nat := 118140960795 + 1506325 * 2 ^ 59
def prefixEnd_1506325 : Nat := 4983230072969 + 3 ^ 40 * 1506325 * 2
def baseEnd_1506325 : Nat := 343763887503966324537797

theorem tailTrace_1506325 : CollatzResearch.WordTrace tailWord_1506325 prefixEnd_1506325 343763887503966324537797 := by
  unfold tailWord_1506325
  simp only [CollatzResearch.WordTrace]
  refine ⟨54940186267849259673608429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36626790845232839782405619 54940186267849259673608429)
  ·
    refine ⟨20602569850443472377603161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54940186267849259673608429 20602569850443472377603161)
    ·
      refine ⟨15451927387832604283202371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20602569850443472377603161 15451927387832604283202371)
      ·
        refine ⟨23177891081748906424803557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15451927387832604283202371 23177891081748906424803557)
        ·
          refine ⟨4345854577827919954650667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23177891081748906424803557 4345854577827919954650667)
          ·
            refine ⟨6518781866741879931976001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4345854577827919954650667 6518781866741879931976001)
            ·
              refine ⟨4889086400056409948982001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6518781866741879931976001 4889086400056409948982001)
              ·
                refine ⟨3666814800042307461736501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4889086400056409948982001 3666814800042307461736501)
                ·
                  refine ⟨343763887503966324537797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3666814800042307461736501 343763887503966324537797)
                  ·
                    rfl

theorem cell21_1506325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 2, 5].length) (baseStart_1506325 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1506325 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1506325 prefixEnd_1506325 := by exact prefixLift 1506325
  have htrace : WordTrace (prefixWord ++ tailWord_1506325) baseStart_1506325 baseEnd_1506325 := by
    simpa [prefixWord, tailWord_1506325, baseEnd_1506325] using wordTrace_append hprefix tailTrace_1506325
  have hstable : (prefixWord ++ tailWord_1506325).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506325).length < 2 ^ (prefixWord ++ tailWord_1506325).sum := by decide
  have hdescent : baseEnd_1506325 < baseStart_1506325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506339 : List Nat := [1, 1, 1, 4, 3, 2, 1, 2, 6]
def baseStart_1506339 : Nat := 118140960795 + 1506339 * 2 ^ 59
def prefixEnd_1506339 : Nat := 4983230072969 + 3 ^ 40 * 1506339 * 2
def baseEnd_1506339 : Nat := 343767082494705411304435

theorem tailTrace_1506339 : CollatzResearch.WordTrace tailWord_1506339 prefixEnd_1506339 343767082494705411304435 := by
  unfold tailWord_1506339
  simp only [CollatzResearch.WordTrace]
  refine ⟨54940696889798540064618071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36627131259865693376412047 54940696889798540064618071)
  ·
    refine ⟨82411045334697810096927107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54940696889798540064618071 82411045334697810096927107)
    ·
      refine ⟨123616568002046715145390661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82411045334697810096927107 123616568002046715145390661)
      ·
        refine ⟨23178106500383759089760749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123616568002046715145390661 23178106500383759089760749)
        ·
          refine ⟨8691789937643909658660281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23178106500383759089760749 8691789937643909658660281)
          ·
            refine ⟨6518842453232932243995211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8691789937643909658660281 6518842453232932243995211)
            ·
              refine ⟨9778263679849398365992817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6518842453232932243995211 9778263679849398365992817)
              ·
                refine ⟨7333697759887048774494613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9778263679849398365992817 7333697759887048774494613)
                ·
                  refine ⟨343767082494705411304435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7333697759887048774494613 343767082494705411304435)
                  ·
                    rfl

theorem cell21_1506339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 2, 6].length) (baseStart_1506339 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1506339 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1506339 prefixEnd_1506339 := by exact prefixLift 1506339
  have htrace : WordTrace (prefixWord ++ tailWord_1506339) baseStart_1506339 baseEnd_1506339 := by
    simpa [prefixWord, tailWord_1506339, baseEnd_1506339] using wordTrace_append hprefix tailTrace_1506339
  have hstable : (prefixWord ++ tailWord_1506339).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506339).length < 2 ^ (prefixWord ++ tailWord_1506339).sum := by decide
  have hdescent : baseEnd_1506339 < baseStart_1506339 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506384 : List Nat := [2, 1, 1, 1, 1, 3, 1, 6, 5]
def baseStart_1506384 : Nat := 118140960795 + 1506384 * 2 ^ 59
def prefixEnd_1506384 : Nat := 4983230072969 + 3 ^ 40 * 1506384 * 2
def baseEnd_1506384 : Nat := 343777352107795333054343

theorem tailTrace_1506384 : CollatzResearch.WordTrace tailWord_1506384 prefixEnd_1506384 343777352107795333054343 := by
  unfold tailWord_1506384
  simp only [CollatzResearch.WordTrace]
  refine ⟨27471169087317756375003103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36628225449757008500004137 27471169087317756375003103)
  ·
    refine ⟨41206753630976634562504655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27471169087317756375003103 41206753630976634562504655)
    ·
      refine ⟨61810130446464951843756983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41206753630976634562504655 61810130446464951843756983)
      ·
        refine ⟨92715195669697427765635475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61810130446464951843756983 92715195669697427765635475)
        ·
          refine ⟨139072793504546141648453213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92715195669697427765635475 139072793504546141648453213)
          ·
            refine ⟨52152297564204803118169955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139072793504546141648453213 52152297564204803118169955)
            ·
              refine ⟨78228446346307204677254933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52152297564204803118169955 78228446346307204677254933)
              ·
                refine ⟨3666958422483150219246325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 78228446346307204677254933 3666958422483150219246325)
                ·
                  refine ⟨343777352107795333054343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3666958422483150219246325 343777352107795333054343)
                  ·
                    rfl

theorem cell21_1506384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 6, 5].length) (baseStart_1506384 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1506384 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1506384 prefixEnd_1506384 := by exact prefixLift 1506384
  have htrace : WordTrace (prefixWord ++ tailWord_1506384) baseStart_1506384 baseEnd_1506384 := by
    simpa [prefixWord, tailWord_1506384, baseEnd_1506384] using wordTrace_append hprefix tailTrace_1506384
  have hstable : (prefixWord ++ tailWord_1506384).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506384).length < 2 ^ (prefixWord ++ tailWord_1506384).sum := by decide
  have hdescent : baseEnd_1506384 < baseStart_1506384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506418 : List Nat := [3, 2, 1, 2, 2, 1, 3, 4, 3]
def baseStart_1506418 : Nat := 118140960795 + 1506418 * 2 ^ 59
def prefixEnd_1506418 : Nat := 4983230072969 + 3 ^ 40 * 1506418 * 2
def baseEnd_1506418 : Nat := 343785111371018829487607

theorem tailTrace_1506418 : CollatzResearch.WordTrace tailWord_1506418 prefixEnd_1506418 343785111371018829487607 := by
  unfold tailWord_1506418
  simp only [CollatzResearch.WordTrace]
  refine ⟨13735894564128084139185977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36629052171008224371162605 13735894564128084139185977)
  ·
    refine ⟨10301920923096063104389483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13735894564128084139185977 10301920923096063104389483)
    ·
      refine ⟨15452881384644094656584225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10301920923096063104389483 15452881384644094656584225)
      ·
        refine ⟨11589661038483070992438169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15452881384644094656584225 11589661038483070992438169)
        ·
          refine ⟨8692245778862303244328627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11589661038483070992438169 8692245778862303244328627)
          ·
            refine ⟨13038368668293454866492941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8692245778862303244328627 13038368668293454866492941)
            ·
              refine ⟨4889388250610045574934853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13038368668293454866492941 4889388250610045574934853)
              ·
                refine ⟨916760296989383545300285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4889388250610045574934853 916760296989383545300285)
                ·
                  refine ⟨343785111371018829487607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 916760296989383545300285 343785111371018829487607)
                  ·
                    rfl

theorem cell21_1506418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 4, 3].length) (baseStart_1506418 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1506418 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1506418 prefixEnd_1506418 := by exact prefixLift 1506418
  have htrace : WordTrace (prefixWord ++ tailWord_1506418) baseStart_1506418 baseEnd_1506418 := by
    simpa [prefixWord, tailWord_1506418, baseEnd_1506418] using wordTrace_append hprefix tailTrace_1506418
  have hstable : (prefixWord ++ tailWord_1506418).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506418).length < 2 ^ (prefixWord ++ tailWord_1506418).sum := by decide
  have hdescent : baseEnd_1506418 < baseStart_1506418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506421 : List Nat := [1, 3, 4, 3, 2, 1, 1, 6]
def baseStart_1506421 : Nat := 118140960795 + 1506421 * 2 ^ 59
def prefixEnd_1506421 : Nat := 4983230072969 + 3 ^ 40 * 1506421 * 2
def baseEnd_1506421 : Nat := 114595265337297163645867

theorem tailTrace_1506421 : CollatzResearch.WordTrace tailWord_1506421 prefixEnd_1506421 114595265337297163645867 := by
  unfold tailWord_1506421
  simp only [CollatzResearch.WordTrace]
  refine ⟨54943687675501468069103117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36629125117000978712735411 54943687675501468069103117)
  ·
    refine ⟨20603882878313050525913669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54943687675501468069103117 20603882878313050525913669)
    ·
      refine ⟨3863228039683696973608813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20603882878313050525913669 3863228039683696973608813)
      ·
        refine ⟨1448710514881386365103305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3863228039683696973608813 1448710514881386365103305)
        ·
          refine ⟨1086532886161039773827479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1448710514881386365103305 1086532886161039773827479)
          ·
            refine ⟨1629799329241559660741219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1086532886161039773827479 1629799329241559660741219)
            ·
              refine ⟨2444698993862339491111829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1629799329241559660741219 2444698993862339491111829)
              ·
                refine ⟨114595265337297163645867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2444698993862339491111829 114595265337297163645867)
                ·
                  rfl

theorem cell21_1506421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 6].length) (baseStart_1506421 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1506421 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1506421 prefixEnd_1506421 := by exact prefixLift 1506421
  have htrace : WordTrace (prefixWord ++ tailWord_1506421) baseStart_1506421 baseEnd_1506421 := by
    simpa [prefixWord, tailWord_1506421, baseEnd_1506421] using wordTrace_append hprefix tailTrace_1506421
  have hstable : (prefixWord ++ tailWord_1506421).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506421).length < 2 ^ (prefixWord ++ tailWord_1506421).sum := by decide
  have hdescent : baseEnd_1506421 < baseStart_1506421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506466 : List Nat := [3, 3, 1, 3, 2, 2, 1, 2, 4]
def baseStart_1506466 : Nat := 118140960795 + 1506466 * 2 ^ 59
def prefixEnd_1506466 : Nat := 4983230072969 + 3 ^ 40 * 1506466 * 2
def baseEnd_1506466 : Nat := 343796065624981412687509

theorem tailTrace_1506466 : CollatzResearch.WordTrace tailWord_1506466 prefixEnd_1506466 343796065624981412687509 := by
  unfold tailWord_1506466
  simp only [CollatzResearch.WordTrace]
  refine ⟨13736332240084610188622813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36630219306892293836327501 13736332240084610188622813)
  ·
    refine ⟨5151124590031728820733555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13736332240084610188622813 5151124590031728820733555)
    ·
      refine ⟨7726686885047593231100333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5151124590031728820733555 7726686885047593231100333)
      ·
        refine ⟨2897507581892847461662625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7726686885047593231100333 2897507581892847461662625)
        ·
          refine ⟨2173130686419635596246969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2897507581892847461662625 2173130686419635596246969)
          ·
            refine ⟨1629848014814726697185227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2173130686419635596246969 1629848014814726697185227)
            ·
              refine ⟨2444772022222090045777841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1629848014814726697185227 2444772022222090045777841)
              ·
                refine ⟨1833579016666567534333381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2444772022222090045777841 1833579016666567534333381)
                ·
                  refine ⟨343796065624981412687509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1833579016666567534333381 343796065624981412687509)
                  ·
                    rfl

theorem cell21_1506466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_1506466 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1506466 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1506466 prefixEnd_1506466 := by exact prefixLift 1506466
  have htrace : WordTrace (prefixWord ++ tailWord_1506466) baseStart_1506466 baseEnd_1506466 := by
    simpa [prefixWord, tailWord_1506466, baseEnd_1506466] using wordTrace_append hprefix tailTrace_1506466
  have hstable : (prefixWord ++ tailWord_1506466).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506466).length < 2 ^ (prefixWord ++ tailWord_1506466).sum := by decide
  have hdescent : baseEnd_1506466 < baseStart_1506466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506584 : List Nat := [2, 1, 2, 3, 1, 4, 2, 2, 4]
def baseStart_1506584 : Nat := 118140960795 + 1506584 * 2 ^ 59
def prefixEnd_1506584 : Nat := 4983230072969 + 3 ^ 40 * 1506584 * 2
def baseEnd_1506584 : Nat := 343822994832639429720601

theorem tailTrace_1506584 : CollatzResearch.WordTrace tailWord_1506584 prefixEnd_1506584 343822994832639429720601 := by
  unfold tailWord_1506584
  simp only [CollatzResearch.WordTrace]
  refine ⟨27474816386955473453643403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36633088515940631271524537 27474816386955473453643403)
  ·
    refine ⟨41212224580433210180465105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27474816386955473453643403 41212224580433210180465105)
    ·
      refine ⟨30909168435324907635348829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41212224580433210180465105 30909168435324907635348829)
      ·
        refine ⟨11590938163246840363255811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30909168435324907635348829 11590938163246840363255811)
        ·
          refine ⟨17386407244870260544883717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11590938163246840363255811 17386407244870260544883717)
          ·
            refine ⟨3259951358413173852165697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17386407244870260544883717 3259951358413173852165697)
            ·
              refine ⟨2444963518809880389124273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3259951358413173852165697 2444963518809880389124273)
              ·
                refine ⟨1833722639107410291843205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2444963518809880389124273 1833722639107410291843205)
                ·
                  refine ⟨343822994832639429720601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1833722639107410291843205 343822994832639429720601)
                  ·
                    rfl

theorem cell21_1506584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 2, 4].length) (baseStart_1506584 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1506584 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1506584 prefixEnd_1506584 := by exact prefixLift 1506584
  have htrace : WordTrace (prefixWord ++ tailWord_1506584) baseStart_1506584 baseEnd_1506584 := by
    simpa [prefixWord, tailWord_1506584, baseEnd_1506584] using wordTrace_append hprefix tailTrace_1506584
  have hstable : (prefixWord ++ tailWord_1506584).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506584).length < 2 ^ (prefixWord ++ tailWord_1506584).sum := by decide
  have hdescent : baseEnd_1506584 < baseStart_1506584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506756 : List Nat := [2, 3, 3, 2, 1, 3, 2, 2, 3]
def baseStart_1506756 : Nat := 118140960795 + 1506756 * 2 ^ 59
def prefixEnd_1506756 : Nat := 4983230072969 + 3 ^ 40 * 1506756 * 2
def baseEnd_1506756 : Nat := 343862247576005352853583

theorem tailTrace_1506756 : CollatzResearch.WordTrace tailWord_1506756 prefixEnd_1506756 343862247576005352853583 := by
  unfold tailWord_1506756
  simp only [CollatzResearch.WordTrace]
  refine ⟨27477953064643910141274061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36637270752858546855032081 27477953064643910141274061)
  ·
    refine ⟨10304232399241466302977773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27477953064643910141274061 10304232399241466302977773)
    ·
      refine ⟨3864087149715549863616665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10304232399241466302977773 3864087149715549863616665)
      ·
        refine ⟨2898065362286662397712499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3864087149715549863616665 2898065362286662397712499)
        ·
          refine ⟨4347098043429993596568749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2898065362286662397712499 4347098043429993596568749)
          ·
            refine ⟨1630161766286247598713281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4347098043429993596568749 1630161766286247598713281)
            ·
              refine ⟨1222621324714685699034961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1630161766286247598713281 1222621324714685699034961)
              ·
                refine ⟨916965993536014274276221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1222621324714685699034961 916965993536014274276221)
                ·
                  refine ⟨343862247576005352853583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 916965993536014274276221 343862247576005352853583)
                  ·
                    rfl

theorem cell21_1506756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 2, 2, 3].length) (baseStart_1506756 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1506756 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1506756 prefixEnd_1506756 := by exact prefixLift 1506756
  have htrace : WordTrace (prefixWord ++ tailWord_1506756) baseStart_1506756 baseEnd_1506756 := by
    simpa [prefixWord, tailWord_1506756, baseEnd_1506756] using wordTrace_append hprefix tailTrace_1506756
  have hstable : (prefixWord ++ tailWord_1506756).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506756).length < 2 ^ (prefixWord ++ tailWord_1506756).sum := by decide
  have hdescent : baseEnd_1506756 < baseStart_1506756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506781 : List Nat := [1, 4, 3, 1, 1, 3, 1, 2, 5]
def baseStart_1506781 : Nat := 118140960795 + 1506781 * 2 ^ 59
def prefixEnd_1506781 : Nat := 4983230072969 + 3 ^ 40 * 1506781 * 2
def baseEnd_1506781 : Nat := 343867952916610864936865

theorem tailTrace_1506781 : CollatzResearch.WordTrace tailWord_1506781 prefixEnd_1506781 343867952916610864936865 := by
  unfold tailWord_1506781
  simp only [CollatzResearch.WordTrace]
  refine ⟨54956817954197249552208197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36637878636131499701472131 54956817954197249552208197)
  ·
    refine ⟨10304403366411984291039037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54956817954197249552208197 10304403366411984291039037)
    ·
      refine ⟨3864151262404494109139639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10304403366411984291039037 3864151262404494109139639)
      ·
        refine ⟨5796226893606741163709459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3864151262404494109139639 5796226893606741163709459)
        ·
          refine ⟨8694340340410111745564189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5796226893606741163709459 8694340340410111745564189)
          ·
            refine ⟨3260377627653791904586571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8694340340410111745564189 3260377627653791904586571)
            ·
              refine ⟨4890566441480687856879857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3260377627653791904586571 4890566441480687856879857)
              ·
                refine ⟨3667924831110515892659893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4890566441480687856879857 3667924831110515892659893)
                ·
                  refine ⟨343867952916610864936865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3667924831110515892659893 343867952916610864936865)
                  ·
                    rfl

theorem cell21_1506781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 2, 5].length) (baseStart_1506781 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1506781 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1506781 prefixEnd_1506781 := by exact prefixLift 1506781
  have htrace : WordTrace (prefixWord ++ tailWord_1506781) baseStart_1506781 baseEnd_1506781 := by
    simpa [prefixWord, tailWord_1506781, baseEnd_1506781] using wordTrace_append hprefix tailTrace_1506781
  have hstable : (prefixWord ++ tailWord_1506781).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506781).length < 2 ^ (prefixWord ++ tailWord_1506781).sum := by decide
  have hdescent : baseEnd_1506781 < baseStart_1506781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506798 : List Nat := [4, 1, 2, 1, 2, 1, 4, 3, 3]
def baseStart_1506798 : Nat := 118140960795 + 1506798 * 2 ^ 59
def prefixEnd_1506798 : Nat := 4983230072969 + 3 ^ 40 * 1506798 * 2
def baseEnd_1506798 : Nat := 343871832548222613153497

theorem tailTrace_1506798 : CollatzResearch.WordTrace tailWord_1506798 prefixEnd_1506798 343871832548222613153497 := by
  unfold tailWord_1506798
  simp only [CollatzResearch.WordTrace]
  refine ⟨6869679749391957681947131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36638291996757107637051365 6869679749391957681947131)
  ·
    refine ⟨10304519624087936522920697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6869679749391957681947131 10304519624087936522920697)
    ·
      refine ⟨7728389718065952392190523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10304519624087936522920697 7728389718065952392190523)
      ·
        refine ⟨11592584577098928588285785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7728389718065952392190523 11592584577098928588285785)
        ·
          refine ⟨8694438432824196441214339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11592584577098928588285785 8694438432824196441214339)
          ·
            refine ⟨13041657649236294661821509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8694438432824196441214339 13041657649236294661821509)
            ·
              refine ⟨2445310809231805249091533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13041657649236294661821509 2445310809231805249091533)
              ·
                refine ⟨916991553461926968409325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2445310809231805249091533 916991553461926968409325)
                ·
                  refine ⟨343871832548222613153497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 916991553461926968409325 343871832548222613153497)
                  ·
                    rfl

theorem cell21_1506798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 3, 3].length) (baseStart_1506798 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1506798 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1506798 prefixEnd_1506798 := by exact prefixLift 1506798
  have htrace : WordTrace (prefixWord ++ tailWord_1506798) baseStart_1506798 baseEnd_1506798 := by
    simpa [prefixWord, tailWord_1506798, baseEnd_1506798] using wordTrace_append hprefix tailTrace_1506798
  have hstable : (prefixWord ++ tailWord_1506798).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506798).length < 2 ^ (prefixWord ++ tailWord_1506798).sum := by decide
  have hdescent : baseEnd_1506798 < baseStart_1506798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506874 : List Nat := [3, 1, 1, 1, 3, 2, 5, 2, 3]
def baseStart_1506874 : Nat := 118140960795 + 1506874 * 2 ^ 59
def prefixEnd_1506874 : Nat := 4983230072969 + 3 ^ 40 * 1506874 * 2
def baseEnd_1506874 : Nat := 343889176783663369886675

theorem tailTrace_1506874 : CollatzResearch.WordTrace tailWord_1506874 prefixEnd_1506874 343889176783663369886675 := by
  unfold tailWord_1506874
  simp only [CollatzResearch.WordTrace]
  refine ⟨13740052485715081608835919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36640139961906884290229117 13740052485715081608835919)
  ·
    refine ⟨20610078728572622413253879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13740052485715081608835919 20610078728572622413253879)
    ·
      refine ⟨30915118092858933619880819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20610078728572622413253879 30915118092858933619880819)
      ·
        refine ⟨46372677139288400429821229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30915118092858933619880819 46372677139288400429821229)
        ·
          refine ⟨17389753927233150161182961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46372677139288400429821229 17389753927233150161182961)
          ·
            refine ⟨13042315445424862620887221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17389753927233150161182961 13042315445424862620887221)
            ·
              refine ⟨1222717073008580870708177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13042315445424862620887221 1222717073008580870708177)
              ·
                refine ⟨917037804756435653031133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1222717073008580870708177 917037804756435653031133)
                ·
                  refine ⟨343889176783663369886675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 917037804756435653031133 343889176783663369886675)
                  ·
                    rfl

theorem cell21_1506874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 5, 2, 3].length) (baseStart_1506874 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1506874 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1506874 prefixEnd_1506874 := by exact prefixLift 1506874
  have htrace : WordTrace (prefixWord ++ tailWord_1506874) baseStart_1506874 baseEnd_1506874 := by
    simpa [prefixWord, tailWord_1506874, baseEnd_1506874] using wordTrace_append hprefix tailTrace_1506874
  have hstable : (prefixWord ++ tailWord_1506874).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506874).length < 2 ^ (prefixWord ++ tailWord_1506874).sum := by decide
  have hdescent : baseEnd_1506874 < baseStart_1506874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506885 : List Nat := [1, 3, 1, 1, 1, 4, 4, 6]
def baseStart_1506885 : Nat := 118140960795 + 1506885 * 2 ^ 59
def prefixEnd_1506885 : Nat := 4983230072969 + 3 ^ 40 * 1506885 * 2
def baseEnd_1506885 : Nat := 114630562377843265067773

theorem tailTrace_1506885 : CollatzResearch.WordTrace tailWord_1506885 prefixEnd_1506885 114630562377843265067773 := by
  unfold tailWord_1506885
  simp only [CollatzResearch.WordTrace]
  refine ⟨54960611145820475313994109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36640407430546983542662739 54960611145820475313994109)
  ·
    refine ⟨20610229179682678242747791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54960611145820475313994109 20610229179682678242747791)
    ·
      refine ⟨30915343769524017364121687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20610229179682678242747791 30915343769524017364121687)
      ·
        refine ⟨46373015654286026046182531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30915343769524017364121687 46373015654286026046182531)
        ·
          refine ⟨69559523481429039069273797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46373015654286026046182531 69559523481429039069273797)
          ·
            refine ⟨13042410652767944825488837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69559523481429039069273797 13042410652767944825488837)
            ·
              refine ⟨2445451997393989654779157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13042410652767944825488837 2445451997393989654779157)
              ·
                refine ⟨114630562377843265067773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2445451997393989654779157 114630562377843265067773)
                ·
                  rfl

theorem cell21_1506885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 6].length) (baseStart_1506885 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1506885 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1506885 prefixEnd_1506885 := by exact prefixLift 1506885
  have htrace : WordTrace (prefixWord ++ tailWord_1506885) baseStart_1506885 baseEnd_1506885 := by
    simpa [prefixWord, tailWord_1506885, baseEnd_1506885] using wordTrace_append hprefix tailTrace_1506885
  have hstable : (prefixWord ++ tailWord_1506885).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506885).length < 2 ^ (prefixWord ++ tailWord_1506885).sum := by decide
  have hdescent : baseEnd_1506885 < baseStart_1506885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506998 : List Nat := [5, 1, 3, 1, 1, 2, 3, 1, 4]
def baseStart_1506998 : Nat := 118140960795 + 1506998 * 2 ^ 59
def prefixEnd_1506998 : Nat := 4983230072969 + 3 ^ 40 * 1506998 * 2
def baseEnd_1506998 : Nat := 343917475273066709819755

theorem tailTrace_1506998 : CollatzResearch.WordTrace tailWord_1506998 prefixEnd_1506998 343917475273066709819755 := by
  unfold tailWord_1506998
  simp only [CollatzResearch.WordTrace]
  refine ⟨3435295787150693475803603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36643155062940730408571765 3435295787150693475803603)
  ·
    refine ⟨5152943680726040213705405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3435295787150693475803603 5152943680726040213705405)
    ·
      refine ⟨1932353880272265080139527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5152943680726040213705405 1932353880272265080139527)
      ·
        refine ⟨2898530820408397620209291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1932353880272265080139527 2898530820408397620209291)
        ·
          refine ⟨4347796230612596430313937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2898530820408397620209291 4347796230612596430313937)
          ·
            refine ⟨3260847172959447322735453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4347796230612596430313937 3260847172959447322735453)
            ·
              refine ⟨1222817689859792746025795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3260847172959447322735453 1222817689859792746025795)
              ·
                refine ⟨1834226534789689119038693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1222817689859792746025795 1834226534789689119038693)
                ·
                  refine ⟨343917475273066709819755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1834226534789689119038693 343917475273066709819755)
                  ·
                    rfl

theorem cell21_1506998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_1506998 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1506998 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1506998 prefixEnd_1506998 := by exact prefixLift 1506998
  have htrace : WordTrace (prefixWord ++ tailWord_1506998) baseStart_1506998 baseEnd_1506998 := by
    simpa [prefixWord, tailWord_1506998, baseEnd_1506998] using wordTrace_append hprefix tailTrace_1506998
  have hstable : (prefixWord ++ tailWord_1506998).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506998).length < 2 ^ (prefixWord ++ tailWord_1506998).sum := by decide
  have hdescent : baseEnd_1506998 < baseStart_1506998 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507026 : List Nat := [3, 2, 2, 2, 2, 1, 3, 3, 3]
def baseStart_1507026 : Nat := 118140960795 + 1507026 * 2 ^ 59
def prefixEnd_1507026 : Nat := 4983230072969 + 3 ^ 40 * 1507026 * 2
def baseEnd_1507026 : Nat := 343923865254544883353031

theorem tailTrace_1507026 : CollatzResearch.WordTrace tailWord_1507026 prefixEnd_1507026 343923865254544883353031 := by
  unfold tailWord_1507026
  simp only [CollatzResearch.WordTrace]
  refine ⟨13741438459577414098719233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36643835892206437596584621 13741438459577414098719233)
  ·
    refine ⟨10306078844683060574039425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13741438459577414098719233 10306078844683060574039425)
    ·
      refine ⟨7729559133512295430529569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10306078844683060574039425 7729559133512295430529569)
      ·
        refine ⟨5797169350134221572897177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7729559133512295430529569 5797169350134221572897177)
        ·
          refine ⟨4347877012600666179672883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5797169350134221572897177 4347877012600666179672883)
          ·
            refine ⟨6521815518900999269509325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4347877012600666179672883 6521815518900999269509325)
            ·
              refine ⟨2445680819587874726065997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6521815518900999269509325 2445680819587874726065997)
              ·
                refine ⟨917130307345453022274749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2445680819587874726065997 917130307345453022274749)
                ·
                  refine ⟨343923865254544883353031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 917130307345453022274749 343923865254544883353031)
                  ·
                    rfl

theorem cell21_1507026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 3, 3].length) (baseStart_1507026 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1507026 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1507026 prefixEnd_1507026 := by exact prefixLift 1507026
  have htrace : WordTrace (prefixWord ++ tailWord_1507026) baseStart_1507026 baseEnd_1507026 := by
    simpa [prefixWord, tailWord_1507026, baseEnd_1507026] using wordTrace_append hprefix tailTrace_1507026
  have hstable : (prefixWord ++ tailWord_1507026).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507026).length < 2 ^ (prefixWord ++ tailWord_1507026).sum := by decide
  have hdescent : baseEnd_1507026 < baseStart_1507026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507043 : List Nat := [1, 1, 1, 7, 2, 1, 3, 2, 3]
def baseStart_1507043 : Nat := 118140960795 + 1507043 * 2 ^ 59
def prefixEnd_1507043 : Nat := 4983230072969 + 3 ^ 40 * 1507043 * 2
def baseEnd_1507043 : Nat := 343927744886156631569663

theorem tailTrace_1507043 : CollatzResearch.WordTrace tailWord_1507043 prefixEnd_1507043 343927744886156631569663 := by
  unfold tailWord_1507043
  simp only [CollatzResearch.WordTrace]
  refine ⟨54966373879248068298245783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36644249252832045532163855 54966373879248068298245783)
  ·
    refine ⟨82449560818872102447368675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54966373879248068298245783 82449560818872102447368675)
    ·
      refine ⟨123674341228308153671053013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82449560818872102447368675 123674341228308153671053013)
      ·
        refine ⟨2898617372538472351665305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 123674341228308153671053013 2898617372538472351665305)
        ·
          refine ⟨2173963029403854263748979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2898617372538472351665305 2173963029403854263748979)
          ·
            refine ⟨3260944544105781395623469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2173963029403854263748979 3260944544105781395623469)
            ·
              refine ⟨1222854204039668023358801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3260944544105781395623469 1222854204039668023358801)
              ·
                refine ⟨917140653029751017519101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1222854204039668023358801 917140653029751017519101)
                ·
                  refine ⟨343927744886156631569663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 917140653029751017519101 343927744886156631569663)
                  ·
                    rfl

theorem cell21_1507043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 3, 2, 3].length) (baseStart_1507043 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1507043 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1507043 prefixEnd_1507043 := by exact prefixLift 1507043
  have htrace : WordTrace (prefixWord ++ tailWord_1507043) baseStart_1507043 baseEnd_1507043 := by
    simpa [prefixWord, tailWord_1507043, baseEnd_1507043] using wordTrace_append hprefix tailTrace_1507043
  have hstable : (prefixWord ++ tailWord_1507043).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507043).length < 2 ^ (prefixWord ++ tailWord_1507043).sum := by decide
  have hdescent : baseEnd_1507043 < baseStart_1507043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507130 : List Nat := [3, 1, 1, 1, 5, 2, 3, 5]
def baseStart_1507130 : Nat := 118140960795 + 1507130 * 2 ^ 59
def prefixEnd_1507130 : Nat := 4983230072969 + 3 ^ 40 * 1507130 * 2
def baseEnd_1507130 : Nat := 114649199823821271206495

theorem tailTrace_1507130 : CollatzResearch.WordTrace tailWord_1507130 prefixEnd_1507130 114649199823821271206495 := by
  unfold tailWord_1507130
  simp only [CollatzResearch.WordTrace]
  refine ⟨13742386757483220539165711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36646364686621921437775229 13742386757483220539165711)
  ·
    refine ⟨20613580136224830808748567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13742386757483220539165711 20613580136224830808748567)
    ·
      refine ⟨30920370204337246213122851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20613580136224830808748567 30920370204337246213122851)
      ·
        refine ⟨46380555306505869319684277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30920370204337246213122851 46380555306505869319684277)
        ·
          refine ⟨4348177059984925248720401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46380555306505869319684277 4348177059984925248720401)
          ·
            refine ⟨3261132794988693936540301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4348177059984925248720401 3261132794988693936540301)
            ·
              refine ⟨1222924798120760226202613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3261132794988693936540301 1222924798120760226202613)
              ·
                refine ⟨114649199823821271206495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1222924798120760226202613 114649199823821271206495)
                ·
                  rfl

theorem cell21_1507130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 3, 5].length) (baseStart_1507130 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1507130 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1507130 prefixEnd_1507130 := by exact prefixLift 1507130
  have htrace : WordTrace (prefixWord ++ tailWord_1507130) baseStart_1507130 baseEnd_1507130 := by
    simpa [prefixWord, tailWord_1507130, baseEnd_1507130] using wordTrace_append hprefix tailTrace_1507130
  have hstable : (prefixWord ++ tailWord_1507130).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507130).length < 2 ^ (prefixWord ++ tailWord_1507130).sum := by decide
  have hdescent : baseEnd_1507130 < baseStart_1507130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507189 : List Nat := [1, 3, 4, 1, 1, 1, 3, 7]
def baseStart_1507189 : Nat := 118140960795 + 1507189 * 2 ^ 59
def prefixEnd_1507189 : Nat := 4983230072969 + 3 ^ 40 * 1507189 * 2
def baseEnd_1507189 : Nat := 114653688025097607378677

theorem tailTrace_1507189 : CollatzResearch.WordTrace tailWord_1507189 prefixEnd_1507189 114653688025097607378677 := by
  unfold tailWord_1507189
  simp only [CollatzResearch.WordTrace]
  refine ⟨54971698936719135233060621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36647799291146090155373747 54971698936719135233060621)
  ·
    refine ⟨20614387101269675712397733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54971698936719135233060621 20614387101269675712397733)
    ·
      refine ⟨3865197581488064196074575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20614387101269675712397733 3865197581488064196074575)
      ·
        refine ⟨5797796372232096294111863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3865197581488064196074575 5797796372232096294111863)
        ·
          refine ⟨8696694558348144441167795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5797796372232096294111863 8696694558348144441167795)
          ·
            refine ⟨13045041837522216661751693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8696694558348144441167795 13045041837522216661751693)
            ·
              refine ⟨4891890689070831248156885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13045041837522216661751693 4891890689070831248156885)
              ·
                refine ⟨114653688025097607378677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4891890689070831248156885 114653688025097607378677)
                ·
                  rfl

theorem cell21_1507189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 7].length) (baseStart_1507189 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1507189 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1507189 prefixEnd_1507189 := by exact prefixLift 1507189
  have htrace : WordTrace (prefixWord ++ tailWord_1507189) baseStart_1507189 baseEnd_1507189 := by
    simpa [prefixWord, tailWord_1507189, baseEnd_1507189] using wordTrace_append hprefix tailTrace_1507189
  have hstable : (prefixWord ++ tailWord_1507189).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507189).length < 2 ^ (prefixWord ++ tailWord_1507189).sum := by decide
  have hdescent : baseEnd_1507189 < baseStart_1507189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507279 : List Nat := [1, 1, 2, 1, 1, 5, 2, 3, 5]
def baseStart_1507279 : Nat := 118140960795 + 1507279 * 2 ^ 59
def prefixEnd_1507279 : Nat := 4983230072969 + 3 ^ 40 * 1507279 * 2
def baseEnd_1507279 : Nat := 343981603301472665635847

theorem tailTrace_1507279 : CollatzResearch.WordTrace tailWord_1507279 prefixEnd_1507279 343981603301472665635847 := by
  unfold tailWord_1507279
  simp only [CollatzResearch.WordTrace]
  refine ⟨54974981506393080603836891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36649987670928720402557927 54974981506393080603836891)
  ·
    refine ⟨82462472259589620905755337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54974981506393080603836891 82462472259589620905755337)
    ·
      refine ⟨61846854194692215679316503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82462472259589620905755337 61846854194692215679316503)
      ·
        refine ⟨92770281292038323518974755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61846854194692215679316503 92770281292038323518974755)
        ·
          refine ⟨139155421938057485278462133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92770281292038323518974755 139155421938057485278462133)
          ·
            refine ⟨13045820806692889244855825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 139155421938057485278462133 13045820806692889244855825)
            ·
              refine ⟨9784365605019666933641869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13045820806692889244855825 9784365605019666933641869)
              ·
                refine ⟨3669137101882375100115701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9784365605019666933641869 3669137101882375100115701)
                ·
                  refine ⟨343981603301472665635847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3669137101882375100115701 343981603301472665635847)
                  ·
                    rfl

theorem cell21_1507279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 3, 5].length) (baseStart_1507279 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1507279 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1507279 prefixEnd_1507279 := by exact prefixLift 1507279
  have htrace : WordTrace (prefixWord ++ tailWord_1507279) baseStart_1507279 baseEnd_1507279 := by
    simpa [prefixWord, tailWord_1507279, baseEnd_1507279] using wordTrace_append hprefix tailTrace_1507279
  have hstable : (prefixWord ++ tailWord_1507279).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507279).length < 2 ^ (prefixWord ++ tailWord_1507279).sum := by decide
  have hdescent : baseEnd_1507279 < baseStart_1507279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507324 : List Nat := [2, 2, 2, 1, 2, 2, 10]
def baseStart_1507324 : Nat := 118140960795 + 1507324 * 2 ^ 59
def prefixEnd_1507324 : Nat := 4983230072969 + 3 ^ 40 * 1507324 * 2
def baseEnd_1507324 : Nat := 38221319212729176376195

theorem tailTrace_1507324 : CollatzResearch.WordTrace tailWord_1507324 prefixEnd_1507324 38221319212729176376195 := by
  unfold tailWord_1507324
  simp only [CollatzResearch.WordTrace]
  refine ⟨27488311395615026644612513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36651081860820035526150017 27488311395615026644612513)
  ·
    refine ⟨20616233546711269983459385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27488311395615026644612513 20616233546711269983459385)
    ·
      refine ⟨15462175160033452487594539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20616233546711269983459385 15462175160033452487594539)
      ·
        refine ⟨23193262740050178731391809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15462175160033452487594539 23193262740050178731391809)
        ·
          refine ⟨17394947055037634048543857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23193262740050178731391809 17394947055037634048543857)
          ·
            refine ⟨13046210291278225536407893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17394947055037634048543857 13046210291278225536407893)
            ·
              refine ⟨38221319212729176376195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13046210291278225536407893 38221319212729176376195)
              ·
                rfl

theorem cell21_1507324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 10].length) (baseStart_1507324 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1507324 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1507324 prefixEnd_1507324 := by exact prefixLift 1507324
  have htrace : WordTrace (prefixWord ++ tailWord_1507324) baseStart_1507324 baseEnd_1507324 := by
    simpa [prefixWord, tailWord_1507324, baseEnd_1507324] using wordTrace_append hprefix tailTrace_1507324
  have hstable : (prefixWord ++ tailWord_1507324).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507324).length < 2 ^ (prefixWord ++ tailWord_1507324).sum := by decide
  have hdescent : baseEnd_1507324 < baseStart_1507324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507372 : List Nat := [2, 2, 1, 1, 1, 2, 2, 7, 3]
def baseStart_1507372 : Nat := 118140960795 + 1507372 * 2 ^ 59
def prefixEnd_1507372 : Nat := 4983230072969 + 3 ^ 40 * 1507372 * 2
def baseEnd_1507372 : Nat := 344002827168525170585657

theorem tailTrace_1507372 : CollatzResearch.WordTrace tailWord_1507372 prefixEnd_1507372 344002827168525170585657 := by
  unfold tailWord_1507372
  simp only [CollatzResearch.WordTrace]
  refine ⟨27489186747528078743486185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36652248996704104991314913 27489186747528078743486185)
  ·
    refine ⟨20616890060646059057614639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27489186747528078743486185 20616890060646059057614639)
    ·
      refine ⟨30925335090969088586421959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20616890060646059057614639 30925335090969088586421959)
      ·
        refine ⟨46388002636453632879632939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30925335090969088586421959 46388002636453632879632939)
        ·
          refine ⟨69582003954680449319449409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46388002636453632879632939 69582003954680449319449409)
          ·
            refine ⟨52186502966010336989587057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69582003954680449319449409 52186502966010336989587057)
            ·
              refine ⟨39139877224507752742190293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52186502966010336989587057 39139877224507752742190293)
              ·
                refine ⟨917340872449400454895085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 39139877224507752742190293 917340872449400454895085)
                ·
                  refine ⟨344002827168525170585657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 917340872449400454895085 344002827168525170585657)
                  ·
                    rfl

theorem cell21_1507372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 7, 3].length) (baseStart_1507372 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1507372 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1507372 prefixEnd_1507372 := by exact prefixLift 1507372
  have htrace : WordTrace (prefixWord ++ tailWord_1507372) baseStart_1507372 baseEnd_1507372 := by
    simpa [prefixWord, tailWord_1507372, baseEnd_1507372] using wordTrace_append hprefix tailTrace_1507372
  have hstable : (prefixWord ++ tailWord_1507372).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507372).length < 2 ^ (prefixWord ++ tailWord_1507372).sum := by decide
  have hdescent : baseEnd_1507372 < baseStart_1507372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507386 : List Nat := [3, 1, 1, 1, 3, 1, 1, 6, 4]
def baseStart_1507386 : Nat := 118140960795 + 1507386 * 2 ^ 59
def prefixEnd_1507386 : Nat := 4983230072969 + 3 ^ 40 * 1507386 * 2
def baseEnd_1507386 : Nat := 344006022159264257352295

theorem tailTrace_1507386 : CollatzResearch.WordTrace tailWord_1507386 prefixEnd_1507386 344006022159264257352295 := by
  unfold tailWord_1507386
  simp only [CollatzResearch.WordTrace]
  refine ⟨13744721029251359469495503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36652589411336958585321341 13744721029251359469495503)
  ·
    refine ⟨20617081543877039204243255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13744721029251359469495503 20617081543877039204243255)
    ·
      refine ⟨30925622315815558806364883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20617081543877039204243255 30925622315815558806364883)
      ·
        refine ⟨46388433473723338209547325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30925622315815558806364883 46388433473723338209547325)
        ·
          refine ⟨17395662552646251828580247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46388433473723338209547325 17395662552646251828580247)
          ·
            refine ⟨26093493828969377742870371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17395662552646251828580247 26093493828969377742870371)
            ·
              refine ⟨39140240743454066614305557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26093493828969377742870371 39140240743454066614305557)
              ·
                refine ⟨1834698784849409372545573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 39140240743454066614305557 1834698784849409372545573)
                ·
                  refine ⟨344006022159264257352295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1834698784849409372545573 344006022159264257352295)
                  ·
                    rfl

theorem cell21_1507386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 6, 4].length) (baseStart_1507386 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1507386 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1507386 prefixEnd_1507386 := by exact prefixLift 1507386
  have htrace : WordTrace (prefixWord ++ tailWord_1507386) baseStart_1507386 baseEnd_1507386 := by
    simpa [prefixWord, tailWord_1507386, baseEnd_1507386] using wordTrace_append hprefix tailTrace_1507386
  have hstable : (prefixWord ++ tailWord_1507386).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507386).length < 2 ^ (prefixWord ++ tailWord_1507386).sum := by decide
  have hdescent : baseEnd_1507386 < baseStart_1507386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507482 : List Nat := [3, 1, 1, 5, 2, 1, 2, 3, 3]
def baseStart_1507482 : Nat := 118140960795 + 1507482 * 2 ^ 59
def prefixEnd_1507482 : Nat := 4983230072969 + 3 ^ 40 * 1507482 * 2
def baseEnd_1507482 : Nat := 344027930667189423752099

theorem tailTrace_1507482 : CollatzResearch.WordTrace tailWord_1507482 prefixEnd_1507482 344027930667189423752099 := by
  unfold tailWord_1507482
  simp only [CollatzResearch.WordTrace]
  refine ⟨13745596381164411568369175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36654923683105097515651133 13745596381164411568369175)
  ·
    refine ⟨20618394571746617352553763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13745596381164411568369175 20618394571746617352553763)
    ·
      refine ⟨30927591857619926028830645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20618394571746617352553763 30927591857619926028830645)
      ·
        refine ⟨2899461736651868065202873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30927591857619926028830645 2899461736651868065202873)
        ·
          refine ⟨2174596302488901048902155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2899461736651868065202873 2174596302488901048902155)
          ·
            refine ⟨3261894453733351573353233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2174596302488901048902155 3261894453733351573353233)
            ·
              refine ⟨2446420840300013680014925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3261894453733351573353233 2446420840300013680014925)
              ·
                refine ⟨917407815112505130005597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2446420840300013680014925 917407815112505130005597)
                ·
                  refine ⟨344027930667189423752099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 917407815112505130005597 344027930667189423752099)
                  ·
                    rfl

theorem cell21_1507482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 3, 3].length) (baseStart_1507482 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1507482 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1507482 prefixEnd_1507482 := by exact prefixLift 1507482
  have htrace : WordTrace (prefixWord ++ tailWord_1507482) baseStart_1507482 baseEnd_1507482 := by
    simpa [prefixWord, tailWord_1507482, baseEnd_1507482] using wordTrace_append hprefix tailTrace_1507482
  have hstable : (prefixWord ++ tailWord_1507482).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507482).length < 2 ^ (prefixWord ++ tailWord_1507482).sum := by decide
  have hdescent : baseEnd_1507482 < baseStart_1507482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507524 : List Nat := [2, 3, 3, 1, 2, 1, 2, 2, 5]
def baseStart_1507524 : Nat := 118140960795 + 1507524 * 2 ^ 59
def prefixEnd_1507524 : Nat := 4983230072969 + 3 ^ 40 * 1507524 * 2
def baseEnd_1507524 : Nat := 344037515639406684052013

theorem tailTrace_1507524 : CollatzResearch.WordTrace tailWord_1507524 prefixEnd_1507524 344037515639406684052013 := by
  unfold tailWord_1507524
  simp only [CollatzResearch.WordTrace]
  refine ⟨27491958695252743723252813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36655944927003658297670417 27491958695252743723252813)
  ·
    refine ⟨10309484510719778896219805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27491958695252743723252813 10309484510719778896219805)
    ·
      refine ⟨3866056691519917086082427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10309484510719778896219805 3866056691519917086082427)
      ·
        refine ⟨5799085037279875629123641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3866056691519917086082427 5799085037279875629123641)
        ·
          refine ⟨4349313777959906721842731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5799085037279875629123641 4349313777959906721842731)
          ·
            refine ⟨6523970666939860082764097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4349313777959906721842731 6523970666939860082764097)
            ·
              refine ⟨4892978000204895062073073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6523970666939860082764097 4892978000204895062073073)
              ·
                refine ⟨3669733500153671296554805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4892978000204895062073073 3669733500153671296554805)
                ·
                  refine ⟨344037515639406684052013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3669733500153671296554805 344037515639406684052013)
                  ·
                    rfl

theorem cell21_1507524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 2, 5].length) (baseStart_1507524 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1507524 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1507524 prefixEnd_1507524 := by exact prefixLift 1507524
  have htrace : WordTrace (prefixWord ++ tailWord_1507524) baseStart_1507524 baseEnd_1507524 := by
    simpa [prefixWord, tailWord_1507524, baseEnd_1507524] using wordTrace_append hprefix tailTrace_1507524
  have hstable : (prefixWord ++ tailWord_1507524).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507524).length < 2 ^ (prefixWord ++ tailWord_1507524).sum := by decide
  have hdescent : baseEnd_1507524 < baseStart_1507524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507538 : List Nat := [3, 2, 2, 2, 1, 2, 1, 2, 6]
def baseStart_1507538 : Nat := 118140960795 + 1507538 * 2 ^ 59
def prefixEnd_1507538 : Nat := 4983230072969 + 3 ^ 40 * 1507538 * 2
def baseEnd_1507538 : Nat := 344040710630145770818651

theorem tailTrace_1507538 : CollatzResearch.WordTrace tailWord_1507538 prefixEnd_1507538 344040710630145770818651 := by
  unfold tailWord_1507538
  simp only [CollatzResearch.WordTrace]
  refine ⟨13746107003113691959378817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36656285341636511891676845 13746107003113691959378817)
  ·
    refine ⟨10309580252335268969534113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13746107003113691959378817 10309580252335268969534113)
    ·
      refine ⟨7732185189251451727150585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10309580252335268969534113 7732185189251451727150585)
      ·
        refine ⟨5799138891938588795362939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7732185189251451727150585 5799138891938588795362939)
        ·
          refine ⟨8698708337907883193044409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5799138891938588795362939 8698708337907883193044409)
          ·
            refine ⟨6524031253430912394783307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8698708337907883193044409 6524031253430912394783307)
            ·
              refine ⟨9786046880146368592174961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6524031253430912394783307 9786046880146368592174961)
              ·
                refine ⟨7339535160109776444131221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9786046880146368592174961 7339535160109776444131221)
                ·
                  refine ⟨344040710630145770818651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7339535160109776444131221 344040710630145770818651)
                  ·
                    rfl

theorem cell21_1507538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 2, 6].length) (baseStart_1507538 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1507538 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1507538 prefixEnd_1507538 := by exact prefixLift 1507538
  have htrace : WordTrace (prefixWord ++ tailWord_1507538) baseStart_1507538 baseEnd_1507538 := by
    simpa [prefixWord, tailWord_1507538, baseEnd_1507538] using wordTrace_append hprefix tailTrace_1507538
  have hstable : (prefixWord ++ tailWord_1507538).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507538).length < 2 ^ (prefixWord ++ tailWord_1507538).sum := by decide
  have hdescent : baseEnd_1507538 < baseStart_1507538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507617 : List Nat := [1, 2, 3, 2, 1, 1, 6, 2, 3]
def baseStart_1507617 : Nat := 118140960795 + 1507617 * 2 ^ 59
def prefixEnd_1507617 : Nat := 4983230072969 + 3 ^ 40 * 1507617 * 2
def baseEnd_1507617 : Nat := 344058739506459189001823

theorem tailTrace_1507617 : CollatzResearch.WordTrace tailWord_1507617 prefixEnd_1507617 344058739506459189001823 := by
  unfold tailWord_1507617
  simp only [CollatzResearch.WordTrace]
  refine ⟨54987309379168564329641105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36658206252779042886427403 54987309379168564329641105)
  ·
    refine ⟨41240482034376423247230829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54987309379168564329641105 41240482034376423247230829)
    ·
      refine ⟨15465180762891158717711561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41240482034376423247230829 15465180762891158717711561)
      ·
        refine ⟨11598885572168369038283671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15465180762891158717711561 11598885572168369038283671)
        ·
          refine ⟨17398328358252553557425507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11598885572168369038283671 17398328358252553557425507)
          ·
            refine ⟨26097492537378830336138261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17398328358252553557425507 26097492537378830336138261)
            ·
              refine ⟨1223319962689632672006481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 26097492537378830336138261 1223319962689632672006481)
              ·
                refine ⟨917489972017224504004861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1223319962689632672006481 917489972017224504004861)
                ·
                  refine ⟨344058739506459189001823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 917489972017224504004861 344058739506459189001823)
                  ·
                    rfl

theorem cell21_1507617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 6, 2, 3].length) (baseStart_1507617 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1507617 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1507617 prefixEnd_1507617 := by exact prefixLift 1507617
  have htrace : WordTrace (prefixWord ++ tailWord_1507617) baseStart_1507617 baseEnd_1507617 := by
    simpa [prefixWord, tailWord_1507617, baseEnd_1507617] using wordTrace_append hprefix tailTrace_1507617
  have hstable : (prefixWord ++ tailWord_1507617).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507617).length < 2 ^ (prefixWord ++ tailWord_1507617).sum := by decide
  have hdescent : baseEnd_1507617 < baseStart_1507617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507628 : List Nat := [2, 2, 1, 1, 1, 3, 5, 6]
def baseStart_1507628 : Nat := 118140960795 + 1507628 * 2 ^ 59
def prefixEnd_1507628 : Nat := 4983230072969 + 3 ^ 40 * 1507628 * 2
def baseEnd_1507628 : Nat := 114687083285441871439489

theorem tailTrace_1507628 : CollatzResearch.WordTrace tailWord_1507628 prefixEnd_1507628 114687083285441871439489 := by
  unfold tailWord_1507628
  simp only [CollatzResearch.WordTrace]
  refine ⟨27493855291064356604145769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36658473721419142138861025 27493855291064356604145769)
  ·
    refine ⟨20620391468298267453109327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27493855291064356604145769 20620391468298267453109327)
    ·
      refine ⟨30930587202447401179663991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20620391468298267453109327 30930587202447401179663991)
      ·
        refine ⟨46395880803671101769495987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30930587202447401179663991 46395880803671101769495987)
        ·
          refine ⟨69593821205506652654243981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46395880803671101769495987 69593821205506652654243981)
          ·
            refine ⟨26097682952064994745341493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69593821205506652654243981 26097682952064994745341493)
            ·
              refine ⟨2446657776756093257375765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26097682952064994745341493 2446657776756093257375765)
              ·
                refine ⟨114687083285441871439489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2446657776756093257375765 114687083285441871439489)
                ·
                  rfl

theorem cell21_1507628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 6].length) (baseStart_1507628 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1507628 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1507628 prefixEnd_1507628 := by exact prefixLift 1507628
  have htrace : WordTrace (prefixWord ++ tailWord_1507628) baseStart_1507628 baseEnd_1507628 := by
    simpa [prefixWord, tailWord_1507628, baseEnd_1507628] using wordTrace_append hprefix tailTrace_1507628
  have hstable : (prefixWord ++ tailWord_1507628).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507628).length < 2 ^ (prefixWord ++ tailWord_1507628).sum := by decide
  have hdescent : baseEnd_1507628 < baseStart_1507628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507735 : List Nat := [1, 1, 3, 3, 1, 1, 5, 1, 5]
def baseStart_1507735 : Nat := 118140960795 + 1507735 * 2 ^ 59
def prefixEnd_1507735 : Nat := 4983230072969 + 3 ^ 40 * 1507735 * 2
def baseEnd_1507735 : Nat := 344085668714117206034915

theorem tailTrace_1507735 : CollatzResearch.WordTrace tailWord_1507735 prefixEnd_1507735 344085668714117206034915 := by
  unfold tailWord_1507735
  simp only [CollatzResearch.WordTrace]
  refine ⟨54991613192741070482436659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36661075461827380321624439 54991613192741070482436659)
  ·
    refine ⟨82487419789111605723654989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54991613192741070482436659 82487419789111605723654989)
    ·
      refine ⟨30932782420916852146370621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82487419789111605723654989 30932782420916852146370621)
      ·
        refine ⟨11599793407843819554888983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30932782420916852146370621 11599793407843819554888983)
        ·
          refine ⟨17399690111765729332333475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11599793407843819554888983 17399690111765729332333475)
          ·
            refine ⟨26099535167648593998500213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17399690111765729332333475 26099535167648593998500213)
            ·
              refine ⟨2446831421967055687359395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26099535167648593998500213 2446831421967055687359395)
              ·
                refine ⟨3670247132950583531039093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2446831421967055687359395 3670247132950583531039093)
                ·
                  refine ⟨344085668714117206034915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3670247132950583531039093 344085668714117206034915)
                  ·
                    rfl

theorem cell21_1507735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 1, 5].length) (baseStart_1507735 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1507735 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1507735 prefixEnd_1507735 := by exact prefixLift 1507735
  have htrace : WordTrace (prefixWord ++ tailWord_1507735) baseStart_1507735 baseEnd_1507735 := by
    simpa [prefixWord, tailWord_1507735, baseEnd_1507735] using wordTrace_append hprefix tailTrace_1507735
  have hstable : (prefixWord ++ tailWord_1507735).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507735).length < 2 ^ (prefixWord ++ tailWord_1507735).sum := by decide
  have hdescent : baseEnd_1507735 < baseStart_1507735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507741 : List Nat := [1, 4, 2, 1, 5, 1, 2, 1, 4]
def baseStart_1507741 : Nat := 118140960795 + 1507741 * 2 ^ 59
def prefixEnd_1507741 : Nat := 4983230072969 + 3 ^ 40 * 1507741 * 2
def baseEnd_1507741 : Nat := 344087037995862528934903

theorem tailTrace_1507741 : CollatzResearch.WordTrace tailWord_1507741 prefixEnd_1507741 344087037995862528934903 := by
  unfold tailWord_1507741
  simp only [CollatzResearch.WordTrace]
  refine ⟨54991832030719333507155077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36661221353812889004770051 54991832030719333507155077)
  ·
    refine ⟨10310968505759875032591577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54991832030719333507155077 10310968505759875032591577)
    ·
      refine ⟨7733226379319906274443683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10310968505759875032591577 7733226379319906274443683)
      ·
        refine ⟨11599839568979859411665525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7733226379319906274443683 11599839568979859411665525)
        ·
          refine ⟨1087484959591861819843643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11599839568979859411665525 1087484959591861819843643)
          ·
            refine ⟨1631227439387792729765465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1087484959591861819843643 1631227439387792729765465)
            ·
              refine ⟨1223420579540844547324099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1631227439387792729765465 1223420579540844547324099)
              ·
                refine ⟨1835130869311266820986149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1223420579540844547324099 1835130869311266820986149)
                ·
                  refine ⟨344087037995862528934903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1835130869311266820986149 344087037995862528934903)
                  ·
                    rfl

theorem cell21_1507741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 2, 1, 4].length) (baseStart_1507741 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1507741 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1507741 prefixEnd_1507741 := by exact prefixLift 1507741
  have htrace : WordTrace (prefixWord ++ tailWord_1507741) baseStart_1507741 baseEnd_1507741 := by
    simpa [prefixWord, tailWord_1507741, baseEnd_1507741] using wordTrace_append hprefix tailTrace_1507741
  have hstable : (prefixWord ++ tailWord_1507741).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507741).length < 2 ^ (prefixWord ++ tailWord_1507741).sum := by decide
  have hdescent : baseEnd_1507741 < baseStart_1507741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507780 : List Nat := [2, 3, 3, 2, 11]
def baseStart_1507780 : Nat := 118140960795 + 1507780 * 2 ^ 59
def prefixEnd_1507780 : Nat := 4983230072969 + 3 ^ 40 * 1507780 * 2
def baseEnd_1507780 : Nat := 4248098004039594170183

theorem tailTrace_1507780 : CollatzResearch.WordTrace tailWord_1507780 prefixEnd_1507780 4248098004039594170183 := by
  unfold tailWord_1507780
  simp only [CollatzResearch.WordTrace]
  refine ⟨27496627238789021583912397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36662169651718695445216529 27496627238789021583912397)
  ·
    refine ⟨10311235214545883093967149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27496627238789021583912397 10311235214545883093967149)
    ·
      refine ⟨3866713205454706160237681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10311235214545883093967149 3866713205454706160237681)
      ·
        refine ⟨2900034904091029620178261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3866713205454706160237681 2900034904091029620178261)
        ·
          refine ⟨4248098004039594170183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 2900034904091029620178261 4248098004039594170183)
          ·
            rfl

theorem cell21_1507780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 11].length) (baseStart_1507780 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1507780 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1507780 prefixEnd_1507780 := by exact prefixLift 1507780
  have htrace : WordTrace (prefixWord ++ tailWord_1507780) baseStart_1507780 baseEnd_1507780 := by
    simpa [prefixWord, tailWord_1507780, baseEnd_1507780] using wordTrace_append hprefix tailTrace_1507780
  have hstable : (prefixWord ++ tailWord_1507780).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507780).length < 2 ^ (prefixWord ++ tailWord_1507780).sum := by decide
  have hdescent : baseEnd_1507780 < baseStart_1507780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507797 : List Nat := [1, 3, 2, 3, 1, 4, 1, 6]
def baseStart_1507797 : Nat := 118140960795 + 1507797 * 2 ^ 59
def prefixEnd_1507797 : Nat := 4983230072969 + 3 ^ 40 * 1507797 * 2
def baseEnd_1507797 : Nat := 114699939319606292000485

theorem tailTrace_1507797 : CollatzResearch.WordTrace tailWord_1507797 prefixEnd_1507797 114699939319606292000485 := by
  unfold tailWord_1507797
  simp only [CollatzResearch.WordTrace]
  refine ⟨54993874518516455071193645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36662583012344303380795763 54993874518516455071193645)
  ·
    refine ⟨20622702944443670651697617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54993874518516455071193645 20622702944443670651697617)
    ·
      refine ⟨15467027208332752988773213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20622702944443670651697617 15467027208332752988773213)
      ·
        refine ⟨5800135203124782370789955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15467027208332752988773213 5800135203124782370789955)
        ·
          refine ⟨8700202804687173556184933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5800135203124782370789955 8700202804687173556184933)
          ·
            refine ⟨1631288025878845041784675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8700202804687173556184933 1631288025878845041784675)
            ·
              refine ⟨2446932038818267562677013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1631288025878845041784675 2446932038818267562677013)
              ·
                refine ⟨114699939319606292000485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2446932038818267562677013 114699939319606292000485)
                ·
                  rfl

theorem cell21_1507797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 6].length) (baseStart_1507797 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1507797 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1507797 prefixEnd_1507797 := by exact prefixLift 1507797
  have htrace : WordTrace (prefixWord ++ tailWord_1507797) baseStart_1507797 baseEnd_1507797 := by
    simpa [prefixWord, tailWord_1507797, baseEnd_1507797] using wordTrace_append hprefix tailTrace_1507797
  have hstable : (prefixWord ++ tailWord_1507797).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507797).length < 2 ^ (prefixWord ++ tailWord_1507797).sum := by decide
  have hdescent : baseEnd_1507797 < baseStart_1507797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507825 : List Nat := [1, 2, 2, 2, 3, 1, 2, 2, 6]
def baseStart_1507825 : Nat := 118140960795 + 1507825 * 2 ^ 59
def prefixEnd_1507825 : Nat := 4983230072969 + 3 ^ 40 * 1507825 * 2
def baseEnd_1507825 : Nat := 344106207940297049534731

theorem tailTrace_1507825 : CollatzResearch.WordTrace tailWord_1507825 prefixEnd_1507825 344106207940297049534731 := by
  unfold tailWord_1507825
  simp only [CollatzResearch.WordTrace]
  refine ⟨54994895762415015853212929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36663263841610010568808619 54994895762415015853212929)
  ·
    refine ⟨41246171821811261889909697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54994895762415015853212929 41246171821811261889909697)
    ·
      refine ⟨30934628866358446417432273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41246171821811261889909697 30934628866358446417432273)
      ·
        refine ⟨23200971649768834813074205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30934628866358446417432273 23200971649768834813074205)
        ·
          refine ⟨8700364368663313054902827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23200971649768834813074205 8700364368663313054902827)
          ·
            refine ⟨13050546552994969582354241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8700364368663313054902827 13050546552994969582354241)
            ·
              refine ⟨9787909914746227186765681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13050546552994969582354241 9787909914746227186765681)
              ·
                refine ⟨7340932436059670390074261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9787909914746227186765681 7340932436059670390074261)
                ·
                  refine ⟨344106207940297049534731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7340932436059670390074261 344106207940297049534731)
                  ·
                    rfl

theorem cell21_1507825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 2, 6].length) (baseStart_1507825 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1507825 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1507825 prefixEnd_1507825 := by exact prefixLift 1507825
  have htrace : WordTrace (prefixWord ++ tailWord_1507825) baseStart_1507825 baseEnd_1507825 := by
    simpa [prefixWord, tailWord_1507825, baseEnd_1507825] using wordTrace_append hprefix tailTrace_1507825
  have hstable : (prefixWord ++ tailWord_1507825).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507825).length < 2 ^ (prefixWord ++ tailWord_1507825).sum := by decide
  have hdescent : baseEnd_1507825 < baseStart_1507825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507839 : List Nat := [1, 1, 2, 2, 1, 2, 12]
def baseStart_1507839 : Nat := 118140960795 + 1507839 * 2 ^ 59
def prefixEnd_1507839 : Nat := 4983230072969 + 3 ^ 40 * 1507839 * 2
def baseEnd_1507839 : Nat := 38234378103448459589041

theorem tailTrace_1507839 : CollatzResearch.WordTrace tailWord_1507839 prefixEnd_1507839 38234378103448459589041 := by
  unfold tailWord_1507839
  simp only [CollatzResearch.WordTrace]
  refine ⟨54995406384364296244222571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36663604256242864162815047 54995406384364296244222571)
  ·
    refine ⟨82493109576546444366333857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54995406384364296244222571 82493109576546444366333857)
    ·
      refine ⟨61869832182409833274750393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82493109576546444366333857 61869832182409833274750393)
      ·
        refine ⟨46402374136807374956062795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61869832182409833274750393 46402374136807374956062795)
        ·
          refine ⟨69603561205211062434094193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46402374136807374956062795 69603561205211062434094193)
          ·
            refine ⟨52202670903908296825570645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69603561205211062434094193 52202670903908296825570645)
            ·
              refine ⟨38234378103448459589041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 52202670903908296825570645 38234378103448459589041)
              ·
                rfl

theorem cell21_1507839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 12].length) (baseStart_1507839 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1507839 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1507839 prefixEnd_1507839 := by exact prefixLift 1507839
  have htrace : WordTrace (prefixWord ++ tailWord_1507839) baseStart_1507839 baseEnd_1507839 := by
    simpa [prefixWord, tailWord_1507839, baseEnd_1507839] using wordTrace_append hprefix tailTrace_1507839
  have hstable : (prefixWord ++ tailWord_1507839).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507839).length < 2 ^ (prefixWord ++ tailWord_1507839).sum := by decide
  have hdescent : baseEnd_1507839 < baseStart_1507839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507879 : List Nat := [1, 1, 7, 2, 1, 2, 1, 3, 3]
def baseStart_1507879 : Nat := 118140960795 + 1507879 * 2 ^ 59
def prefixEnd_1507879 : Nat := 4983230072969 + 3 ^ 40 * 1507879 * 2
def baseEnd_1507879 : Nat := 344118531476004955634621

theorem tailTrace_1507879 : CollatzResearch.WordTrace tailWord_1507879 prefixEnd_1507879 344118531476004955634621 := by
  unfold tailWord_1507879
  simp only [CollatzResearch.WordTrace]
  refine ⟨54996865304219383075678691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36664576869479588717119127 54996865304219383075678691)
  ·
    refine ⟨82495297956329074613518037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54996865304219383075678691 82495297956329074613518037)
    ·
      refine ⟨1933483545851462686254329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 82495297956329074613518037 1933483545851462686254329)
      ·
        refine ⟨1450112659388597014690747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1933483545851462686254329 1450112659388597014690747)
        ·
          refine ⟨2175168989082895522036121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1450112659388597014690747 2175168989082895522036121)
          ·
            refine ⟨1631376741812171641527091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2175168989082895522036121 1631376741812171641527091)
            ·
              refine ⟨2447065112718257462290637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1631376741812171641527091 2447065112718257462290637)
              ·
                refine ⟨917649417269346548358989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2447065112718257462290637 917649417269346548358989)
                ·
                  refine ⟨344118531476004955634621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 917649417269346548358989 344118531476004955634621)
                  ·
                    rfl

theorem cell21_1507879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 3, 3].length) (baseStart_1507879 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1507879 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1507879 prefixEnd_1507879 := by exact prefixLift 1507879
  have htrace : WordTrace (prefixWord ++ tailWord_1507879) baseStart_1507879 baseEnd_1507879 := by
    simpa [prefixWord, tailWord_1507879, baseEnd_1507879] using wordTrace_append hprefix tailTrace_1507879
  have hstable : (prefixWord ++ tailWord_1507879).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507879).length < 2 ^ (prefixWord ++ tailWord_1507879).sum := by decide
  have hdescent : baseEnd_1507879 < baseStart_1507879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507915 : List Nat := [1, 1, 1, 1, 3, 1, 5, 8]
def baseStart_1507915 : Nat := 118140960795 + 1507915 * 2 ^ 59
def prefixEnd_1507915 : Nat := 4983230072969 + 3 ^ 40 * 1507915 * 2
def baseEnd_1507915 : Nat := 114708915722158964344849

theorem tailTrace_1507915 : CollatzResearch.WordTrace tailWord_1507915 prefixEnd_1507915 114708915722158964344849 := by
  unfold tailWord_1507915
  simp only [CollatzResearch.WordTrace]
  refine ⟨54998178332088961223989199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36665452221392640815992799 54998178332088961223989199)
  ·
    refine ⟨82497267498133441835983799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54998178332088961223989199 82497267498133441835983799)
    ·
      refine ⟨123745901247200162753975699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82497267498133441835983799 123745901247200162753975699)
      ·
        refine ⟨185618851870800244130963549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123745901247200162753975699 185618851870800244130963549)
        ·
          refine ⟨69607069451550091549111331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 185618851870800244130963549 69607069451550091549111331)
          ·
            refine ⟨104410604177325137323666997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69607069451550091549111331 104410604177325137323666997)
            ·
              refine ⟨9788494141624231624093781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 104410604177325137323666997 9788494141624231624093781)
              ·
                refine ⟨114708915722158964344849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9788494141624231624093781 114708915722158964344849)
                ·
                  rfl

theorem cell21_1507915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 8].length) (baseStart_1507915 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1507915 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1507915 prefixEnd_1507915 := by exact prefixLift 1507915
  have htrace : WordTrace (prefixWord ++ tailWord_1507915) baseStart_1507915 baseEnd_1507915 := by
    simpa [prefixWord, tailWord_1507915, baseEnd_1507915] using wordTrace_append hprefix tailTrace_1507915
  have hstable : (prefixWord ++ tailWord_1507915).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507915).length < 2 ^ (prefixWord ++ tailWord_1507915).sum := by decide
  have hdescent : baseEnd_1507915 < baseStart_1507915 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508056 : List Nat := [2, 1, 2, 2, 3, 2, 3, 3, 3]
def baseStart_1508056 : Nat := 118140960795 + 1508056 * 2 ^ 59
def prefixEnd_1508056 : Nat := 4983230072969 + 3 ^ 40 * 1508056 * 2
def baseEnd_1508056 : Nat := 344158925287491981184259

theorem tailTrace_1508056 : CollatzResearch.WordTrace tailWord_1508056 prefixEnd_1508056 344158925287491981184259 := by
  unfold tailWord_1508056
  simp only [CollatzResearch.WordTrace]
  refine ⟨27501660512289071152436011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36668880683052094869914681 27501660512289071152436011)
  ·
    refine ⟨41252490768433606728654017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27501660512289071152436011 41252490768433606728654017)
    ·
      refine ⟨30939368076325205046490513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41252490768433606728654017 30939368076325205046490513)
      ·
        refine ⟨23204526057243903784867885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30939368076325205046490513 23204526057243903784867885)
        ·
          refine ⟨8701697271466463919325457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23204526057243903784867885 8701697271466463919325457)
          ·
            refine ⟨6526272953599847939494093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8701697271466463919325457 6526272953599847939494093)
            ·
              refine ⟨2447352357599942977310285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6526272953599847939494093 2447352357599942977310285)
              ·
                refine ⟨917757134099978616491357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2447352357599942977310285 917757134099978616491357)
                ·
                  refine ⟨344158925287491981184259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 917757134099978616491357 344158925287491981184259)
                  ·
                    rfl

theorem cell21_1508056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 3, 3].length) (baseStart_1508056 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1508056 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1508056 prefixEnd_1508056 := by exact prefixLift 1508056
  have htrace : WordTrace (prefixWord ++ tailWord_1508056) baseStart_1508056 baseEnd_1508056 := by
    simpa [prefixWord, tailWord_1508056, baseEnd_1508056] using wordTrace_append hprefix tailTrace_1508056
  have hstable : (prefixWord ++ tailWord_1508056).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508056).length < 2 ^ (prefixWord ++ tailWord_1508056).sum := by decide
  have hdescent : baseEnd_1508056 < baseStart_1508056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508115 : List Nat := [1, 1, 1, 2, 1, 3, 4, 5, 3]
def baseStart_1508115 : Nat := 118140960795 + 1508115 * 2 ^ 59
def prefixEnd_1508115 : Nat := 4983230072969 + 3 ^ 40 * 1508115 * 2
def baseEnd_1508115 : Nat := 344172389891320989700805

theorem tailTrace_1508115 : CollatzResearch.WordTrace tailWord_1508115 prefixEnd_1508115 344172389891320989700805 := by
  unfold tailWord_1508115
  simp only [CollatzResearch.WordTrace]
  refine ⟨55005472931364395381269799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36670315287576263587513199 55005472931364395381269799)
  ·
    refine ⟨82508209397046593071904699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55005472931364395381269799 82508209397046593071904699)
    ·
      refine ⟨123762314095569889607857049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82508209397046593071904699 123762314095569889607857049)
      ·
        refine ⟨92821735571677417205892787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123762314095569889607857049 92821735571677417205892787)
        ·
          refine ⟨139232603357516125808839181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92821735571677417205892787 139232603357516125808839181)
          ·
            refine ⟨52212226259068547178314693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139232603357516125808839181 52212226259068547178314693)
            ·
              refine ⟨9789792423575352595934005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52212226259068547178314693 9789792423575352595934005)
              ·
                refine ⟨917793039710189305868813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9789792423575352595934005 917793039710189305868813)
                ·
                  refine ⟨344172389891320989700805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 917793039710189305868813 344172389891320989700805)
                  ·
                    rfl

theorem cell21_1508115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 5, 3].length) (baseStart_1508115 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1508115 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1508115 prefixEnd_1508115 := by exact prefixLift 1508115
  have htrace : WordTrace (prefixWord ++ tailWord_1508115) baseStart_1508115 baseEnd_1508115 := by
    simpa [prefixWord, tailWord_1508115, baseEnd_1508115] using wordTrace_append hprefix tailTrace_1508115
  have hstable : (prefixWord ++ tailWord_1508115).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508115).length < 2 ^ (prefixWord ++ tailWord_1508115).sum := by decide
  have hdescent : baseEnd_1508115 < baseStart_1508115 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508180 : List Nat := [2, 4, 1, 1, 5, 1, 1, 2, 4]
def baseStart_1508180 : Nat := 118140960795 + 1508180 * 2 ^ 59
def prefixEnd_1508180 : Nat := 4983230072969 + 3 ^ 40 * 1508180 * 2
def baseEnd_1508180 : Nat := 344187223776895321117339

theorem tailTrace_1508180 : CollatzResearch.WordTrace tailWord_1508180 prefixEnd_1508180 344187223776895321117339 := by
  unfold tailWord_1508180
  simp only [CollatzResearch.WordTrace]
  refine ⟨27503921838064455741192997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36671895784085940988257329 27503921838064455741192997)
  ·
    refine ⟨5156985344637085451473687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27503921838064455741192997 5156985344637085451473687)
    ·
      refine ⟨7735478016955628177210531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5156985344637085451473687 7735478016955628177210531)
      ·
        refine ⟨11603217025433442265815797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7735478016955628177210531 11603217025433442265815797)
        ·
          refine ⟨1087801596134385212420231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11603217025433442265815797 1087801596134385212420231)
          ·
            refine ⟨1631702394201577818630347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1087801596134385212420231 1631702394201577818630347)
            ·
              refine ⟨2447553591302366727945521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1631702394201577818630347 2447553591302366727945521)
              ·
                refine ⟨1835665193476775045959141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2447553591302366727945521 1835665193476775045959141)
                ·
                  refine ⟨344187223776895321117339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1835665193476775045959141 344187223776895321117339)
                  ·
                    rfl

theorem cell21_1508180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 2, 4].length) (baseStart_1508180 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1508180 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1508180 prefixEnd_1508180 := by exact prefixLift 1508180
  have htrace : WordTrace (prefixWord ++ tailWord_1508180) baseStart_1508180 baseEnd_1508180 := by
    simpa [prefixWord, tailWord_1508180, baseEnd_1508180] using wordTrace_append hprefix tailTrace_1508180
  have hstable : (prefixWord ++ tailWord_1508180).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508180).length < 2 ^ (prefixWord ++ tailWord_1508180).sum := by decide
  have hdescent : baseEnd_1508180 < baseStart_1508180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508191 : List Nat := [1, 1, 2, 3, 1, 3, 1, 6, 3]
def baseStart_1508191 : Nat := 118140960795 + 1508191 * 2 ^ 59
def prefixEnd_1508191 : Nat := 4983230072969 + 3 ^ 40 * 1508191 * 2
def baseEnd_1508191 : Nat := 344189734126761746433983

theorem tailTrace_1508191 : CollatzResearch.WordTrace tailWord_1508191 prefixEnd_1508191 344189734126761746433983 := by
  unfold tailWord_1508191
  simp only [CollatzResearch.WordTrace]
  refine ⟨55008244879089060361036427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36672163252726040240690951 55008244879089060361036427)
  ·
    refine ⟨82512367318633590541554641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55008244879089060361036427 82512367318633590541554641)
    ·
      refine ⟨61884275488975192906165981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82512367318633590541554641 61884275488975192906165981)
      ·
        refine ⟨23206603308365697339812243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61884275488975192906165981 23206603308365697339812243)
        ·
          refine ⟨34809904962548546009718365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23206603308365697339812243 34809904962548546009718365)
          ·
            refine ⟨13053714360955704753644387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34809904962548546009718365 13053714360955704753644387)
            ·
              refine ⟨19580571541433557130466581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13053714360955704753644387 19580571541433557130466581)
              ·
                refine ⟨917839291004697990490621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19580571541433557130466581 917839291004697990490621)
                ·
                  refine ⟨344189734126761746433983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 917839291004697990490621 344189734126761746433983)
                  ·
                    rfl

theorem cell21_1508191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 6, 3].length) (baseStart_1508191 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1508191 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1508191 prefixEnd_1508191 := by exact prefixLift 1508191
  have htrace : WordTrace (prefixWord ++ tailWord_1508191) baseStart_1508191 baseEnd_1508191 := by
    simpa [prefixWord, tailWord_1508191, baseEnd_1508191] using wordTrace_append hprefix tailTrace_1508191
  have hstable : (prefixWord ++ tailWord_1508191).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508191).length < 2 ^ (prefixWord ++ tailWord_1508191).sum := by decide
  have hdescent : baseEnd_1508191 < baseStart_1508191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508242 : List Nat := [3, 2, 3, 2, 2, 1, 3, 2, 3]
def baseStart_1508242 : Nat := 118140960795 + 1508242 * 2 ^ 59
def prefixEnd_1508242 : Nat := 4983230072969 + 3 ^ 40 * 1508242 * 2
def baseEnd_1508242 : Nat := 344201373021596991083879

theorem tailTrace_1508242 : CollatzResearch.WordTrace tailWord_1508242 prefixEnd_1508242 344201373021596991083879 := by
  unfold tailWord_1508242
  simp only [CollatzResearch.WordTrace]
  refine ⟨13752526250476074017785745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36673403334602864047428653 13752526250476074017785745)
  ·
    refine ⟨10314394687857055513339309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13752526250476074017785745 10314394687857055513339309)
    ·
      refine ⟨3867898007946395817502241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10314394687857055513339309 3867898007946395817502241)
      ·
        refine ⟨2900923505959796863126681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3867898007946395817502241 2900923505959796863126681)
        ·
          refine ⟨2175692629469847647345011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2900923505959796863126681 2175692629469847647345011)
          ·
            refine ⟨3263538944204771471017517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2175692629469847647345011 3263538944204771471017517)
            ·
              refine ⟨1223827104076789301631569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3263538944204771471017517 1223827104076789301631569)
              ·
                refine ⟨917870328057591976223677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1223827104076789301631569 917870328057591976223677)
                ·
                  refine ⟨344201373021596991083879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 917870328057591976223677 344201373021596991083879)
                  ·
                    rfl

theorem cell21_1508242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 3, 2, 3].length) (baseStart_1508242 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1508242 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1508242 prefixEnd_1508242 := by exact prefixLift 1508242
  have htrace : WordTrace (prefixWord ++ tailWord_1508242) baseStart_1508242 baseEnd_1508242 := by
    simpa [prefixWord, tailWord_1508242, baseEnd_1508242] using wordTrace_append hprefix tailTrace_1508242
  have hstable : (prefixWord ++ tailWord_1508242).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508242).length < 2 ^ (prefixWord ++ tailWord_1508242).sum := by decide
  have hdescent : baseEnd_1508242 < baseStart_1508242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508312 : List Nat := [2, 1, 2, 2, 2, 5, 1, 6]
def baseStart_1508312 : Nat := 118140960795 + 1508312 * 2 ^ 59
def prefixEnd_1508312 : Nat := 4983230072969 + 3 ^ 40 * 1508312 * 2
def baseEnd_1508312 : Nat := 114739115991764141639023

theorem tailTrace_1508312 : CollatzResearch.WordTrace tailWord_1508312 prefixEnd_1508312 114739115991764141639023 := by
  unfold tailWord_1508312
  simp only [CollatzResearch.WordTrace]
  refine ⟨27506329055825349013095595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36675105407767132017460793 27506329055825349013095595)
  ·
    refine ⟨41259493583738023519643393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27506329055825349013095595 41259493583738023519643393)
    ·
      refine ⟨30944620187803517639732545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41259493583738023519643393 30944620187803517639732545)
      ·
        refine ⟨23208465140852638229799409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30944620187803517639732545 23208465140852638229799409)
        ·
          refine ⟨17406348855639478672349557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23208465140852638229799409 17406348855639478672349557)
          ·
            refine ⟨1631845205216201125532771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17406348855639478672349557 1631845205216201125532771)
            ·
              refine ⟨2447767807824301688299157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1631845205216201125532771 2447767807824301688299157)
              ·
                refine ⟨114739115991764141639023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2447767807824301688299157 114739115991764141639023)
                ·
                  rfl

theorem cell21_1508312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 6].length) (baseStart_1508312 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1508312 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1508312 prefixEnd_1508312 := by exact prefixLift 1508312
  have htrace : WordTrace (prefixWord ++ tailWord_1508312) baseStart_1508312 baseEnd_1508312 := by
    simpa [prefixWord, tailWord_1508312, baseEnd_1508312] using wordTrace_append hprefix tailTrace_1508312
  have hstable : (prefixWord ++ tailWord_1508312).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508312).length < 2 ^ (prefixWord ++ tailWord_1508312).sum := by decide
  have hdescent : baseEnd_1508312 < baseStart_1508312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508388 : List Nat := [2, 3, 1, 4, 1, 2, 1, 7]
def baseStart_1508388 : Nat := 118140960795 + 1508388 * 2 ^ 59
def prefixEnd_1508388 : Nat := 4983230072969 + 3 ^ 40 * 1508388 * 2
def baseEnd_1508388 : Nat := 114744897403577727216749

theorem tailTrace_1508388 : CollatzResearch.WordTrace tailWord_1508388 prefixEnd_1508388 114744897403577727216749 := by
  unfold tailWord_1508388
  simp only [CollatzResearch.WordTrace]
  refine ⟨27507715029687681502978909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36676953372916908670638545 27507715029687681502978909)
  ·
    refine ⟨10315393136132880563617091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27507715029687681502978909 10315393136132880563617091)
    ·
      refine ⟨15473089704199320845425637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10315393136132880563617091 15473089704199320845425637)
      ·
        refine ⟨2901204319537372658517307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15473089704199320845425637 2901204319537372658517307)
        ·
          refine ⟨4351806479306058987775961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2901204319537372658517307 4351806479306058987775961)
          ·
            refine ⟨3263854859479544240831971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4351806479306058987775961 3263854859479544240831971)
            ·
              refine ⟨4895782289219316361247957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3263854859479544240831971 4895782289219316361247957)
              ·
                refine ⟨114744897403577727216749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4895782289219316361247957 114744897403577727216749)
                ·
                  rfl

theorem cell21_1508388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 7].length) (baseStart_1508388 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1508388 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1508388 prefixEnd_1508388 := by exact prefixLift 1508388
  have htrace : WordTrace (prefixWord ++ tailWord_1508388) baseStart_1508388 baseEnd_1508388 := by
    simpa [prefixWord, tailWord_1508388, baseEnd_1508388] using wordTrace_append hprefix tailTrace_1508388
  have hstable : (prefixWord ++ tailWord_1508388).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508388).length < 2 ^ (prefixWord ++ tailWord_1508388).sum := by decide
  have hdescent : baseEnd_1508388 < baseStart_1508388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508394 : List Nat := [3, 1, 4, 1, 4, 1, 1, 3, 3]
def baseStart_1508394 : Nat := 118140960795 + 1508394 * 2 ^ 59
def prefixEnd_1508394 : Nat := 4983230072969 + 3 ^ 40 * 1508394 * 2
def baseEnd_1508394 : Nat := 344236061492478504550235

theorem tailTrace_1508394 : CollatzResearch.WordTrace tailWord_1508394 prefixEnd_1508394 344236061492478504550235 := by
  unfold tailWord_1508394
  simp only [CollatzResearch.WordTrace]
  refine ⟨13753912224338406507669059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36677099264902417353784157 13753912224338406507669059)
  ·
    refine ⟨20630868336507609761503589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13753912224338406507669059 20630868336507609761503589)
    ·
      refine ⟨3868287813095176830281923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20630868336507609761503589 3868287813095176830281923)
      ·
        refine ⟨5802431719642765245422885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3868287813095176830281923 5802431719642765245422885)
        ·
          refine ⟨1087955947433018483516791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5802431719642765245422885 1087955947433018483516791)
          ·
            refine ⟨1631933921149527725275187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1087955947433018483516791 1631933921149527725275187)
            ·
              refine ⟨2447900881724291587912781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1631933921149527725275187 2447900881724291587912781)
              ·
                refine ⟨917962830646609345467293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2447900881724291587912781 917962830646609345467293)
                ·
                  refine ⟨344236061492478504550235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 917962830646609345467293 344236061492478504550235)
                  ·
                    rfl

theorem cell21_1508394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 3, 3].length) (baseStart_1508394 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1508394 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1508394 prefixEnd_1508394 := by exact prefixLift 1508394
  have htrace : WordTrace (prefixWord ++ tailWord_1508394) baseStart_1508394 baseEnd_1508394 := by
    simpa [prefixWord, tailWord_1508394, baseEnd_1508394] using wordTrace_append hprefix tailTrace_1508394
  have hstable : (prefixWord ++ tailWord_1508394).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508394).length < 2 ^ (prefixWord ++ tailWord_1508394).sum := by decide
  have hdescent : baseEnd_1508394 < baseStart_1508394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508416 : List Nat := [2, 1, 1, 2, 2, 3, 1, 3, 6]
def baseStart_1508416 : Nat := 118140960795 + 1508416 * 2 ^ 59
def prefixEnd_1508416 : Nat := 4983230072969 + 3 ^ 40 * 1508416 * 2
def baseEnd_1508416 : Nat := 344241082192211355183523

theorem tailTrace_1508416 : CollatzResearch.WordTrace tailWord_1508416 prefixEnd_1508416 344241082192211355183523 := by
  unfold tailWord_1508416
  simp only [CollatzResearch.WordTrace]
  refine ⟨27508225651636961893988551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36677634202182615858651401 27508225651636961893988551)
  ·
    refine ⟨41262338477455442840982827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27508225651636961893988551 41262338477455442840982827)
    ·
      refine ⟨61893507716183164261474241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41262338477455442840982827 61893507716183164261474241)
      ·
        refine ⟨46420130787137373196105681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61893507716183164261474241 46420130787137373196105681)
        ·
          refine ⟨34815098090353029897079261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46420130787137373196105681 34815098090353029897079261)
          ·
            refine ⟨13055661783882386211404723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34815098090353029897079261 13055661783882386211404723)
            ·
              refine ⟨19583492675823579317107085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13055661783882386211404723 19583492675823579317107085)
              ·
                refine ⟨7343809753433842243915157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19583492675823579317107085 7343809753433842243915157)
                ·
                  refine ⟨344241082192211355183523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7343809753433842243915157 344241082192211355183523)
                  ·
                    rfl

theorem cell21_1508416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 3, 6].length) (baseStart_1508416 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1508416 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1508416 prefixEnd_1508416 := by exact prefixLift 1508416
  have htrace : WordTrace (prefixWord ++ tailWord_1508416) baseStart_1508416 baseEnd_1508416 := by
    simpa [prefixWord, tailWord_1508416, baseEnd_1508416] using wordTrace_append hprefix tailTrace_1508416
  have hstable : (prefixWord ++ tailWord_1508416).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508416).length < 2 ^ (prefixWord ++ tailWord_1508416).sum := by decide
  have hdescent : baseEnd_1508416 < baseStart_1508416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508554 : List Nat := [3, 1, 2, 1, 3, 2, 2, 2, 5]
def baseStart_1508554 : Nat := 118140960795 + 1508554 * 2 ^ 59
def prefixEnd_1508554 : Nat := 4983230072969 + 3 ^ 40 * 1508554 * 2
def baseEnd_1508554 : Nat := 344272575672353781883241

theorem tailTrace_1508554 : CollatzResearch.WordTrace tailWord_1508554 prefixEnd_1508554 344272575672353781883241 := by
  unfold tailWord_1508554
  simp only [CollatzResearch.WordTrace]
  refine ⟨13755371144193493339125179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36680989717849315571000477 13755371144193493339125179)
  ·
    refine ⟨20633056716290240008687769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13755371144193493339125179 20633056716290240008687769)
    ·
      refine ⟨15474792537217680006515827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20633056716290240008687769 15474792537217680006515827)
      ·
        refine ⟨23212188805826520009773741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15474792537217680006515827 23212188805826520009773741)
        ·
          refine ⟨8704570802184945003665153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23212188805826520009773741 8704570802184945003665153)
          ·
            refine ⟨6528428101638708752748865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8704570802184945003665153 6528428101638708752748865)
            ·
              refine ⟨4896321076229031564561649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6528428101638708752748865 4896321076229031564561649)
              ·
                refine ⟨3672240807171773673421237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4896321076229031564561649 3672240807171773673421237)
                ·
                  refine ⟨344272575672353781883241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3672240807171773673421237 344272575672353781883241)
                  ·
                    rfl

theorem cell21_1508554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 2, 5].length) (baseStart_1508554 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1508554 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1508554 prefixEnd_1508554 := by exact prefixLift 1508554
  have htrace : WordTrace (prefixWord ++ tailWord_1508554) baseStart_1508554 baseEnd_1508554 := by
    simpa [prefixWord, tailWord_1508554, baseEnd_1508554] using wordTrace_append hprefix tailTrace_1508554
  have hstable : (prefixWord ++ tailWord_1508554).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508554).length < 2 ^ (prefixWord ++ tailWord_1508554).sum := by decide
  have hdescent : baseEnd_1508554 < baseStart_1508554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508588 : List Nat := [2, 2, 1, 1, 2, 5, 3, 2, 3]
def baseStart_1508588 : Nat := 118140960795 + 1508588 * 2 ^ 59
def prefixEnd_1508588 : Nat := 4983230072969 + 3 ^ 40 * 1508588 * 2
def baseEnd_1508588 : Nat := 344280334935577278316505

theorem tailTrace_1508588 : CollatzResearch.WordTrace tailWord_1508588 prefixEnd_1508588 344280334935577278316505 := by
  unfold tailWord_1508588
  simp only [CollatzResearch.WordTrace]
  refine ⟨27511362329325398581619209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36681816439100531442158945 27511362329325398581619209)
  ·
    refine ⟨20633521746994048936214407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27511362329325398581619209 20633521746994048936214407)
    ·
      refine ⟨30950282620491073404321611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20633521746994048936214407 30950282620491073404321611)
      ·
        refine ⟨46425423930736610106482417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30950282620491073404321611 46425423930736610106482417)
        ·
          refine ⟨34819067948052457579861813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46425423930736610106482417 34819067948052457579861813)
          ·
            refine ⟨3264287620129917898112045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34819067948052457579861813 3264287620129917898112045)
            ·
              refine ⟨1224107857548719211792017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3264287620129917898112045 1224107857548719211792017)
              ·
                refine ⟨918080893161539408844013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1224107857548719211792017 918080893161539408844013)
                ·
                  refine ⟨344280334935577278316505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 918080893161539408844013 344280334935577278316505)
                  ·
                    rfl

theorem cell21_1508588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 3, 2, 3].length) (baseStart_1508588 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1508588 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1508588 prefixEnd_1508588 := by exact prefixLift 1508588
  have htrace : WordTrace (prefixWord ++ tailWord_1508588) baseStart_1508588 baseEnd_1508588 := by
    simpa [prefixWord, tailWord_1508588, baseEnd_1508588] using wordTrace_append hprefix tailTrace_1508588
  have hstable : (prefixWord ++ tailWord_1508588).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508588).length < 2 ^ (prefixWord ++ tailWord_1508588).sum := by decide
  have hdescent : baseEnd_1508588 < baseStart_1508588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508613 : List Nat := [1, 3, 1, 1, 2, 1, 4, 1, 7]
def baseStart_1508613 : Nat := 118140960795 + 1508613 * 2 ^ 59
def prefixEnd_1508613 : Nat := 4983230072969 + 3 ^ 40 * 1508613 * 2
def baseEnd_1508613 : Nat := 344286040276182790399787

theorem tailTrace_1508613 : CollatzResearch.WordTrace tailWord_1508613 prefixEnd_1508613 344286040276182790399787 := by
  unfold tailWord_1508613
  simp only [CollatzResearch.WordTrace]
  refine ⟨55023636483560226432898493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36682424322373484288598995 55023636483560226432898493)
  ·
    refine ⟨20633863681335084912336935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55023636483560226432898493 20633863681335084912336935)
    ·
      refine ⟨30950795522002627368505403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20633863681335084912336935 30950795522002627368505403)
      ·
        refine ⟨46426193283003941052758105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30950795522002627368505403 46426193283003941052758105)
        ·
          refine ⟨34819644962252955789568579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46426193283003941052758105 34819644962252955789568579)
          ·
            refine ⟨52229467443379433684352869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34819644962252955789568579 52229467443379433684352869)
            ·
              refine ⟨9793025145633643815816163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52229467443379433684352869 9793025145633643815816163)
              ·
                refine ⟨14689537718450465723724245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9793025145633643815816163 14689537718450465723724245)
                ·
                  refine ⟨344286040276182790399787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14689537718450465723724245 344286040276182790399787)
                  ·
                    rfl

theorem cell21_1508613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 7].length) (baseStart_1508613 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1508613 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1508613 prefixEnd_1508613 := by exact prefixLift 1508613
  have htrace : WordTrace (prefixWord ++ tailWord_1508613) baseStart_1508613 baseEnd_1508613 := by
    simpa [prefixWord, tailWord_1508613, baseEnd_1508613] using wordTrace_append hprefix tailTrace_1508613
  have hstable : (prefixWord ++ tailWord_1508613).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508613).length < 2 ^ (prefixWord ++ tailWord_1508613).sum := by decide
  have hdescent : baseEnd_1508613 < baseStart_1508613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508661 : List Nat := [1, 3, 3, 1, 2, 2, 2, 3, 4]
def baseStart_1508661 : Nat := 118140960795 + 1508661 * 2 ^ 59
def prefixEnd_1508661 : Nat := 4983230072969 + 3 ^ 40 * 1508661 * 2
def baseEnd_1508661 : Nat := 344296994530145373599689

theorem tailTrace_1508661 : CollatzResearch.WordTrace tailWord_1508661 prefixEnd_1508661 344296994530145373599689 := by
  unfold tailWord_1508661
  simp only [CollatzResearch.WordTrace]
  refine ⟨55025387187386330630645837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36683591458257553753763891 55025387187386330630645837)
  ·
    refine ⟨20634520195269873986492189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55025387187386330630645837 20634520195269873986492189)
    ·
      refine ⟨7737945073226202744934571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20634520195269873986492189 7737945073226202744934571)
      ·
        refine ⟨11606917609839304117401857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7737945073226202744934571 11606917609839304117401857)
        ·
          refine ⟨8705188207379478088051393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11606917609839304117401857 8705188207379478088051393)
          ·
            refine ⟨6528891155534608566038545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8705188207379478088051393 6528891155534608566038545)
            ·
              refine ⟨4896668366650956424528909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6528891155534608566038545 4896668366650956424528909)
              ·
                refine ⟨1836250637494108659198341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4896668366650956424528909 1836250637494108659198341)
                ·
                  refine ⟨344296994530145373599689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1836250637494108659198341 344296994530145373599689)
                  ·
                    rfl

theorem cell21_1508661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 3, 4].length) (baseStart_1508661 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1508661 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1508661 prefixEnd_1508661 := by exact prefixLift 1508661
  have htrace : WordTrace (prefixWord ++ tailWord_1508661) baseStart_1508661 baseEnd_1508661 := by
    simpa [prefixWord, tailWord_1508661, baseEnd_1508661] using wordTrace_append hprefix tailTrace_1508661
  have hstable : (prefixWord ++ tailWord_1508661).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508661).length < 2 ^ (prefixWord ++ tailWord_1508661).sum := by decide
  have hdescent : baseEnd_1508661 < baseStart_1508661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508689 : List Nat := [1, 2, 2, 1, 4, 1, 1, 2, 7]
def baseStart_1508689 : Nat := 118140960795 + 1508689 * 2 ^ 59
def prefixEnd_1508689 : Nat := 4983230072969 + 3 ^ 40 * 1508689 * 2
def baseEnd_1508689 : Nat := 344303384511623547132965

theorem tailTrace_1508689 : CollatzResearch.WordTrace tailWord_1508689 prefixEnd_1508689 344303384511623547132965 := by
  unfold tailWord_1508689
  simp only [CollatzResearch.WordTrace]
  refine ⟨55026408431284891412665121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36684272287523260941776747 55026408431284891412665121)
  ·
    refine ⟨41269806323463668559498841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55026408431284891412665121 41269806323463668559498841)
    ·
      refine ⟨30952354742597751419624131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41269806323463668559498841 30952354742597751419624131)
      ·
        refine ⟨46428532113896627129436197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30952354742597751419624131 46428532113896627129436197)
        ·
          refine ⟨8705349771355617586769287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46428532113896627129436197 8705349771355617586769287)
          ·
            refine ⟨13058024657033426380153931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8705349771355617586769287 13058024657033426380153931)
            ·
              refine ⟨19587036985550139570230897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13058024657033426380153931 19587036985550139570230897)
              ·
                refine ⟨14690277739162604677673173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19587036985550139570230897 14690277739162604677673173)
                ·
                  refine ⟨344303384511623547132965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14690277739162604677673173 344303384511623547132965)
                  ·
                    rfl

theorem cell21_1508689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 7].length) (baseStart_1508689 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1508689 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1508689 prefixEnd_1508689 := by exact prefixLift 1508689
  have htrace : WordTrace (prefixWord ++ tailWord_1508689) baseStart_1508689 baseEnd_1508689 := by
    simpa [prefixWord, tailWord_1508689, baseEnd_1508689] using wordTrace_append hprefix tailTrace_1508689
  have hstable : (prefixWord ++ tailWord_1508689).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508689).length < 2 ^ (prefixWord ++ tailWord_1508689).sum := by decide
  have hdescent : baseEnd_1508689 < baseStart_1508689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508740 : List Nat := [2, 3, 2, 1, 1, 5, 1, 3, 3]
def baseStart_1508740 : Nat := 118140960795 + 1508740 * 2 ^ 59
def prefixEnd_1508740 : Nat := 4983230072969 + 3 ^ 40 * 1508740 * 2
def baseEnd_1508740 : Nat := 344315023406458791782861

theorem tailTrace_1508740 : CollatzResearch.WordTrace tailWord_1508740 prefixEnd_1508740 344315023406458791782861 := by
  unfold tailWord_1508740
  simp only [CollatzResearch.WordTrace]
  refine ⟨27514134277050063561385837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36685512369400084748514449 27514134277050063561385837)
  ·
    refine ⟨10317800353893773835519689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27514134277050063561385837 10317800353893773835519689)
    ·
      refine ⟨7738350265420330376639767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10317800353893773835519689 7738350265420330376639767)
      ·
        refine ⟨11607525398130495564959651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7738350265420330376639767 11607525398130495564959651)
        ·
          refine ⟨17411288097195743347439477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11607525398130495564959651 17411288097195743347439477)
          ·
            refine ⟨1632308259112100938822451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17411288097195743347439477 1632308259112100938822451)
            ·
              refine ⟨2448462388668151408233677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1632308259112100938822451 2448462388668151408233677)
              ·
                refine ⟨918173395750556778087629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2448462388668151408233677 918173395750556778087629)
                ·
                  refine ⟨344315023406458791782861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 918173395750556778087629 344315023406458791782861)
                  ·
                    rfl

theorem cell21_1508740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 3, 3].length) (baseStart_1508740 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1508740 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1508740 prefixEnd_1508740 := by exact prefixLift 1508740
  have htrace : WordTrace (prefixWord ++ tailWord_1508740) baseStart_1508740 baseEnd_1508740 := by
    simpa [prefixWord, tailWord_1508740, baseEnd_1508740] using wordTrace_append hprefix tailTrace_1508740
  have hstable : (prefixWord ++ tailWord_1508740).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508740).length < 2 ^ (prefixWord ++ tailWord_1508740).sum := by decide
  have hdescent : baseEnd_1508740 < baseStart_1508740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508802 : List Nat := [3, 5, 2, 1, 1, 9]
def baseStart_1508802 : Nat := 118140960795 + 1508802 * 2 ^ 59
def prefixEnd_1508802 : Nat := 4983230072969 + 3 ^ 40 * 1508802 * 2
def baseEnd_1508802 : Nat := 12752932320413350435163

theorem tailTrace_1508802 : CollatzResearch.WordTrace tailWord_1508802 prefixEnd_1508802 12752932320413350435163 := by
  unfold tailWord_1508802
  simp only [CollatzResearch.WordTrace]
  refine ⟨13757632469968877927882165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36687019919917007807685773 13757632469968877927882165)
  ·
    refine ⟨1289778044059582305738953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13757632469968877927882165 1289778044059582305738953)
    ·
      refine ⟨967333533044686729304215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1289778044059582305738953 967333533044686729304215)
      ·
        refine ⟨1451000299567030093956323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 967333533044686729304215 1451000299567030093956323)
        ·
          refine ⟨2176500449350545140934485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1451000299567030093956323 2176500449350545140934485)
          ·
            refine ⟨12752932320413350435163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2176500449350545140934485 12752932320413350435163)
            ·
              rfl

theorem cell21_1508802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 9].length) (baseStart_1508802 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1508802 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1508802 prefixEnd_1508802 := by exact prefixLift 1508802
  have htrace : WordTrace (prefixWord ++ tailWord_1508802) baseStart_1508802 baseEnd_1508802 := by
    simpa [prefixWord, tailWord_1508802, baseEnd_1508802] using wordTrace_append hprefix tailTrace_1508802
  have hstable : (prefixWord ++ tailWord_1508802).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508802).length < 2 ^ (prefixWord ++ tailWord_1508802).sum := by decide
  have hdescent : baseEnd_1508802 < baseStart_1508802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508810 : List Nat := [3, 1, 2, 1, 2, 12]
def baseStart_1508810 : Nat := 118140960795 + 1508810 * 2 ^ 59
def prefixEnd_1508810 : Nat := 4983230072969 + 3 ^ 40 * 1508810 * 2
def baseEnd_1508810 : Nat := 12752999939264971319113

theorem tailTrace_1508810 : CollatzResearch.WordTrace tailWord_1508810 prefixEnd_1508810 12752999939264971319113 := by
  unfold tailWord_1508810
  simp only [CollatzResearch.WordTrace]
  refine ⟨13757705415961632269454971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36687214442564352718546589 13757705415961632269454971)
  ·
    refine ⟨20636558123942448404182457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13757705415961632269454971 20636558123942448404182457)
    ·
      refine ⟨15477418592956836303136843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20636558123942448404182457 15477418592956836303136843)
      ·
        refine ⟨23216127889435254454705265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15477418592956836303136843 23216127889435254454705265)
        ·
          refine ⟨17412095917076440841028949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23216127889435254454705265 17412095917076440841028949)
          ·
            refine ⟨12752999939264971319113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 17412095917076440841028949 12752999939264971319113)
            ·
              rfl

theorem cell21_1508810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 12].length) (baseStart_1508810 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1508810 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1508810 prefixEnd_1508810 := by exact prefixLift 1508810
  have htrace : WordTrace (prefixWord ++ tailWord_1508810) baseStart_1508810 baseEnd_1508810 := by
    simpa [prefixWord, tailWord_1508810, baseEnd_1508810] using wordTrace_append hprefix tailTrace_1508810
  have hstable : (prefixWord ++ tailWord_1508810).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508810).length < 2 ^ (prefixWord ++ tailWord_1508810).sum := by decide
  have hdescent : baseEnd_1508810 < baseStart_1508810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508982 : List Nat := [5, 1, 1, 2, 2, 2, 2, 2, 4]
def baseStart_1508982 : Nat := 118140960795 + 1508982 * 2 ^ 59
def prefixEnd_1508982 : Nat := 4983230072969 + 3 ^ 40 * 1508982 * 2
def baseEnd_1508982 : Nat := 344370251103520148749033

theorem tailTrace_1508982 : CollatzResearch.WordTrace tailWord_1508982 prefixEnd_1508982 344370251103520148749033 := by
  unfold tailWord_1508982
  simp only [CollatzResearch.WordTrace]
  refine ⟨3439818438701462653317575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36691396679482268302054133 3439818438701462653317575)
  ·
    refine ⟨5159727658052193979976363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3439818438701462653317575 5159727658052193979976363)
    ·
      refine ⟨7739591487078290969964545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5159727658052193979976363 7739591487078290969964545)
      ·
        refine ⟨5804693615308718227473409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7739591487078290969964545 5804693615308718227473409)
        ·
          refine ⟨4353520211481538670605057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5804693615308718227473409 4353520211481538670605057)
          ·
            refine ⟨3265140158611154002953793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4353520211481538670605057 3265140158611154002953793)
            ·
              refine ⟨2448855118958365502215345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3265140158611154002953793 2448855118958365502215345)
              ·
                refine ⟨1836641339218774126661509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2448855118958365502215345 1836641339218774126661509)
                ·
                  refine ⟨344370251103520148749033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1836641339218774126661509 344370251103520148749033)
                  ·
                    rfl

theorem cell21_1508982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_1508982 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1508982 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1508982 prefixEnd_1508982 := by exact prefixLift 1508982
  have htrace : WordTrace (prefixWord ++ tailWord_1508982) baseStart_1508982 baseEnd_1508982 := by
    simpa [prefixWord, tailWord_1508982, baseEnd_1508982] using wordTrace_append hprefix tailTrace_1508982
  have hstable : (prefixWord ++ tailWord_1508982).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508982).length < 2 ^ (prefixWord ++ tailWord_1508982).sum := by decide
  have hdescent : baseEnd_1508982 < baseStart_1508982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508996 : List Nat := [2, 3, 2, 1, 4, 2, 1, 6]
def baseStart_1508996 : Nat := 118140960795 + 1508996 * 2 ^ 59
def prefixEnd_1508996 : Nat := 4983230072969 + 3 ^ 40 * 1508996 * 2
def baseEnd_1508996 : Nat := 114791148698086411838557

theorem tailTrace_1508996 : CollatzResearch.WordTrace tailWord_1508996 prefixEnd_1508996 114791148698086411838557 := by
  unfold tailWord_1508996
  simp only [CollatzResearch.WordTrace]
  refine ⟨27518802820586341422045421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36691737094115121896060561 27518802820586341422045421)
  ·
    refine ⟨10319551057719878033267033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27518802820586341422045421 10319551057719878033267033)
    ·
      refine ⟨7739663293289908524950275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10319551057719878033267033 7739663293289908524950275)
      ·
        refine ⟨11609494939934862787425413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7739663293289908524950275 11609494939934862787425413)
        ·
          refine ⟨2176780301237786772642265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11609494939934862787425413 2176780301237786772642265)
          ·
            refine ⟨1632585225928340079481699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2176780301237786772642265 1632585225928340079481699)
            ·
              refine ⟨2448877838892510119222549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1632585225928340079481699 2448877838892510119222549)
              ·
                refine ⟨114791148698086411838557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2448877838892510119222549 114791148698086411838557)
                ·
                  rfl

theorem cell21_1508996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 6].length) (baseStart_1508996 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1508996 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1508996 prefixEnd_1508996 := by exact prefixLift 1508996
  have htrace : WordTrace (prefixWord ++ tailWord_1508996) baseStart_1508996 baseEnd_1508996 := by
    simpa [prefixWord, tailWord_1508996, baseEnd_1508996] using wordTrace_append hprefix tailTrace_1508996
  have hstable : (prefixWord ++ tailWord_1508996).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508996).length < 2 ^ (prefixWord ++ tailWord_1508996).sum := by decide
  have hdescent : baseEnd_1508996 < baseStart_1508996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1509078 : List Nat := [5, 2, 1, 3, 1, 2, 1, 3, 3]
def baseStart_1509078 : Nat := 118140960795 + 1509078 * 2 ^ 59
def prefixEnd_1509078 : Nat := 4983230072969 + 3 ^ 40 * 1509078 * 2
def baseEnd_1509078 : Nat := 344392159611445315148837

theorem tailTrace_1509078 : CollatzResearch.WordTrace tailWord_1509078 prefixEnd_1509078 344392159611445315148837 := by
  unfold tailWord_1509078
  simp only [CollatzResearch.WordTrace]
  refine ⟨3440037276679725678035993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36693730951250407232383925 3440037276679725678035993)
  ·
    refine ⟨2580027957509794258526995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3440037276679725678035993 2580027957509794258526995)
    ·
      refine ⟨3870041936264691387790493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2580027957509794258526995 3870041936264691387790493)
      ·
        refine ⟨1451265726099259270421435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3870041936264691387790493 1451265726099259270421435)
        ·
          refine ⟨2176898589148888905632153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1451265726099259270421435 2176898589148888905632153)
          ·
            refine ⟨1632673941861666679224115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2176898589148888905632153 1632673941861666679224115)
            ·
              refine ⟨2449010912792500018836173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1632673941861666679224115 2449010912792500018836173)
              ·
                refine ⟨918379092297187507063565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2449010912792500018836173 918379092297187507063565)
                ·
                  refine ⟨344392159611445315148837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 918379092297187507063565 344392159611445315148837)
                  ·
                    rfl

theorem cell21_1509078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_1509078 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1509078 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1509078 prefixEnd_1509078 := by exact prefixLift 1509078
  have htrace : WordTrace (prefixWord ++ tailWord_1509078) baseStart_1509078 baseEnd_1509078 := by
    simpa [prefixWord, tailWord_1509078, baseEnd_1509078] using wordTrace_append hprefix tailTrace_1509078
  have hstable : (prefixWord ++ tailWord_1509078).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509078).length < 2 ^ (prefixWord ++ tailWord_1509078).sum := by decide
  have hdescent : baseEnd_1509078 < baseStart_1509078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1509103 : List Nat := [1, 1, 2, 1, 5, 1, 5, 2, 3]
def baseStart_1509103 : Nat := 118140960795 + 1509103 * 2 ^ 59
def prefixEnd_1509103 : Nat := 4983230072969 + 3 ^ 40 * 1509103 * 2
def baseEnd_1509103 : Nat := 344397864952050827232119

theorem tailTrace_1509103 : CollatzResearch.WordTrace tailWord_1509103 prefixEnd_1509103 344397864952050827232119 := by
  unfold tailWord_1509103
  simp only [CollatzResearch.WordTrace]
  refine ⟨55041508251785040118235963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36694338834523360078823975 55041508251785040118235963)
  ·
    refine ⟨82562262377677560177353945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55041508251785040118235963 82562262377677560177353945)
    ·
      refine ⟨61921696783258170133015459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82562262377677560177353945 61921696783258170133015459)
      ·
        refine ⟨92882545174887255199523189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61921696783258170133015459 92882545174887255199523189)
        ·
          refine ⟨8707738610145680174955299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 92882545174887255199523189 8707738610145680174955299)
          ·
            refine ⟨13061607915218520262432949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8707738610145680174955299 13061607915218520262432949)
            ·
              refine ⟨1224525742051736274603089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13061607915218520262432949 1224525742051736274603089)
              ·
                refine ⟨918394306538802205952317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1224525742051736274603089 918394306538802205952317)
                ·
                  refine ⟨344397864952050827232119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 918394306538802205952317 344397864952050827232119)
                  ·
                    rfl

theorem cell21_1509103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 5, 2, 3].length) (baseStart_1509103 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1509103 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1509103 prefixEnd_1509103 := by exact prefixLift 1509103
  have htrace : WordTrace (prefixWord ++ tailWord_1509103) baseStart_1509103 baseEnd_1509103 := by
    simpa [prefixWord, tailWord_1509103, baseEnd_1509103] using wordTrace_append hprefix tailTrace_1509103
  have hstable : (prefixWord ++ tailWord_1509103).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509103).length < 2 ^ (prefixWord ++ tailWord_1509103).sum := by decide
  have hdescent : baseEnd_1509103 < baseStart_1509103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1509176 : List Nat := [2, 1, 2, 1, 3, 3, 2, 3, 4]
def baseStart_1509176 : Nat := 118140960795 + 1509176 * 2 ^ 59
def prefixEnd_1509176 : Nat := 4983230072969 + 3 ^ 40 * 1509176 * 2
def baseEnd_1509176 : Nat := 344414524546618922515303

theorem tailTrace_1509176 : CollatzResearch.WordTrace tailWord_1509176 prefixEnd_1509176 344414524546618922515303 := by
  unfold tailWord_1509176
  simp only [CollatzResearch.WordTrace]
  refine ⟨27522085390260286792821691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36696113853680382390428921 27522085390260286792821691)
  ·
    refine ⟨41283128085390430189232537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27522085390260286792821691 41283128085390430189232537)
    ·
      refine ⟨30962346064042822641924403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41283128085390430189232537 30962346064042822641924403)
      ·
        refine ⟨46443519096064233962886605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30962346064042822641924403 46443519096064233962886605)
        ·
          refine ⟨17416319661024087736082477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46443519096064233962886605 17416319661024087736082477)
          ·
            refine ⟨6531119872884032901030929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17416319661024087736082477 6531119872884032901030929)
            ·
              refine ⟨4898339904663024675773197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6531119872884032901030929 4898339904663024675773197)
              ·
                refine ⟨1836877464248634253414949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4898339904663024675773197 1836877464248634253414949)
                ·
                  refine ⟨344414524546618922515303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1836877464248634253414949 344414524546618922515303)
                  ·
                    rfl

theorem cell21_1509176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 3, 4].length) (baseStart_1509176 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1509176 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1509176 prefixEnd_1509176 := by exact prefixLift 1509176
  have htrace : WordTrace (prefixWord ++ tailWord_1509176) baseStart_1509176 baseEnd_1509176 := by
    simpa [prefixWord, tailWord_1509176, baseEnd_1509176] using wordTrace_append hprefix tailTrace_1509176
  have hstable : (prefixWord ++ tailWord_1509176).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509176).length < 2 ^ (prefixWord ++ tailWord_1509176).sum := by decide
  have hdescent : baseEnd_1509176 < baseStart_1509176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1509272 : List Nat := [2, 1, 2, 6, 2, 1, 1, 1, 5]
def baseStart_1509272 : Nat := 118140960795 + 1509272 * 2 ^ 59
def prefixEnd_1509272 : Nat := 4983230072969 + 3 ^ 40 * 1509272 * 2
def baseEnd_1509272 : Nat := 344436433054544088915107

theorem tailTrace_1509272 : CollatzResearch.WordTrace tailWord_1509272 prefixEnd_1509272 344436433054544088915107 := by
  unfold tailWord_1509272
  simp only [CollatzResearch.WordTrace]
  refine ⟨27523836094086390990569035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36698448125448521320758713 27523836094086390990569035)
  ·
    refine ⟨41285754141129586485853553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27523836094086390990569035 41285754141129586485853553)
    ·
      refine ⟨30964315605847189864390165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41285754141129586485853553 30964315605847189864390165)
      ·
        refine ⟨1451452294024087024893289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 30964315605847189864390165 1451452294024087024893289)
        ·
          refine ⟨1088589220518065268669967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1451452294024087024893289 1088589220518065268669967)
          ·
            refine ⟨1632883830777097903004951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1088589220518065268669967 1632883830777097903004951)
            ·
              refine ⟨2449325746165646854507427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1632883830777097903004951 2449325746165646854507427)
              ·
                refine ⟨3673988619248470281761141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2449325746165646854507427 3673988619248470281761141)
                ·
                  refine ⟨344436433054544088915107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3673988619248470281761141 344436433054544088915107)
                  ·
                    rfl

theorem cell21_1509272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 1, 5].length) (baseStart_1509272 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1509272 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1509272 prefixEnd_1509272 := by exact prefixLift 1509272
  have htrace : WordTrace (prefixWord ++ tailWord_1509272) baseStart_1509272 baseEnd_1509272 := by
    simpa [prefixWord, tailWord_1509272, baseEnd_1509272] using wordTrace_append hprefix tailTrace_1509272
  have hstable : (prefixWord ++ tailWord_1509272).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509272).length < 2 ^ (prefixWord ++ tailWord_1509272).sum := by decide
  have hdescent : baseEnd_1509272 < baseStart_1509272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1509387 : List Nat := [1, 1, 1, 1, 6, 1, 3, 1, 6]
def baseStart_1509387 : Nat := 118140960795 + 1509387 * 2 ^ 59
def prefixEnd_1509387 : Nat := 4983230072969 + 3 ^ 40 * 1509387 * 2
def baseEnd_1509387 : Nat := 344462677621329444498205

theorem tailTrace_1509387 : CollatzResearch.WordTrace tailWord_1509387 prefixEnd_1509387 344462677621329444498205 := by
  unfold tailWord_1509387
  simp only [CollatzResearch.WordTrace]
  refine ⟨55051866582756156621574415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36701244388504104414382943 55051866582756156621574415)
  ·
    refine ⟨82577799874134234932361623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55051866582756156621574415 82577799874134234932361623)
    ·
      refine ⟨123866699811201352398542435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82577799874134234932361623 123866699811201352398542435)
      ·
        refine ⟨185800049716802028597813653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123866699811201352398542435 185800049716802028597813653)
        ·
          refine ⟨8709377330475095090522515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 185800049716802028597813653 8709377330475095090522515)
          ·
            refine ⟨13064065995712642635783773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8709377330475095090522515 13064065995712642635783773)
            ·
              refine ⟨4899024748392240988418915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13064065995712642635783773 4899024748392240988418915)
              ·
                refine ⟨7348537122588361482628373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4899024748392240988418915 7348537122588361482628373)
                ·
                  refine ⟨344462677621329444498205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7348537122588361482628373 344462677621329444498205)
                  ·
                    rfl

theorem cell21_1509387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 1, 6].length) (baseStart_1509387 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1509387 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1509387 prefixEnd_1509387 := by exact prefixLift 1509387
  have htrace : WordTrace (prefixWord ++ tailWord_1509387) baseStart_1509387 baseEnd_1509387 := by
    simpa [prefixWord, tailWord_1509387, baseEnd_1509387] using wordTrace_append hprefix tailTrace_1509387
  have hstable : (prefixWord ++ tailWord_1509387).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509387).length < 2 ^ (prefixWord ++ tailWord_1509387).sum := by decide
  have hdescent : baseEnd_1509387 < baseStart_1509387 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1509390 : List Nat := [4, 1, 1, 2, 2, 1, 1, 6, 3]
def baseStart_1509390 : Nat := 118140960795 + 1509390 * 2 ^ 59
def prefixEnd_1509390 : Nat := 4983230072969 + 3 ^ 40 * 1509390 * 2
def baseEnd_1509390 : Nat := 344463362262202105948199

theorem tailTrace_1509390 : CollatzResearch.WordTrace tailWord_1509390 prefixEnd_1509390 344463362262202105948199 := by
  unfold tailWord_1509390
  simp only [CollatzResearch.WordTrace]
  refine ⟨6881497000218161016741703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36701317334496858755955749 6881497000218161016741703)
  ·
    refine ⟨10322245500327241525112555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6881497000218161016741703 10322245500327241525112555)
    ·
      refine ⟨15483368250490862287668833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10322245500327241525112555 15483368250490862287668833)
      ·
        refine ⟨11612526187868146715751625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15483368250490862287668833 11612526187868146715751625)
        ·
          refine ⟨8709394640901110036813719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11612526187868146715751625 8709394640901110036813719)
          ·
            refine ⟨13064091961351665055220579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8709394640901110036813719 13064091961351665055220579)
            ·
              refine ⟨19596137942027497582830869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13064091961351665055220579 19596137942027497582830869)
              ·
                refine ⟨918568966032538949195197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19596137942027497582830869 918568966032538949195197)
                ·
                  refine ⟨344463362262202105948199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 918568966032538949195197 344463362262202105948199)
                  ·
                    rfl

theorem cell21_1509390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 6, 3].length) (baseStart_1509390 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1509390 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1509390 prefixEnd_1509390 := by exact prefixLift 1509390
  have htrace : WordTrace (prefixWord ++ tailWord_1509390) baseStart_1509390 baseEnd_1509390 := by
    simpa [prefixWord, tailWord_1509390, baseEnd_1509390] using wordTrace_append hprefix tailTrace_1509390
  have hstable : (prefixWord ++ tailWord_1509390).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509390).length < 2 ^ (prefixWord ++ tailWord_1509390).sum := by decide
  have hdescent : baseEnd_1509390 < baseStart_1509390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1509401 : List Nat := [1, 2, 1, 2, 1, 1, 3, 10]
def baseStart_1509401 : Nat := 118140960795 + 1509401 * 2 ^ 59
def prefixEnd_1509401 : Nat := 4983230072969 + 3 ^ 40 * 1509401 * 2
def baseEnd_1509401 : Nat := 114821957537356177088281

theorem tailTrace_1509401 : CollatzResearch.WordTrace tailWord_1509401 prefixEnd_1509401 114821957537356177088281 := by
  unfold tailWord_1509401
  simp only [CollatzResearch.WordTrace]
  refine ⟨55052377204705437012584057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36701584803136958008389371 55052377204705437012584057)
  ·
    refine ⟨41289282903529077759438043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55052377204705437012584057 41289282903529077759438043)
    ·
      refine ⟨61933924355293616639157065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41289282903529077759438043 61933924355293616639157065)
      ·
        refine ⟨46450443266470212479367799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61933924355293616639157065 46450443266470212479367799)
        ·
          refine ⟨69675664899705318719051699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46450443266470212479367799 69675664899705318719051699)
          ·
            refine ⟨104513497349557978078577549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69675664899705318719051699 104513497349557978078577549)
            ·
              refine ⟨39192561506084241779466581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104513497349557978078577549 39192561506084241779466581)
              ·
                refine ⟨114821957537356177088281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 39192561506084241779466581 114821957537356177088281)
                ·
                  rfl

theorem cell21_1509401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 10].length) (baseStart_1509401 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1509401 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1509401 prefixEnd_1509401 := by exact prefixLift 1509401
  have htrace : WordTrace (prefixWord ++ tailWord_1509401) baseStart_1509401 baseEnd_1509401 := by
    simpa [prefixWord, tailWord_1509401, baseEnd_1509401] using wordTrace_append hprefix tailTrace_1509401
  have hstable : (prefixWord ++ tailWord_1509401).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509401).length < 2 ^ (prefixWord ++ tailWord_1509401).sum := by decide
  have hdescent : baseEnd_1509401 < baseStart_1509401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1509494 : List Nat := [5, 1, 1, 2, 1, 11]
def baseStart_1509494 : Nat := 118140960795 + 1509494 * 2 ^ 59
def prefixEnd_1509494 : Nat := 4983230072969 + 3 ^ 40 * 1509494 * 2
def baseEnd_1509494 : Nat := 12758781351078556896839

theorem tailTrace_1509494 : CollatzResearch.WordTrace tailWord_1509494 prefixEnd_1509494 12758781351078556896839 := by
  unfold tailWord_1509494
  simp only [CollatzResearch.WordTrace]
  refine ⟨3440985574585532118482471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36703846128912342597146357 3440985574585532118482471)
  ·
    refine ⟨5161478361878298177723707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3440985574585532118482471 5161478361878298177723707)
    ·
      refine ⟨7742217542817447266585561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5161478361878298177723707 7742217542817447266585561)
      ·
        refine ⟨5806663157113085449939171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7742217542817447266585561 5806663157113085449939171)
        ·
          refine ⟨8709994735669628174908757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5806663157113085449939171 8709994735669628174908757)
          ·
            refine ⟨12758781351078556896839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8709994735669628174908757 12758781351078556896839)
            ·
              rfl

theorem cell21_1509494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 11].length) (baseStart_1509494 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1509494 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1509494 prefixEnd_1509494 := by exact prefixLift 1509494
  have htrace : WordTrace (prefixWord ++ tailWord_1509494) baseStart_1509494 baseEnd_1509494 := by
    simpa [prefixWord, tailWord_1509494, baseEnd_1509494] using wordTrace_append hprefix tailTrace_1509494
  have hstable : (prefixWord ++ tailWord_1509494).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509494).length < 2 ^ (prefixWord ++ tailWord_1509494).sum := by decide
  have hdescent : baseEnd_1509494 < baseStart_1509494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1509615 : List Nat := [1, 1, 2, 1, 6, 1, 2, 1, 6]
def baseStart_1509615 : Nat := 118140960795 + 1509615 * 2 ^ 59
def prefixEnd_1509615 : Nat := 4983230072969 + 3 ^ 40 * 1509615 * 2
def baseEnd_1509615 : Nat := 344514710327651714697739

theorem tailTrace_1509615 : CollatzResearch.WordTrace tailWord_1509615 prefixEnd_1509615 344514710327651714697739 := by
  unfold tailWord_1509615
  simp only [CollatzResearch.WordTrace]
  refine ⟨55060182425930151560874299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36706788283953434373916199 55060182425930151560874299)
  ·
    refine ⟨82590273638895227341311449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55060182425930151560874299 82590273638895227341311449)
    ·
      refine ⟨61942705229171420505983587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82590273638895227341311449 61942705229171420505983587)
      ·
        refine ⟨92914057843757130758975381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61942705229171420505983587 92914057843757130758975381)
        ·
          refine ⟨4355346461426115504326971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 92914057843757130758975381 4355346461426115504326971)
          ·
            refine ⟨6533019692139173256490457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4355346461426115504326971 6533019692139173256490457)
            ·
              refine ⟨4899764769104379942367843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6533019692139173256490457 4899764769104379942367843)
              ·
                refine ⟨7349647153656569913551765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4899764769104379942367843 7349647153656569913551765)
                ·
                  refine ⟨344514710327651714697739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7349647153656569913551765 344514710327651714697739)
                  ·
                    rfl

theorem cell21_1509615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 1, 6].length) (baseStart_1509615 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1509615 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1509615 prefixEnd_1509615 := by exact prefixLift 1509615
  have htrace : WordTrace (prefixWord ++ tailWord_1509615) baseStart_1509615 baseEnd_1509615 := by
    simpa [prefixWord, tailWord_1509615, baseEnd_1509615] using wordTrace_append hprefix tailTrace_1509615
  have hstable : (prefixWord ++ tailWord_1509615).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509615).length < 2 ^ (prefixWord ++ tailWord_1509615).sum := by decide
  have hdescent : baseEnd_1509615 < baseStart_1509615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1509618 : List Nat := [3, 2, 1, 3, 2, 3, 1, 1, 5]
def baseStart_1509618 : Nat := 118140960795 + 1509618 * 2 ^ 59
def prefixEnd_1509618 : Nat := 4983230072969 + 3 ^ 40 * 1509618 * 2
def baseEnd_1509618 : Nat := 344515394968524376147733

theorem tailTrace_1509618 : CollatzResearch.WordTrace tailWord_1509618 prefixEnd_1509618 344515394968524376147733 := by
  unfold tailWord_1509618
  simp only [CollatzResearch.WordTrace]
  refine ⟨13765072961229820768308377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36706861229946188715489005 13765072961229820768308377)
  ·
    refine ⟨10323804720922365576231283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13765072961229820768308377 10323804720922365576231283)
    ·
      refine ⟨15485707081383548364346925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10323804720922365576231283 15485707081383548364346925)
      ·
        refine ⟨5807140155518830636630097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15485707081383548364346925 5807140155518830636630097)
        ·
          refine ⟨4355355116639122977472573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5807140155518830636630097 4355355116639122977472573)
          ·
            refine ⟨1633258168739671116552215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4355355116639122977472573 1633258168739671116552215)
            ·
              refine ⟨2449887253109506674828323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1633258168739671116552215 2449887253109506674828323)
              ·
                refine ⟨3674830879664260012242485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2449887253109506674828323 3674830879664260012242485)
                ·
                  refine ⟨344515394968524376147733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3674830879664260012242485 344515394968524376147733)
                  ·
                    rfl

theorem cell21_1509618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 1, 5].length) (baseStart_1509618 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1509618 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1509618 prefixEnd_1509618 := by exact prefixLift 1509618
  have htrace : WordTrace (prefixWord ++ tailWord_1509618) baseStart_1509618 baseEnd_1509618 := by
    simpa [prefixWord, tailWord_1509618, baseEnd_1509618] using wordTrace_append hprefix tailTrace_1509618
  have hstable : (prefixWord ++ tailWord_1509618).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509618).length < 2 ^ (prefixWord ++ tailWord_1509618).sum := by decide
  have hdescent : baseEnd_1509618 < baseStart_1509618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1509632 : List Nat := [2, 1, 1, 2, 1, 1, 8, 1, 4]
def baseStart_1509632 : Nat := 118140960795 + 1509632 * 2 ^ 59
def prefixEnd_1509632 : Nat := 4983230072969 + 3 ^ 40 * 1509632 * 2
def baseEnd_1509632 : Nat := 344518589959263462914371

theorem tailTrace_1509632 : CollatzResearch.WordTrace tailWord_1509632 prefixEnd_1509632 344518589959263462914371 := by
  unfold tailWord_1509632
  simp only [CollatzResearch.WordTrace]
  refine ⟨27530401233434281732121575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36707201644579042309495433 27530401233434281732121575)
  ·
    refine ⟨41295601850151422598182363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27530401233434281732121575 41295601850151422598182363)
    ·
      refine ⟨61943402775227133897273545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41295601850151422598182363 61943402775227133897273545)
      ·
        refine ⟨46457552081420350422955159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61943402775227133897273545 46457552081420350422955159)
        ·
          refine ⟨69686328122130525634432739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46457552081420350422955159 69686328122130525634432739)
          ·
            refine ⟨104529492183195788451649109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69686328122130525634432739 104529492183195788451649109)
            ·
              refine ⟨1224954986521825645917763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 104529492183195788451649109 1224954986521825645917763)
              ·
                refine ⟨1837432479782738468876645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1224954986521825645917763 1837432479782738468876645)
                ·
                  refine ⟨344518589959263462914371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1837432479782738468876645 344518589959263462914371)
                  ·
                    rfl

theorem cell21_1509632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 8, 1, 4].length) (baseStart_1509632 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1509632 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1509632 prefixEnd_1509632 := by exact prefixLift 1509632
  have htrace : WordTrace (prefixWord ++ tailWord_1509632) baseStart_1509632 baseEnd_1509632 := by
    simpa [prefixWord, tailWord_1509632, baseEnd_1509632] using wordTrace_append hprefix tailTrace_1509632
  have hstable : (prefixWord ++ tailWord_1509632).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509632).length < 2 ^ (prefixWord ++ tailWord_1509632).sum := by decide
  have hdescent : baseEnd_1509632 < baseStart_1509632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1509894 : List Nat := [6, 2, 1, 1, 1, 2, 1, 1, 6]
def baseStart_1509894 : Nat := 118140960795 + 1509894 * 2 ^ 59
def prefixEnd_1509894 : Nat := 4983230072969 + 3 ^ 40 * 1509894 * 2
def baseEnd_1509894 : Nat := 344578381928809229547169

theorem tailTrace_1509894 : CollatzResearch.WordTrace tailWord_1509894 prefixEnd_1509894 344578381928809229547169 := by
  unfold tailWord_1509894
  simp only [CollatzResearch.WordTrace]
  refine ⟨1720948699747480694071273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 36713572261279588140187157 1720948699747480694071273)
  ·
    refine ⟨1290711524810610520553455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1720948699747480694071273 1290711524810610520553455)
    ·
      refine ⟨1936067287215915780830183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1290711524810610520553455 1936067287215915780830183)
      ·
        refine ⟨2904100930823873671245275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1936067287215915780830183 2904100930823873671245275)
        ·
          refine ⟨4356151396235810506867913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2904100930823873671245275 4356151396235810506867913)
          ·
            refine ⟨3267113547176857880150935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4356151396235810506867913 3267113547176857880150935)
            ·
              refine ⟨4900670320765286820226403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3267113547176857880150935 4900670320765286820226403)
              ·
                refine ⟨7351005481147930230339605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4900670320765286820226403 7351005481147930230339605)
                ·
                  refine ⟨344578381928809229547169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7351005481147930230339605 344578381928809229547169)
                  ·
                    rfl

theorem cell21_1509894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_1509894 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1509894 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1509894 prefixEnd_1509894 := by exact prefixLift 1509894
  have htrace : WordTrace (prefixWord ++ tailWord_1509894) baseStart_1509894 baseEnd_1509894 := by
    simpa [prefixWord, tailWord_1509894, baseEnd_1509894] using wordTrace_append hprefix tailTrace_1509894
  have hstable : (prefixWord ++ tailWord_1509894).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509894).length < 2 ^ (prefixWord ++ tailWord_1509894).sum := by decide
  have hdescent : baseEnd_1509894 < baseStart_1509894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
