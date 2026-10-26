import V185TrunkScan22Chunk142

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1279306 : List Nat := [3, 1, 2, 1, 1, 1, 1, 4, 3, 5]
def baseStart_1279306 : Nat := 118140960795 + 1279306 * 2 ^ 59
def prefixEnd_1279306 : Nat := 4983230072969 + 3 ^ 40 * 1279306 * 2
def baseEnd_1279306 : Nat := 437932588120584628727723

theorem tailTrace_1279306 : CollatzResearch.WordTrace tailWord_1279306 prefixEnd_1279306 437932588120584628727723 := by
  unfold tailWord_1279306
  simp only [CollatzResearch.WordTrace]
  refine ⟨11665030775825081228796443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31106748735533549943457181 11665030775825081228796443)
  ·
    refine ⟨17497546163737621843194665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11665030775825081228796443 17497546163737621843194665)
    ·
      refine ⟨13123159622803216382395999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17497546163737621843194665 13123159622803216382395999)
      ·
        refine ⟨19684739434204824573593999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13123159622803216382395999 19684739434204824573593999)
        ·
          refine ⟨29527109151307236860390999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19684739434204824573593999 29527109151307236860390999)
          ·
            refine ⟨44290663726960855290586499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29527109151307236860390999 44290663726960855290586499)
            ·
              refine ⟨66435995590441282935879749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44290663726960855290586499 66435995590441282935879749)
              ·
                refine ⟨12456749173207740550477453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66435995590441282935879749 12456749173207740550477453)
                ·
                  refine ⟨4671280939952902706429045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12456749173207740550477453 4671280939952902706429045)
                  ·
                    refine ⟨437932588120584628727723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4671280939952902706429045 437932588120584628727723)
                    ·
                      rfl

theorem cell22_1279306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 3, 5].length) (baseStart_1279306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1279306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1279306 prefixEnd_1279306 := by exact prefixLift 1279306
  have htrace : WordTrace (prefixWord ++ tailWord_1279306) baseStart_1279306 baseEnd_1279306 := by
    simpa [prefixWord, tailWord_1279306, baseEnd_1279306] using wordTrace_append hprefix tailTrace_1279306
  have hstable : (prefixWord ++ tailWord_1279306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279306).length < 2 ^ (prefixWord ++ tailWord_1279306).sum := by decide
  have hdescent : baseEnd_1279306 < baseStart_1279306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279308 : List Nat := [2, 2, 1, 3, 2, 3, 2, 1, 6]
def baseStart_1279308 : Nat := 118140960795 + 1279308 * 2 ^ 59
def prefixEnd_1279308 : Nat := 4983230072969 + 3 ^ 40 * 1279308 * 2
def baseEnd_1279308 : Nat := 145977757587152430059239

theorem tailTrace_1279308 : CollatzResearch.WordTrace tailWord_1279308 prefixEnd_1279308 145977757587152430059239 := by
  unfold tailWord_1279308
  simp only [CollatzResearch.WordTrace]
  refine ⟨23330098024646539628379289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31106797366195386171172385 23330098024646539628379289)
  ·
    refine ⟨17497573518484904721284467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23330098024646539628379289 17497573518484904721284467)
    ·
      refine ⟨26246360277727357081926701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17497573518484904721284467 26246360277727357081926701)
      ·
        refine ⟨9842385104147758905722513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26246360277727357081926701 9842385104147758905722513)
        ·
          refine ⟨7381788828110819179291885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9842385104147758905722513 7381788828110819179291885)
          ·
            refine ⟨2768170810541557192234457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7381788828110819179291885 2768170810541557192234457)
            ·
              refine ⟨2076128107906167894175843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2768170810541557192234457 2076128107906167894175843)
              ·
                refine ⟨3114192161859251841263765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2076128107906167894175843 3114192161859251841263765)
                ·
                  refine ⟨145977757587152430059239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3114192161859251841263765 145977757587152430059239)
                  ·
                    rfl

theorem cell22_1279308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 1, 6].length) (baseStart_1279308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1279308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1279308 prefixEnd_1279308 := by exact prefixLift 1279308
  have htrace : WordTrace (prefixWord ++ tailWord_1279308) baseStart_1279308 baseEnd_1279308 := by
    simpa [prefixWord, tailWord_1279308, baseEnd_1279308] using wordTrace_append hprefix tailTrace_1279308
  have hstable : (prefixWord ++ tailWord_1279308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279308).length < 2 ^ (prefixWord ++ tailWord_1279308).sum := by decide
  have hdescent : baseEnd_1279308 < baseStart_1279308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279321 : List Nat := [1, 2, 1, 2, 2, 2, 3, 2, 1, 6]
def baseStart_1279321 : Nat := 118140960795 + 1279321 * 2 ^ 59
def prefixEnd_1279321 : Nat := 4983230072969 + 3 ^ 40 * 1279321 * 2
def baseEnd_1279321 : Nat := 437937722927129589602677

theorem tailTrace_1279321 : CollatzResearch.WordTrace tailWord_1279321 prefixEnd_1279321 437937722927129589602677 := by
  unfold tailWord_1279321
  simp only [CollatzResearch.WordTrace]
  refine ⟨46660670198245982476981817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31107113465497321651321211 46660670198245982476981817)
  ·
    refine ⟨34995502648684486857736363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46660670198245982476981817 34995502648684486857736363)
    ·
      refine ⟨52493253973026730286604545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34995502648684486857736363 52493253973026730286604545)
      ·
        refine ⟨39369940479770047714953409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52493253973026730286604545 39369940479770047714953409)
        ·
          refine ⟨29527455359827535786215057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39369940479770047714953409 29527455359827535786215057)
          ·
            refine ⟨22145591519870651839661293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29527455359827535786215057 22145591519870651839661293)
            ·
              refine ⟨8304596819951494439872985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22145591519870651839661293 8304596819951494439872985)
              ·
                refine ⟨6228447614963620829904739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8304596819951494439872985 6228447614963620829904739)
                ·
                  refine ⟨9342671422445431244857109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6228447614963620829904739 9342671422445431244857109)
                  ·
                    refine ⟨437937722927129589602677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9342671422445431244857109 437937722927129589602677)
                    ·
                      rfl

theorem cell22_1279321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 2, 1, 6].length) (baseStart_1279321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1279321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1279321 prefixEnd_1279321 := by exact prefixLift 1279321
  have htrace : WordTrace (prefixWord ++ tailWord_1279321) baseStart_1279321 baseEnd_1279321 := by
    simpa [prefixWord, tailWord_1279321, baseEnd_1279321] using wordTrace_append hprefix tailTrace_1279321
  have hstable : (prefixWord ++ tailWord_1279321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279321).length < 2 ^ (prefixWord ++ tailWord_1279321).sum := by decide
  have hdescent : baseEnd_1279321 < baseStart_1279321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279445 : List Nat := [1, 3, 2, 3, 1, 1, 2, 4, 1, 4]
def baseStart_1279445 : Nat := 118140960795 + 1279445 * 2 ^ 59
def prefixEnd_1279445 : Nat := 4983230072969 + 3 ^ 40 * 1279445 * 2
def baseEnd_1279445 : Nat := 437980170661234599502297

theorem tailTrace_1279445 : CollatzResearch.WordTrace tailWord_1279445 prefixEnd_1279445 437980170661234599502297 := by
  unfold tailWord_1279445
  simp only [CollatzResearch.WordTrace]
  refine ⟨46665192849796751654495789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31110128566531167769663859 46665192849796751654495789)
  ·
    refine ⟨17499447318673781870435921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46665192849796751654495789 17499447318673781870435921)
    ·
      refine ⟨13124585489005336402826941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17499447318673781870435921 13124585489005336402826941)
      ·
        refine ⟨4921719558377001151060103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13124585489005336402826941 4921719558377001151060103)
        ·
          refine ⟨7382579337565501726590155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4921719558377001151060103 7382579337565501726590155)
          ·
            refine ⟨11073869006348252589885233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7382579337565501726590155 11073869006348252589885233)
            ·
              refine ⟨8305401754761189442413925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11073869006348252589885233 8305401754761189442413925)
              ·
                refine ⟨1557262829017723020452611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8305401754761189442413925 1557262829017723020452611)
                ·
                  refine ⟨2335894243526584530678917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1557262829017723020452611 2335894243526584530678917)
                  ·
                    refine ⟨437980170661234599502297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2335894243526584530678917 437980170661234599502297)
                    ·
                      rfl

theorem cell22_1279445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 4, 1, 4].length) (baseStart_1279445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1279445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1279445 prefixEnd_1279445 := by exact prefixLift 1279445
  have htrace : WordTrace (prefixWord ++ tailWord_1279445) baseStart_1279445 baseEnd_1279445 := by
    simpa [prefixWord, tailWord_1279445, baseEnd_1279445] using wordTrace_append hprefix tailTrace_1279445
  have hstable : (prefixWord ++ tailWord_1279445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279445).length < 2 ^ (prefixWord ++ tailWord_1279445).sum := by decide
  have hdescent : baseEnd_1279445 < baseStart_1279445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279475 : List Nat := [1, 1, 1, 2, 2, 2, 2, 6, 2, 3]
def baseStart_1279475 : Nat := 118140960795 + 1279475 * 2 ^ 59
def prefixEnd_1279475 : Nat := 4983230072969 + 3 ^ 40 * 1279475 * 2
def baseEnd_1279475 : Nat := 437990440274324521252205

theorem tailTrace_1279475 : CollatzResearch.WordTrace tailWord_1279475 prefixEnd_1279475 437990440274324521252205 := by
  unfold tailWord_1279475
  simp only [CollatzResearch.WordTrace]
  refine ⟨46666287039688066778087879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31110858026458711185391919 46666287039688066778087879)
  ·
    refine ⟨69999430559532100167131819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46666287039688066778087879 69999430559532100167131819)
    ·
      refine ⟨104999145839298150250697729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69999430559532100167131819 104999145839298150250697729)
      ·
        refine ⟨78749359379473612688023297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104999145839298150250697729 78749359379473612688023297)
        ·
          refine ⟨59062019534605209516017473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78749359379473612688023297 59062019534605209516017473)
          ·
            refine ⟨44296514650953907137013105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59062019534605209516017473 44296514650953907137013105)
            ·
              refine ⟨33222385988215430352759829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44296514650953907137013105 33222385988215430352759829)
              ·
                refine ⟨1557299343197598297785617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 33222385988215430352759829 1557299343197598297785617)
                ·
                  refine ⟨1167974507398198723339213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1557299343197598297785617 1167974507398198723339213)
                  ·
                    refine ⟨437990440274324521252205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1167974507398198723339213 437990440274324521252205)
                    ·
                      rfl

theorem cell22_1279475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 6, 2, 3].length) (baseStart_1279475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1279475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1279475 prefixEnd_1279475 := by exact prefixLift 1279475
  have htrace : WordTrace (prefixWord ++ tailWord_1279475) baseStart_1279475 baseEnd_1279475 := by
    simpa [prefixWord, tailWord_1279475, baseEnd_1279475] using wordTrace_append hprefix tailTrace_1279475
  have hstable : (prefixWord ++ tailWord_1279475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279475).length < 2 ^ (prefixWord ++ tailWord_1279475).sum := by decide
  have hdescent : baseEnd_1279475 < baseStart_1279475 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279477 : List Nat := [1, 3, 5, 1, 1, 2, 2, 1, 6]
def baseStart_1279477 : Nat := 118140960795 + 1279477 * 2 ^ 59
def prefixEnd_1279477 : Nat := 4983230072969 + 3 ^ 40 * 1279477 * 2
def baseEnd_1279477 : Nat := 145997041638399060900733

theorem tailTrace_1279477 : CollatzResearch.WordTrace tailWord_1279477 prefixEnd_1279477 145997041638399060900733 := by
  unfold tailWord_1279477
  simp only [CollatzResearch.WordTrace]
  refine ⟨46666359985680821119660685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31110906657120547413107123 46666359985680821119660685)
  ·
    refine ⟨17499884994630307919872757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46666359985680821119660685 17499884994630307919872757)
    ·
      refine ⟨1640614218246591367488071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17499884994630307919872757 1640614218246591367488071)
      ·
        refine ⟨2460921327369887051232107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1640614218246591367488071 2460921327369887051232107)
        ·
          refine ⟨3691381991054830576848161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2460921327369887051232107 3691381991054830576848161)
          ·
            refine ⟨2768536493291122932636121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3691381991054830576848161 2768536493291122932636121)
            ·
              refine ⟨2076402369968342199477091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2768536493291122932636121 2076402369968342199477091)
              ·
                refine ⟨3114603554952513299215637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2076402369968342199477091 3114603554952513299215637)
                ·
                  refine ⟨145997041638399060900733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3114603554952513299215637 145997041638399060900733)
                  ·
                    rfl

theorem cell22_1279477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 1, 6].length) (baseStart_1279477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1279477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1279477 prefixEnd_1279477 := by exact prefixLift 1279477
  have htrace : WordTrace (prefixWord ++ tailWord_1279477) baseStart_1279477 baseEnd_1279477 := by
    simpa [prefixWord, tailWord_1279477, baseEnd_1279477] using wordTrace_append hprefix tailTrace_1279477
  have hstable : (prefixWord ++ tailWord_1279477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279477).length < 2 ^ (prefixWord ++ tailWord_1279477).sum := by decide
  have hdescent : baseEnd_1279477 < baseStart_1279477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279640 : List Nat := [2, 1, 2, 4, 1, 3, 9]
def baseStart_1279640 : Nat := 118140960795 + 1279640 * 2 ^ 59
def prefixEnd_1279640 : Nat := 4983230072969 + 3 ^ 40 * 1279640 * 2
def baseEnd_1279640 : Nat := 16223960116530336699137

theorem tailTrace_1279640 : CollatzResearch.WordTrace tailWord_1279640 prefixEnd_1279640 16223960116530336699137 := by
  unfold tailWord_1279640
  simp only [CollatzResearch.WordTrace]
  refine ⟨23336152542045149978922187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31114870056060199971896249 23336152542045149978922187)
  ·
    refine ⟨35004228813067724968383281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23336152542045149978922187 35004228813067724968383281)
    ·
      refine ⟨26253171609800793726287461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35004228813067724968383281 26253171609800793726287461)
      ·
        refine ⟨4922469676837648823678899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26253171609800793726287461 4922469676837648823678899)
        ·
          refine ⟨7383704515256473235518349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4922469676837648823678899 7383704515256473235518349)
          ·
            refine ⟨2768889193221177463319381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7383704515256473235518349 2768889193221177463319381)
            ·
              refine ⟨16223960116530336699137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2768889193221177463319381 16223960116530336699137)
              ·
                rfl

theorem cell22_1279640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 9].length) (baseStart_1279640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1279640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1279640 prefixEnd_1279640 := by exact prefixLift 1279640
  have htrace : WordTrace (prefixWord ++ tailWord_1279640) baseStart_1279640 baseEnd_1279640 := by
    simpa [prefixWord, tailWord_1279640, baseEnd_1279640] using wordTrace_append hprefix tailTrace_1279640
  have hstable : (prefixWord ++ tailWord_1279640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279640).length < 2 ^ (prefixWord ++ tailWord_1279640).sum := by decide
  have hdescent : baseEnd_1279640 < baseStart_1279640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279644 : List Nat := [2, 2, 3, 2, 3, 1, 1, 1, 4, 3]
def baseStart_1279644 : Nat := 118140960795 + 1279644 * 2 ^ 59
def prefixEnd_1279644 : Nat := 4983230072969 + 3 ^ 40 * 1279644 * 2
def baseEnd_1279644 : Nat := 438048292428064413776687

theorem tailTrace_1279644 : CollatzResearch.WordTrace tailWord_1279644 prefixEnd_1279644 438048292428064413776687 := by
  unfold tailWord_1279644
  simp only [CollatzResearch.WordTrace]
  refine ⟨23336225488037904320494993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31114967317383872427326657 23336225488037904320494993)
  ·
    refine ⟨17502169116028428240371245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23336225488037904320494993 17502169116028428240371245)
    ·
      refine ⟨6563313418510660590139217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17502169116028428240371245 6563313418510660590139217)
      ·
        refine ⟨4922485063882995442604413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6563313418510660590139217 4922485063882995442604413)
        ·
          refine ⟨1845931898956123290976655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4922485063882995442604413 1845931898956123290976655)
          ·
            refine ⟨2768897848434184936464983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1845931898956123290976655 2768897848434184936464983)
            ·
              refine ⟨4153346772651277404697475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2768897848434184936464983 4153346772651277404697475)
              ·
                refine ⟨6230020158976916107046213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4153346772651277404697475 6230020158976916107046213)
                ·
                  refine ⟨1168128779808171770071165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6230020158976916107046213 1168128779808171770071165)
                  ·
                    refine ⟨438048292428064413776687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1168128779808171770071165 438048292428064413776687)
                    ·
                      rfl

theorem cell22_1279644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 1, 4, 3].length) (baseStart_1279644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1279644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1279644 prefixEnd_1279644 := by exact prefixLift 1279644
  have htrace : WordTrace (prefixWord ++ tailWord_1279644) baseStart_1279644 baseEnd_1279644 := by
    simpa [prefixWord, tailWord_1279644, baseEnd_1279644] using wordTrace_append hprefix tailTrace_1279644
  have hstable : (prefixWord ++ tailWord_1279644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279644).length < 2 ^ (prefixWord ++ tailWord_1279644).sum := by decide
  have hdescent : baseEnd_1279644 < baseStart_1279644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279661 : List Nat := [1, 5, 2, 1, 1, 1, 5, 1, 2, 3]
def baseStart_1279661 : Nat := 118140960795 + 1279661 * 2 ^ 59
def prefixEnd_1279661 : Nat := 4983230072969 + 3 ^ 40 * 1279661 * 2
def baseEnd_1279661 : Nat := 438054111875482036101635

theorem tailTrace_1279661 : CollatzResearch.WordTrace tailWord_1279661 prefixEnd_1279661 438054111875482036101635 := by
  unfold tailWord_1279661
  simp only [CollatzResearch.WordTrace]
  refine ⟨46673071017014220544358837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31115380678009480362905891 46673071017014220544358837)
  ·
    refine ⟨4375600407845083176033641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46673071017014220544358837 4375600407845083176033641)
    ·
      refine ⟨3281700305883812382025231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4375600407845083176033641 3281700305883812382025231)
      ·
        refine ⟨4922550458825718573037847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3281700305883812382025231 4922550458825718573037847)
        ·
          refine ⟨7383825688238577859556771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4922550458825718573037847 7383825688238577859556771)
          ·
            refine ⟨11075738532357866789335157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7383825688238577859556771 11075738532357866789335157)
            ·
              refine ⟨1038350487408550011500171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11075738532357866789335157 1038350487408550011500171)
              ·
                refine ⟨1557525731112825017250257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1038350487408550011500171 1557525731112825017250257)
                ·
                  refine ⟨1168144298334618762937693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1557525731112825017250257 1168144298334618762937693)
                  ·
                    refine ⟨438054111875482036101635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1168144298334618762937693 438054111875482036101635)
                    ·
                      rfl

theorem cell22_1279661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_1279661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1279661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1279661 prefixEnd_1279661 := by exact prefixLift 1279661
  have htrace : WordTrace (prefixWord ++ tailWord_1279661) baseStart_1279661 baseEnd_1279661 := by
    simpa [prefixWord, tailWord_1279661, baseEnd_1279661] using wordTrace_append hprefix tailTrace_1279661
  have hstable : (prefixWord ++ tailWord_1279661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279661).length < 2 ^ (prefixWord ++ tailWord_1279661).sum := by decide
  have hdescent : baseEnd_1279661 < baseStart_1279661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279779 : List Nat := [1, 1, 1, 4, 2, 1, 4, 3, 2, 3]
def baseStart_1279779 : Nat := 118140960795 + 1279779 * 2 ^ 59
def prefixEnd_1279779 : Nat := 4983230072969 + 3 ^ 40 * 1279779 * 2
def baseEnd_1279779 : Nat := 438094505686969061651273

theorem tailTrace_1279779 : CollatzResearch.WordTrace tailWord_1279779 prefixEnd_1279779 438094505686969061651273 := by
  unfold tailWord_1279779
  simp only [CollatzResearch.WordTrace]
  refine ⟨46677374830586726697154391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31118249887057817798102927 46677374830586726697154391)
  ·
    refine ⟨70016062245880090045731587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46677374830586726697154391 70016062245880090045731587)
    ·
      refine ⟨105024093368820135068597381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70016062245880090045731587 105024093368820135068597381)
      ·
        refine ⟨19692017506653775325362009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 105024093368820135068597381 19692017506653775325362009)
        ·
          refine ⟨14769013129990331494021507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19692017506653775325362009 14769013129990331494021507)
          ·
            refine ⟨22153519694985497241032261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14769013129990331494021507 22153519694985497241032261)
            ·
              refine ⟨4153784942809780732693549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22153519694985497241032261 4153784942809780732693549)
              ·
                refine ⟨1557669353553667774760081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4153784942809780732693549 1557669353553667774760081)
                ·
                  refine ⟨1168252015165250831070061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1557669353553667774760081 1168252015165250831070061)
                  ·
                    refine ⟨438094505686969061651273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1168252015165250831070061 438094505686969061651273)
                    ·
                      rfl

theorem cell22_1279779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 3, 2, 3].length) (baseStart_1279779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1279779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1279779 prefixEnd_1279779 := by exact prefixLift 1279779
  have htrace : WordTrace (prefixWord ++ tailWord_1279779) baseStart_1279779 baseEnd_1279779 := by
    simpa [prefixWord, tailWord_1279779, baseEnd_1279779] using wordTrace_append hprefix tailTrace_1279779
  have hstable : (prefixWord ++ tailWord_1279779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279779).length < 2 ^ (prefixWord ++ tailWord_1279779).sum := by decide
  have hdescent : baseEnd_1279779 < baseStart_1279779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279794 : List Nat := [3, 2, 1, 1, 3, 2, 3, 1, 2, 4]
def baseStart_1279794 : Nat := 118140960795 + 1279794 * 2 ^ 59
def prefixEnd_1279794 : Nat := 4983230072969 + 3 ^ 40 * 1279794 * 2
def baseEnd_1279794 : Nat := 438099640493514022526227

theorem tailTrace_1279794 : CollatzResearch.WordTrace tailWord_1279794 prefixEnd_1279794 438099640493514022526227 := by
  unfold tailWord_1279794
  simp only [CollatzResearch.WordTrace]
  refine ⟨11669480481383096064737609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31118614617021589505966957 11669480481383096064737609)
  ·
    refine ⟨8752110361037322048553207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11669480481383096064737609 8752110361037322048553207)
    ·
      refine ⟨13128165541555983072829811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8752110361037322048553207 13128165541555983072829811)
      ·
        refine ⟨19692248312333974609244717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13128165541555983072829811 19692248312333974609244717)
        ·
          refine ⟨7384593117125240478466769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19692248312333974609244717 7384593117125240478466769)
          ·
            refine ⟨5538444837843930358850077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7384593117125240478466769 5538444837843930358850077)
            ·
              refine ⟨2076916814191473884568779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5538444837843930358850077 2076916814191473884568779)
              ·
                refine ⟨3115375221287210826853169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2076916814191473884568779 3115375221287210826853169)
                ·
                  refine ⟨2336531415965408120139877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3115375221287210826853169 2336531415965408120139877)
                  ·
                    refine ⟨438099640493514022526227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2336531415965408120139877 438099640493514022526227)
                    ·
                      rfl

theorem cell22_1279794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 1, 2, 4].length) (baseStart_1279794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1279794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1279794 prefixEnd_1279794 := by exact prefixLift 1279794
  have htrace : WordTrace (prefixWord ++ tailWord_1279794) baseStart_1279794 baseEnd_1279794 := by
    simpa [prefixWord, tailWord_1279794, baseEnd_1279794] using wordTrace_append hprefix tailTrace_1279794
  have hstable : (prefixWord ++ tailWord_1279794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279794).length < 2 ^ (prefixWord ++ tailWord_1279794).sum := by decide
  have hdescent : baseEnd_1279794 < baseStart_1279794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279798 : List Nat := [5, 1, 2, 2, 1, 2, 2, 3, 4]
def baseStart_1279798 : Nat := 118140960795 + 1279798 * 2 ^ 59
def prefixEnd_1279798 : Nat := 4983230072969 + 3 ^ 40 * 1279798 * 2
def baseEnd_1279798 : Nat := 146033669925086448475405

theorem tailTrace_1279798 : CollatzResearch.WordTrace tailWord_1279798 prefixEnd_1279798 146033669925086448475405 := by
  unfold tailWord_1279798
  simp only [CollatzResearch.WordTrace]
  refine ⟨2917379238594868308881003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31118711878345261961397365 2917379238594868308881003)
  ·
    refine ⟨4376068857892302463321505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2917379238594868308881003 4376068857892302463321505)
    ·
      refine ⟨3282051643419226847491129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4376068857892302463321505 3282051643419226847491129)
      ·
        refine ⟨2461538732564420135618347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3282051643419226847491129 2461538732564420135618347)
        ·
          refine ⟨3692308098846630203427521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2461538732564420135618347 3692308098846630203427521)
          ·
            refine ⟨2769231074134972652570641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3692308098846630203427521 2769231074134972652570641)
            ·
              refine ⟨2076923305601229489427981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2769231074134972652570641 2076923305601229489427981)
              ·
                refine ⟨778846239600461058535493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2076923305601229489427981 778846239600461058535493)
                ·
                  refine ⟨146033669925086448475405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 778846239600461058535493 146033669925086448475405)
                  ·
                    rfl

theorem cell22_1279798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 3, 4].length) (baseStart_1279798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1279798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1279798 prefixEnd_1279798 := by exact prefixLift 1279798
  have htrace : WordTrace (prefixWord ++ tailWord_1279798) baseStart_1279798 baseEnd_1279798 := by
    simpa [prefixWord, tailWord_1279798, baseEnd_1279798] using wordTrace_append hprefix tailTrace_1279798
  have hstable : (prefixWord ++ tailWord_1279798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279798).length < 2 ^ (prefixWord ++ tailWord_1279798).sum := by decide
  have hdescent : baseEnd_1279798 < baseStart_1279798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279854 : List Nat := [4, 1, 2, 3, 1, 1, 1, 2, 7]
def baseStart_1279854 : Nat := 118140960795 + 1279854 * 2 ^ 59
def prefixEnd_1279854 : Nat := 4983230072969 + 3 ^ 40 * 1279854 * 2
def baseEnd_1279854 : Nat := 146040059906564622008681

theorem tailTrace_1279854 : CollatzResearch.WordTrace tailWord_1279854 prefixEnd_1279854 146040059906564622008681 := by
  unfold tailWord_1279854
  simp only [CollatzResearch.WordTrace]
  refine ⟨5835013788164376813266827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31120073536876676337423077 5835013788164376813266827)
  ·
    refine ⟨8752520682246565219900241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5835013788164376813266827 8752520682246565219900241)
    ·
      refine ⟨6564390511684923914925181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8752520682246565219900241 6564390511684923914925181)
      ·
        refine ⟨2461646441881846468096943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6564390511684923914925181 2461646441881846468096943)
        ·
          refine ⟨3692469662822769702145415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2461646441881846468096943 3692469662822769702145415)
          ·
            refine ⟨5538704494234154553218123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3692469662822769702145415 5538704494234154553218123)
            ·
              refine ⟨8308056741351231829827185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5538704494234154553218123 8308056741351231829827185)
              ·
                refine ⟨6231042556013423872370389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8308056741351231829827185 6231042556013423872370389)
                ·
                  refine ⟨146040059906564622008681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6231042556013423872370389 146040059906564622008681)
                  ·
                    rfl

theorem cell22_1279854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 2, 7].length) (baseStart_1279854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1279854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1279854 prefixEnd_1279854 := by exact prefixLift 1279854
  have htrace : WordTrace (prefixWord ++ tailWord_1279854) baseStart_1279854 baseEnd_1279854 := by
    simpa [prefixWord, tailWord_1279854, baseEnd_1279854] using wordTrace_append hprefix tailTrace_1279854
  have hstable : (prefixWord ++ tailWord_1279854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279854).length < 2 ^ (prefixWord ++ tailWord_1279854).sum := by decide
  have hdescent : baseEnd_1279854 < baseStart_1279854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279867 : List Nat := [1, 1, 1, 1, 1, 5, 1, 2, 5, 4]
def baseStart_1279867 : Nat := 118140960795 + 1279867 * 2 ^ 59
def prefixEnd_1279867 : Nat := 4983230072969 + 3 ^ 40 * 1279867 * 2
def baseEnd_1279867 : Nat := 438124629885366165451003

theorem tailTrace_1279867 : CollatzResearch.WordTrace tailWord_1279867 prefixEnd_1279867 438124629885366165451003 := by
  unfold tailWord_1279867
  simp only [CollatzResearch.WordTrace]
  refine ⟨46680584454267917726357855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31120389636178611817571903 46680584454267917726357855)
  ·
    refine ⟨70020876681401876589536783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46680584454267917726357855 70020876681401876589536783)
    ·
      refine ⟨105031315022102814884305175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70020876681401876589536783 105031315022102814884305175)
      ·
        refine ⟨157546972533154222326457763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105031315022102814884305175 157546972533154222326457763)
        ·
          refine ⟨236320458799731333489686645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157546972533154222326457763 236320458799731333489686645)
          ·
            refine ⟨22155043012474812514658123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 236320458799731333489686645 22155043012474812514658123)
            ·
              refine ⟨33232564518712218771987185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22155043012474812514658123 33232564518712218771987185)
              ·
                refine ⟨24924423389034164078990389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33232564518712218771987185 24924423389034164078990389)
                ·
                  refine ⟨2336664692721952882405349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24924423389034164078990389 2336664692721952882405349)
                  ·
                    refine ⟨438124629885366165451003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2336664692721952882405349 438124629885366165451003)
                    ·
                      rfl

theorem cell22_1279867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 5, 4].length) (baseStart_1279867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1279867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1279867 prefixEnd_1279867 := by exact prefixLift 1279867
  have htrace : WordTrace (prefixWord ++ tailWord_1279867) baseStart_1279867 baseEnd_1279867 := by
    simpa [prefixWord, tailWord_1279867, baseEnd_1279867] using wordTrace_append hprefix tailTrace_1279867
  have hstable : (prefixWord ++ tailWord_1279867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279867).length < 2 ^ (prefixWord ++ tailWord_1279867).sum := by decide
  have hdescent : baseEnd_1279867 < baseStart_1279867 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279901 : List Nat := [1, 4, 2, 1, 2, 2, 3, 2, 1, 4]
def baseStart_1279901 : Nat := 118140960795 + 1279901 * 2 ^ 59
def prefixEnd_1279901 : Nat := 4983230072969 + 3 ^ 40 * 1279901 * 2
def baseEnd_1279901 : Nat := 438136268780201410100899

theorem tailTrace_1279901 : CollatzResearch.WordTrace tailWord_1279901 prefixEnd_1279901 438136268780201410100899 := by
  unfold tailWord_1279901
  simp only [CollatzResearch.WordTrace]
  refine ⟨46681824536144741533095557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31121216357429827688730371 46681824536144741533095557)
  ·
    refine ⟨8752842100527139037455417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46681824536144741533095557 8752842100527139037455417)
    ·
      refine ⟨6564631575395354278091563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8752842100527139037455417 6564631575395354278091563)
      ·
        refine ⟨9846947363093031417137345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6564631575395354278091563 9846947363093031417137345)
        ·
          refine ⟨7385210522319773562853009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9846947363093031417137345 7385210522319773562853009)
          ·
            refine ⟨5538907891739830172139757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7385210522319773562853009 5538907891739830172139757)
            ·
              refine ⟨2077090459402436314552409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5538907891739830172139757 2077090459402436314552409)
              ·
                refine ⟨1557817844551827235914307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2077090459402436314552409 1557817844551827235914307)
                ·
                  refine ⟨2336726766827740853871461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1557817844551827235914307 2336726766827740853871461)
                  ·
                    refine ⟨438136268780201410100899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2336726766827740853871461 438136268780201410100899)
                    ·
                      rfl

theorem cell22_1279901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_1279901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1279901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1279901 prefixEnd_1279901 := by exact prefixLift 1279901
  have htrace : WordTrace (prefixWord ++ tailWord_1279901) baseStart_1279901 baseEnd_1279901 := by
    simpa [prefixWord, tailWord_1279901, baseEnd_1279901] using wordTrace_append hprefix tailTrace_1279901
  have hstable : (prefixWord ++ tailWord_1279901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279901).length < 2 ^ (prefixWord ++ tailWord_1279901).sum := by decide
  have hdescent : baseEnd_1279901 < baseStart_1279901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279929 : List Nat := [1, 2, 1, 4, 2, 1, 1, 4, 2, 4]
def baseStart_1279929 : Nat := 118140960795 + 1279929 * 2 ^ 59
def prefixEnd_1279929 : Nat := 4983230072969 + 3 ^ 40 * 1279929 * 2
def baseEnd_1279929 : Nat := 438145853752418670400813

theorem tailTrace_1279929 : CollatzResearch.WordTrace tailWord_1279929 prefixEnd_1279929 438145853752418670400813 := by
  unfold tailWord_1279929
  simp only [CollatzResearch.WordTrace]
  refine ⟨46682845780043302315114841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31121897186695534876743227 46682845780043302315114841)
  ·
    refine ⟨35012134335032476736336131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46682845780043302315114841 35012134335032476736336131)
    ·
      refine ⟨52518201502548715104504197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35012134335032476736336131 52518201502548715104504197)
      ·
        refine ⟨9847162781727884082094537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52518201502548715104504197 9847162781727884082094537)
        ·
          refine ⟨7385372086295913061570903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9847162781727884082094537 7385372086295913061570903)
          ·
            refine ⟨11078058129443869592356355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7385372086295913061570903 11078058129443869592356355)
            ·
              refine ⟨16617087194165804388534533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11078058129443869592356355 16617087194165804388534533)
              ·
                refine ⟨3115703848906088322850225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16617087194165804388534533 3115703848906088322850225)
                ·
                  refine ⟨2336777886679566242137669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3115703848906088322850225 2336777886679566242137669)
                  ·
                    refine ⟨438145853752418670400813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2336777886679566242137669 438145853752418670400813)
                    ·
                      rfl

theorem cell22_1279929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 4, 2, 4].length) (baseStart_1279929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1279929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1279929 prefixEnd_1279929 := by exact prefixLift 1279929
  have htrace : WordTrace (prefixWord ++ tailWord_1279929) baseStart_1279929 baseEnd_1279929 := by
    simpa [prefixWord, tailWord_1279929, baseEnd_1279929] using wordTrace_append hprefix tailTrace_1279929
  have hstable : (prefixWord ++ tailWord_1279929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279929).length < 2 ^ (prefixWord ++ tailWord_1279929).sum := by decide
  have hdescent : baseEnd_1279929 < baseStart_1279929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279933 : List Nat := [1, 4, 1, 2, 3, 1, 4, 2, 4]
def baseStart_1279933 : Nat := 118140960795 + 1279933 * 2 ^ 59
def prefixEnd_1279933 : Nat := 4983230072969 + 3 ^ 40 * 1279933 * 2
def baseEnd_1279933 : Nat := 146049074344721331100267

theorem tailTrace_1279933 : CollatzResearch.WordTrace tailWord_1279933 prefixEnd_1279933 146049074344721331100267 := by
  unfold tailWord_1279933
  simp only [CollatzResearch.WordTrace]
  refine ⟨46682991672028810998260453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31121994448019207332173635 46682991672028810998260453)
  ·
    refine ⟨8753060938505402062173835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46682991672028810998260453 8753060938505402062173835)
    ·
      refine ⟨13129591407758103093260753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8753060938505402062173835 13129591407758103093260753)
      ·
        refine ⟨9847193555818577319945565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13129591407758103093260753 9847193555818577319945565)
        ·
          refine ⟨3692697583431966494979587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9847193555818577319945565 3692697583431966494979587)
          ·
            refine ⟨5539046375147949742469381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3692697583431966494979587 5539046375147949742469381)
            ·
              refine ⟨1038571195340240576713009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5539046375147949742469381 1038571195340240576713009)
              ·
                refine ⟨778928396505180432534757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1038571195340240576713009 778928396505180432534757)
                ·
                  refine ⟨146049074344721331100267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 778928396505180432534757 146049074344721331100267)
                  ·
                    rfl

theorem cell22_1279933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 4, 2, 4].length) (baseStart_1279933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1279933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1279933 prefixEnd_1279933 := by exact prefixLift 1279933
  have htrace : WordTrace (prefixWord ++ tailWord_1279933) baseStart_1279933 baseEnd_1279933 := by
    simpa [prefixWord, tailWord_1279933, baseEnd_1279933] using wordTrace_append hprefix tailTrace_1279933
  have hstable : (prefixWord ++ tailWord_1279933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279933).length < 2 ^ (prefixWord ++ tailWord_1279933).sum := by decide
  have hdescent : baseEnd_1279933 < baseStart_1279933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279944 : List Nat := [2, 1, 3, 1, 4, 1, 3, 7]
def baseStart_1279944 : Nat := 118140960795 + 1279944 * 2 ^ 59
def prefixEnd_1279944 : Nat := 4983230072969 + 3 ^ 40 * 1279944 * 2
def baseEnd_1279944 : Nat := 48683443173218181252863

theorem tailTrace_1279944 : CollatzResearch.WordTrace tailWord_1279944 prefixEnd_1279944 48683443173218181252863 := by
  unfold tailWord_1279944
  simp only [CollatzResearch.WordTrace]
  refine ⟨23341696437494479938455443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31122261916659306584607257 23341696437494479938455443)
  ·
    refine ⟨35012544656241719907683165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23341696437494479938455443 35012544656241719907683165)
    ·
      refine ⟨13129704246090644965381187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35012544656241719907683165 13129704246090644965381187)
      ·
        refine ⟨19694556369135967448071781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13129704246090644965381187 19694556369135967448071781)
        ·
          refine ⟨3692729319212993896513459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19694556369135967448071781 3692729319212993896513459)
          ·
            refine ⟨5539093978819490844770189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3692729319212993896513459 5539093978819490844770189)
            ·
              refine ⟨2077160242057309066788821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5539093978819490844770189 2077160242057309066788821)
              ·
                refine ⟨48683443173218181252863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2077160242057309066788821 48683443173218181252863)
                ·
                  rfl

theorem cell22_1279944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 7].length) (baseStart_1279944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1279944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1279944 prefixEnd_1279944 := by exact prefixLift 1279944
  have htrace : WordTrace (prefixWord ++ tailWord_1279944) baseStart_1279944 baseEnd_1279944 := by
    simpa [prefixWord, tailWord_1279944, baseEnd_1279944] using wordTrace_append hprefix tailTrace_1279944
  have hstable : (prefixWord ++ tailWord_1279944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279944).length < 2 ^ (prefixWord ++ tailWord_1279944).sum := by decide
  have hdescent : baseEnd_1279944 < baseStart_1279944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279961 : List Nat := [1, 2, 1, 2, 6, 1, 3, 6]
def baseStart_1279961 : Nat := 118140960795 + 1279961 * 2 ^ 59
def prefixEnd_1279961 : Nat := 4983230072969 + 3 ^ 40 * 1279961 * 2
def baseEnd_1279961 : Nat := 48684089778486805955635

theorem tailTrace_1279961 : CollatzResearch.WordTrace tailWord_1279961 prefixEnd_1279961 48684089778486805955635 := by
  unfold tailWord_1279961
  simp only [CollatzResearch.WordTrace]
  refine ⟨46684012915927371780279737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31122675277284914520186491 46684012915927371780279737)
  ·
    refine ⟨35013009686945528835209803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46684012915927371780279737 35013009686945528835209803)
    ·
      refine ⟨52519514530418293252814705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35013009686945528835209803 52519514530418293252814705)
      ·
        refine ⟨39389635897813719939611029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52519514530418293252814705 39389635897813719939611029)
        ·
          refine ⟨1846389182710018122169267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 39389635897813719939611029 1846389182710018122169267)
          ·
            refine ⟨2769583774065027183253901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1846389182710018122169267 2769583774065027183253901)
            ·
              refine ⟨1038593915274385193720213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2769583774065027183253901 1038593915274385193720213)
              ·
                refine ⟨48684089778486805955635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1038593915274385193720213 48684089778486805955635)
                ·
                  rfl

theorem cell22_1279961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 3, 6].length) (baseStart_1279961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1279961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1279961 prefixEnd_1279961 := by exact prefixLift 1279961
  have htrace : WordTrace (prefixWord ++ tailWord_1279961) baseStart_1279961 baseEnd_1279961 := by
    simpa [prefixWord, tailWord_1279961, baseEnd_1279961] using wordTrace_append hprefix tailTrace_1279961
  have hstable : (prefixWord ++ tailWord_1279961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279961).length < 2 ^ (prefixWord ++ tailWord_1279961).sum := by decide
  have hdescent : baseEnd_1279961 < baseStart_1279961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279993 : List Nat := [1, 2, 1, 3, 1, 4, 2, 4, 1, 3]
def baseStart_1279993 : Nat := 118140960795 + 1279993 * 2 ^ 59
def prefixEnd_1279993 : Nat := 4983230072969 + 3 ^ 40 * 1279993 * 2
def baseEnd_1279993 : Nat := 438167762260343836800617

theorem tailTrace_1279993 : CollatzResearch.WordTrace tailWord_1279993 prefixEnd_1279993 438167762260343836800617 := by
  unfold tailWord_1279993
  simp only [CollatzResearch.WordTrace]
  refine ⟨46685180051811441245444633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31123453367874294163629755 46685180051811441245444633)
  ·
    refine ⟨35013885038858580934083475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46685180051811441245444633 35013885038858580934083475)
    ·
      refine ⟨52520827558287871401125213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35013885038858580934083475 52520827558287871401125213)
      ·
        refine ⟨19695310334357951775421955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52520827558287871401125213 19695310334357951775421955)
        ·
          refine ⟨29542965501536927663132933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19695310334357951775421955 29542965501536927663132933)
          ·
            refine ⟨5539306031538173936837425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29542965501536927663132933 5539306031538173936837425)
            ·
              refine ⟨4154479523653630452628069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5539306031538173936837425 4154479523653630452628069)
              ·
                refine ⟨778964910685055709867763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4154479523653630452628069 778964910685055709867763)
                ·
                  refine ⟨1168447366027583564801645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 778964910685055709867763 1168447366027583564801645)
                  ·
                    refine ⟨438167762260343836800617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1168447366027583564801645 438167762260343836800617)
                    ·
                      rfl

theorem cell22_1279993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 4, 1, 3].length) (baseStart_1279993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1279993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1279993 prefixEnd_1279993 := by exact prefixLift 1279993
  have htrace : WordTrace (prefixWord ++ tailWord_1279993) baseStart_1279993 baseEnd_1279993 := by
    simpa [prefixWord, tailWord_1279993, baseEnd_1279993] using wordTrace_append hprefix tailTrace_1279993
  have hstable : (prefixWord ++ tailWord_1279993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279993).length < 2 ^ (prefixWord ++ tailWord_1279993).sum := by decide
  have hdescent : baseEnd_1279993 < baseStart_1279993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280019 : List Nat := [1, 1, 1, 2, 1, 4, 2, 3, 3, 4]
def baseStart_1280019 : Nat := 118140960795 + 1280019 * 2 ^ 59
def prefixEnd_1280019 : Nat := 4983230072969 + 3 ^ 40 * 1280019 * 2
def baseEnd_1280019 : Nat := 438176662591688435650537

theorem tailTrace_1280019 : CollatzResearch.WordTrace tailWord_1280019 prefixEnd_1280019 438176662591688435650537 := by
  unfold tailWord_1280019
  simp only [CollatzResearch.WordTrace]
  refine ⟨46686128349717247685891111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31124085566478165123927407 46686128349717247685891111)
  ·
    refine ⟨70029192524575871528836667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46686128349717247685891111 70029192524575871528836667)
    ·
      refine ⟨105043788786863807293255001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70029192524575871528836667 105043788786863807293255001)
      ·
        refine ⟨78782841590147855469941251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105043788786863807293255001 78782841590147855469941251)
        ·
          refine ⟨118174262385221783204911877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78782841590147855469941251 118174262385221783204911877)
          ·
            refine ⟨22157674197229084350920977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 118174262385221783204911877 22157674197229084350920977)
            ·
              refine ⟨16618255647921813263190733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22157674197229084350920977 16618255647921813263190733)
              ·
                refine ⟨6231845867970679973696525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16618255647921813263190733 6231845867970679973696525)
                ·
                  refine ⟨2336942200489004990136197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6231845867970679973696525 2336942200489004990136197)
                  ·
                    refine ⟨438176662591688435650537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2336942200489004990136197 438176662591688435650537)
                    ·
                      rfl

theorem cell22_1280019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 3, 3, 4].length) (baseStart_1280019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1280019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1280019 prefixEnd_1280019 := by exact prefixLift 1280019
  have htrace : WordTrace (prefixWord ++ tailWord_1280019) baseStart_1280019 baseEnd_1280019 := by
    simpa [prefixWord, tailWord_1280019, baseEnd_1280019] using wordTrace_append hprefix tailTrace_1280019
  have hstable : (prefixWord ++ tailWord_1280019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280019).length < 2 ^ (prefixWord ++ tailWord_1280019).sum := by decide
  have hdescent : baseEnd_1280019 < baseStart_1280019 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280051 : List Nat := [1, 1, 1, 2, 4, 1, 2, 6, 4]
def baseStart_1280051 : Nat := 118140960795 + 1280051 * 2 ^ 59
def prefixEnd_1280051 : Nat := 4983230072969 + 3 ^ 40 * 1280051 * 2
def baseEnd_1280051 : Nat := 146062538948550339616813

theorem tailTrace_1280051 : CollatzResearch.WordTrace tailWord_1280051 prefixEnd_1280051 146062538948550339616813 := by
  unfold tailWord_1280051
  simp only [CollatzResearch.WordTrace]
  refine ⟨46687295485601317151056007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31124863657067544767370671 46687295485601317151056007)
  ·
    refine ⟨70030943228401975726584011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46687295485601317151056007 70030943228401975726584011)
    ·
      refine ⟨105046414842602963589876017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70030943228401975726584011 105046414842602963589876017)
      ·
        refine ⟨78784811131952222692407013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105046414842602963589876017 78784811131952222692407013)
        ·
          refine ⟨14772152087241041754826315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78784811131952222692407013 14772152087241041754826315)
          ·
            refine ⟨22158228130861562632239473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14772152087241041754826315 22158228130861562632239473)
            ·
              refine ⟨16618671098146171974179605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22158228130861562632239473 16618671098146171974179605)
              ·
                refine ⟨779000207725601811289669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16618671098146171974179605 779000207725601811289669)
                ·
                  refine ⟨146062538948550339616813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 779000207725601811289669 146062538948550339616813)
                  ·
                    rfl

theorem cell22_1280051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 6, 4].length) (baseStart_1280051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1280051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1280051 prefixEnd_1280051 := by exact prefixLift 1280051
  have htrace : WordTrace (prefixWord ++ tailWord_1280051) baseStart_1280051 baseEnd_1280051 := by
    simpa [prefixWord, tailWord_1280051, baseEnd_1280051] using wordTrace_append hprefix tailTrace_1280051
  have hstable : (prefixWord ++ tailWord_1280051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280051).length < 2 ^ (prefixWord ++ tailWord_1280051).sum := by decide
  have hdescent : baseEnd_1280051 < baseStart_1280051 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280156 : List Nat := [2, 2, 3, 2, 1, 1, 1, 1, 4, 5]
def baseStart_1280156 : Nat := 118140960795 + 1280156 * 2 ^ 59
def prefixEnd_1280156 : Nat := 4983230072969 + 3 ^ 40 * 1280156 * 2
def baseEnd_1280156 : Nat := 438223560491465744975117

theorem tailTrace_1280156 : CollatzResearch.WordTrace tailWord_1280156 prefixEnd_1280156 438223560491465744975117 := by
  unfold tailWord_1280156
  simp only [CollatzResearch.WordTrace]
  refine ⟨23345562575110460041814161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31127416766813946722418881 23345562575110460041814161)
  ·
    refine ⟨17509171931332845031360621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23345562575110460041814161 17509171931332845031360621)
    ·
      refine ⟨6565939474249816886760233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17509171931332845031360621 6565939474249816886760233)
      ·
        refine ⟨4924454605687362665070175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6565939474249816886760233 4924454605687362665070175)
        ·
          refine ⟨7386681908531043997605263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4924454605687362665070175 7386681908531043997605263)
          ·
            refine ⟨11080022862796565996407895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7386681908531043997605263 11080022862796565996407895)
            ·
              refine ⟨16620034294194848994611843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11080022862796565996407895 16620034294194848994611843)
              ·
                refine ⟨24930051441292273491917765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16620034294194848994611843 24930051441292273491917765)
                ·
                  refine ⟨4674384645242301279734581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24930051441292273491917765 4674384645242301279734581)
                  ·
                    refine ⟨438223560491465744975117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4674384645242301279734581 438223560491465744975117)
                    ·
                      rfl

theorem cell22_1280156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_1280156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1280156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1280156 prefixEnd_1280156 := by exact prefixLift 1280156
  have htrace : WordTrace (prefixWord ++ tailWord_1280156) baseStart_1280156 baseEnd_1280156 := by
    simpa [prefixWord, tailWord_1280156, baseEnd_1280156] using wordTrace_append hprefix tailTrace_1280156
  have hstable : (prefixWord ++ tailWord_1280156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280156).length < 2 ^ (prefixWord ++ tailWord_1280156).sum := by decide
  have hdescent : baseEnd_1280156 < baseStart_1280156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280162 : List Nat := [3, 3, 1, 3, 1, 1, 2, 4, 1, 3]
def baseStart_1280162 : Nat := 118140960795 + 1280162 * 2 ^ 59
def prefixEnd_1280162 : Nat := 4983230072969 + 3 ^ 40 * 1280162 * 2
def baseEnd_1280162 : Nat := 438225614414083729325099

theorem tailTrace_1280162 : CollatzResearch.WordTrace tailWord_1280162 prefixEnd_1280162 438225614414083729325099 := by
  unfold tailWord_1280162
  simp only [CollatzResearch.WordTrace]
  refine ⟨11672835997049795777086685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31127562658799455405564493 11672835997049795777086685)
  ·
    refine ⟨4377313498893673416407507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11672835997049795777086685 4377313498893673416407507)
    ·
      refine ⟨6565970248340510124611261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4377313498893673416407507 6565970248340510124611261)
      ·
        refine ⟨2462238843127691296729223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6565970248340510124611261 2462238843127691296729223)
        ·
          refine ⟨3693358264691536945093835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2462238843127691296729223 3693358264691536945093835)
          ·
            refine ⟨5540037397037305417640753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3693358264691536945093835 5540037397037305417640753)
            ·
              refine ⟨4155028047777979063230565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5540037397037305417640753 4155028047777979063230565)
              ·
                refine ⟨779067758958371074355731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4155028047777979063230565 779067758958371074355731)
                ·
                  refine ⟨1168601638437556611533597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 779067758958371074355731 1168601638437556611533597)
                  ·
                    refine ⟨438225614414083729325099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1168601638437556611533597 438225614414083729325099)
                    ·
                      rfl

theorem cell22_1280162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 4, 1, 3].length) (baseStart_1280162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1280162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1280162 prefixEnd_1280162 := by exact prefixLift 1280162
  have htrace : WordTrace (prefixWord ++ tailWord_1280162) baseStart_1280162 baseEnd_1280162 := by
    simpa [prefixWord, tailWord_1280162, baseEnd_1280162] using wordTrace_append hprefix tailTrace_1280162
  have hstable : (prefixWord ++ tailWord_1280162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280162).length < 2 ^ (prefixWord ++ tailWord_1280162).sum := by decide
  have hdescent : baseEnd_1280162 < baseStart_1280162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280173 : List Nat := [1, 5, 2, 1, 2, 1, 2, 1, 2, 5]
def baseStart_1280173 : Nat := 118140960795 + 1280173 * 2 ^ 59
def prefixEnd_1280173 : Nat := 4983230072969 + 3 ^ 40 * 1280173 * 2
def baseEnd_1280173 : Nat := 438229379938883367300065

theorem tailTrace_1280173 : CollatzResearch.WordTrace tailWord_1280173 prefixEnd_1280173 438229379938883367300065 := by
  unfold tailWord_1280173
  simp only [CollatzResearch.WordTrace]
  refine ⟨46691745191159331986997173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31127830127439554657998115 46691745191159331986997173)
  ·
    refine ⟨4377351111671187373780985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46691745191159331986997173 4377351111671187373780985)
    ·
      refine ⟨3283013333753390530335739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4377351111671187373780985 3283013333753390530335739)
      ·
        refine ⟨4924520000630085795503609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3283013333753390530335739 4924520000630085795503609)
        ·
          refine ⟨3693390000472564346627707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4924520000630085795503609 3693390000472564346627707)
          ·
            refine ⟨5540085000708846519941561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3693390000472564346627707 5540085000708846519941561)
            ·
              refine ⟨4155063750531634889956171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5540085000708846519941561 4155063750531634889956171)
              ·
                refine ⟨6232595625797452334934257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4155063750531634889956171 6232595625797452334934257)
                ·
                  refine ⟨4674446719348089251200693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6232595625797452334934257 4674446719348089251200693)
                  ·
                    refine ⟨438229379938883367300065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4674446719348089251200693 438229379938883367300065)
                    ·
                      rfl

theorem cell22_1280173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_1280173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1280173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1280173 prefixEnd_1280173 := by exact prefixLift 1280173
  have htrace : WordTrace (prefixWord ++ tailWord_1280173) baseStart_1280173 baseEnd_1280173 := by
    simpa [prefixWord, tailWord_1280173, baseEnd_1280173] using wordTrace_append hprefix tailTrace_1280173
  have hstable : (prefixWord ++ tailWord_1280173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280173).length < 2 ^ (prefixWord ++ tailWord_1280173).sum := by decide
  have hdescent : baseEnd_1280173 < baseStart_1280173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280186 : List Nat := [3, 1, 1, 1, 2, 2, 4, 2, 6]
def baseStart_1280186 : Nat := 118140960795 + 1280186 * 2 ^ 59
def prefixEnd_1280186 : Nat := 4983230072969 + 3 ^ 40 * 1280186 * 2
def baseEnd_1280186 : Nat := 146077943368185222241675

theorem tailTrace_1280186 : CollatzResearch.WordTrace tailWord_1280186 prefixEnd_1280186 146077943368185222241675 := by
  unfold tailWord_1280186
  simp only [CollatzResearch.WordTrace]
  refine ⟨11673054835028058801805103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31128146226741490138146941 11673054835028058801805103)
  ·
    refine ⟨17509582252542088202707655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11673054835028058801805103 17509582252542088202707655)
    ·
      refine ⟨26264373378813132304061483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17509582252542088202707655 26264373378813132304061483)
      ·
        refine ⟨39396560068219698456092225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26264373378813132304061483 39396560068219698456092225)
        ·
          refine ⟨29547420051164773842069169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39396560068219698456092225 29547420051164773842069169)
          ·
            refine ⟨22160565038373580381551877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29547420051164773842069169 22160565038373580381551877)
            ·
              refine ⟨4155105944695046321540977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22160565038373580381551877 4155105944695046321540977)
              ·
                refine ⟨3116329458521284741155733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4155105944695046321540977 3116329458521284741155733)
                ·
                  refine ⟨146077943368185222241675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3116329458521284741155733 146077943368185222241675)
                  ·
                    rfl

theorem cell22_1280186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 2, 6].length) (baseStart_1280186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1280186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1280186 prefixEnd_1280186 := by exact prefixLift 1280186
  have htrace : WordTrace (prefixWord ++ tailWord_1280186) baseStart_1280186 baseEnd_1280186 := by
    simpa [prefixWord, tailWord_1280186, baseEnd_1280186] using wordTrace_append hprefix tailTrace_1280186
  have hstable : (prefixWord ++ tailWord_1280186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280186).length < 2 ^ (prefixWord ++ tailWord_1280186).sum := by decide
  have hdescent : baseEnd_1280186 < baseStart_1280186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280218 : List Nat := [3, 1, 1, 2, 2, 1, 4, 1, 4, 3]
def baseStart_1280218 : Nat := 118140960795 + 1280218 * 2 ^ 59
def prefixEnd_1280218 : Nat := 4983230072969 + 3 ^ 40 * 1280218 * 2
def baseEnd_1280218 : Nat := 438244784358518249924927

theorem tailTrace_1280218 : CollatzResearch.WordTrace tailWord_1280218 prefixEnd_1280218 438244784358518249924927 := by
  unfold tailWord_1280218
  simp only [CollatzResearch.WordTrace]
  refine ⟨11673346618999076168096327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31128924317330869781590205 11673346618999076168096327)
  ·
    refine ⟨17510019928498614252144491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11673346618999076168096327 17510019928498614252144491)
    ·
      refine ⟨26265029892747921378216737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17510019928498614252144491 26265029892747921378216737)
      ·
        refine ⟨19698772419560941033662553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26265029892747921378216737 19698772419560941033662553)
        ·
          refine ⟨14774079314670705775246915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19698772419560941033662553 14774079314670705775246915)
          ·
            refine ⟨22161118972006058662870373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14774079314670705775246915 22161118972006058662870373)
            ·
              refine ⟨4155209807251135999288195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22161118972006058662870373 4155209807251135999288195)
              ·
                refine ⟨6232814710876703998932293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4155209807251135999288195 6232814710876703998932293)
                ·
                  refine ⟨1168652758289381999799805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6232814710876703998932293 1168652758289381999799805)
                  ·
                    refine ⟨438244784358518249924927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1168652758289381999799805 438244784358518249924927)
                    ·
                      rfl

theorem cell22_1280218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 1, 4, 3].length) (baseStart_1280218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1280218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1280218 prefixEnd_1280218 := by exact prefixLift 1280218
  have htrace : WordTrace (prefixWord ++ tailWord_1280218) baseStart_1280218 baseEnd_1280218 := by
    simpa [prefixWord, tailWord_1280218, baseEnd_1280218] using wordTrace_append hprefix tailTrace_1280218
  have hstable : (prefixWord ++ tailWord_1280218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280218).length < 2 ^ (prefixWord ++ tailWord_1280218).sum := by decide
  have hdescent : baseEnd_1280218 < baseStart_1280218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280226 : List Nat := [3, 3, 4, 1, 1, 2, 2, 1, 5]
def baseStart_1280226 : Nat := 118140960795 + 1280226 * 2 ^ 59
def prefixEnd_1280226 : Nat := 4983230072969 + 3 ^ 40 * 1280226 * 2
def baseEnd_1280226 : Nat := 146082507640669631908301

theorem tailTrace_1280226 : CollatzResearch.WordTrace tailWord_1280226 prefixEnd_1280226 146082507640669631908301 := by
  unfold tailWord_1280226
  simp only [CollatzResearch.WordTrace]
  refine ⟨11673419564991830509669133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31129118839978214692451021 11673419564991830509669133)
  ·
    refine ⟨4377532336871936441125925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11673419564991830509669133 4377532336871936441125925)
    ·
      refine ⟨820787313163488082711111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4377532336871936441125925 820787313163488082711111)
      ·
        refine ⟨1231180969745232124066667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 820787313163488082711111 1231180969745232124066667)
        ·
          refine ⟨1846771454617848186100001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1231180969745232124066667 1846771454617848186100001)
          ·
            refine ⟨1385078590963386139575001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1846771454617848186100001 1385078590963386139575001)
            ·
              refine ⟨1038808943222539604681251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1385078590963386139575001 1038808943222539604681251)
              ·
                refine ⟨1558213414833809407021877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1038808943222539604681251 1558213414833809407021877)
                ·
                  refine ⟨146082507640669631908301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1558213414833809407021877 146082507640669631908301)
                  ·
                    rfl

theorem cell22_1280226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 2, 1, 5].length) (baseStart_1280226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1280226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1280226 prefixEnd_1280226 := by exact prefixLift 1280226
  have htrace : WordTrace (prefixWord ++ tailWord_1280226) baseStart_1280226 baseEnd_1280226 := by
    simpa [prefixWord, tailWord_1280226, baseEnd_1280226] using wordTrace_append hprefix tailTrace_1280226
  have hstable : (prefixWord ++ tailWord_1280226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280226).length < 2 ^ (prefixWord ++ tailWord_1280226).sum := by decide
  have hdescent : baseEnd_1280226 < baseStart_1280226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280338 : List Nat := [3, 2, 2, 1, 1, 1, 3, 3, 6]
def baseStart_1280338 : Nat := 118140960795 + 1280338 * 2 ^ 59
def prefixEnd_1280338 : Nat := 4983230072969 + 3 ^ 40 * 1280338 * 2
def baseEnd_1280338 : Nat := 146095287603625978974853

theorem tailTrace_1280338 : CollatzResearch.WordTrace tailWord_1280338 prefixEnd_1280338 146095287603625978974853 := by
  unfold tailWord_1280338
  simp only [CollatzResearch.WordTrace]
  refine ⟨11674440808890391291688417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31131842157041043444502445 11674440808890391291688417)
  ·
    refine ⟨8755830606667793468766313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11674440808890391291688417 8755830606667793468766313)
    ·
      refine ⟨6566872955000845101574735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8755830606667793468766313 6566872955000845101574735)
      ·
        refine ⟨9850309432501267652362103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6566872955000845101574735 9850309432501267652362103)
        ·
          refine ⟨14775464148751901478543155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9850309432501267652362103 14775464148751901478543155)
          ·
            refine ⟨22163196223127852217814733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14775464148751901478543155 22163196223127852217814733)
            ·
              refine ⟨8311198583672944581680525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22163196223127852217814733 8311198583672944581680525)
              ·
                refine ⟨3116699468877354218130197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8311198583672944581680525 3116699468877354218130197)
                ·
                  refine ⟨146095287603625978974853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3116699468877354218130197 146095287603625978974853)
                  ·
                    rfl

theorem cell22_1280338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 3, 6].length) (baseStart_1280338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1280338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1280338 prefixEnd_1280338 := by exact prefixLift 1280338
  have htrace : WordTrace (prefixWord ++ tailWord_1280338) baseStart_1280338 baseEnd_1280338 := by
    simpa [prefixWord, tailWord_1280338, baseEnd_1280338] using wordTrace_append hprefix tailTrace_1280338
  have hstable : (prefixWord ++ tailWord_1280338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280338).length < 2 ^ (prefixWord ++ tailWord_1280338).sum := by decide
  have hdescent : baseEnd_1280338 < baseStart_1280338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280368 : List Nat := [2, 1, 1, 1, 4, 3, 2, 1, 1, 6]
def baseStart_1280368 : Nat := 118140960795 + 1280368 * 2 ^ 59
def prefixEnd_1280368 : Nat := 4983230072969 + 3 ^ 40 * 1280368 * 2
def baseEnd_1280368 : Nat := 438296132423967858674467

theorem tailTrace_1280368 : CollatzResearch.WordTrace tailWord_1280368 prefixEnd_1280368 438296132423967858674467 := by
  unfold tailWord_1280368
  simp only [CollatzResearch.WordTrace]
  refine ⟨23349428712726440145172879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31132571616968586860230505 23349428712726440145172879)
  ·
    refine ⟨35024143069089660217759319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23349428712726440145172879 35024143069089660217759319)
    ·
      refine ⟨52536214603634490326638979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35024143069089660217759319 52536214603634490326638979)
      ·
        refine ⟨78804321905451735489958469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52536214603634490326638979 78804321905451735489958469)
        ·
          refine ⟨14775810357272200404367213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78804321905451735489958469 14775810357272200404367213)
          ·
            refine ⟨5540928883977075151637705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14775810357272200404367213 5540928883977075151637705)
            ·
              refine ⟨4155696662982806363728279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5540928883977075151637705 4155696662982806363728279)
              ·
                refine ⟨6233544994474209545592419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4155696662982806363728279 6233544994474209545592419)
                ·
                  refine ⟨9350317491711314318388629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6233544994474209545592419 9350317491711314318388629)
                  ·
                    refine ⟨438296132423967858674467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9350317491711314318388629 438296132423967858674467)
                    ·
                      rfl

theorem cell22_1280368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 1, 1, 6].length) (baseStart_1280368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1280368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1280368 prefixEnd_1280368 := by exact prefixLift 1280368
  have htrace : WordTrace (prefixWord ++ tailWord_1280368) baseStart_1280368 baseEnd_1280368 := by
    simpa [prefixWord, tailWord_1280368, baseEnd_1280368] using wordTrace_append hprefix tailTrace_1280368
  have hstable : (prefixWord ++ tailWord_1280368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280368).length < 2 ^ (prefixWord ++ tailWord_1280368).sum := by decide
  have hdescent : baseEnd_1280368 < baseStart_1280368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280370 : List Nat := [3, 2, 1, 2, 1, 3, 1, 2, 4, 3]
def baseStart_1280370 : Nat := 118140960795 + 1280370 * 2 ^ 59
def prefixEnd_1280370 : Nat := 4983230072969 + 3 ^ 40 * 1280370 * 2
def baseEnd_1280370 : Nat := 438296817064840520124461

theorem tailTrace_1280370 : CollatzResearch.WordTrace tailWord_1280370 prefixEnd_1280370 438296817064840520124461 := by
  unfold tailWord_1280370
  simp only [CollatzResearch.WordTrace]
  refine ⟨11674732592861408657979641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31132620247630423087945709 11674732592861408657979641)
  ·
    refine ⟨8756049444646056493484731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11674732592861408657979641 8756049444646056493484731)
    ·
      refine ⟨13134074166969084740227097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8756049444646056493484731 13134074166969084740227097)
      ·
        refine ⟨9850555625226813555170323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13134074166969084740227097 9850555625226813555170323)
        ·
          refine ⟨14775833437840220332755485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9850555625226813555170323 14775833437840220332755485)
          ·
            refine ⟨5540937539190082624783307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14775833437840220332755485 5540937539190082624783307)
            ·
              refine ⟨8311406308785123937174961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5540937539190082624783307 8311406308785123937174961)
              ·
                refine ⟨6233554731588842952881221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8311406308785123937174961 6233554731588842952881221)
                ·
                  refine ⟨1168791512172908053665229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6233554731588842952881221 1168791512172908053665229)
                  ·
                    refine ⟨438296817064840520124461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1168791512172908053665229 438296817064840520124461)
                    ·
                      rfl

theorem cell22_1280370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 2, 4, 3].length) (baseStart_1280370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1280370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1280370 prefixEnd_1280370 := by exact prefixLift 1280370
  have htrace : WordTrace (prefixWord ++ tailWord_1280370) baseStart_1280370 baseEnd_1280370 := by
    simpa [prefixWord, tailWord_1280370, baseEnd_1280370] using wordTrace_append hprefix tailTrace_1280370
  have hstable : (prefixWord ++ tailWord_1280370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280370).length < 2 ^ (prefixWord ++ tailWord_1280370).sum := by decide
  have hdescent : baseEnd_1280370 < baseStart_1280370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280385 : List Nat := [1, 2, 4, 3, 1, 1, 1, 1, 4, 4]
def baseStart_1280385 : Nat := 118140960795 + 1280385 * 2 ^ 59
def prefixEnd_1280385 : Nat := 4983230072969 + 3 ^ 40 * 1280385 * 2
def baseEnd_1280385 : Nat := 438301951871385480999415

theorem tailTrace_1280385 : CollatzResearch.WordTrace tailWord_1280385 prefixEnd_1280385 438301951871385480999415 := by
  unfold tailWord_1280385
  simp only [CollatzResearch.WordTrace]
  refine ⟨46699477466391292193714609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31132984977594194795809739 46699477466391292193714609)
  ·
    refine ⟨35024608099793469145285957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46699477466391292193714609 35024608099793469145285957)
    ·
      refine ⟨6567114018711275464741117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35024608099793469145285957 6567114018711275464741117)
      ·
        refine ⟨2462667757016728299277919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6567114018711275464741117 2462667757016728299277919)
        ·
          refine ⟨3694001635525092448916879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2462667757016728299277919 3694001635525092448916879)
          ·
            refine ⟨5541002453287638673375319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3694001635525092448916879 5541002453287638673375319)
            ·
              refine ⟨8311503679931458010062979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5541002453287638673375319 8311503679931458010062979)
              ·
                refine ⟨12467255519897187015094469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8311503679931458010062979 12467255519897187015094469)
                ·
                  refine ⟨2337610409980722565330213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12467255519897187015094469 2337610409980722565330213)
                  ·
                    refine ⟨438301951871385480999415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2337610409980722565330213 438301951871385480999415)
                    ·
                      rfl

theorem cell22_1280385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_1280385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1280385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1280385 prefixEnd_1280385 := by exact prefixLift 1280385
  have htrace : WordTrace (prefixWord ++ tailWord_1280385) baseStart_1280385 baseEnd_1280385 := by
    simpa [prefixWord, tailWord_1280385, baseEnd_1280385] using wordTrace_append hprefix tailTrace_1280385
  have hstable : (prefixWord ++ tailWord_1280385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280385).length < 2 ^ (prefixWord ++ tailWord_1280385).sum := by decide
  have hdescent : baseEnd_1280385 < baseStart_1280385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280404 : List Nat := [2, 4, 2, 1, 3, 1, 1, 3, 2, 3]
def baseStart_1280404 : Nat := 118140960795 + 1280404 * 2 ^ 59
def prefixEnd_1280404 : Nat := 4983230072969 + 3 ^ 40 * 1280404 * 2
def baseEnd_1280404 : Nat := 438308455959675764774357

theorem tailTrace_1280404 : CollatzResearch.WordTrace tailWord_1280404 prefixEnd_1280404 438308455959675764774357 := by
  unfold tailWord_1280404
  simp only [CollatzResearch.WordTrace]
  refine ⟨23350085226661229219328133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31133446968881638959104177 23350085226661229219328133)
  ·
    refine ⟨4378140979998980478624025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23350085226661229219328133 4378140979998980478624025)
    ·
      refine ⟨3283605734999235358968019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4378140979998980478624025 3283605734999235358968019)
      ·
        refine ⟨4925408602498853038452029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3283605734999235358968019 4925408602498853038452029)
        ·
          refine ⟨1847028225937069889419511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4925408602498853038452029 1847028225937069889419511)
          ·
            refine ⟨2770542338905604834129267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1847028225937069889419511 2770542338905604834129267)
            ·
              refine ⟨4155813508358407251193901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2770542338905604834129267 4155813508358407251193901)
              ·
                refine ⟨1558430065634402719197713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4155813508358407251193901 1558430065634402719197713)
                ·
                  refine ⟨1168822549225802039398285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1558430065634402719197713 1168822549225802039398285)
                  ·
                    refine ⟨438308455959675764774357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1168822549225802039398285 438308455959675764774357)
                    ·
                      rfl

theorem cell22_1280404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_1280404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1280404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1280404 prefixEnd_1280404 := by exact prefixLift 1280404
  have htrace : WordTrace (prefixWord ++ tailWord_1280404) baseStart_1280404 baseEnd_1280404 := by
    simpa [prefixWord, tailWord_1280404, baseEnd_1280404] using wordTrace_append hprefix tailTrace_1280404
  have hstable : (prefixWord ++ tailWord_1280404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280404).length < 2 ^ (prefixWord ++ tailWord_1280404).sum := by decide
  have hdescent : baseEnd_1280404 < baseStart_1280404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280415 : List Nat := [1, 1, 2, 5, 1, 1, 2, 1, 5, 3]
def baseStart_1280415 : Nat := 118140960795 + 1280415 * 2 ^ 59
def prefixEnd_1280415 : Nat := 4983230072969 + 3 ^ 40 * 1280415 * 2
def baseEnd_1280415 : Nat := 438312221484475402749323

theorem tailTrace_1280415 : CollatzResearch.WordTrace tailWord_1280415 prefixEnd_1280415 438312221484475402749323 := by
  unfold tailWord_1280415
  simp only [CollatzResearch.WordTrace]
  refine ⟨46700571656282607317306699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31133714437521738211537799 46700571656282607317306699)
  ·
    refine ⟨70050857484423910975960049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46700571656282607317306699 70050857484423910975960049)
    ·
      refine ⟨52538143113317933231970037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70050857484423910975960049 52538143113317933231970037)
      ·
        refine ⟨4925450916873556240497191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 52538143113317933231970037 4925450916873556240497191)
        ·
          refine ⟨7388176375310334360745787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4925450916873556240497191 7388176375310334360745787)
          ·
            refine ⟨11082264562965501541118681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7388176375310334360745787 11082264562965501541118681)
            ·
              refine ⟨8311698422224126155839011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11082264562965501541118681 8311698422224126155839011)
              ·
                refine ⟨12467547633336189233758517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8311698422224126155839011 12467547633336189233758517)
                ·
                  refine ⟨1168832590625267740664861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12467547633336189233758517 1168832590625267740664861)
                  ·
                    refine ⟨438312221484475402749323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1168832590625267740664861 438312221484475402749323)
                    ·
                      rfl

theorem cell22_1280415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 5, 3].length) (baseStart_1280415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1280415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1280415 prefixEnd_1280415 := by exact prefixLift 1280415
  have htrace : WordTrace (prefixWord ++ tailWord_1280415) baseStart_1280415 baseEnd_1280415 := by
    simpa [prefixWord, tailWord_1280415, baseEnd_1280415] using wordTrace_append hprefix tailTrace_1280415
  have hstable : (prefixWord ++ tailWord_1280415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280415).length < 2 ^ (prefixWord ++ tailWord_1280415).sum := by decide
  have hdescent : baseEnd_1280415 < baseStart_1280415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280445 : List Nat := [1, 4, 1, 2, 2, 2, 1, 4, 5]
def baseStart_1280445 : Nat := 118140960795 + 1280445 * 2 ^ 59
def prefixEnd_1280445 : Nat := 4983230072969 + 3 ^ 40 * 1280445 * 2
def baseEnd_1280445 : Nat := 146107497032521774833077

theorem tailTrace_1280445 : CollatzResearch.WordTrace tailWord_1280445 prefixEnd_1280445 146107497032521774833077 := by
  unfold tailWord_1280445
  simp only [CollatzResearch.WordTrace]
  refine ⟨46701665846173922440898789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31134443897449281627265859 46701665846173922440898789)
  ·
    refine ⟨8756562346157610457668523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46701665846173922440898789 8756562346157610457668523)
    ·
      refine ⟨13134843519236415686502785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8756562346157610457668523 13134843519236415686502785)
      ·
        refine ⟨9851132639427311764877089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13134843519236415686502785 9851132639427311764877089)
        ·
          refine ⟨7388349479570483823657817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9851132639427311764877089 7388349479570483823657817)
          ·
            refine ⟨5541262109677862867743363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7388349479570483823657817 5541262109677862867743363)
            ·
              refine ⟨8311893164516794301615045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5541262109677862867743363 8311893164516794301615045)
              ·
                refine ⟨1558479968346898931552821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8311893164516794301615045 1558479968346898931552821)
                ·
                  refine ⟨146107497032521774833077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1558479968346898931552821 146107497032521774833077)
                  ·
                    rfl

theorem cell22_1280445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 4, 5].length) (baseStart_1280445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1280445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1280445 prefixEnd_1280445 := by exact prefixLift 1280445
  have htrace : WordTrace (prefixWord ++ tailWord_1280445) baseStart_1280445 baseEnd_1280445 := by
    simpa [prefixWord, tailWord_1280445, baseEnd_1280445] using wordTrace_append hprefix tailTrace_1280445
  have hstable : (prefixWord ++ tailWord_1280445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280445).length < 2 ^ (prefixWord ++ tailWord_1280445).sum := by decide
  have hdescent : baseEnd_1280445 < baseStart_1280445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280552 : List Nat := [2, 1, 5, 2, 1, 3, 8]
def baseStart_1280552 : Nat := 118140960795 + 1280552 * 2 ^ 59
def prefixEnd_1280552 : Nat := 4983230072969 + 3 ^ 40 * 1280552 * 2
def baseEnd_1280552 : Nat := 16235522940157507854589

theorem tailTrace_1280552 : CollatzResearch.WordTrace tailWord_1280552 prefixEnd_1280552 16235522940157507854589 := by
  unfold tailWord_1280552
  simp only [CollatzResearch.WordTrace]
  refine ⟨23352784228393139857521955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31137045637857519810029273 23352784228393139857521955)
  ·
    refine ⟨35029176342589709786282933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23352784228393139857521955 35029176342589709786282933)
    ·
      refine ⟨3283985282117785292464025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35029176342589709786282933 3283985282117785292464025)
      ·
        refine ⟨2462988961588338969348019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3283985282117785292464025 2462988961588338969348019)
        ·
          refine ⟨3694483442382508454022029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2462988961588338969348019 3694483442382508454022029)
          ·
            refine ⟨1385431290893440670258261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3694483442382508454022029 1385431290893440670258261)
            ·
              refine ⟨16235522940157507854589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1385431290893440670258261 16235522940157507854589)
              ·
                rfl

theorem cell22_1280552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 8].length) (baseStart_1280552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1280552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1280552 prefixEnd_1280552 := by exact prefixLift 1280552
  have htrace : WordTrace (prefixWord ++ tailWord_1280552) baseStart_1280552 baseEnd_1280552 := by
    simpa [prefixWord, tailWord_1280552, baseEnd_1280552] using wordTrace_append hprefix tailTrace_1280552
  have hstable : (prefixWord ++ tailWord_1280552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280552).length < 2 ^ (prefixWord ++ tailWord_1280552).sum := by decide
  have hdescent : baseEnd_1280552 < baseStart_1280552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280565 : List Nat := [1, 3, 3, 1, 1, 2, 2, 1, 2, 6]
def baseStart_1280565 : Nat := 118140960795 + 1280565 * 2 ^ 59
def prefixEnd_1280565 : Nat := 4983230072969 + 3 ^ 40 * 1280565 * 2
def baseEnd_1280565 : Nat := 438363569549925011498863

theorem tailTrace_1280565 : CollatzResearch.WordTrace tailWord_1280565 prefixEnd_1280565 438363569549925011498863 := by
  unfold tailWord_1280565
  simp only [CollatzResearch.WordTrace]
  refine ⟨46706042605739182935267149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31137361737159455290178099 46706042605739182935267149)
  ·
    refine ⟨17514765977152193600725181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46706042605739182935267149 17514765977152193600725181)
    ·
      refine ⟨6568037241432072600271943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17514765977152193600725181 6568037241432072600271943)
      ·
        refine ⟨9852055862148108900407915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6568037241432072600271943 9852055862148108900407915)
        ·
          refine ⟨14778083793222163350611873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9852055862148108900407915 14778083793222163350611873)
          ·
            refine ⟨11083562844916622512958905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14778083793222163350611873 11083562844916622512958905)
            ·
              refine ⟨8312672133687466884719179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11083562844916622512958905 8312672133687466884719179)
              ·
                refine ⟨12469008200531200327078769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8312672133687466884719179 12469008200531200327078769)
                ·
                  refine ⟨9351756150398400245309077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12469008200531200327078769 9351756150398400245309077)
                  ·
                    refine ⟨438363569549925011498863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9351756150398400245309077 438363569549925011498863)
                    ·
                      rfl

theorem cell22_1280565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_1280565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1280565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1280565 prefixEnd_1280565 := by exact prefixLift 1280565
  have htrace : WordTrace (prefixWord ++ tailWord_1280565) baseStart_1280565 baseEnd_1280565 := by
    simpa [prefixWord, tailWord_1280565, baseEnd_1280565] using wordTrace_append hprefix tailTrace_1280565
  have hstable : (prefixWord ++ tailWord_1280565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280565).length < 2 ^ (prefixWord ++ tailWord_1280565).sum := by decide
  have hdescent : baseEnd_1280565 < baseStart_1280565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280629 : List Nat := [1, 3, 4, 2, 2, 1, 1, 1, 2, 5]
def baseStart_1280629 : Nat := 118140960795 + 1280629 * 2 ^ 59
def prefixEnd_1280629 : Nat := 4983230072969 + 3 ^ 40 * 1280629 * 2
def baseEnd_1280629 : Nat := 438385478057850177898667

theorem tailTrace_1280629 : CollatzResearch.WordTrace tailWord_1280629 prefixEnd_1280629 438385478057850177898667 := by
  unfold tailWord_1280629
  simp only [CollatzResearch.WordTrace]
  refine ⟨46708376877507321865596941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31138917918338214577064627 46708376877507321865596941)
  ·
    refine ⟨17515641329065245699598853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46708376877507321865596941 17515641329065245699598853)
    ·
      refine ⟨3284182749199733568674785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17515641329065245699598853 3284182749199733568674785)
      ·
        refine ⟨2463137061899800176506089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3284182749199733568674785 2463137061899800176506089)
        ·
          refine ⟨1847352796424850132379567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2463137061899800176506089 1847352796424850132379567)
          ·
            refine ⟨2771029194637275198569351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1847352796424850132379567 2771029194637275198569351)
            ·
              refine ⟨4156543791955912797854027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2771029194637275198569351 4156543791955912797854027)
              ·
                refine ⟨6234815687933869196781041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4156543791955912797854027 6234815687933869196781041)
                ·
                  refine ⟨4676111765950401897585781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6234815687933869196781041 4676111765950401897585781)
                  ·
                    refine ⟨438385478057850177898667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4676111765950401897585781 438385478057850177898667)
                    ·
                      rfl

theorem cell22_1280629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_1280629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1280629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1280629 prefixEnd_1280629 := by exact prefixLift 1280629
  have htrace : WordTrace (prefixWord ++ tailWord_1280629) baseStart_1280629 baseEnd_1280629 := by
    simpa [prefixWord, tailWord_1280629, baseEnd_1280629] using wordTrace_append hprefix tailTrace_1280629
  have hstable : (prefixWord ++ tailWord_1280629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280629).length < 2 ^ (prefixWord ++ tailWord_1280629).sum := by decide
  have hdescent : baseEnd_1280629 < baseStart_1280629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280655 : List Nat := [1, 1, 2, 1, 1, 1, 1, 7, 1, 6]
def baseStart_1280655 : Nat := 118140960795 + 1280655 * 2 ^ 59
def prefixEnd_1280655 : Nat := 4983230072969 + 3 ^ 40 * 1280655 * 2
def baseEnd_1280655 : Nat := 438394378389194776748587

theorem tailTrace_1280655 : CollatzResearch.WordTrace tailWord_1280655 prefixEnd_1280655 438394378389194776748587 := by
  unfold tailWord_1280655
  simp only [CollatzResearch.WordTrace]
  refine ⟨46709325175413128306043419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31139550116942085537362279 46709325175413128306043419)
  ·
    refine ⟨70063987763119692459065129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46709325175413128306043419 70063987763119692459065129)
    ·
      refine ⟨52547990822339769344298847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70063987763119692459065129 52547990822339769344298847)
      ·
        refine ⟨78821986233509654016448271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52547990822339769344298847 78821986233509654016448271)
        ·
          refine ⟨118232979350264481024672407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78821986233509654016448271 118232979350264481024672407)
          ·
            refine ⟨177349469025396721537008611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118232979350264481024672407 177349469025396721537008611)
            ·
              refine ⟨266024203538095082305512917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177349469025396721537008611 266024203538095082305512917)
              ·
                refine ⟨6234942270424103491535459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 266024203538095082305512917 6234942270424103491535459)
                ·
                  refine ⟨9352413405636155237303189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6234942270424103491535459 9352413405636155237303189)
                  ·
                    refine ⟨438394378389194776748587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9352413405636155237303189 438394378389194776748587)
                    ·
                      rfl

theorem cell22_1280655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 7, 1, 6].length) (baseStart_1280655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1280655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1280655 prefixEnd_1280655 := by exact prefixLift 1280655
  have htrace : WordTrace (prefixWord ++ tailWord_1280655) baseStart_1280655 baseEnd_1280655 := by
    simpa [prefixWord, tailWord_1280655, baseEnd_1280655] using wordTrace_append hprefix tailTrace_1280655
  have hstable : (prefixWord ++ tailWord_1280655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280655).length < 2 ^ (prefixWord ++ tailWord_1280655).sum := by decide
  have hdescent : baseEnd_1280655 < baseStart_1280655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280691 : List Nat := [1, 1, 1, 2, 3, 5, 3, 1, 2, 3]
def baseStart_1280691 : Nat := 118140960795 + 1280691 * 2 ^ 59
def prefixEnd_1280691 : Nat := 4983230072969 + 3 ^ 40 * 1280691 * 2
def baseEnd_1280691 : Nat := 438406701924902682848477

theorem tailTrace_1280691 : CollatzResearch.WordTrace tailWord_1280691 prefixEnd_1280691 438406701924902682848477 := by
  unfold tailWord_1280691
  simp only [CollatzResearch.WordTrace]
  refine ⟨46710638203282706454353927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31140425468855137636235951 46710638203282706454353927)
  ·
    refine ⟨70065957304924059681530891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46710638203282706454353927 70065957304924059681530891)
    ·
      refine ⟨105098935957386089522296337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70065957304924059681530891 105098935957386089522296337)
      ·
        refine ⟨78824201968039567141722253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105098935957386089522296337 78824201968039567141722253)
        ·
          refine ⟨29559075738014837678145845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78824201968039567141722253 29559075738014837678145845)
          ·
            refine ⟨2771163350438891032326173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29559075738014837678145845 2771163350438891032326173)
            ·
              refine ⟨1039186256414584137122315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2771163350438891032326173 1039186256414584137122315)
              ·
                refine ⟨1558779384621876205683473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1039186256414584137122315 1558779384621876205683473)
                ·
                  refine ⟨1169084538466407154262605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1558779384621876205683473 1169084538466407154262605)
                  ·
                    refine ⟨438406701924902682848477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1169084538466407154262605 438406701924902682848477)
                    ·
                      rfl

theorem cell22_1280691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 3, 1, 2, 3].length) (baseStart_1280691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1280691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1280691 prefixEnd_1280691 := by exact prefixLift 1280691
  have htrace : WordTrace (prefixWord ++ tailWord_1280691) baseStart_1280691 baseEnd_1280691 := by
    simpa [prefixWord, tailWord_1280691, baseEnd_1280691] using wordTrace_append hprefix tailTrace_1280691
  have hstable : (prefixWord ++ tailWord_1280691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280691).length < 2 ^ (prefixWord ++ tailWord_1280691).sum := by decide
  have hdescent : baseEnd_1280691 < baseStart_1280691 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280702 : List Nat := [4, 2, 1, 1, 2, 1, 1, 1, 2, 7]
def baseStart_1280702 : Nat := 118140960795 + 1280702 * 2 ^ 59
def prefixEnd_1280702 : Nat := 4983230072969 + 3 ^ 40 * 1280702 * 2
def baseEnd_1280702 : Nat := 438410467449702320823443

theorem tailTrace_1280702 : CollatzResearch.WordTrace tailWord_1280702 prefixEnd_1280702 438410467449702320823443 := by
  unfold tailWord_1280702
  simp only [CollatzResearch.WordTrace]
  refine ⟨5838879925780356916625545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31140692937495236888669573 5838879925780356916625545)
  ·
    refine ⟨4379159944335267687469159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5838879925780356916625545 4379159944335267687469159)
    ·
      refine ⟨6568739916502901531203739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4379159944335267687469159 6568739916502901531203739)
      ·
        refine ⟨9853109874754352296805609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6568739916502901531203739 9853109874754352296805609)
        ·
          refine ⟨7389832406065764222604207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9853109874754352296805609 7389832406065764222604207)
          ·
            refine ⟨11084748609098646333906311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7389832406065764222604207 11084748609098646333906311)
            ·
              refine ⟨16627122913647969500859467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11084748609098646333906311 16627122913647969500859467)
              ·
                refine ⟨24940684370471954251289201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16627122913647969500859467 24940684370471954251289201)
                ·
                  refine ⟨18705513277853965688466901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24940684370471954251289201 18705513277853965688466901)
                  ·
                    refine ⟨438410467449702320823443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18705513277853965688466901 438410467449702320823443)
                    ·
                      rfl

theorem cell22_1280702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_1280702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1280702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1280702 prefixEnd_1280702 := by exact prefixLift 1280702
  have htrace : WordTrace (prefixWord ++ tailWord_1280702) baseStart_1280702 baseEnd_1280702 := by
    simpa [prefixWord, tailWord_1280702, baseEnd_1280702] using wordTrace_append hprefix tailTrace_1280702
  have hstable : (prefixWord ++ tailWord_1280702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280702).length < 2 ^ (prefixWord ++ tailWord_1280702).sum := by decide
  have hdescent : baseEnd_1280702 < baseStart_1280702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280704 : List Nat := [2, 1, 1, 2, 4, 4, 2, 6]
def baseStart_1280704 : Nat := 118140960795 + 1280704 * 2 ^ 59
def prefixEnd_1280704 : Nat := 4983230072969 + 3 ^ 40 * 1280704 * 2
def baseEnd_1280704 : Nat := 48712350232286109141493

theorem tailTrace_1280704 : CollatzResearch.WordTrace tailWord_1280704 prefixEnd_1280704 48712350232286109141493 := by
  unfold tailWord_1280704
  simp only [CollatzResearch.WordTrace]
  refine ⟨23355556176117804837288583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31140741568157073116384777 23355556176117804837288583)
  ·
    refine ⟨35033334264176707255932875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23355556176117804837288583 35033334264176707255932875)
    ·
      refine ⟨52550001396265060883899313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35033334264176707255932875 52550001396265060883899313)
      ·
        refine ⟨39412501047198795662924485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52550001396265060883899313 39412501047198795662924485)
        ·
          refine ⟨7389843946349774186798341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39412501047198795662924485 7389843946349774186798341)
          ·
            refine ⟨1385595739940582660024689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7389843946349774186798341 1385595739940582660024689)
            ·
              refine ⟨1039196804955436995018517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1385595739940582660024689 1039196804955436995018517)
              ·
                refine ⟨48712350232286109141493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1039196804955436995018517 48712350232286109141493)
                ·
                  rfl

theorem cell22_1280704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 2, 6].length) (baseStart_1280704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1280704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1280704 prefixEnd_1280704 := by exact prefixLift 1280704
  have htrace : WordTrace (prefixWord ++ tailWord_1280704) baseStart_1280704 baseEnd_1280704 := by
    simpa [prefixWord, tailWord_1280704, baseEnd_1280704] using wordTrace_append hprefix tailTrace_1280704
  have hstable : (prefixWord ++ tailWord_1280704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280704).length < 2 ^ (prefixWord ++ tailWord_1280704).sum := by decide
  have hdescent : baseEnd_1280704 < baseStart_1280704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280749 : List Nat := [1, 5, 1, 2, 1, 1, 3, 3, 5]
def baseStart_1280749 : Nat := 118140960795 + 1280749 * 2 ^ 59
def prefixEnd_1280749 : Nat := 4983230072969 + 3 ^ 40 * 1280749 * 2
def baseEnd_1280749 : Nat := 146142185503403288299433

theorem tailTrace_1280749 : CollatzResearch.WordTrace tailWord_1280749 prefixEnd_1280749 146142185503403288299433 := by
  unfold tailWord_1280749
  simp only [CollatzResearch.WordTrace]
  refine ⟨46712753637072582359965301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31141835758048388239976867 46712753637072582359965301)
  ·
    refine ⟨4379320653475554596246747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46712753637072582359965301 4379320653475554596246747)
    ·
      refine ⟨6568980980213331894370121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4379320653475554596246747 6568980980213331894370121)
      ·
        refine ⟨4926735735159998920777591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6568980980213331894370121 4926735735159998920777591)
        ·
          refine ⟨7390103602739998381166387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4926735735159998920777591 7390103602739998381166387)
          ·
            refine ⟨11085155404109997571749581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7390103602739998381166387 11085155404109997571749581)
            ·
              refine ⟨4156933276541249089406093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11085155404109997571749581 4156933276541249089406093)
              ·
                refine ⟨1558849978702968408527285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4156933276541249089406093 1558849978702968408527285)
                ·
                  refine ⟨146142185503403288299433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1558849978702968408527285 146142185503403288299433)
                  ·
                    rfl

theorem cell22_1280749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 3, 5].length) (baseStart_1280749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1280749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1280749 prefixEnd_1280749 := by exact prefixLift 1280749
  have htrace : WordTrace (prefixWord ++ tailWord_1280749) baseStart_1280749 baseEnd_1280749 := by
    simpa [prefixWord, tailWord_1280749, baseEnd_1280749] using wordTrace_append hprefix tailTrace_1280749
  have hstable : (prefixWord ++ tailWord_1280749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280749).length < 2 ^ (prefixWord ++ tailWord_1280749).sum := by decide
  have hdescent : baseEnd_1280749 < baseStart_1280749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280792 : List Nat := [2, 1, 2, 3, 1, 1, 1, 1, 5, 5]
def baseStart_1280792 : Nat := 118140960795 + 1280792 * 2 ^ 59
def prefixEnd_1280792 : Nat := 4983230072969 + 3 ^ 40 * 1280792 * 2
def baseEnd_1280792 : Nat := 438441276288972086073167

theorem tailTrace_1280792 : CollatzResearch.WordTrace tailWord_1280792 prefixEnd_1280792 438441276288972086073167 := by
  unfold tailWord_1280792
  simp only [CollatzResearch.WordTrace]
  refine ⟨23357160987958400351890315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31142881317277867135853753 23357160987958400351890315)
  ·
    refine ⟨35035741481937600527835473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23357160987958400351890315 35035741481937600527835473)
    ·
      refine ⟨26276806111453200395876605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35035741481937600527835473 26276806111453200395876605)
      ·
        refine ⟨9853802291794950148453727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26276806111453200395876605 9853802291794950148453727)
        ·
          refine ⟨14780703437692425222680591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9853802291794950148453727 14780703437692425222680591)
          ·
            refine ⟨22171055156538637834020887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14780703437692425222680591 22171055156538637834020887)
            ·
              refine ⟨33256582734807956751031331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22171055156538637834020887 33256582734807956751031331)
              ·
                refine ⟨49884874102211935126546997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33256582734807956751031331 49884874102211935126546997)
                ·
                  refine ⟨4676706947082368918113781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49884874102211935126546997 4676706947082368918113781)
                  ·
                    refine ⟨438441276288972086073167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4676706947082368918113781 438441276288972086073167)
                    ·
                      rfl

theorem cell22_1280792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 5, 5].length) (baseStart_1280792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1280792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1280792 prefixEnd_1280792 := by exact prefixLift 1280792
  have htrace : WordTrace (prefixWord ++ tailWord_1280792) baseStart_1280792 baseEnd_1280792 := by
    simpa [prefixWord, tailWord_1280792, baseEnd_1280792] using wordTrace_append hprefix tailTrace_1280792
  have hstable : (prefixWord ++ tailWord_1280792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280792).length < 2 ^ (prefixWord ++ tailWord_1280792).sum := by decide
  have hdescent : baseEnd_1280792 < baseStart_1280792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280830 : List Nat := [4, 2, 1, 2, 3, 2, 2, 1, 1, 4]
def baseStart_1280830 : Nat := 118140960795 + 1280830 * 2 ^ 59
def prefixEnd_1280830 : Nat := 4983230072969 + 3 ^ 40 * 1280830 * 2
def baseEnd_1280830 : Nat := 438454284465552653623051

theorem tailTrace_1280830 : CollatzResearch.WordTrace tailWord_1280830 prefixEnd_1280830 438454284465552653623051 := by
  unfold tailWord_1280830
  simp only [CollatzResearch.WordTrace]
  refine ⟨5839463493722391649207993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31143805299852755462442629 5839463493722391649207993)
  ·
    refine ⟨4379597620291793736905995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5839463493722391649207993 4379597620291793736905995)
    ·
      refine ⟨6569396430437690605358993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4379597620291793736905995 6569396430437690605358993)
      ·
        refine ⟨4927047322828267954019245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6569396430437690605358993 4927047322828267954019245)
        ·
          refine ⟨1847642746060600482757217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4927047322828267954019245 1847642746060600482757217)
          ·
            refine ⟨1385732059545450362067913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1847642746060600482757217 1385732059545450362067913)
            ·
              refine ⟨1039299044659087771550935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1385732059545450362067913 1039299044659087771550935)
              ·
                refine ⟨1558948566988631657326403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1039299044659087771550935 1558948566988631657326403)
                ·
                  refine ⟨2338422850482947485989605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1558948566988631657326403 2338422850482947485989605)
                  ·
                    refine ⟨438454284465552653623051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2338422850482947485989605 438454284465552653623051)
                    ·
                      rfl

theorem cell22_1280830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 2, 1, 1, 4].length) (baseStart_1280830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1280830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1280830 prefixEnd_1280830 := by exact prefixLift 1280830
  have htrace : WordTrace (prefixWord ++ tailWord_1280830) baseStart_1280830 baseEnd_1280830 := by
    simpa [prefixWord, tailWord_1280830, baseEnd_1280830] using wordTrace_append hprefix tailTrace_1280830
  have hstable : (prefixWord ++ tailWord_1280830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280830).length < 2 ^ (prefixWord ++ tailWord_1280830).sum := by decide
  have hdescent : baseEnd_1280830 < baseStart_1280830 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280860 : List Nat := [2, 2, 4, 2, 1, 2, 3, 1, 2, 3]
def baseStart_1280860 : Nat := 118140960795 + 1280860 * 2 ^ 59
def prefixEnd_1280860 : Nat := 4983230072969 + 3 ^ 40 * 1280860 * 2
def baseEnd_1280860 : Nat := 438464554078642575372959

theorem tailTrace_1280860 : CollatzResearch.WordTrace tailWord_1280860 prefixEnd_1280860 438464554078642575372959 := by
  unfold tailWord_1280860
  simp only [CollatzResearch.WordTrace]
  refine ⟨23358401069835224158628017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31144534759780298878170689 23358401069835224158628017)
  ·
    refine ⟨17518800802376418118971013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23358401069835224158628017 17518800802376418118971013)
    ·
      refine ⟨3284775150445578397307065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17518800802376418118971013 3284775150445578397307065)
      ·
        refine ⟨2463581362834183797980299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3284775150445578397307065 2463581362834183797980299)
        ·
          refine ⟨3695372044251275696970449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2463581362834183797980299 3695372044251275696970449)
          ·
            refine ⟨2771529033188456772727837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3695372044251275696970449 2771529033188456772727837)
            ·
              refine ⟨1039323387445671289772939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2771529033188456772727837 1039323387445671289772939)
              ·
                refine ⟨1558985081168506934659409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1039323387445671289772939 1558985081168506934659409)
                ·
                  refine ⟨1169238810876380200994557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1558985081168506934659409 1169238810876380200994557)
                  ·
                    refine ⟨438464554078642575372959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1169238810876380200994557 438464554078642575372959)
                    ·
                      rfl

theorem cell22_1280860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_1280860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1280860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1280860 prefixEnd_1280860 := by exact prefixLift 1280860
  have htrace : WordTrace (prefixWord ++ tailWord_1280860) baseStart_1280860 baseEnd_1280860 := by
    simpa [prefixWord, tailWord_1280860, baseEnd_1280860] using wordTrace_append hprefix tailTrace_1280860
  have hstable : (prefixWord ++ tailWord_1280860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280860).length < 2 ^ (prefixWord ++ tailWord_1280860).sum := by decide
  have hdescent : baseEnd_1280860 < baseStart_1280860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280871 : List Nat := [1, 1, 5, 1, 2, 2, 2, 2, 3, 3]
def baseStart_1280871 : Nat := 118140960795 + 1280871 * 2 ^ 59
def prefixEnd_1280871 : Nat := 4983230072969 + 3 ^ 40 * 1280871 * 2
def baseEnd_1280871 : Nat := 438468319603442213347925

theorem tailTrace_1280871 : CollatzResearch.WordTrace tailWord_1280871 prefixEnd_1280871 438468319603442213347925 := by
  unfold tailWord_1280871
  simp only [CollatzResearch.WordTrace]
  refine ⟨46717203342630597195906467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31144802228420398130604311 46717203342630597195906467)
  ·
    refine ⟨70075805013945895793859701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46717203342630597195906467 70075805013945895793859701)
    ·
      refine ⟨6569606720057427730674347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 70075805013945895793859701 6569606720057427730674347)
      ·
        refine ⟨9854410080086141596011521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6569606720057427730674347 9854410080086141596011521)
        ·
          refine ⟨7390807560064606197008641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9854410080086141596011521 7390807560064606197008641)
          ·
            refine ⟨5543105670048454647756481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7390807560064606197008641 5543105670048454647756481)
            ·
              refine ⟨4157329252536340985817361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5543105670048454647756481 4157329252536340985817361)
              ·
                refine ⟨3117996939402255739363021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4157329252536340985817361 3117996939402255739363021)
                ·
                  refine ⟨1169248852275845902261133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3117996939402255739363021 1169248852275845902261133)
                  ·
                    refine ⟨438468319603442213347925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1169248852275845902261133 438468319603442213347925)
                    ·
                      rfl

theorem cell22_1280871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 2, 3, 3].length) (baseStart_1280871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1280871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1280871 prefixEnd_1280871 := by exact prefixLift 1280871
  have htrace : WordTrace (prefixWord ++ tailWord_1280871) baseStart_1280871 baseEnd_1280871 := by
    simpa [prefixWord, tailWord_1280871, baseEnd_1280871] using wordTrace_append hprefix tailTrace_1280871
  have hstable : (prefixWord ++ tailWord_1280871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280871).length < 2 ^ (prefixWord ++ tailWord_1280871).sum := by decide
  have hdescent : baseEnd_1280871 < baseStart_1280871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280905 : List Nat := [1, 2, 1, 1, 5, 3, 3, 2, 1, 3]
def baseStart_1280905 : Nat := 118140960795 + 1280905 * 2 ^ 59
def prefixEnd_1280905 : Nat := 4983230072969 + 3 ^ 40 * 1280905 * 2
def baseEnd_1280905 : Nat := 438479958498277457997821

theorem tailTrace_1280905 : CollatzResearch.WordTrace tailWord_1280905 prefixEnd_1280905 438479958498277457997821 := by
  unfold tailWord_1280905
  simp only [CollatzResearch.WordTrace]
  refine ⟨46718443424507421002644169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31145628949671614001762779 46718443424507421002644169)
  ·
    refine ⟨35038832568380565751983127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46718443424507421002644169 35038832568380565751983127)
    ·
      refine ⟨52558248852570848627974691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35038832568380565751983127 52558248852570848627974691)
      ·
        refine ⟨78837373278856272941962037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52558248852570848627974691 78837373278856272941962037)
        ·
          refine ⟨7391003744892775588308941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 78837373278856272941962037 7391003744892775588308941)
          ·
            refine ⟨2771626404334790845615853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7391003744892775588308941 2771626404334790845615853)
            ·
              refine ⟨1039359901625546567105945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2771626404334790845615853 1039359901625546567105945)
              ·
                refine ⟨779519926219159925329459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1039359901625546567105945 779519926219159925329459)
                ·
                  refine ⟨1169279889328739887994189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 779519926219159925329459 1169279889328739887994189)
                  ·
                    refine ⟨438479958498277457997821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1169279889328739887994189 438479958498277457997821)
                    ·
                      rfl

theorem cell22_1280905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 3, 2, 1, 3].length) (baseStart_1280905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1280905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1280905 prefixEnd_1280905 := by exact prefixLift 1280905
  have htrace : WordTrace (prefixWord ++ tailWord_1280905) baseStart_1280905 baseEnd_1280905 := by
    simpa [prefixWord, tailWord_1280905, baseEnd_1280905] using wordTrace_append hprefix tailTrace_1280905
  have hstable : (prefixWord ++ tailWord_1280905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280905).length < 2 ^ (prefixWord ++ tailWord_1280905).sum := by decide
  have hdescent : baseEnd_1280905 < baseStart_1280905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280931 : List Nat := [1, 1, 1, 4, 1, 2, 5, 2, 1, 4]
def baseStart_1280931 : Nat := 118140960795 + 1280931 * 2 ^ 59
def prefixEnd_1280931 : Nat := 4983230072969 + 3 ^ 40 * 1280931 * 2
def baseEnd_1280931 : Nat := 438488858829622056847741

theorem tailTrace_1280931 : CollatzResearch.WordTrace tailWord_1280931 prefixEnd_1280931 438488858829622056847741 := by
  unfold tailWord_1280931
  simp only [CollatzResearch.WordTrace]
  refine ⟨46719391722413227443090647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31146261148275484962060431 46719391722413227443090647)
  ·
    refine ⟨70079087583619841164635971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46719391722413227443090647 70079087583619841164635971)
    ·
      refine ⟨105118631375429761746953957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70079087583619841164635971 105118631375429761746953957)
      ·
        refine ⟨19709743382893080327553867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 105118631375429761746953957 19709743382893080327553867)
        ·
          refine ⟨29564615074339620491330801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19709743382893080327553867 29564615074339620491330801)
          ·
            refine ⟨22173461305754715368498101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29564615074339620491330801 22173461305754715368498101)
            ·
              refine ⟨2078761997414504565796697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22173461305754715368498101 2078761997414504565796697)
              ·
                refine ⟨1559071498060878424347523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2078761997414504565796697 1559071498060878424347523)
                ·
                  refine ⟨2338607247091317636521285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1559071498060878424347523 2338607247091317636521285)
                  ·
                    refine ⟨438488858829622056847741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2338607247091317636521285 438488858829622056847741)
                    ·
                      rfl

theorem cell22_1280931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 2, 1, 4].length) (baseStart_1280931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1280931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1280931 prefixEnd_1280931 := by exact prefixLift 1280931
  have htrace : WordTrace (prefixWord ++ tailWord_1280931) baseStart_1280931 baseEnd_1280931 := by
    simpa [prefixWord, tailWord_1280931, baseEnd_1280931] using wordTrace_append hprefix tailTrace_1280931
  have hstable : (prefixWord ++ tailWord_1280931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280931).length < 2 ^ (prefixWord ++ tailWord_1280931).sum := by decide
  have hdescent : baseEnd_1280931 < baseStart_1280931 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280959 : List Nat := [1, 1, 2, 2, 2, 1, 2, 3, 4, 4]
def baseStart_1280959 : Nat := 118140960795 + 1280959 * 2 ^ 59
def prefixEnd_1280959 : Nat := 4983230072969 + 3 ^ 40 * 1280959 * 2
def baseEnd_1280959 : Nat := 438498443801839317147655

theorem tailTrace_1280959 : CollatzResearch.WordTrace tailWord_1280959 prefixEnd_1280959 438498443801839317147655 := by
  unfold tailWord_1280959
  simp only [CollatzResearch.WordTrace]
  refine ⟨46720412966311788225109931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31146941977541192150073287 46720412966311788225109931)
  ·
    refine ⟨70080619449467682337664897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46720412966311788225109931 70080619449467682337664897)
    ·
      refine ⟨52560464587100761753248673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70080619449467682337664897 52560464587100761753248673)
      ·
        refine ⟨39420348440325571314936505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52560464587100761753248673 39420348440325571314936505)
        ·
          refine ⟨29565261330244178486202379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39420348440325571314936505 29565261330244178486202379)
          ·
            refine ⟨44347891995366267729303569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29565261330244178486202379 44347891995366267729303569)
            ·
              refine ⟨33260918996524700796977677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44347891995366267729303569 33260918996524700796977677)
              ·
                refine ⟨12472844623696762798866629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33260918996524700796977677 12472844623696762798866629)
                ·
                  refine ⟨2338658366943143024787493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12472844623696762798866629 2338658366943143024787493)
                  ·
                    refine ⟨438498443801839317147655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2338658366943143024787493 438498443801839317147655)
                    ·
                      rfl

theorem cell22_1280959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 4, 4].length) (baseStart_1280959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1280959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1280959 prefixEnd_1280959 := by exact prefixLift 1280959
  have htrace : WordTrace (prefixWord ++ tailWord_1280959) baseStart_1280959 baseEnd_1280959 := by
    simpa [prefixWord, tailWord_1280959, baseEnd_1280959] using wordTrace_append hprefix tailTrace_1280959
  have hstable : (prefixWord ++ tailWord_1280959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280959).length < 2 ^ (prefixWord ++ tailWord_1280959).sum := by decide
  have hdescent : baseEnd_1280959 < baseStart_1280959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1280978 : List Nat := [3, 2, 2, 3, 1, 2, 2, 1, 1, 5]
def baseStart_1280978 : Nat := 118140960795 + 1280978 * 2 ^ 59
def prefixEnd_1280978 : Nat := 4983230072969 + 3 ^ 40 * 1280978 * 2
def baseEnd_1280978 : Nat := 438504947890129600922597

theorem tailTrace_1280978 : CollatzResearch.WordTrace tailWord_1280978 prefixEnd_1280978 438504947890129600922597 := by
  unfold tailWord_1280978
  simp only [CollatzResearch.WordTrace]
  refine ⟨11680276488310738617512897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31147403968828636313367725 11680276488310738617512897)
  ·
    refine ⟨8760207366233053963134673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11680276488310738617512897 8760207366233053963134673)
    ·
      refine ⟨6570155524674790472351005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8760207366233053963134673 6570155524674790472351005)
      ·
        refine ⟨2463808321753046427131627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6570155524674790472351005 2463808321753046427131627)
        ·
          refine ⟨3695712482629569640697441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2463808321753046427131627 3695712482629569640697441)
          ·
            refine ⟨2771784361972177230523081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3695712482629569640697441 2771784361972177230523081)
            ·
              refine ⟨2078838271479132922892311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2771784361972177230523081 2078838271479132922892311)
              ·
                refine ⟨3118257407218699384338467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2078838271479132922892311 3118257407218699384338467)
                ·
                  refine ⟨4677386110828049076507701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3118257407218699384338467 4677386110828049076507701)
                  ·
                    refine ⟨438504947890129600922597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4677386110828049076507701 438504947890129600922597)
                    ·
                      rfl

theorem cell22_1280978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_1280978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1280978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1280978 prefixEnd_1280978 := by exact prefixLift 1280978
  have htrace : WordTrace (prefixWord ++ tailWord_1280978) baseStart_1280978 baseEnd_1280978 := by
    simpa [prefixWord, tailWord_1280978, baseEnd_1280978] using wordTrace_append hprefix tailTrace_1280978
  have hstable : (prefixWord ++ tailWord_1280978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1280978).length < 2 ^ (prefixWord ++ tailWord_1280978).sum := by decide
  have hdescent : baseEnd_1280978 < baseStart_1280978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1280978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281057 : List Nat := [1, 2, 3, 2, 3, 3, 1, 3, 1, 3]
def baseStart_1281057 : Nat := 118140960795 + 1281057 * 2 ^ 59
def prefixEnd_1281057 : Nat := 4983230072969 + 3 ^ 40 * 1281057 * 2
def baseEnd_1281057 : Nat := 438531991204599728197355

theorem tailTrace_1281057 : CollatzResearch.WordTrace tailWord_1281057 prefixEnd_1281057 438531991204599728197355 := by
  unfold tailWord_1281057
  simp only [CollatzResearch.WordTrace]
  refine ⟨46723987319956750962177425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31149324879971167308118283 46723987319956750962177425)
  ·
    refine ⟨35042990489967563221633069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46723987319956750962177425 35042990489967563221633069)
    ·
      refine ⟨13141121433737836208112401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35042990489967563221633069 13141121433737836208112401)
      ·
        refine ⟨9855841075303377156084301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13141121433737836208112401 9855841075303377156084301)
        ·
          refine ⟨3695940403238766433531613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9855841075303377156084301 3695940403238766433531613)
          ·
            refine ⟨1385977651214537412574355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3695940403238766433531613 1385977651214537412574355)
            ·
              refine ⟨2078966476821806118861533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1385977651214537412574355 2078966476821806118861533)
              ·
                refine ⟨779612428808177294573075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2078966476821806118861533 779612428808177294573075)
                ·
                  refine ⟨1169418643212265941859613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 779612428808177294573075 1169418643212265941859613)
                  ·
                    refine ⟨438531991204599728197355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1169418643212265941859613 438531991204599728197355)
                    ·
                      rfl

theorem cell22_1281057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 3, 1, 3].length) (baseStart_1281057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1281057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1281057 prefixEnd_1281057 := by exact prefixLift 1281057
  have htrace : WordTrace (prefixWord ++ tailWord_1281057) baseStart_1281057 baseEnd_1281057 := by
    simpa [prefixWord, tailWord_1281057, baseEnd_1281057] using wordTrace_append hprefix tailTrace_1281057
  have hstable : (prefixWord ++ tailWord_1281057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281057).length < 2 ^ (prefixWord ++ tailWord_1281057).sum := by decide
  have hdescent : baseEnd_1281057 < baseStart_1281057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281096 : List Nat := [2, 1, 3, 1, 1, 1, 4, 3, 1, 5]
def baseStart_1281096 : Nat := 118140960795 + 1281096 * 2 ^ 59
def prefixEnd_1281096 : Nat := 4983230072969 + 3 ^ 40 * 1281096 * 2
def baseEnd_1281096 : Nat := 438545341701616626472235

theorem tailTrace_1281096 : CollatzResearch.WordTrace tailWord_1281096 prefixEnd_1281096 438545341701616626472235 := by
  unfold tailWord_1281096
  simp only [CollatzResearch.WordTrace]
  refine ⟨23362704883407730311423571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31150273177876973748564761 23362704883407730311423571)
  ·
    refine ⟨35044057325111595467135357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23362704883407730311423571 35044057325111595467135357)
    ·
      refine ⟨13141521496916848300175759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35044057325111595467135357 13141521496916848300175759)
      ·
        refine ⟨19712282245375272450263639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13141521496916848300175759 19712282245375272450263639)
        ·
          refine ⟨29568423368062908675395459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19712282245375272450263639 29568423368062908675395459)
          ·
            refine ⟨44352635052094363013093189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29568423368062908675395459 44352635052094363013093189)
            ·
              refine ⟨8316119072267693064954973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44352635052094363013093189 8316119072267693064954973)
              ·
                refine ⟨3118544652100384899358115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8316119072267693064954973 3118544652100384899358115)
                ·
                  refine ⟨4677816978150577349037173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3118544652100384899358115 4677816978150577349037173)
                  ·
                    refine ⟨438545341701616626472235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4677816978150577349037173 438545341701616626472235)
                    ·
                      rfl

theorem cell22_1281096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 3, 1, 5].length) (baseStart_1281096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1281096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1281096 prefixEnd_1281096 := by exact prefixLift 1281096
  have htrace : WordTrace (prefixWord ++ tailWord_1281096) baseStart_1281096 baseEnd_1281096 := by
    simpa [prefixWord, tailWord_1281096, baseEnd_1281096] using wordTrace_append hprefix tailTrace_1281096
  have hstable : (prefixWord ++ tailWord_1281096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281096).length < 2 ^ (prefixWord ++ tailWord_1281096).sum := by decide
  have hdescent : baseEnd_1281096 < baseStart_1281096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281130 : List Nat := [3, 1, 3, 2, 2, 1, 1, 4, 2, 3]
def baseStart_1281130 : Nat := 118140960795 + 1281130 * 2 ^ 59
def prefixEnd_1281130 : Nat := 4983230072969 + 3 ^ 40 * 1281130 * 2
def baseEnd_1281130 : Nat := 438556980596451871122131

theorem tailTrace_1281130 : CollatzResearch.WordTrace tailWord_1281130 prefixEnd_1281130 438556980596451871122131 := by
  unfold tailWord_1281130
  simp only [CollatzResearch.WordTrace]
  refine ⟨11681662462173071107396211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31151099899128189619723229 11681662462173071107396211)
  ·
    refine ⟨17522493693259606661094317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11681662462173071107396211 17522493693259606661094317)
    ·
      refine ⟨6570935134972352497910369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17522493693259606661094317 6570935134972352497910369)
      ·
        refine ⟨4928201351229264373432777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6570935134972352497910369 4928201351229264373432777)
        ·
          refine ⟨3696151013421948280074583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4928201351229264373432777 3696151013421948280074583)
          ·
            refine ⟨5544226520132922420111875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3696151013421948280074583 5544226520132922420111875)
            ·
              refine ⟨8316339780199383630167813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5544226520132922420111875 8316339780199383630167813)
              ·
                refine ⟨1559313708787384430656465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8316339780199383630167813 1559313708787384430656465)
                ·
                  refine ⟨1169485281590538322992349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1559313708787384430656465 1169485281590538322992349)
                  ·
                    refine ⟨438556980596451871122131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1169485281590538322992349 438556980596451871122131)
                    ·
                      rfl

theorem cell22_1281130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 4, 2, 3].length) (baseStart_1281130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1281130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1281130 prefixEnd_1281130 := by exact prefixLift 1281130
  have htrace : WordTrace (prefixWord ++ tailWord_1281130) baseStart_1281130 baseEnd_1281130 := by
    simpa [prefixWord, tailWord_1281130, baseEnd_1281130] using wordTrace_append hprefix tailTrace_1281130
  have hstable : (prefixWord ++ tailWord_1281130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281130).length < 2 ^ (prefixWord ++ tailWord_1281130).sum := by decide
  have hdescent : baseEnd_1281130 < baseStart_1281130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281160 : List Nat := [2, 1, 3, 4, 2, 1, 3, 6]
def baseStart_1281160 : Nat := 118140960795 + 1281160 * 2 ^ 59
def prefixEnd_1281160 : Nat := 4983230072969 + 3 ^ 40 * 1281160 * 2
def baseEnd_1281160 : Nat := 48729694467726865874671

theorem tailTrace_1281160 : CollatzResearch.WordTrace tailWord_1281160 prefixEnd_1281160 48729694467726865874671 := by
  unfold tailWord_1281160
  simp only [CollatzResearch.WordTrace]
  refine ⟨23363872019291799776588467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31151829359055733035451289 23363872019291799776588467)
  ·
    refine ⟨35045808028937699664882701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23363872019291799776588467 35045808028937699664882701)
    ·
      refine ⟨13142178010851637374331013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35045808028937699664882701 13142178010851637374331013)
      ·
        refine ⟨2464158377034682007687065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13142178010851637374331013 2464158377034682007687065)
        ·
          refine ⟨1848118782776011505765299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2464158377034682007687065 1848118782776011505765299)
          ·
            refine ⟨2772178174164017258647949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1848118782776011505765299 2772178174164017258647949)
            ·
              refine ⟨1039566815311506471992981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2772178174164017258647949 1039566815311506471992981)
              ·
                refine ⟨48729694467726865874671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1039566815311506471992981 48729694467726865874671)
                ·
                  rfl

theorem cell22_1281160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 3, 6].length) (baseStart_1281160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1281160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1281160 prefixEnd_1281160 := by exact prefixLift 1281160
  have htrace : WordTrace (prefixWord ++ tailWord_1281160) baseStart_1281160 baseEnd_1281160 := by
    simpa [prefixWord, tailWord_1281160, baseEnd_1281160] using wordTrace_append hprefix tailTrace_1281160
  have hstable : (prefixWord ++ tailWord_1281160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281160).length < 2 ^ (prefixWord ++ tailWord_1281160).sum := by decide
  have hdescent : baseEnd_1281160 < baseStart_1281160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281188 : List Nat := [2, 3, 1, 2, 3, 2, 1, 1, 7]
def baseStart_1281188 : Nat := 118140960795 + 1281188 * 2 ^ 59
def prefixEnd_1281188 : Nat := 4983230072969 + 3 ^ 40 * 1281188 * 2
def baseEnd_1281188 : Nat := 146192278393919684390651

theorem tailTrace_1281188 : CollatzResearch.WordTrace tailWord_1281188 prefixEnd_1281188 146192278393919684390651 := by
  unfold tailWord_1281188
  simp only [CollatzResearch.WordTrace]
  refine ⟨23364382641241080167598109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31152510188321440223464145 23364382641241080167598109)
  ·
    refine ⟨8761643490465405062849291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23364382641241080167598109 8761643490465405062849291)
    ·
      refine ⟨13142465235698107594273937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8761643490465405062849291 13142465235698107594273937)
      ·
        refine ⟨9856848926773580695705453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13142465235698107594273937 9856848926773580695705453)
        ·
          refine ⟨3696318347540092760889545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9856848926773580695705453 3696318347540092760889545)
          ·
            refine ⟨2772238760655069570667159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3696318347540092760889545 2772238760655069570667159)
            ·
              refine ⟨4158358140982604356000739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2772238760655069570667159 4158358140982604356000739)
              ·
                refine ⟨6237537211473906534001109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4158358140982604356000739 6237537211473906534001109)
                ·
                  refine ⟨146192278393919684390651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6237537211473906534001109 146192278393919684390651)
                  ·
                    rfl

theorem cell22_1281188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 1, 7].length) (baseStart_1281188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1281188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1281188 prefixEnd_1281188 := by exact prefixLift 1281188
  have htrace : WordTrace (prefixWord ++ tailWord_1281188) baseStart_1281188 baseEnd_1281188 := by
    simpa [prefixWord, tailWord_1281188, baseEnd_1281188] using wordTrace_append hprefix tailTrace_1281188
  have hstable : (prefixWord ++ tailWord_1281188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281188).length < 2 ^ (prefixWord ++ tailWord_1281188).sum := by decide
  have hdescent : baseEnd_1281188 < baseStart_1281188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281282 : List Nat := [3, 4, 1, 1, 3, 1, 1, 2, 1, 5]
def baseStart_1281282 : Nat := 118140960795 + 1281282 * 2 ^ 59
def prefixEnd_1281282 : Nat := 4983230072969 + 3 ^ 40 * 1281282 * 2
def baseEnd_1281282 : Nat := 438609013302774141321665

theorem tailTrace_1281282 : CollatzResearch.WordTrace tailWord_1281282 prefixEnd_1281282 438609013302774141321665 := by
  unfold tailWord_1281282
  simp only [CollatzResearch.WordTrace]
  refine ⟨11683048436035403597279525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31154795829427742926078733 11683048436035403597279525)
  ·
    refine ⟨2190571581756638174489911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11683048436035403597279525 2190571581756638174489911)
    ·
      refine ⟨3285857372634957261734867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2190571581756638174489911 3285857372634957261734867)
      ·
        refine ⟨4928786058952435892602301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3285857372634957261734867 4928786058952435892602301)
        ·
          refine ⟨1848294772107163459725863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4928786058952435892602301 1848294772107163459725863)
          ·
            refine ⟨2772442158160745189588795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1848294772107163459725863 2772442158160745189588795)
            ·
              refine ⟨4158663237241117784383193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2772442158160745189588795 4158663237241117784383193)
              ·
                refine ⟨3118997427930838338287395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4158663237241117784383193 3118997427930838338287395)
                ·
                  refine ⟨4678496141896257507431093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3118997427930838338287395 4678496141896257507431093)
                  ·
                    refine ⟨438609013302774141321665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4678496141896257507431093 438609013302774141321665)
                    ·
                      rfl

theorem cell22_1281282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_1281282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1281282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1281282 prefixEnd_1281282 := by exact prefixLift 1281282
  have htrace : WordTrace (prefixWord ++ tailWord_1281282) baseStart_1281282 baseEnd_1281282 := by
    simpa [prefixWord, tailWord_1281282, baseEnd_1281282] using wordTrace_append hprefix tailTrace_1281282
  have hstable : (prefixWord ++ tailWord_1281282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281282).length < 2 ^ (prefixWord ++ tailWord_1281282).sum := by decide
  have hdescent : baseEnd_1281282 < baseStart_1281282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281308 : List Nat := [2, 2, 3, 1, 1, 1, 3, 1, 2, 6]
def baseStart_1281308 : Nat := 118140960795 + 1281308 * 2 ^ 59
def prefixEnd_1281308 : Nat := 4983230072969 + 3 ^ 40 * 1281308 * 2
def baseEnd_1281308 : Nat := 438617913634118740171585

theorem tailTrace_1281308 : CollatzResearch.WordTrace tailWord_1281308 prefixEnd_1281308 438617913634118740171585 := by
  unfold tailWord_1281308
  simp only [CollatzResearch.WordTrace]
  refine ⟨23366571021023710414782289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31155428028031613886376385 23366571021023710414782289)
  ·
    refine ⟨17524928265767782811086717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23366571021023710414782289 17524928265767782811086717)
    ·
      refine ⟨6571848099662918554157519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17524928265767782811086717 6571848099662918554157519)
      ·
        refine ⟨9857772149494377831236279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6571848099662918554157519 9857772149494377831236279)
        ·
          refine ⟨14786658224241566746854419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9857772149494377831236279 14786658224241566746854419)
          ·
            refine ⟨22179987336362350120281629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14786658224241566746854419 22179987336362350120281629)
            ·
              refine ⟨8317495251135881295105611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22179987336362350120281629 8317495251135881295105611)
              ·
                refine ⟨12476242876703821942658417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8317495251135881295105611 12476242876703821942658417)
                ·
                  refine ⟨9357182157527866456993813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12476242876703821942658417 9357182157527866456993813)
                  ·
                    refine ⟨438617913634118740171585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9357182157527866456993813 438617913634118740171585)
                    ·
                      rfl

theorem cell22_1281308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_1281308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1281308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1281308 prefixEnd_1281308 := by exact prefixLift 1281308
  have htrace : WordTrace (prefixWord ++ tailWord_1281308) baseStart_1281308 baseEnd_1281308 := by
    simpa [prefixWord, tailWord_1281308, baseEnd_1281308] using wordTrace_append hprefix tailTrace_1281308
  have hstable : (prefixWord ++ tailWord_1281308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281308).length < 2 ^ (prefixWord ++ tailWord_1281308).sum := by decide
  have hdescent : baseEnd_1281308 < baseStart_1281308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281312 : List Nat := [2, 1, 1, 5, 4, 1, 1, 7]
def baseStart_1281312 : Nat := 118140960795 + 1281312 * 2 ^ 59
def prefixEnd_1281312 : Nat := 4983230072969 + 3 ^ 40 * 1281312 * 2
def baseEnd_1281312 : Nat := 48735475879540451452397

theorem tailTrace_1281312 : CollatzResearch.WordTrace tailWord_1281312 prefixEnd_1281312 48735475879540451452397 := by
  unfold tailWord_1281312
  simp only [CollatzResearch.WordTrace]
  refine ⟨23366643967016464756355095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31155525289355286341806793 23366643967016464756355095)
  ·
    refine ⟨35049965950524697134532643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23366643967016464756355095 35049965950524697134532643)
    ·
      refine ⟨52574948925787045701798965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35049965950524697134532643 52574948925787045701798965)
      ·
        refine ⟨4928901461792535534543653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 52574948925787045701798965 4928901461792535534543653)
        ·
          refine ⟨924169024086100412726935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4928901461792535534543653 924169024086100412726935)
          ·
            refine ⟨1386253536129150619090403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 924169024086100412726935 1386253536129150619090403)
            ·
              refine ⟨2079380304193725928635605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1386253536129150619090403 2079380304193725928635605)
              ·
                refine ⟨48735475879540451452397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2079380304193725928635605 48735475879540451452397)
                ·
                  rfl

theorem cell22_1281312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 7].length) (baseStart_1281312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1281312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1281312 prefixEnd_1281312 := by exact prefixLift 1281312
  have htrace : WordTrace (prefixWord ++ tailWord_1281312) baseStart_1281312 baseEnd_1281312 := by
    simpa [prefixWord, tailWord_1281312, baseEnd_1281312] using wordTrace_append hprefix tailTrace_1281312
  have hstable : (prefixWord ++ tailWord_1281312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281312).length < 2 ^ (prefixWord ++ tailWord_1281312).sum := by decide
  have hdescent : baseEnd_1281312 < baseStart_1281312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281338 : List Nat := [3, 1, 1, 1, 4, 1, 1, 2, 1, 7]
def baseStart_1281338 : Nat := 118140960795 + 1281338 * 2 ^ 59
def prefixEnd_1281338 : Nat := 4983230072969 + 3 ^ 40 * 1281338 * 2
def baseEnd_1281338 : Nat := 438628183247208661921493

theorem tailTrace_1281338 : CollatzResearch.WordTrace tailWord_1281338 prefixEnd_1281338 438628183247208661921493 := by
  unfold tailWord_1281338
  simp only [CollatzResearch.WordTrace]
  refine ⟨11683559057984683988289167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31156157487959157302104445 11683559057984683988289167)
  ·
    refine ⟨17525338586977025982433751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11683559057984683988289167 17525338586977025982433751)
    ·
      refine ⟨26288007880465538973650627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17525338586977025982433751 26288007880465538973650627)
      ·
        refine ⟨39432011820698308460475941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26288007880465538973650627 39432011820698308460475941)
        ·
          refine ⟨7393502216380932836339239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39432011820698308460475941 7393502216380932836339239)
          ·
            refine ⟨11090253324571399254508859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7393502216380932836339239 11090253324571399254508859)
            ·
              refine ⟨16635379986857098881763289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11090253324571399254508859 16635379986857098881763289)
              ·
                refine ⟨12476534990142824161322467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16635379986857098881763289 12476534990142824161322467)
                ·
                  refine ⟨18714802485214236241983701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12476534990142824161322467 18714802485214236241983701)
                  ·
                    refine ⟨438628183247208661921493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18714802485214236241983701 438628183247208661921493)
                    ·
                      rfl

theorem cell22_1281338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 1, 7].length) (baseStart_1281338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1281338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1281338 prefixEnd_1281338 := by exact prefixLift 1281338
  have htrace : WordTrace (prefixWord ++ tailWord_1281338) baseStart_1281338 baseEnd_1281338 := by
    simpa [prefixWord, tailWord_1281338, baseEnd_1281338] using wordTrace_append hprefix tailTrace_1281338
  have hstable : (prefixWord ++ tailWord_1281338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281338).length < 2 ^ (prefixWord ++ tailWord_1281338).sum := by decide
  have hdescent : baseEnd_1281338 < baseStart_1281338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281350 : List Nat := [6, 1, 1, 3, 2, 1, 1, 2, 2, 3]
def baseStart_1281350 : Nat := 118140960795 + 1281350 * 2 ^ 59
def prefixEnd_1281350 : Nat := 4983230072969 + 3 ^ 40 * 1281350 * 2
def baseEnd_1281350 : Nat := 438632291092444630621457

theorem tailTrace_1281350 : CollatzResearch.WordTrace tailWord_1281350 prefixEnd_1281350 438632291092444630621457 := by
  unfold tailWord_1281350
  simp only [CollatzResearch.WordTrace]
  refine ⟨1460458559621726937581047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 31156449271930174668395669 1460458559621726937581047)
  ·
    refine ⟨2190687839432590406371571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1460458559621726937581047 2190687839432590406371571)
    ·
      refine ⟨3286031759148885609557357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2190687839432590406371571 3286031759148885609557357)
      ·
        refine ⟨1232261909680832103584009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3286031759148885609557357 1232261909680832103584009)
        ·
          refine ⟨924196432260624077688007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1232261909680832103584009 924196432260624077688007)
          ·
            refine ⟨1386294648390936116532011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 924196432260624077688007 1386294648390936116532011)
            ·
              refine ⟨2079441972586404174798017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1386294648390936116532011 2079441972586404174798017)
              ·
                refine ⟨1559581479439803131098513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2079441972586404174798017 1559581479439803131098513)
                ·
                  refine ⟨1169686109579852348323885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1559581479439803131098513 1169686109579852348323885)
                  ·
                    refine ⟨438632291092444630621457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1169686109579852348323885 438632291092444630621457)
                    ·
                      rfl

theorem cell22_1281350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_1281350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1281350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1281350 prefixEnd_1281350 := by exact prefixLift 1281350
  have htrace : WordTrace (prefixWord ++ tailWord_1281350) baseStart_1281350 baseEnd_1281350 := by
    simpa [prefixWord, tailWord_1281350, baseEnd_1281350] using wordTrace_append hprefix tailTrace_1281350
  have hstable : (prefixWord ++ tailWord_1281350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281350).length < 2 ^ (prefixWord ++ tailWord_1281350).sum := by decide
  have hdescent : baseEnd_1281350 < baseStart_1281350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281413 : List Nat := [1, 3, 1, 1, 3, 1, 12]
def baseStart_1281413 : Nat := 118140960795 + 1281413 * 2 ^ 59
def prefixEnd_1281413 : Nat := 4983230072969 + 3 ^ 40 * 1281413 * 2
def baseEnd_1281413 : Nat := 16246439158516054307269

theorem tailTrace_1281413 : CollatzResearch.WordTrace tailWord_1281413 prefixEnd_1281413 16246439158516054307269 := by
  unfold tailWord_1281413
  simp only [CollatzResearch.WordTrace]
  refine ⟨46736971706667023762136893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31157981137778015841424595 46736971706667023762136893)
  ·
    refine ⟨17526364390000133910801335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46736971706667023762136893 17526364390000133910801335)
    ·
      refine ⟨26289546585000200866202003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17526364390000133910801335 26289546585000200866202003)
      ·
        refine ⟨39434319877500301299303005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26289546585000200866202003 39434319877500301299303005)
        ·
          refine ⟨14787869954062612987238627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39434319877500301299303005 14787869954062612987238627)
          ·
            refine ⟨22181804931093919480857941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14787869954062612987238627 22181804931093919480857941)
            ·
              refine ⟨16246439158516054307269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 22181804931093919480857941 16246439158516054307269)
              ·
                rfl

theorem cell22_1281413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 12].length) (baseStart_1281413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1281413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1281413 prefixEnd_1281413 := by exact prefixLift 1281413
  have htrace : WordTrace (prefixWord ++ tailWord_1281413) baseStart_1281413 baseEnd_1281413 := by
    simpa [prefixWord, tailWord_1281413, baseEnd_1281413] using wordTrace_append hprefix tailTrace_1281413
  have hstable : (prefixWord ++ tailWord_1281413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281413).length < 2 ^ (prefixWord ++ tailWord_1281413).sum := by decide
  have hdescent : baseEnd_1281413 < baseStart_1281413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281415 : List Nat := [1, 1, 4, 2, 2, 2, 1, 1, 4, 4]
def baseStart_1281415 : Nat := 118140960795 + 1281415 * 2 ^ 59
def prefixEnd_1281415 : Nat := 4983230072969 + 3 ^ 40 * 1281415 * 2
def baseEnd_1281415 : Nat := 438654541920806127746257

theorem tailTrace_1281415 : CollatzResearch.WordTrace tailWord_1281415 prefixEnd_1281415 438654541920806127746257 := by
  unfold tailWord_1281415
  simp only [CollatzResearch.WordTrace]
  refine ⟨46737044652659778103709699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31158029768439852069139799 46737044652659778103709699)
  ·
    refine ⟨70105566978989667155564549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46737044652659778103709699 70105566978989667155564549)
    ·
      refine ⟨13144793808560562591668353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70105566978989667155564549 13144793808560562591668353)
      ·
        refine ⟨9858595356420421943751265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13144793808560562591668353 9858595356420421943751265)
        ·
          refine ⟨7393946517315316457813449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9858595356420421943751265 7393946517315316457813449)
          ·
            refine ⟨5545459887986487343360087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7393946517315316457813449 5545459887986487343360087)
            ·
              refine ⟨8318189831979731015040131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5545459887986487343360087 8318189831979731015040131)
              ·
                refine ⟨12477284747969596522560197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8318189831979731015040131 12477284747969596522560197)
                ·
                  refine ⟨2339490890244299347980037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12477284747969596522560197 2339490890244299347980037)
                  ·
                    refine ⟨438654541920806127746257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2339490890244299347980037 438654541920806127746257)
                    ·
                      rfl

theorem cell22_1281415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 4, 4].length) (baseStart_1281415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1281415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1281415 prefixEnd_1281415 := by exact prefixLift 1281415
  have htrace : WordTrace (prefixWord ++ tailWord_1281415) baseStart_1281415 baseEnd_1281415 := by
    simpa [prefixWord, tailWord_1281415, baseEnd_1281415] using wordTrace_append hprefix tailTrace_1281415
  have hstable : (prefixWord ++ tailWord_1281415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281415).length < 2 ^ (prefixWord ++ tailWord_1281415).sum := by decide
  have hdescent : baseEnd_1281415 < baseStart_1281415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281438 : List Nat := [4, 3, 1, 2, 3, 1, 1, 2, 1, 4]
def baseStart_1281438 : Nat := 118140960795 + 1281438 * 2 ^ 59
def prefixEnd_1281438 : Nat := 4983230072969 + 3 ^ 40 * 1281438 * 2
def baseEnd_1281438 : Nat := 438662415290841734421187

theorem tailTrace_1281438 : CollatzResearch.WordTrace tailWord_1281438 prefixEnd_1281438 438662415290841734421187 := by
  unfold tailWord_1281438
  simp only [CollatzResearch.WordTrace]
  refine ⟨5842235441447056628974621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31158589021050968687864645 5842235441447056628974621)
  ·
    refine ⟨2190838290542646235865483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5842235441447056628974621 2190838290542646235865483)
    ·
      refine ⟨3286257435813969353798225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2190838290542646235865483 3286257435813969353798225)
      ·
        refine ⟨2464693076860477015348669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3286257435813969353798225 2464693076860477015348669)
        ·
          refine ⟨924259903822678880755751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2464693076860477015348669 924259903822678880755751)
          ·
            refine ⟨1386389855734018321133627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 924259903822678880755751 1386389855734018321133627)
            ·
              refine ⟨2079584783601027481700441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1386389855734018321133627 2079584783601027481700441)
              ·
                refine ⟨1559688587700770611275331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2079584783601027481700441 1559688587700770611275331)
                ·
                  refine ⟨2339532881551155916912997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1559688587700770611275331 2339532881551155916912997)
                  ·
                    refine ⟨438662415290841734421187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2339532881551155916912997 438662415290841734421187)
                    ·
                      rfl

theorem cell22_1281438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_1281438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1281438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1281438 prefixEnd_1281438 := by exact prefixLift 1281438
  have htrace : WordTrace (prefixWord ++ tailWord_1281438) baseStart_1281438 baseEnd_1281438 := by
    simpa [prefixWord, tailWord_1281438, baseEnd_1281438] using wordTrace_append hprefix tailTrace_1281438
  have hstable : (prefixWord ++ tailWord_1281438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281438).length < 2 ^ (prefixWord ++ tailWord_1281438).sum := by decide
  have hdescent : baseEnd_1281438 < baseStart_1281438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281475 : List Nat := [1, 1, 1, 3, 1, 1, 5, 4, 5]
def baseStart_1281475 : Nat := 118140960795 + 1281475 * 2 ^ 59
def prefixEnd_1281475 : Nat := 4983230072969 + 3 ^ 40 * 1281475 * 2
def baseEnd_1281475 : Nat := 146225027048995323748691

theorem tailTrace_1281475 : CollatzResearch.WordTrace tailWord_1281475 prefixEnd_1281475 146225027048995323748691 := by
  unfold tailWord_1281475
  simp only [CollatzResearch.WordTrace]
  refine ⟨46739233032442408350893879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31159488688294938900595919 46739233032442408350893879)
  ·
    refine ⟨70108849548663612526340819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46739233032442408350893879 70108849548663612526340819)
    ·
      refine ⟨105163274322995418789511229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70108849548663612526340819 105163274322995418789511229)
      ·
        refine ⟨39436227871123282046066711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105163274322995418789511229 39436227871123282046066711)
        ·
          refine ⟨59154341806684923069100067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39436227871123282046066711 59154341806684923069100067)
          ·
            refine ⟨88731512710027384603650101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59154341806684923069100067 88731512710027384603650101)
            ·
              refine ⟨8318579316565067306592197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 88731512710027384603650101 8318579316565067306592197)
              ·
                refine ⟨1559733621855950119986037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8318579316565067306592197 1559733621855950119986037)
                ·
                  refine ⟨146225027048995323748691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1559733621855950119986037 146225027048995323748691)
                  ·
                    rfl

theorem cell22_1281475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 4, 5].length) (baseStart_1281475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1281475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1281475 prefixEnd_1281475 := by exact prefixLift 1281475
  have htrace : WordTrace (prefixWord ++ tailWord_1281475) baseStart_1281475 baseEnd_1281475 := by
    simpa [prefixWord, tailWord_1281475, baseEnd_1281475] using wordTrace_append hprefix tailTrace_1281475
  have hstable : (prefixWord ++ tailWord_1281475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281475).length < 2 ^ (prefixWord ++ tailWord_1281475).sum := by decide
  have hdescent : baseEnd_1281475 < baseStart_1281475 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281479 : List Nat := [1, 1, 4, 1, 1, 3, 3, 4, 1, 3]
def baseStart_1281479 : Nat := 118140960795 + 1281479 * 2 ^ 59
def prefixEnd_1281479 : Nat := 4983230072969 + 3 ^ 40 * 1281479 * 2
def baseEnd_1281479 : Nat := 438676450428731294146061

theorem tailTrace_1281479 : CollatzResearch.WordTrace tailWord_1281479 prefixEnd_1281479 438676450428731294146061 := by
  unfold tailWord_1281479
  simp only [CollatzResearch.WordTrace]
  refine ⟨46739378924427917034039491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31159585949618611356026327 46739378924427917034039491)
  ·
    refine ⟨70109068386641875551059237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46739378924427917034039491 70109068386641875551059237)
    ·
      refine ⟨13145450322495351665823607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70109068386641875551059237 13145450322495351665823607)
      ·
        refine ⟨19718175483743027498735411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13145450322495351665823607 19718175483743027498735411)
        ·
          refine ⟨29577263225614541248103117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19718175483743027498735411 29577263225614541248103117)
          ·
            refine ⟨11091473709605452968038669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29577263225614541248103117 11091473709605452968038669)
            ·
              refine ⟨4159302641102044863014501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11091473709605452968038669 4159302641102044863014501)
              ·
                refine ⟨779869245206633411815219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4159302641102044863014501 779869245206633411815219)
                ·
                  refine ⟨1169803867809950117722829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 779869245206633411815219 1169803867809950117722829)
                  ·
                    refine ⟨438676450428731294146061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1169803867809950117722829 438676450428731294146061)
                    ·
                      rfl

theorem cell22_1281479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 4, 1, 3].length) (baseStart_1281479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1281479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1281479 prefixEnd_1281479 := by exact prefixLift 1281479
  have htrace : WordTrace (prefixWord ++ tailWord_1281479) baseStart_1281479 baseEnd_1281479 := by
    simpa [prefixWord, tailWord_1281479, baseEnd_1281479] using wordTrace_append hprefix tailTrace_1281479
  have hstable : (prefixWord ++ tailWord_1281479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281479).length < 2 ^ (prefixWord ++ tailWord_1281479).sum := by decide
  have hdescent : baseEnd_1281479 < baseStart_1281479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281571 : List Nat := [1, 1, 1, 4, 5, 2, 1, 3, 4]
def baseStart_1281571 : Nat := 118140960795 + 1281571 * 2 ^ 59
def prefixEnd_1281571 : Nat := 4983230072969 + 3 ^ 40 * 1281571 * 2
def baseEnd_1281571 : Nat := 146235981302957906948593

theorem tailTrace_1281571 : CollatzResearch.WordTrace tailWord_1281571 prefixEnd_1281571 146235981302957906948593 := by
  unfold tailWord_1281571
  simp only [CollatzResearch.WordTrace]
  refine ⟨46742734440094616746388567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31161822960063077830925711 46742734440094616746388567)
  ·
    refine ⟨70114101660141925119582851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46742734440094616746388567 70114101660141925119582851)
    ·
      refine ⟨105171152490212887679374277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70114101660141925119582851 105171152490212887679374277)
      ·
        refine ⟨19719591091914916439882677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 105171152490212887679374277 19719591091914916439882677)
        ·
          refine ⟨1848711664867023416239001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19719591091914916439882677 1848711664867023416239001)
          ·
            refine ⟨1386533748650267562179251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1848711664867023416239001 1386533748650267562179251)
            ·
              refine ⟨2079800622975401343268877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1386533748650267562179251 2079800622975401343268877)
              ·
                refine ⟨779925233615775503725829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2079800622975401343268877 779925233615775503725829)
                ·
                  refine ⟨146235981302957906948593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 779925233615775503725829 146235981302957906948593)
                  ·
                    rfl

theorem cell22_1281571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 3, 4].length) (baseStart_1281571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1281571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1281571 prefixEnd_1281571 := by exact prefixLift 1281571
  have htrace : WordTrace (prefixWord ++ tailWord_1281571) baseStart_1281571 baseEnd_1281571 := by
    simpa [prefixWord, tailWord_1281571, baseEnd_1281571] using wordTrace_append hprefix tailTrace_1281571
  have hstable : (prefixWord ++ tailWord_1281571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281571).length < 2 ^ (prefixWord ++ tailWord_1281571).sum := by decide
  have hdescent : baseEnd_1281571 < baseStart_1281571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281582 : List Nat := [4, 1, 3, 1, 2, 1, 10]
def baseStart_1281582 : Nat := 118140960795 + 1281582 * 2 ^ 59
def prefixEnd_1281582 : Nat := 4983230072969 + 3 ^ 40 * 1281582 * 2
def baseEnd_1281582 : Nat := 16248581830876791067435

theorem tailTrace_1281582 : CollatzResearch.WordTrace tailWord_1281582 prefixEnd_1281582 16248581830876791067435 := by
  unfold tailWord_1281582
  simp only [CollatzResearch.WordTrace]
  refine ⟨5842891955381845703129875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31162090428703177083359333 5842891955381845703129875)
  ·
    refine ⟨8764337933072768554694813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5842891955381845703129875 8764337933072768554694813)
    ·
      refine ⟨3286626724902288208010555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8764337933072768554694813 3286626724902288208010555)
      ·
        refine ⟨4929940087353432312015833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3286626724902288208010555 4929940087353432312015833)
        ·
          refine ⟨3697455065515074234011875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4929940087353432312015833 3697455065515074234011875)
          ·
            refine ⟨5546182598272611351017813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3697455065515074234011875 5546182598272611351017813)
            ·
              refine ⟨16248581830876791067435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5546182598272611351017813 16248581830876791067435)
              ·
                rfl

theorem cell22_1281582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 10].length) (baseStart_1281582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1281582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1281582 prefixEnd_1281582 := by exact prefixLift 1281582
  have htrace : WordTrace (prefixWord ++ tailWord_1281582) baseStart_1281582 baseEnd_1281582 := by
    simpa [prefixWord, tailWord_1281582, baseEnd_1281582] using wordTrace_append hprefix tailTrace_1281582
  have hstable : (prefixWord ++ tailWord_1281582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281582).length < 2 ^ (prefixWord ++ tailWord_1281582).sum := by decide
  have hdescent : baseEnd_1281582 < baseStart_1281582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281648 : List Nat := [2, 1, 1, 1, 6, 1, 4, 2, 1, 3]
def baseStart_1281648 : Nat := 118140960795 + 1281648 * 2 ^ 59
def prefixEnd_1281648 : Nat := 4983230072969 + 3 ^ 40 * 1281648 * 2
def baseEnd_1281648 : Nat := 438734302582471186670543

theorem tailTrace_1281648 : CollatzResearch.WordTrace tailWord_1281648 prefixEnd_1281648 438734302582471186670543 := by
  unfold tailWord_1281648
  simp only [CollatzResearch.WordTrace]
  refine ⟨23372771430407829448470799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31163695240543772597961065 23372771430407829448470799)
  ·
    refine ⟨35059157145611744172706199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23372771430407829448470799 35059157145611744172706199)
    ·
      refine ⟨52588735718417616259059299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35059157145611744172706199 52588735718417616259059299)
      ·
        refine ⟨78883103577626424388588949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52588735718417616259059299 78883103577626424388588949)
        ·
          refine ⟨3697645480201238643215107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 78883103577626424388588949 3697645480201238643215107)
          ·
            refine ⟨5546468220301857964822661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3697645480201238643215107 5546468220301857964822661)
            ·
              refine ⟨1039962791306598368404249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5546468220301857964822661 1039962791306598368404249)
              ·
                refine ⟨779972093479948776303187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1039962791306598368404249 779972093479948776303187)
                ·
                  refine ⟨1169958140219923164454781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 779972093479948776303187 1169958140219923164454781)
                  ·
                    refine ⟨438734302582471186670543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1169958140219923164454781 438734302582471186670543)
                    ·
                      rfl

theorem cell22_1281648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 4, 2, 1, 3].length) (baseStart_1281648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1281648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1281648 prefixEnd_1281648 := by exact prefixLift 1281648
  have htrace : WordTrace (prefixWord ++ tailWord_1281648) baseStart_1281648 baseEnd_1281648 := by
    simpa [prefixWord, tailWord_1281648, baseEnd_1281648] using wordTrace_append hprefix tailTrace_1281648
  have hstable : (prefixWord ++ tailWord_1281648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281648).length < 2 ^ (prefixWord ++ tailWord_1281648).sum := by decide
  have hdescent : baseEnd_1281648 < baseStart_1281648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281657 : List Nat := [1, 2, 1, 3, 3, 1, 1, 1, 5, 4]
def baseStart_1281657 : Nat := 118140960795 + 1281657 * 2 ^ 59
def prefixEnd_1281657 : Nat := 4983230072969 + 3 ^ 40 * 1281657 * 2
def baseEnd_1281657 : Nat := 438737383466398163195515

theorem tailTrace_1281657 : CollatzResearch.WordTrace tailWord_1281657 prefixEnd_1281657 438737383466398163195515 := by
  unfold tailWord_1281657
  simp only [CollatzResearch.WordTrace]
  refine ⟨46745871117783053434019225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31163914078522035622679483 46745871117783053434019225)
  ·
    refine ⟨35059403338337290075514419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46745871117783053434019225 35059403338337290075514419)
    ·
      refine ⟨52589105007505935113271629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35059403338337290075514419 52589105007505935113271629)
      ·
        refine ⟨19720914377814725667476861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52589105007505935113271629 19720914377814725667476861)
        ·
          refine ⟨7395342891680522125303823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19720914377814725667476861 7395342891680522125303823)
          ·
            refine ⟨11093014337520783187955735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7395342891680522125303823 11093014337520783187955735)
            ·
              refine ⟨16639521506281174781933603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11093014337520783187955735 16639521506281174781933603)
              ·
                refine ⟨24959282259421762172900405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16639521506281174781933603 24959282259421762172900405)
                ·
                  refine ⟨2339932711820790203709413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24959282259421762172900405 2339932711820790203709413)
                  ·
                    refine ⟨438737383466398163195515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2339932711820790203709413 438737383466398163195515)
                    ·
                      rfl

theorem cell22_1281657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 5, 4].length) (baseStart_1281657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1281657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1281657 prefixEnd_1281657 := by exact prefixLift 1281657
  have htrace : WordTrace (prefixWord ++ tailWord_1281657) baseStart_1281657 baseEnd_1281657 := by
    simpa [prefixWord, tailWord_1281657, baseEnd_1281657] using wordTrace_append hprefix tailTrace_1281657
  have hstable : (prefixWord ++ tailWord_1281657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281657).length < 2 ^ (prefixWord ++ tailWord_1281657).sum := by decide
  have hdescent : baseEnd_1281657 < baseStart_1281657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281674 : List Nat := [3, 1, 2, 3, 2, 1, 2, 1, 3, 4]
def baseStart_1281674 : Nat := 118140960795 + 1281674 * 2 ^ 59
def prefixEnd_1281674 : Nat := 4983230072969 + 3 ^ 40 * 1281674 * 2
def baseEnd_1281674 : Nat := 438743202913815785520463

theorem tailTrace_1281674 : CollatzResearch.WordTrace tailWord_1281674 prefixEnd_1281674 438743202913815785520463 := by
  unfold tailWord_1281674
  simp only [CollatzResearch.WordTrace]
  refine ⟨11686622789680366334347019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31164327439147643558258717 11686622789680366334347019)
  ·
    refine ⟨17529934184520549501520529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11686622789680366334347019 17529934184520549501520529)
    ·
      refine ⟨13147450638390412126140397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17529934184520549501520529 13147450638390412126140397)
      ·
        refine ⟨4930293989396404547302649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13147450638390412126140397 4930293989396404547302649)
        ·
          refine ⟨3697720492047303410476987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4930293989396404547302649 3697720492047303410476987)
          ·
            refine ⟨5546580738070955115715481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3697720492047303410476987 5546580738070955115715481)
            ·
              refine ⟨4159935553553216336786611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5546580738070955115715481 4159935553553216336786611)
              ·
                refine ⟨6239903330329824505179917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4159935553553216336786611 6239903330329824505179917)
                ·
                  refine ⟨2339963748873684189442469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6239903330329824505179917 2339963748873684189442469)
                  ·
                    refine ⟨438743202913815785520463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2339963748873684189442469 438743202913815785520463)
                    ·
                      rfl

theorem cell22_1281674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 1, 3, 4].length) (baseStart_1281674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1281674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1281674 prefixEnd_1281674 := by exact prefixLift 1281674
  have htrace : WordTrace (prefixWord ++ tailWord_1281674) baseStart_1281674 baseEnd_1281674 := by
    simpa [prefixWord, tailWord_1281674, baseEnd_1281674] using wordTrace_append hprefix tailTrace_1281674
  have hstable : (prefixWord ++ tailWord_1281674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281674).length < 2 ^ (prefixWord ++ tailWord_1281674).sum := by decide
  have hdescent : baseEnd_1281674 < baseStart_1281674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281740 : List Nat := [2, 2, 1, 5, 3, 1, 1, 3, 4]
def baseStart_1281740 : Nat := 118140960795 + 1281740 * 2 ^ 59
def prefixEnd_1281740 : Nat := 4983230072969 + 3 ^ 40 * 1281740 * 2
def baseEnd_1281740 : Nat := 146255265354204537790087

theorem tailTrace_1281740 : CollatzResearch.WordTrace tailWord_1281740 prefixEnd_1281740 146255265354204537790087 := by
  unfold tailWord_1281740
  simp only [CollatzResearch.WordTrace]
  refine ⟨23374449188241179304645337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31165932250988239072860449 23374449188241179304645337)
  ·
    refine ⟨17530836891180884478484003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23374449188241179304645337 17530836891180884478484003)
    ·
      refine ⟨26296255336771326717726005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17530836891180884478484003 26296255336771326717726005)
      ·
        refine ⟨2465273937822311879786813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26296255336771326717726005 2465273937822311879786813)
        ·
          refine ⟨924477726683366954920055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2465273937822311879786813 924477726683366954920055)
          ·
            refine ⟨1386716590025050432380083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 924477726683366954920055 1386716590025050432380083)
            ·
              refine ⟨2080074885037575648570125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1386716590025050432380083 2080074885037575648570125)
              ·
                refine ⟨780028081889090868213797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2080074885037575648570125 780028081889090868213797)
                ·
                  refine ⟨146255265354204537790087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 780028081889090868213797 146255265354204537790087)
                  ·
                    rfl

theorem cell22_1281740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 3, 4].length) (baseStart_1281740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1281740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1281740 prefixEnd_1281740 := by exact prefixLift 1281740
  have htrace : WordTrace (prefixWord ++ tailWord_1281740) baseStart_1281740 baseEnd_1281740 := by
    simpa [prefixWord, tailWord_1281740, baseEnd_1281740] using wordTrace_append hprefix tailTrace_1281740
  have hstable : (prefixWord ++ tailWord_1281740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281740).length < 2 ^ (prefixWord ++ tailWord_1281740).sum := by decide
  have hdescent : baseEnd_1281740 < baseStart_1281740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281792 : List Nat := [2, 1, 1, 2, 1, 1, 2, 2, 2, 8]
def baseStart_1281792 : Nat := 118140960795 + 1281792 * 2 ^ 59
def prefixEnd_1281792 : Nat := 4983230072969 + 3 ^ 40 * 1281792 * 2
def baseEnd_1281792 : Nat := 438783596725302811070101

theorem tailTrace_1281792 : CollatzResearch.WordTrace tailWord_1281792 prefixEnd_1281792 438783596725302811070101 := by
  unfold tailWord_1281792
  simp only [CollatzResearch.WordTrace]
  refine ⟨23375397486146985745091815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31167196648195980993455753 23375397486146985745091815)
  ·
    refine ⟨35063096229220478617637723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23375397486146985745091815 35063096229220478617637723)
    ·
      refine ⟨52594644343830717926456585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35063096229220478617637723 52594644343830717926456585)
      ·
        refine ⟨39445983257873038444842439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52594644343830717926456585 39445983257873038444842439)
        ·
          refine ⟨59168974886809557667263659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39445983257873038444842439 59168974886809557667263659)
          ·
            refine ⟨88753462330214336500895489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59168974886809557667263659 88753462330214336500895489)
            ·
              refine ⟨66565096747660752375671617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88753462330214336500895489 66565096747660752375671617)
              ·
                refine ⟨49923822560745564281753713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66565096747660752375671617 49923822560745564281753713)
                ·
                  refine ⟨37442866920559173211315285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49923822560745564281753713 37442866920559173211315285)
                  ·
                    refine ⟨438783596725302811070101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 37442866920559173211315285 438783596725302811070101)
                    ·
                      rfl

theorem cell22_1281792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 2, 8].length) (baseStart_1281792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1281792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1281792 prefixEnd_1281792 := by exact prefixLift 1281792
  have htrace : WordTrace (prefixWord ++ tailWord_1281792) baseStart_1281792 baseEnd_1281792 := by
    simpa [prefixWord, tailWord_1281792, baseEnd_1281792] using wordTrace_append hprefix tailTrace_1281792
  have hstable : (prefixWord ++ tailWord_1281792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281792).length < 2 ^ (prefixWord ++ tailWord_1281792).sum := by decide
  have hdescent : baseEnd_1281792 < baseStart_1281792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281807 : List Nat := [1, 1, 2, 1, 1, 1, 4, 1, 10]
def baseStart_1281807 : Nat := 118140960795 + 1281807 * 2 ^ 59
def prefixEnd_1281807 : Nat := 4983230072969 + 3 ^ 40 * 1281807 * 2
def baseEnd_1281807 : Nat := 146262910510615923981685

theorem tailTrace_1281807 : CollatzResearch.WordTrace tailWord_1281807 prefixEnd_1281807 146262910510615923981685 := by
  unfold tailWord_1281807
  simp only [CollatzResearch.WordTrace]
  refine ⟨46751342067239629051979675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31167561378159752701319783 46751342067239629051979675)
  ·
    refine ⟨70127013100859443577969513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46751342067239629051979675 70127013100859443577969513)
    ·
      refine ⟨52595259825644582683477135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70127013100859443577969513 52595259825644582683477135)
      ·
        refine ⟨78892889738466874025215703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52595259825644582683477135 78892889738466874025215703)
        ·
          refine ⟨118339334607700311037823555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78892889738466874025215703 118339334607700311037823555)
          ·
            refine ⟨177509001911550466556735333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118339334607700311037823555 177509001911550466556735333)
            ·
              refine ⟨33282937858415712479387875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 177509001911550466556735333 33282937858415712479387875)
              ·
                refine ⟨49924406787623568719081813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33282937858415712479387875 49924406787623568719081813)
                ·
                  refine ⟨146262910510615923981685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 49924406787623568719081813 146262910510615923981685)
                  ·
                    rfl

theorem cell22_1281807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 10].length) (baseStart_1281807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1281807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1281807 prefixEnd_1281807 := by exact prefixLift 1281807
  have htrace : WordTrace (prefixWord ++ tailWord_1281807) baseStart_1281807 baseEnd_1281807 := by
    simpa [prefixWord, tailWord_1281807, baseEnd_1281807] using wordTrace_append hprefix tailTrace_1281807
  have hstable : (prefixWord ++ tailWord_1281807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281807).length < 2 ^ (prefixWord ++ tailWord_1281807).sum := by decide
  have hdescent : baseEnd_1281807 < baseStart_1281807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281824 : List Nat := [2, 1, 1, 5, 1, 1, 2, 3, 6]
def baseStart_1281824 : Nat := 118140960795 + 1281824 * 2 ^ 59
def prefixEnd_1281824 : Nat := 4983230072969 + 3 ^ 40 * 1281824 * 2
def baseEnd_1281824 : Nat := 146264850326421798090001

theorem tailTrace_1281824 : CollatzResearch.WordTrace tailWord_1281824 prefixEnd_1281824 146264850326421798090001 := by
  unfold tailWord_1281824
  simp only [CollatzResearch.WordTrace]
  refine ⟨23375981054089020477674263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31167974738785360636899017 23375981054089020477674263)
  ·
    refine ⟨35063971581133530716511395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23375981054089020477674263 35063971581133530716511395)
    ·
      refine ⟨52595957371700296074767093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35063971581133530716511395 52595957371700296074767093)
      ·
        refine ⟨4930871003596902757009415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 52595957371700296074767093 4930871003596902757009415)
        ·
          refine ⟨7396306505395354135514123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4930871003596902757009415 7396306505395354135514123)
          ·
            refine ⟨11094459758093031203271185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7396306505395354135514123 11094459758093031203271185)
            ·
              refine ⟨8320844818569773402453389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11094459758093031203271185 8320844818569773402453389)
              ·
                refine ⟨3120316806963665025920021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8320844818569773402453389 3120316806963665025920021)
                ·
                  refine ⟨146264850326421798090001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3120316806963665025920021 146264850326421798090001)
                  ·
                    rfl

theorem cell22_1281824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 3, 6].length) (baseStart_1281824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1281824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1281824 prefixEnd_1281824 := by exact prefixLift 1281824
  have htrace : WordTrace (prefixWord ++ tailWord_1281824) baseStart_1281824 baseEnd_1281824 := by
    simpa [prefixWord, tailWord_1281824, baseEnd_1281824] using wordTrace_append hprefix tailTrace_1281824
  have hstable : (prefixWord ++ tailWord_1281824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281824).length < 2 ^ (prefixWord ++ tailWord_1281824).sum := by decide
  have hdescent : baseEnd_1281824 < baseStart_1281824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281873 : List Nat := [1, 2, 2, 1, 5, 1, 3, 2, 2, 3]
def baseStart_1281873 : Nat := 118140960795 + 1281873 * 2 ^ 59
def prefixEnd_1281873 : Nat := 4983230072969 + 3 ^ 40 * 1281873 * 2
def baseEnd_1281873 : Nat := 438811324680645599794853

theorem tailTrace_1281873 : CollatzResearch.WordTrace tailWord_1281873 prefixEnd_1281873 438811324680645599794853 := by
  unfold tailWord_1281873
  simp only [CollatzResearch.WordTrace]
  refine ⟨46753749285000522323882273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31169166190000348215921515 46753749285000522323882273)
  ·
    refine ⟨35065311963750391742911705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46753749285000522323882273 35065311963750391742911705)
    ·
      refine ⟨26298983972812793807183779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35065311963750391742911705 26298983972812793807183779)
      ·
        refine ⟨39448475959219190710775669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26298983972812793807183779 39448475959219190710775669)
        ·
          refine ⟨3698294621176799129135219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39448475959219190710775669 3698294621176799129135219)
          ·
            refine ⟨5547441931765198693702829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3698294621176799129135219 5547441931765198693702829)
            ·
              refine ⟨2080290724411949510138561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5547441931765198693702829 2080290724411949510138561)
              ·
                refine ⟨1560218043308962132603921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2080290724411949510138561 1560218043308962132603921)
                ·
                  refine ⟨1170163532481721599452941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1560218043308962132603921 1170163532481721599452941)
                  ·
                    refine ⟨438811324680645599794853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1170163532481721599452941 438811324680645599794853)
                    ·
                      rfl

theorem cell22_1281873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 2, 2, 3].length) (baseStart_1281873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1281873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1281873 prefixEnd_1281873 := by exact prefixLift 1281873
  have htrace : WordTrace (prefixWord ++ tailWord_1281873) baseStart_1281873 baseEnd_1281873 := by
    simpa [prefixWord, tailWord_1281873, baseEnd_1281873] using wordTrace_append hprefix tailTrace_1281873
  have hstable : (prefixWord ++ tailWord_1281873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281873).length < 2 ^ (prefixWord ++ tailWord_1281873).sum := by decide
  have hdescent : baseEnd_1281873 < baseStart_1281873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281914 : List Nat := [3, 1, 1, 1, 1, 1, 5, 2, 7]
def baseStart_1281914 : Nat := 118140960795 + 1281914 * 2 ^ 59
def prefixEnd_1281914 : Nat := 4983230072969 + 3 ^ 40 * 1281914 * 2
def baseEnd_1281914 : Nat := 146275119939511719839909

theorem tailTrace_1281914 : CollatzResearch.WordTrace tailWord_1281914 prefixEnd_1281914 146275119939511719839909 := by
  unfold tailWord_1281914
  simp only [CollatzResearch.WordTrace]
  refine ⟨11688811169462996581531199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31170163118567990884083197 11688811169462996581531199)
  ·
    refine ⟨17533216754194494872296799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11688811169462996581531199 17533216754194494872296799)
    ·
      refine ⟨26299825131291742308445199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17533216754194494872296799 26299825131291742308445199)
      ·
        refine ⟨39449737696937613462667799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26299825131291742308445199 39449737696937613462667799)
        ·
          refine ⟨59174606545406420194001699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39449737696937613462667799 59174606545406420194001699)
          ·
            refine ⟨88761909818109630291002549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59174606545406420194001699 88761909818109630291002549)
            ·
              refine ⟨8321429045447777839781489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 88761909818109630291002549 8321429045447777839781489)
              ·
                refine ⟨6241071784085833379836117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8321429045447777839781489 6241071784085833379836117)
                ·
                  refine ⟨146275119939511719839909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6241071784085833379836117 146275119939511719839909)
                  ·
                    rfl

theorem cell22_1281914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 2, 7].length) (baseStart_1281914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1281914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1281914 prefixEnd_1281914 := by exact prefixLift 1281914
  have htrace : WordTrace (prefixWord ++ tailWord_1281914) baseStart_1281914 baseEnd_1281914 := by
    simpa [prefixWord, tailWord_1281914, baseEnd_1281914] using wordTrace_append hprefix tailTrace_1281914
  have hstable : (prefixWord ++ tailWord_1281914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281914).length < 2 ^ (prefixWord ++ tailWord_1281914).sum := by decide
  have hdescent : baseEnd_1281914 < baseStart_1281914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281948 : List Nat := [2, 2, 3, 3, 1, 2, 1, 3, 5]
def baseStart_1281948 : Nat := 118140960795 + 1281948 * 2 ^ 59
def prefixEnd_1281948 : Nat := 4983230072969 + 3 ^ 40 * 1281948 * 2
def baseEnd_1281948 : Nat := 146278999571123468056541

theorem tailTrace_1281948 : CollatzResearch.WordTrace tailWord_1281948 prefixEnd_1281948 146278999571123468056541 := by
  unfold tailWord_1281948
  simp only [CollatzResearch.WordTrace]
  refine ⟨23378242379864405066431249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31170989839819206755241665 23378242379864405066431249)
  ·
    refine ⟨17533681784898303799823437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23378242379864405066431249 17533681784898303799823437)
    ·
      refine ⟨6575130669336863924933789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17533681784898303799823437 6575130669336863924933789)
      ·
        refine ⟨2465674001001323971850171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6575130669336863924933789 2465674001001323971850171)
        ·
          refine ⟨3698511001501985957775257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2465674001001323971850171 3698511001501985957775257)
          ·
            refine ⟨2773883251126489468331443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3698511001501985957775257 2773883251126489468331443)
            ·
              refine ⟨4160824876689734202497165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2773883251126489468331443 4160824876689734202497165)
              ·
                refine ⟨1560309328758650325936437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4160824876689734202497165 1560309328758650325936437)
                ·
                  refine ⟨146278999571123468056541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1560309328758650325936437 146278999571123468056541)
                  ·
                    rfl

theorem cell22_1281948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 3, 5].length) (baseStart_1281948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1281948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1281948 prefixEnd_1281948 := by exact prefixLift 1281948
  have htrace : WordTrace (prefixWord ++ tailWord_1281948) baseStart_1281948 baseEnd_1281948 := by
    simpa [prefixWord, tailWord_1281948, baseEnd_1281948] using wordTrace_append hprefix tailTrace_1281948
  have hstable : (prefixWord ++ tailWord_1281948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281948).length < 2 ^ (prefixWord ++ tailWord_1281948).sum := by decide
  have hdescent : baseEnd_1281948 < baseStart_1281948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1281961 : List Nat := [1, 2, 1, 1, 1, 1, 4, 6, 1, 4]
def baseStart_1281961 : Nat := 118140960795 + 1281961 * 2 ^ 59
def prefixEnd_1281961 : Nat := 4983230072969 + 3 ^ 40 * 1281961 * 2
def baseEnd_1281961 : Nat := 438841448879042703594583

theorem tailTrace_1281961 : CollatzResearch.WordTrace tailWord_1281961 prefixEnd_1281961 438841448879042703594583 := by
  unfold tailWord_1281961
  simp only [CollatzResearch.WordTrace]
  refine ⟨46756958908681713353085737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31171305939121142235390491 46756958908681713353085737)
  ·
    refine ⟨35067719181511285014814303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46756958908681713353085737 35067719181511285014814303)
    ·
      refine ⟨52601578772266927522221455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35067719181511285014814303 52601578772266927522221455)
      ·
        refine ⟨78902368158400391283332183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52601578772266927522221455 78902368158400391283332183)
        ·
          refine ⟨118353552237600586924998275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78902368158400391283332183 118353552237600586924998275)
          ·
            refine ⟨177530328356400880387497413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118353552237600586924998275 177530328356400880387497413)
            ·
              refine ⟨33286936566825165072655765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 177530328356400880387497413 33286936566825165072655765)
              ·
                refine ⟨1560325151569929612780739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 33286936566825165072655765 1560325151569929612780739)
                ·
                  refine ⟨2340487727354894419171109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1560325151569929612780739 2340487727354894419171109)
                  ·
                    refine ⟨438841448879042703594583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2340487727354894419171109 438841448879042703594583)
                    ·
                      rfl

theorem cell22_1281961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 6, 1, 4].length) (baseStart_1281961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1281961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1281961 prefixEnd_1281961 := by exact prefixLift 1281961
  have htrace : WordTrace (prefixWord ++ tailWord_1281961) baseStart_1281961 baseEnd_1281961 := by
    simpa [prefixWord, tailWord_1281961, baseEnd_1281961] using wordTrace_append hprefix tailTrace_1281961
  have hstable : (prefixWord ++ tailWord_1281961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1281961).length < 2 ^ (prefixWord ++ tailWord_1281961).sum := by decide
  have hdescent : baseEnd_1281961 < baseStart_1281961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1281961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282008 : List Nat := [2, 1, 2, 2, 2, 2, 1, 5, 2, 3]
def baseStart_1282008 : Nat := 118140960795 + 1282008 * 2 ^ 59
def prefixEnd_1282008 : Nat := 4983230072969 + 3 ^ 40 * 1282008 * 2
def baseEnd_1282008 : Nat := 438857537939550247669439

theorem tailTrace_1282008 : CollatzResearch.WordTrace tailWord_1282008 prefixEnd_1282008 438857537939550247669439 := by
  unfold tailWord_1282008
  simp only [CollatzResearch.WordTrace]
  refine ⟨23379336569755720190023339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31172448759674293586697785 23379336569755720190023339)
  ·
    refine ⟨35069004854633580285035009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23379336569755720190023339 35069004854633580285035009)
    ·
      refine ⟨26301753640975185213776257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35069004854633580285035009 26301753640975185213776257)
      ·
        refine ⟨19726315230731388910332193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26301753640975185213776257 19726315230731388910332193)
        ·
          refine ⟨14794736423048541682749145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19726315230731388910332193 14794736423048541682749145)
          ·
            refine ⟨11096052317286406262061859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14794736423048541682749145 11096052317286406262061859)
            ·
              refine ⟨16644078475929609393092789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11096052317286406262061859 16644078475929609393092789)
              ·
                refine ⟨1560382357118400880602449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16644078475929609393092789 1560382357118400880602449)
                ·
                  refine ⟨1170286767838800660451837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1560382357118400880602449 1170286767838800660451837)
                  ·
                    refine ⟨438857537939550247669439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1170286767838800660451837 438857537939550247669439)
                    ·
                      rfl

theorem cell22_1282008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 5, 2, 3].length) (baseStart_1282008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1282008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1282008 prefixEnd_1282008 := by exact prefixLift 1282008
  have htrace : WordTrace (prefixWord ++ tailWord_1282008) baseStart_1282008 baseEnd_1282008 := by
    simpa [prefixWord, tailWord_1282008, baseEnd_1282008] using wordTrace_append hprefix tailTrace_1282008
  have hstable : (prefixWord ++ tailWord_1282008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282008).length < 2 ^ (prefixWord ++ tailWord_1282008).sum := by decide
  have hdescent : baseEnd_1282008 < baseStart_1282008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282023 : List Nat := [1, 1, 5, 2, 3, 1, 1, 1, 1, 6]
def baseStart_1282023 : Nat := 118140960795 + 1282023 * 2 ^ 59
def prefixEnd_1282023 : Nat := 4983230072969 + 3 ^ 40 * 1282023 * 2
def baseEnd_1282023 : Nat := 438862672746095208544393

theorem tailTrace_1282023 : CollatzResearch.WordTrace tailWord_1282023 prefixEnd_1282023 438862672746095208544393 := by
  unfold tailWord_1282023
  simp only [CollatzResearch.WordTrace]
  refine ⟨46759220234457097941842723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31172813489638065294561815 46759220234457097941842723)
  ·
    refine ⟨70138830351685646912764085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46759220234457097941842723 70138830351685646912764085)
    ·
      refine ⟨6575515345470529398071633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 70138830351685646912764085 6575515345470529398071633)
      ·
        refine ⟨4931636509102897048553725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6575515345470529398071633 4931636509102897048553725)
        ·
          refine ⟨1849363690913586393207647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4931636509102897048553725 1849363690913586393207647)
          ·
            refine ⟨2774045536370379589811471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1849363690913586393207647 2774045536370379589811471)
            ·
              refine ⟨4161068304555569384717207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2774045536370379589811471 4161068304555569384717207)
              ·
                refine ⟨6241602456833354077075811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4161068304555569384717207 6241602456833354077075811)
                ·
                  refine ⟨9362403685250031115613717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6241602456833354077075811 9362403685250031115613717)
                  ·
                    refine ⟨438862672746095208544393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9362403685250031115613717 438862672746095208544393)
                    ·
                      rfl

theorem cell22_1282023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_1282023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1282023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1282023 prefixEnd_1282023 := by exact prefixLift 1282023
  have htrace : WordTrace (prefixWord ++ tailWord_1282023) baseStart_1282023 baseEnd_1282023 := by
    simpa [prefixWord, tailWord_1282023, baseEnd_1282023] using wordTrace_append hprefix tailTrace_1282023
  have hstable : (prefixWord ++ tailWord_1282023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282023).length < 2 ^ (prefixWord ++ tailWord_1282023).sum := by decide
  have hdescent : baseEnd_1282023 < baseStart_1282023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282029 : List Nat := [1, 5, 1, 4, 1, 2, 2, 1, 1, 4]
def baseStart_1282029 : Nat := 118140960795 + 1282029 * 2 ^ 59
def prefixEnd_1282029 : Nat := 4983230072969 + 3 ^ 40 * 1282029 * 2
def baseEnd_1282029 : Nat := 438864726668713192894375

theorem tailTrace_1282029 : CollatzResearch.WordTrace tailWord_1282029 prefixEnd_1282029 438864726668713192894375 := by
  unfold tailWord_1282029
  simp only [CollatzResearch.WordTrace]
  refine ⟨46759439072435360966561141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31172959381623573977707427 46759439072435360966561141)
  ·
    refine ⟨4383697413040815090615107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46759439072435360966561141 4383697413040815090615107)
    ·
      refine ⟨6575546119561222635922661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4383697413040815090615107 6575546119561222635922661)
      ·
        refine ⟨1232914897417729244235499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6575546119561222635922661 1232914897417729244235499)
        ·
          refine ⟨1849372346126593866353249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1232914897417729244235499 1849372346126593866353249)
          ·
            refine ⟨1387029259594945399764937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1849372346126593866353249 1387029259594945399764937)
            ·
              refine ⟨1040271944696209049823703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1387029259594945399764937 1040271944696209049823703)
              ·
                refine ⟨1560407917044313574735555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1040271944696209049823703 1560407917044313574735555)
                ·
                  refine ⟨2340611875566470362103333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1560407917044313574735555 2340611875566470362103333)
                  ·
                    refine ⟨438864726668713192894375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2340611875566470362103333 438864726668713192894375)
                    ·
                      rfl

theorem cell22_1282029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 2, 1, 1, 4].length) (baseStart_1282029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1282029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1282029 prefixEnd_1282029 := by exact prefixLift 1282029
  have htrace : WordTrace (prefixWord ++ tailWord_1282029) baseStart_1282029 baseEnd_1282029 := by
    simpa [prefixWord, tailWord_1282029, baseEnd_1282029] using wordTrace_append hprefix tailTrace_1282029
  have hstable : (prefixWord ++ tailWord_1282029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282029).length < 2 ^ (prefixWord ++ tailWord_1282029).sum := by decide
  have hdescent : baseEnd_1282029 < baseStart_1282029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282038 : List Nat := [5, 1, 1, 1, 4, 1, 9]
def baseStart_1282038 : Nat := 118140960795 + 1282038 * 2 ^ 59
def prefixEnd_1282038 : Nat := 4983230072969 + 3 ^ 40 * 1282038 * 2
def baseEnd_1282038 : Nat := 16254363242690376645161

theorem tailTrace_1282038 : CollatzResearch.WordTrace tailWord_1282038 prefixEnd_1282038 16254363242690376645161 := by
  unfold tailWord_1282038
  simp only [CollatzResearch.WordTrace]
  refine ⟨2922485458087672218977423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31173178219601837002425845 2922485458087672218977423)
  ·
    refine ⟨4383728187131508328466135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2922485458087672218977423 4383728187131508328466135)
    ·
      refine ⟨6575592280697262492699203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4383728187131508328466135 6575592280697262492699203)
      ·
        refine ⟨9863388421045893739048805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6575592280697262492699203 9863388421045893739048805)
        ·
          refine ⟨1849385328946105076071651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9863388421045893739048805 1849385328946105076071651)
          ·
            refine ⟨2774077993419157614107477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1849385328946105076071651 2774077993419157614107477)
            ·
              refine ⟨16254363242690376645161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2774077993419157614107477 16254363242690376645161)
              ·
                rfl

theorem cell22_1282038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 9].length) (baseStart_1282038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1282038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1282038 prefixEnd_1282038 := by exact prefixLift 1282038
  have htrace : WordTrace (prefixWord ++ tailWord_1282038) baseStart_1282038 baseEnd_1282038 := by
    simpa [prefixWord, tailWord_1282038, baseEnd_1282038] using wordTrace_append hprefix tailTrace_1282038
  have hstable : (prefixWord ++ tailWord_1282038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282038).length < 2 ^ (prefixWord ++ tailWord_1282038).sum := by decide
  have hdescent : baseEnd_1282038 < baseStart_1282038 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282053 : List Nat := [1, 3, 1, 1, 2, 4, 1, 3, 3, 3]
def baseStart_1282053 : Nat := 118140960795 + 1282053 * 2 ^ 59
def prefixEnd_1282053 : Nat := 4983230072969 + 3 ^ 40 * 1282053 * 2
def baseEnd_1282053 : Nat := 438872942359185130294301

theorem tailTrace_1282053 : CollatzResearch.WordTrace tailWord_1282053 prefixEnd_1282053 438872942359185130294301 := by
  unfold tailWord_1282053
  simp only [CollatzResearch.WordTrace]
  refine ⟨46760314424348413065434813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31173542949565608710289875 46760314424348413065434813)
  ·
    refine ⟨17535117909130654899538055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46760314424348413065434813 17535117909130654899538055)
    ·
      refine ⟨26302676863695982349307083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17535117909130654899538055 26302676863695982349307083)
      ·
        refine ⟨39454015295543973523960625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26302676863695982349307083 39454015295543973523960625)
        ·
          refine ⟨29590511471657980142970469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39454015295543973523960625 29590511471657980142970469)
          ·
            refine ⟨5548220900935871276806963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29590511471657980142970469 5548220900935871276806963)
            ·
              refine ⟨8322331351403806915210445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5548220900935871276806963 8322331351403806915210445)
              ·
                refine ⟨3120874256776427593203917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8322331351403806915210445 3120874256776427593203917)
                ·
                  refine ⟨1170327846291160347451469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3120874256776427593203917 1170327846291160347451469)
                  ·
                    refine ⟨438872942359185130294301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1170327846291160347451469 438872942359185130294301)
                    ·
                      rfl

theorem cell22_1282053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 3, 3, 3].length) (baseStart_1282053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1282053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1282053 prefixEnd_1282053 := by exact prefixLift 1282053
  have htrace : WordTrace (prefixWord ++ tailWord_1282053) baseStart_1282053 baseEnd_1282053 := by
    simpa [prefixWord, tailWord_1282053, baseEnd_1282053] using wordTrace_append hprefix tailTrace_1282053
  have hstable : (prefixWord ++ tailWord_1282053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282053).length < 2 ^ (prefixWord ++ tailWord_1282053).sum := by decide
  have hdescent : baseEnd_1282053 < baseStart_1282053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282104 : List Nat := [2, 1, 2, 1, 6, 1, 3, 2, 1, 3]
def baseStart_1282104 : Nat := 118140960795 + 1282104 * 2 ^ 59
def prefixEnd_1282104 : Nat := 4983230072969 + 3 ^ 40 * 1282104 * 2
def baseEnd_1282104 : Nat := 438890400701437997269145

theorem tailTrace_1282104 : CollatzResearch.WordTrace tailWord_1282104 prefixEnd_1282104 438890400701437997269145 := by
  unfold tailWord_1282104
  simp only [CollatzResearch.WordTrace]
  refine ⟨23381087273581824387770683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31174783031442432517027577 23381087273581824387770683)
  ·
    refine ⟨35071630910372736581656025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23381087273581824387770683 35071630910372736581656025)
    ·
      refine ⟨26303723182779552436242019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35071630910372736581656025 26303723182779552436242019)
      ·
        refine ⟨39455584774169328654363029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26303723182779552436242019 39455584774169328654363029)
        ·
          refine ⟨1849480536289187280673267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 39455584774169328654363029 1849480536289187280673267)
          ·
            refine ⟨2774220804433780921009901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1849480536289187280673267 2774220804433780921009901)
            ·
              refine ⟨1040332801662667845378713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2774220804433780921009901 1040332801662667845378713)
              ·
                refine ⟨780249601247000884034035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1040332801662667845378713 780249601247000884034035)
                ·
                  refine ⟨1170374401870501326051053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 780249601247000884034035 1170374401870501326051053)
                  ·
                    refine ⟨438890400701437997269145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1170374401870501326051053 438890400701437997269145)
                    ·
                      rfl

theorem cell22_1282104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 3, 2, 1, 3].length) (baseStart_1282104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1282104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1282104 prefixEnd_1282104 := by exact prefixLift 1282104
  have htrace : WordTrace (prefixWord ++ tailWord_1282104) baseStart_1282104 baseEnd_1282104 := by
    simpa [prefixWord, tailWord_1282104, baseEnd_1282104] using wordTrace_append hprefix tailTrace_1282104
  have hstable : (prefixWord ++ tailWord_1282104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282104).length < 2 ^ (prefixWord ++ tailWord_1282104).sum := by decide
  have hdescent : baseEnd_1282104 < baseStart_1282104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282130 : List Nat := [3, 2, 2, 1, 4, 1, 1, 1, 3, 4]
def baseStart_1282130 : Nat := 118140960795 + 1282130 * 2 ^ 59
def prefixEnd_1282130 : Nat := 4983230072969 + 3 ^ 40 * 1282130 * 2
def baseEnd_1282130 : Nat := 438899301032782596119065

theorem tailTrace_1282130 : CollatzResearch.WordTrace tailWord_1282130 prefixEnd_1282130 438899301032782596119065 := by
  unfold tailWord_1282130
  simp only [CollatzResearch.WordTrace]
  refine ⟨11690780711267363803996961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31175415230046303477325229 11690780711267363803996961)
  ·
    refine ⟨8768085533450522852997721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11690780711267363803996961 8768085533450522852997721)
    ·
      refine ⟨6576064150087892139748291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8768085533450522852997721 6576064150087892139748291)
      ·
        refine ⟨9864096225131838209622437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6576064150087892139748291 9864096225131838209622437)
        ·
          refine ⟨1849518042212219664304207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9864096225131838209622437 1849518042212219664304207)
          ·
            refine ⟨2774277063318329496456311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1849518042212219664304207 2774277063318329496456311)
            ·
              refine ⟨4161415594977494244684467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2774277063318329496456311 4161415594977494244684467)
              ·
                refine ⟨6242123392466241367026701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4161415594977494244684467 6242123392466241367026701)
                ·
                  refine ⟨2340796272174840512635013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6242123392466241367026701 2340796272174840512635013)
                  ·
                    refine ⟨438899301032782596119065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2340796272174840512635013 438899301032782596119065)
                    ·
                      rfl

theorem cell22_1282130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_1282130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1282130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1282130 prefixEnd_1282130 := by exact prefixLift 1282130
  have htrace : WordTrace (prefixWord ++ tailWord_1282130) baseStart_1282130 baseEnd_1282130 := by
    simpa [prefixWord, tailWord_1282130, baseEnd_1282130] using wordTrace_append hprefix tailTrace_1282130
  have hstable : (prefixWord ++ tailWord_1282130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282130).length < 2 ^ (prefixWord ++ tailWord_1282130).sum := by decide
  have hdescent : baseEnd_1282130 < baseStart_1282130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282143 : List Nat := [1, 1, 2, 3, 1, 1, 2, 4, 4, 3]
def baseStart_1282143 : Nat := 118140960795 + 1282143 * 2 ^ 59
def prefixEnd_1282143 : Nat := 4983230072969 + 3 ^ 40 * 1282143 * 2
def baseEnd_1282143 : Nat := 438903751198454895544025

theorem tailTrace_1282143 : CollatzResearch.WordTrace tailWord_1282143 prefixEnd_1282143 438903751198454895544025 := by
  unfold tailWord_1282143
  simp only [CollatzResearch.WordTrace]
  refine ⟨46763596994022358436211083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31175731329348238957474055 46763596994022358436211083)
  ·
    refine ⟨70145395491033537654316625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46763596994022358436211083 70145395491033537654316625)
    ·
      refine ⟨52609046618275153240737469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70145395491033537654316625 52609046618275153240737469)
      ·
        refine ⟨19728392481853182465276551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52609046618275153240737469 19728392481853182465276551)
        ·
          refine ⟨29592588722779773697914827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19728392481853182465276551 29592588722779773697914827)
          ·
            refine ⟨44388883084169660546872241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29592588722779773697914827 44388883084169660546872241)
            ·
              refine ⟨33291662313127245410154181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44388883084169660546872241 33291662313127245410154181)
              ·
                refine ⟨6242186683711358514403909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33291662313127245410154181 6242186683711358514403909)
                ·
                  refine ⟨1170410003195879721450733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6242186683711358514403909 1170410003195879721450733)
                  ·
                    refine ⟨438903751198454895544025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1170410003195879721450733 438903751198454895544025)
                    ·
                      rfl

theorem cell22_1282143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 4, 4, 3].length) (baseStart_1282143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1282143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1282143 prefixEnd_1282143 := by exact prefixLift 1282143
  have htrace : WordTrace (prefixWord ++ tailWord_1282143) baseStart_1282143 baseEnd_1282143 := by
    simpa [prefixWord, tailWord_1282143, baseEnd_1282143] using wordTrace_append hprefix tailTrace_1282143
  have hstable : (prefixWord ++ tailWord_1282143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282143).length < 2 ^ (prefixWord ++ tailWord_1282143).sum := by decide
  have hdescent : baseEnd_1282143 < baseStart_1282143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282156 : List Nat := [2, 2, 1, 1, 3, 13]
def baseStart_1282156 : Nat := 118140960795 + 1282156 * 2 ^ 59
def prefixEnd_1282156 : Nat := 4983230072969 + 3 ^ 40 * 1282156 * 2
def baseEnd_1282156 : Nat := 5418619769927496234185

theorem tailTrace_1282156 : CollatzResearch.WordTrace tailWord_1282156 prefixEnd_1282156 5418619769927496234185 := by
  unfold tailWord_1282156
  simp only [CollatzResearch.WordTrace]
  refine ⟨23382035571487630828217161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31176047428650174437622881 23382035571487630828217161)
  ·
    refine ⟨17536526678615723121162871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23382035571487630828217161 17536526678615723121162871)
    ·
      refine ⟨26304790017923584681744307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17536526678615723121162871 26304790017923584681744307)
      ·
        refine ⟨39457185026885377022616461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26304790017923584681744307 39457185026885377022616461)
        ·
          refine ⟨14796444385082016383481173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39457185026885377022616461 14796444385082016383481173)
          ·
            refine ⟨5418619769927496234185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 14796444385082016383481173 5418619769927496234185)
            ·
              rfl

theorem cell22_1282156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 13].length) (baseStart_1282156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1282156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1282156 prefixEnd_1282156 := by exact prefixLift 1282156
  have htrace : WordTrace (prefixWord ++ tailWord_1282156) baseStart_1282156 baseEnd_1282156 := by
    simpa [prefixWord, tailWord_1282156, baseEnd_1282156] using wordTrace_append hprefix tailTrace_1282156
  have hstable : (prefixWord ++ tailWord_1282156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282156).length < 2 ^ (prefixWord ++ tailWord_1282156).sum := by decide
  have hdescent : baseEnd_1282156 < baseStart_1282156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282160 : List Nat := [2, 1, 1, 1, 5, 2, 1, 4, 2, 3]
def baseStart_1282160 : Nat := 118140960795 + 1282160 * 2 ^ 59
def prefixEnd_1282160 : Nat := 4983230072969 + 3 ^ 40 * 1282160 * 2
def baseEnd_1282160 : Nat := 438909570645872517868973

theorem tailTrace_1282160 : CollatzResearch.WordTrace tailWord_1282160 prefixEnd_1282160 438909570645872517868973 := by
  unfold tailWord_1282160
  simp only [CollatzResearch.WordTrace]
  refine ⟨23382108517480385169789967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31176144689973846893053289 23382108517480385169789967)
  ·
    refine ⟨35073162776220577754684951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23382108517480385169789967 35073162776220577754684951)
    ·
      refine ⟨52609744164330866632027427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35073162776220577754684951 52609744164330866632027427)
      ·
        refine ⟨78914616246496299948041141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52609744164330866632027427 78914616246496299948041141)
        ·
          refine ⟨7398245273109028120128857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 78914616246496299948041141 7398245273109028120128857)
          ·
            refine ⟨5548683954831771090096643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7398245273109028120128857 5548683954831771090096643)
            ·
              refine ⟨8323025932247656635144965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5548683954831771090096643 8323025932247656635144965)
              ·
                refine ⟨1560567362296435619089681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8323025932247656635144965 1560567362296435619089681)
                ·
                  refine ⟨1170425521722326714317261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1560567362296435619089681 1170425521722326714317261)
                  ·
                    refine ⟨438909570645872517868973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1170425521722326714317261 438909570645872517868973)
                    ·
                      rfl

theorem cell22_1282160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 4, 2, 3].length) (baseStart_1282160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1282160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1282160 prefixEnd_1282160 := by exact prefixLift 1282160
  have htrace : WordTrace (prefixWord ++ tailWord_1282160) baseStart_1282160 baseEnd_1282160 := by
    simpa [prefixWord, tailWord_1282160, baseEnd_1282160] using wordTrace_append hprefix tailTrace_1282160
  have hstable : (prefixWord ++ tailWord_1282160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282160).length < 2 ^ (prefixWord ++ tailWord_1282160).sum := by decide
  have hdescent : baseEnd_1282160 < baseStart_1282160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282162 : List Nat := [3, 2, 1, 2, 2, 2, 4, 2, 4]
def baseStart_1282162 : Nat := 118140960795 + 1282162 * 2 ^ 59
def prefixEnd_1282162 : Nat := 4983230072969 + 3 ^ 40 * 1282162 * 2
def baseEnd_1282162 : Nat := 146303418428915059772989

theorem tailTrace_1282162 : CollatzResearch.WordTrace tailWord_1282162 prefixEnd_1282162 146303418428915059772989 := by
  unfold tailWord_1282162
  simp only [CollatzResearch.WordTrace]
  refine ⟨11691072495238381170288185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31176193320635683120768493 11691072495238381170288185)
  ·
    refine ⟨8768304371428785877716139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11691072495238381170288185 8768304371428785877716139)
    ·
      refine ⟨13152456557143178816574209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8768304371428785877716139 13152456557143178816574209)
      ·
        refine ⟨9864342417857384112430657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13152456557143178816574209 9864342417857384112430657)
        ·
          refine ⟨7398256813393038084322993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9864342417857384112430657 7398256813393038084322993)
          ·
            refine ⟨5548692610044778563242245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7398256813393038084322993 5548692610044778563242245)
            ·
              refine ⟨1040379864383395980607921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5548692610044778563242245 1040379864383395980607921)
              ·
                refine ⟨780284898287546985455941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1040379864383395980607921 780284898287546985455941)
                ·
                  refine ⟨146303418428915059772989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 780284898287546985455941 146303418428915059772989)
                  ·
                    rfl

theorem cell22_1282162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 4, 2, 4].length) (baseStart_1282162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1282162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1282162 prefixEnd_1282162 := by exact prefixLift 1282162
  have htrace : WordTrace (prefixWord ++ tailWord_1282162) baseStart_1282162 baseEnd_1282162 := by
    simpa [prefixWord, tailWord_1282162, baseEnd_1282162] using wordTrace_append hprefix tailTrace_1282162
  have hstable : (prefixWord ++ tailWord_1282162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282162).length < 2 ^ (prefixWord ++ tailWord_1282162).sum := by decide
  have hdescent : baseEnd_1282162 < baseStart_1282162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282171 : List Nat := [1, 1, 1, 1, 1, 4, 1, 1, 4, 7]
def baseStart_1282171 : Nat := 118140960795 + 1282171 * 2 ^ 59
def prefixEnd_1282171 : Nat := 4983230072969 + 3 ^ 40 * 1282171 * 2
def baseEnd_1282171 : Nat := 438913336170672155843939

theorem tailTrace_1282171 : CollatzResearch.WordTrace tailWord_1282171 prefixEnd_1282171 438913336170672155843939 := by
  unfold tailWord_1282171
  simp only [CollatzResearch.WordTrace]
  refine ⟨46764618237920919218230367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31176412158613946145486911 46764618237920919218230367)
  ·
    refine ⟨70146927356881378827345551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46764618237920919218230367 70146927356881378827345551)
    ·
      refine ⟨105220391035322068241018327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70146927356881378827345551 105220391035322068241018327)
      ·
        refine ⟨157830586552983102361527491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105220391035322068241018327 157830586552983102361527491)
        ·
          refine ⟨236745879829474653542291237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157830586552983102361527491 236745879829474653542291237)
          ·
            refine ⟨44389852468026497539179607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 236745879829474653542291237 44389852468026497539179607)
            ·
              refine ⟨66584778702039746308769411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44389852468026497539179607 66584778702039746308769411)
              ·
                refine ⟨99877168053059619463154117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66584778702039746308769411 99877168053059619463154117)
                ·
                  refine ⟨18726969009948678649341397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 99877168053059619463154117 18726969009948678649341397)
                  ·
                    refine ⟨438913336170672155843939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18726969009948678649341397 438913336170672155843939)
                    ·
                      rfl

theorem cell22_1282171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 7].length) (baseStart_1282171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1282171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1282171 prefixEnd_1282171 := by exact prefixLift 1282171
  have htrace : WordTrace (prefixWord ++ tailWord_1282171) baseStart_1282171 baseEnd_1282171 := by
    simpa [prefixWord, tailWord_1282171, baseEnd_1282171] using wordTrace_append hprefix tailTrace_1282171
  have hstable : (prefixWord ++ tailWord_1282171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282171).length < 2 ^ (prefixWord ++ tailWord_1282171).sum := by decide
  have hdescent : baseEnd_1282171 < baseStart_1282171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282173 : List Nat := [1, 4, 1, 1, 3, 2, 3, 7]
def baseStart_1282173 : Nat := 118140960795 + 1282173 * 2 ^ 59
def prefixEnd_1282173 : Nat := 4983230072969 + 3 ^ 40 * 1282173 * 2
def baseEnd_1282173 : Nat := 48768224534616090810437

theorem tailTrace_1282173 : CollatzResearch.WordTrace tailWord_1282173 prefixEnd_1282173 48768224534616090810437 := by
  unfold tailWord_1282173
  simp only [CollatzResearch.WordTrace]
  refine ⟨46764691183913673559803173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31176460789275782373202115 46764691183913673559803173)
  ·
    refine ⟨8768379596983813792463095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46764691183913673559803173 8768379596983813792463095)
    ·
      refine ⟨13152569395475720688694643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8768379596983813792463095 13152569395475720688694643)
      ·
        refine ⟨19728854093213581033041965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13152569395475720688694643 19728854093213581033041965)
        ·
          refine ⟨7398320284955092887390737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19728854093213581033041965 7398320284955092887390737)
          ·
            refine ⟨5548740213716319665543053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7398320284955092887390737 5548740213716319665543053)
            ·
              refine ⟨2080777580143619874578645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5548740213716319665543053 2080777580143619874578645)
              ·
                refine ⟨48768224534616090810437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2080777580143619874578645 48768224534616090810437)
                ·
                  rfl

theorem cell22_1282173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 7].length) (baseStart_1282173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1282173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1282173 prefixEnd_1282173 := by exact prefixLift 1282173
  have htrace : WordTrace (prefixWord ++ tailWord_1282173) baseStart_1282173 baseEnd_1282173 := by
    simpa [prefixWord, tailWord_1282173, baseEnd_1282173] using wordTrace_append hprefix tailTrace_1282173
  have hstable : (prefixWord ++ tailWord_1282173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282173).length < 2 ^ (prefixWord ++ tailWord_1282173).sum := by decide
  have hdescent : baseEnd_1282173 < baseStart_1282173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282198 : List Nat := [5, 3, 2, 1, 1, 1, 1, 3, 1, 4]
def baseStart_1282198 : Nat := 118140960795 + 1282198 * 2 ^ 59
def prefixEnd_1282198 : Nat := 4983230072969 + 3 ^ 40 * 1282198 * 2
def baseEnd_1282198 : Nat := 438922578822453085418857

theorem tailTrace_1282198 : CollatzResearch.WordTrace tailWord_1282198 prefixEnd_1282198 438922578822453085418857 := by
  unfold tailWord_1282198
  simp only [CollatzResearch.WordTrace]
  refine ⟨2922850188051443926841453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31177068672548735219642165 2922850188051443926841453)
  ·
    refine ⟨1096068820519291472565545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2922850188051443926841453 1096068820519291472565545)
    ·
      refine ⟨822051615389468604424159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1096068820519291472565545 822051615389468604424159)
      ·
        refine ⟨1233077423084202906636239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 822051615389468604424159 1233077423084202906636239)
        ·
          refine ⟨1849616134626304359954359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1233077423084202906636239 1849616134626304359954359)
          ·
            refine ⟨2774424201939456539931539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1849616134626304359954359 2774424201939456539931539)
            ·
              refine ⟨4161636302909184809897309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2774424201939456539931539 4161636302909184809897309)
              ·
                refine ⟨1560613613590944303711491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4161636302909184809897309 1560613613590944303711491)
                ·
                  refine ⟨2340920420386416455567237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1560613613590944303711491 2340920420386416455567237)
                  ·
                    refine ⟨438922578822453085418857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2340920420386416455567237 438922578822453085418857)
                    ·
                      rfl

theorem cell22_1282198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_1282198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1282198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1282198 prefixEnd_1282198 := by exact prefixLift 1282198
  have htrace : WordTrace (prefixWord ++ tailWord_1282198) baseStart_1282198 baseEnd_1282198 := by
    simpa [prefixWord, tailWord_1282198, baseEnd_1282198] using wordTrace_append hprefix tailTrace_1282198
  have hstable : (prefixWord ++ tailWord_1282198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282198).length < 2 ^ (prefixWord ++ tailWord_1282198).sum := by decide
  have hdescent : baseEnd_1282198 < baseStart_1282198 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282228 : List Nat := [2, 5, 3, 1, 2, 1, 1, 1, 1, 5]
def baseStart_1282228 : Nat := 118140960795 + 1282228 * 2 ^ 59
def prefixEnd_1282228 : Nat := 4983230072969 + 3 ^ 40 * 1282228 * 2
def baseEnd_1282228 : Nat := 438932848435543007168765

theorem tailTrace_1282228 : CollatzResearch.WordTrace tailWord_1282228 prefixEnd_1282228 438932848435543007168765 := by
  unfold tailWord_1282228
  simp only [CollatzResearch.WordTrace]
  refine ⟨23383348599357208976527669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31177798132476278635370225 23383348599357208976527669)
  ·
    refine ⟨2192188931189738341549469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23383348599357208976527669 2192188931189738341549469)
    ·
      refine ⟨822070849196151878081051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2192188931189738341549469 822070849196151878081051)
      ·
        refine ⟨1233106273794227817121577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 822070849196151878081051 1233106273794227817121577)
        ·
          refine ⟨924829705345670862841183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1233106273794227817121577 924829705345670862841183)
          ·
            refine ⟨1387244558018506294261775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 924829705345670862841183 1387244558018506294261775)
            ·
              refine ⟨2080866837027759441392663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1387244558018506294261775 2080866837027759441392663)
              ·
                refine ⟨3121300255541639162088995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2080866837027759441392663 3121300255541639162088995)
                ·
                  refine ⟨4681950383312458743133493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3121300255541639162088995 4681950383312458743133493)
                  ·
                    refine ⟨438932848435543007168765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4681950383312458743133493 438932848435543007168765)
                    ·
                      rfl

theorem cell22_1282228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_1282228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1282228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1282228 prefixEnd_1282228 := by exact prefixLift 1282228
  have htrace : WordTrace (prefixWord ++ tailWord_1282228) baseStart_1282228 baseEnd_1282228 := by
    simpa [prefixWord, tailWord_1282228, baseEnd_1282228] using wordTrace_append hprefix tailTrace_1282228
  have hstable : (prefixWord ++ tailWord_1282228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282228).length < 2 ^ (prefixWord ++ tailWord_1282228).sum := by decide
  have hdescent : baseEnd_1282228 < baseStart_1282228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282233 : List Nat := [1, 2, 1, 4, 1, 2, 1, 3, 2, 5]
def baseStart_1282233 : Nat := 118140960795 + 1282233 * 2 ^ 59
def prefixEnd_1282233 : Nat := 4983230072969 + 3 ^ 40 * 1282233 * 2
def baseEnd_1282233 : Nat := 438934560037724660793749

theorem tailTrace_1282233 : CollatzResearch.WordTrace tailWord_1282233 prefixEnd_1282233 438934560037724660793749 := by
  unfold tailWord_1282233
  simp only [CollatzResearch.WordTrace]
  refine ⟨46766879563696303806987353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31177919709130869204658235 46766879563696303806987353)
  ·
    refine ⟨35075159672772227855240515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46766879563696303806987353 35075159672772227855240515)
    ·
      refine ⟨52612739509158341782860773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35075159672772227855240515 52612739509158341782860773)
      ·
        refine ⟨9864888657967189084286395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52612739509158341782860773 9864888657967189084286395)
        ·
          refine ⟨14797332986950783626429593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9864888657967189084286395 14797332986950783626429593)
          ·
            refine ⟨11097999740213087719822195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14797332986950783626429593 11097999740213087719822195)
            ·
              refine ⟨16646999610319631579733293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11097999740213087719822195 16646999610319631579733293)
              ·
                refine ⟨6242624853869861842399985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16646999610319631579733293 6242624853869861842399985)
                ·
                  refine ⟨4681968640402396381799989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6242624853869861842399985 4681968640402396381799989)
                  ·
                    refine ⟨438934560037724660793749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4681968640402396381799989 438934560037724660793749)
                    ·
                      rfl

theorem cell22_1282233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 3, 2, 5].length) (baseStart_1282233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1282233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1282233 prefixEnd_1282233 := by exact prefixLift 1282233
  have htrace : WordTrace (prefixWord ++ tailWord_1282233) baseStart_1282233 baseEnd_1282233 := by
    simpa [prefixWord, tailWord_1282233, baseEnd_1282233] using wordTrace_append hprefix tailTrace_1282233
  have hstable : (prefixWord ++ tailWord_1282233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282233).length < 2 ^ (prefixWord ++ tailWord_1282233).sum := by decide
  have hdescent : baseEnd_1282233 < baseStart_1282233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282235 : List Nat := [1, 1, 1, 1, 1, 2, 9, 1, 5]
def baseStart_1282235 : Nat := 118140960795 + 1282235 * 2 ^ 59
def prefixEnd_1282235 : Nat := 4983230072969 + 3 ^ 40 * 1282235 * 2
def baseEnd_1282235 : Nat := 146311748226199107414581

theorem tailTrace_1282235 : CollatzResearch.WordTrace tailWord_1282235 prefixEnd_1282235 146311748226199107414581 := by
  unfold tailWord_1282235
  simp only [CollatzResearch.WordTrace]
  refine ⟨46766952509689058148560159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31177968339792705432373439 46766952509689058148560159)
  ·
    refine ⟨70150428764533587222840239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46766952509689058148560159 70150428764533587222840239)
    ·
      refine ⟨105225643146800380834260359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70150428764533587222840239 105225643146800380834260359)
      ·
        refine ⟨157838464720200571251390539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105225643146800380834260359 157838464720200571251390539)
        ·
          refine ⟨236757697080300856877085809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157838464720200571251390539 236757697080300856877085809)
          ·
            refine ⟨177568272810225642657814357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 236757697080300856877085809 177568272810225642657814357)
            ·
              refine ⟨1040439098497415874948131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 177568272810225642657814357 1040439098497415874948131)
              ·
                refine ⟨1560658647746123812422197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1040439098497415874948131 1560658647746123812422197)
                ·
                  refine ⟨146311748226199107414581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1560658647746123812422197 146311748226199107414581)
                  ·
                    rfl

theorem cell22_1282235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 9, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 9, 1, 5].length) (baseStart_1282235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1282235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1282235 prefixEnd_1282235 := by exact prefixLift 1282235
  have htrace : WordTrace (prefixWord ++ tailWord_1282235) baseStart_1282235 baseEnd_1282235 := by
    simpa [prefixWord, tailWord_1282235, baseEnd_1282235] using wordTrace_append hprefix tailTrace_1282235
  have hstable : (prefixWord ++ tailWord_1282235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282235).length < 2 ^ (prefixWord ++ tailWord_1282235).sum := by decide
  have hdescent : baseEnd_1282235 < baseStart_1282235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282265 : List Nat := [1, 2, 1, 2, 3, 1, 4, 3, 1, 4]
def baseStart_1282265 : Nat := 118140960795 + 1282265 * 2 ^ 59
def prefixEnd_1282265 : Nat := 4983230072969 + 3 ^ 40 * 1282265 * 2
def baseEnd_1282265 : Nat := 438945514291687243993651

theorem tailTrace_1282265 : CollatzResearch.WordTrace tailWord_1282265 prefixEnd_1282265 438945514291687243993651 := by
  unfold tailWord_1282265
  simp only [CollatzResearch.WordTrace]
  refine ⟨46768046699580373272152249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31178697799720248848101499 46768046699580373272152249)
  ·
    refine ⟨35076035024685279954114187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46768046699580373272152249 35076035024685279954114187)
    ·
      refine ⟨52614052537027919931171281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35076035024685279954114187 52614052537027919931171281)
      ·
        refine ⟨39460539402770939948378461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52614052537027919931171281 39460539402770939948378461)
        ·
          refine ⟨14797702276039102480641923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39460539402770939948378461 14797702276039102480641923)
          ·
            refine ⟨22196553414058653720962885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14797702276039102480641923 22196553414058653720962885)
            ·
              refine ⟨4161853765135997572680541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22196553414058653720962885 4161853765135997572680541)
              ·
                refine ⟨1560695161925999089755203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4161853765135997572680541 1560695161925999089755203)
                ·
                  refine ⟨2341042742888998634632805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1560695161925999089755203 2341042742888998634632805)
                  ·
                    refine ⟨438945514291687243993651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2341042742888998634632805 438945514291687243993651)
                    ·
                      rfl

theorem cell22_1282265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 3, 1, 4].length) (baseStart_1282265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1282265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1282265 prefixEnd_1282265 := by exact prefixLift 1282265
  have htrace : WordTrace (prefixWord ++ tailWord_1282265) baseStart_1282265 baseEnd_1282265 := by
    simpa [prefixWord, tailWord_1282265, baseEnd_1282265] using wordTrace_append hprefix tailTrace_1282265
  have hstable : (prefixWord ++ tailWord_1282265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282265).length < 2 ^ (prefixWord ++ tailWord_1282265).sum := by decide
  have hdescent : baseEnd_1282265 < baseStart_1282265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282280 : List Nat := [2, 1, 4, 1, 2, 2, 3, 1, 6]
def baseStart_1282280 : Nat := 118140960795 + 1282280 * 2 ^ 59
def prefixEnd_1282280 : Nat := 4983230072969 + 3 ^ 40 * 1282280 * 2
def baseEnd_1282280 : Nat := 146316883032744068289535

theorem tailTrace_1282280 : CollatzResearch.WordTrace tailWord_1282280 prefixEnd_1282280 146316883032744068289535 := by
  unfold tailWord_1282280
  simp only [CollatzResearch.WordTrace]
  refine ⟨23384296897263015416974147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31179062529684020555965529 23384296897263015416974147)
  ·
    refine ⟨35076445345894523125461221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23384296897263015416974147 35076445345894523125461221)
    ·
      refine ⟨6576833502355223086023979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35076445345894523125461221 6576833502355223086023979)
      ·
        refine ⟨9865250253532834629035969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6576833502355223086023979 9865250253532834629035969)
        ·
          refine ⟨7398937690149625971776977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9865250253532834629035969 7398937690149625971776977)
          ·
            refine ⟨5549203267612219478832733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7398937690149625971776977 5549203267612219478832733)
            ·
              refine ⟨2080951225354582304562275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5549203267612219478832733 2080951225354582304562275)
              ·
                refine ⟨3121426838031873456843413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2080951225354582304562275 3121426838031873456843413)
                ·
                  refine ⟨146316883032744068289535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3121426838031873456843413 146316883032744068289535)
                  ·
                    rfl

theorem cell22_1282280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 1, 6].length) (baseStart_1282280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1282280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1282280 prefixEnd_1282280 := by exact prefixLift 1282280
  have htrace : WordTrace (prefixWord ++ tailWord_1282280) baseStart_1282280 baseEnd_1282280 := by
    simpa [prefixWord, tailWord_1282280, baseEnd_1282280] using wordTrace_append hprefix tailTrace_1282280
  have hstable : (prefixWord ++ tailWord_1282280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282280).length < 2 ^ (prefixWord ++ tailWord_1282280).sum := by decide
  have hdescent : baseEnd_1282280 < baseStart_1282280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282357 : List Nat := [1, 3, 3, 1, 2, 1, 3, 2, 3, 3]
def baseStart_1282357 : Nat := 118140960795 + 1282357 * 2 ^ 59
def prefixEnd_1282357 : Nat := 4983230072969 + 3 ^ 40 * 1282357 * 2
def baseEnd_1282357 : Nat := 438977007771829670693369

theorem tailTrace_1282357 : CollatzResearch.WordTrace tailWord_1282357 prefixEnd_1282357 438977007771829670693369 := by
  unfold tailWord_1282357
  simp only [CollatzResearch.WordTrace]
  refine ⟨46771402215247072984501325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31180934810164715323000883 46771402215247072984501325)
  ·
    refine ⟨17539275830717652369187997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46771402215247072984501325 17539275830717652369187997)
    ·
      refine ⟨6577228436519119638445499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17539275830717652369187997 6577228436519119638445499)
      ·
        refine ⟨9865842654778679457668249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6577228436519119638445499 9865842654778679457668249)
        ·
          refine ⟨7399381991084009593251187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9865842654778679457668249 7399381991084009593251187)
          ·
            refine ⟨11099072986626014389876781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7399381991084009593251187 11099072986626014389876781)
            ·
              refine ⟨4162152369984755396203793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11099072986626014389876781 4162152369984755396203793)
              ·
                refine ⟨3121614277488566547152845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4162152369984755396203793 3121614277488566547152845)
                ·
                  refine ⟨1170605354058212455182317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3121614277488566547152845 1170605354058212455182317)
                  ·
                    refine ⟨438977007771829670693369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1170605354058212455182317 438977007771829670693369)
                    ·
                      rfl

theorem cell22_1282357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 2, 3, 3].length) (baseStart_1282357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1282357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1282357 prefixEnd_1282357 := by exact prefixLift 1282357
  have htrace : WordTrace (prefixWord ++ tailWord_1282357) baseStart_1282357 baseEnd_1282357 := by
    simpa [prefixWord, tailWord_1282357, baseEnd_1282357] using wordTrace_append hprefix tailTrace_1282357
  have hstable : (prefixWord ++ tailWord_1282357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282357).length < 2 ^ (prefixWord ++ tailWord_1282357).sum := by decide
  have hdescent : baseEnd_1282357 < baseStart_1282357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282385 : List Nat := [1, 2, 2, 1, 4, 2, 1, 2, 2, 5]
def baseStart_1282385 : Nat := 118140960795 + 1282385 * 2 ^ 59
def prefixEnd_1282385 : Nat := 4983230072969 + 3 ^ 40 * 1282385 * 2
def baseEnd_1282385 : Nat := 438986592744046930993283

theorem tailTrace_1282385 : CollatzResearch.WordTrace tailWord_1282385 prefixEnd_1282385 438986592744046930993283 := by
  unfold tailWord_1282385
  simp only [CollatzResearch.WordTrace]
  refine ⟨46772423459145633766520609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31181615639430422511013739 46772423459145633766520609)
  ·
    refine ⟨35079317594359225324890457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46772423459145633766520609 35079317594359225324890457)
    ·
      refine ⟨26309488195769418993667843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35079317594359225324890457 26309488195769418993667843)
      ·
        refine ⟨39464232293654128490501765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26309488195769418993667843 39464232293654128490501765)
        ·
          refine ⟨7399543555060149091969081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39464232293654128490501765 7399543555060149091969081)
          ·
            refine ⟨5549657666295111818976811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7399543555060149091969081 5549657666295111818976811)
            ·
              refine ⟨8324486499442667728465217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5549657666295111818976811 8324486499442667728465217)
              ·
                refine ⟨6243364874582000796348913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8324486499442667728465217 6243364874582000796348913)
                ·
                  refine ⟨4682523655936500597261685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6243364874582000796348913 4682523655936500597261685)
                  ·
                    refine ⟨438986592744046930993283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4682523655936500597261685 438986592744046930993283)
                    ·
                      rfl

theorem cell22_1282385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 2, 2, 5].length) (baseStart_1282385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1282385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1282385 prefixEnd_1282385 := by exact prefixLift 1282385
  have htrace : WordTrace (prefixWord ++ tailWord_1282385) baseStart_1282385 baseEnd_1282385 := by
    simpa [prefixWord, tailWord_1282385, baseEnd_1282385] using wordTrace_append hprefix tailTrace_1282385
  have hstable : (prefixWord ++ tailWord_1282385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282385).length < 2 ^ (prefixWord ++ tailWord_1282385).sum := by decide
  have hdescent : baseEnd_1282385 < baseStart_1282385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282402 : List Nat := [3, 3, 2, 1, 1, 2, 2, 1, 2, 5]
def baseStart_1282402 : Nat := 118140960795 + 1282402 * 2 ^ 59
def prefixEnd_1282402 : Nat := 4983230072969 + 3 ^ 40 * 1282402 * 2
def baseEnd_1282402 : Nat := 438992412191464553318231

theorem tailTrace_1282402 : CollatzResearch.WordTrace tailWord_1282402 prefixEnd_1282402 438992412191464553318231 := by
  unfold tailWord_1282402
  simp only [CollatzResearch.WordTrace]
  refine ⟨11693260875021011417472365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31182029000056030446592973 11693260875021011417472365)
  ·
    refine ⟨4384972828132879281552137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11693260875021011417472365 4384972828132879281552137)
    ·
      refine ⟨3288729621099659461164103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4384972828132879281552137 3288729621099659461164103)
      ·
        refine ⟨4933094431649489191746155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3288729621099659461164103 4933094431649489191746155)
        ·
          refine ⟨7399641647474233787619233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4933094431649489191746155 7399641647474233787619233)
          ·
            refine ⟨5549731235605675340714425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7399641647474233787619233 5549731235605675340714425)
            ·
              refine ⟨4162298426704256505535819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5549731235605675340714425 4162298426704256505535819)
              ·
                refine ⟨6243447640056384758303729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4162298426704256505535819 6243447640056384758303729)
                ·
                  refine ⟨4682585730042288568727797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6243447640056384758303729 4682585730042288568727797)
                  ·
                    refine ⟨438992412191464553318231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4682585730042288568727797 438992412191464553318231)
                    ·
                      rfl

theorem cell22_1282402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_1282402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1282402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1282402 prefixEnd_1282402 := by exact prefixLift 1282402
  have htrace : WordTrace (prefixWord ++ tailWord_1282402) baseStart_1282402 baseEnd_1282402 := by
    simpa [prefixWord, tailWord_1282402, baseEnd_1282402] using wordTrace_append hprefix tailTrace_1282402
  have hstable : (prefixWord ++ tailWord_1282402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282402).length < 2 ^ (prefixWord ++ tailWord_1282402).sum := by decide
  have hdescent : baseEnd_1282402 < baseStart_1282402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282464 : List Nat := [2, 1, 1, 4, 1, 4, 1, 3, 2, 3]
def baseStart_1282464 : Nat := 118140960795 + 1282464 * 2 ^ 59
def prefixEnd_1282464 : Nat := 4983230072969 + 3 ^ 40 * 1282464 * 2
def baseEnd_1282464 : Nat := 439013636058517058268041

theorem tailTrace_1282464 : CollatzResearch.WordTrace tailWord_1282464 prefixEnd_1282464 439013636058517058268041 := by
  unfold tailWord_1282464
  simp only [CollatzResearch.WordTrace]
  refine ⟨23387652412929715129323223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31183536550572953505764297 23387652412929715129323223)
  ·
    refine ⟨35081478619394572693984835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23387652412929715129323223 35081478619394572693984835)
    ·
      refine ⟨52622217929091859040977253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35081478619394572693984835 52622217929091859040977253)
      ·
        refine ⟨9866665861704723570183235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52622217929091859040977253 9866665861704723570183235)
        ·
          refine ⟨14799998792557085355274853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9866665861704723570183235 14799998792557085355274853)
          ·
            refine ⟨2774999773604453504114035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14799998792557085355274853 2774999773604453504114035)
            ·
              refine ⟨4162499660406680256171053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2774999773604453504114035 4162499660406680256171053)
              ·
                refine ⟨1560937372652505096064145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4162499660406680256171053 1560937372652505096064145)
                ·
                  refine ⟨1170703029489378822048109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1560937372652505096064145 1170703029489378822048109)
                  ·
                    refine ⟨439013636058517058268041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1170703029489378822048109 439013636058517058268041)
                    ·
                      rfl

theorem cell22_1282464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 3, 2, 3].length) (baseStart_1282464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1282464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1282464 prefixEnd_1282464 := by exact prefixLift 1282464
  have htrace : WordTrace (prefixWord ++ tailWord_1282464) baseStart_1282464 baseEnd_1282464 := by
    simpa [prefixWord, tailWord_1282464, baseEnd_1282464] using wordTrace_append hprefix tailTrace_1282464
  have hstable : (prefixWord ++ tailWord_1282464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282464).length < 2 ^ (prefixWord ++ tailWord_1282464).sum := by decide
  have hdescent : baseEnd_1282464 < baseStart_1282464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282490 : List Nat := [3, 1, 1, 1, 2, 1, 1, 2, 4, 6]
def baseStart_1282490 : Nat := 118140960795 + 1282490 * 2 ^ 59
def prefixEnd_1282490 : Nat := 4983230072969 + 3 ^ 40 * 1282490 * 2
def baseEnd_1282490 : Nat := 439022536389861657117961

theorem tailTrace_1282490 : CollatzResearch.WordTrace tailWord_1282490 prefixEnd_1282490 439022536389861657117961 := by
  unfold tailWord_1282490
  simp only [CollatzResearch.WordTrace]
  refine ⟨11694063280941309174773231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31184168749176824466061949 11694063280941309174773231)
  ·
    refine ⟨17541094921411963762159847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11694063280941309174773231 17541094921411963762159847)
    ·
      refine ⟨26311642382117945643239771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17541094921411963762159847 26311642382117945643239771)
      ·
        refine ⟨39467463573176918464859657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26311642382117945643239771 39467463573176918464859657)
        ·
          refine ⟨29600597679882688848644743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39467463573176918464859657 29600597679882688848644743)
          ·
            refine ⟨44400896519824033272967115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29600597679882688848644743 44400896519824033272967115)
            ·
              refine ⟨66601344779736049909450673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44400896519824033272967115 66601344779736049909450673)
              ·
                refine ⟨49951008584802037432088005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66601344779736049909450673 49951008584802037432088005)
                ·
                  refine ⟨9365814109650382018516501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49951008584802037432088005 9365814109650382018516501)
                  ·
                    refine ⟨439022536389861657117961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9365814109650382018516501 439022536389861657117961)
                    ·
                      rfl

theorem cell22_1282490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 4, 6].length) (baseStart_1282490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1282490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1282490 prefixEnd_1282490 := by exact prefixLift 1282490
  have htrace : WordTrace (prefixWord ++ tailWord_1282490) baseStart_1282490 baseEnd_1282490 := by
    simpa [prefixWord, tailWord_1282490, baseEnd_1282490] using wordTrace_append hprefix tailTrace_1282490
  have hstable : (prefixWord ++ tailWord_1282490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282490).length < 2 ^ (prefixWord ++ tailWord_1282490).sum := by decide
  have hdescent : baseEnd_1282490 < baseStart_1282490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282500 : List Nat := [2, 3, 3, 2, 3, 1, 2, 2, 4]
def baseStart_1282500 : Nat := 118140960795 + 1282500 * 2 ^ 59
def prefixEnd_1282500 : Nat := 4983230072969 + 3 ^ 40 * 1282500 * 2
def baseEnd_1282500 : Nat := 146341986531408321455977

theorem tailTrace_1282500 : CollatzResearch.WordTrace tailWord_1282500 prefixEnd_1282500 146341986531408321455977 := by
  unfold tailWord_1282500
  simp only [CollatzResearch.WordTrace]
  refine ⟨23388308926864504203478477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31184411902486005604637969 23388308926864504203478477)
  ·
    refine ⟨8770615847574189076304429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23388308926864504203478477 8770615847574189076304429)
    ·
      refine ⟨3288980942840320903614161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8770615847574189076304429 3288980942840320903614161)
      ·
        refine ⟨2466735707130240677710621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3288980942840320903614161 2466735707130240677710621)
        ·
          refine ⟨925025890173840254141483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2466735707130240677710621 925025890173840254141483)
          ·
            refine ⟨1387538835260760381212225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 925025890173840254141483 1387538835260760381212225)
            ·
              refine ⟨1040654126445570285909169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1387538835260760381212225 1040654126445570285909169)
              ·
                refine ⟨780490594834177714431877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1040654126445570285909169 780490594834177714431877)
                ·
                  refine ⟨146341986531408321455977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 780490594834177714431877 146341986531408321455977)
                  ·
                    rfl

theorem cell22_1282500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 2, 2, 4].length) (baseStart_1282500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1282500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1282500 prefixEnd_1282500 := by exact prefixLift 1282500
  have htrace : WordTrace (prefixWord ++ tailWord_1282500) baseStart_1282500 baseEnd_1282500 := by
    simpa [prefixWord, tailWord_1282500, baseEnd_1282500] using wordTrace_append hprefix tailTrace_1282500
  have hstable : (prefixWord ++ tailWord_1282500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282500).length < 2 ^ (prefixWord ++ tailWord_1282500).sum := by decide
  have hdescent : baseEnd_1282500 < baseStart_1282500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282505 : List Nat := [1, 2, 1, 1, 2, 1, 4, 3, 7]
def baseStart_1282505 : Nat := 118140960795 + 1282505 * 2 ^ 59
def prefixEnd_1282505 : Nat := 4983230072969 + 3 ^ 40 * 1282505 * 2
def baseEnd_1282505 : Nat := 146342557065468872664305

theorem tailTrace_1282505 : CollatzResearch.WordTrace tailWord_1282505 prefixEnd_1282505 146342557065468872664305 := by
  unfold tailWord_1282505
  simp only [CollatzResearch.WordTrace]
  refine ⟨46776800218710894260888969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31184533479140596173925979 46776800218710894260888969)
  ·
    refine ⟨35082600164033170695666727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46776800218710894260888969 35082600164033170695666727)
    ·
      refine ⟨52623900246049756043500091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35082600164033170695666727 52623900246049756043500091)
      ·
        refine ⟨78935850369074634065250137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52623900246049756043500091 78935850369074634065250137)
        ·
          refine ⟨59201887776805975548937603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78935850369074634065250137 59201887776805975548937603)
          ·
            refine ⟨88802831665208963323406405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59201887776805975548937603 88802831665208963323406405)
            ·
              refine ⟨16650530937226680623138701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 88802831665208963323406405 16650530937226680623138701)
              ·
                refine ⟨6243949101460005233677013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16650530937226680623138701 6243949101460005233677013)
                ·
                  refine ⟨146342557065468872664305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6243949101460005233677013 146342557065468872664305)
                  ·
                    rfl

theorem cell22_1282505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 3, 7].length) (baseStart_1282505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1282505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1282505 prefixEnd_1282505 := by exact prefixLift 1282505
  have htrace : WordTrace (prefixWord ++ tailWord_1282505) baseStart_1282505 baseEnd_1282505 := by
    simpa [prefixWord, tailWord_1282505, baseEnd_1282505] using wordTrace_append hprefix tailTrace_1282505
  have hstable : (prefixWord ++ tailWord_1282505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282505).length < 2 ^ (prefixWord ++ tailWord_1282505).sum := by decide
  have hdescent : baseEnd_1282505 < baseStart_1282505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282522 : List Nat := [3, 1, 1, 2, 3, 1, 1, 5, 5]
def baseStart_1282522 : Nat := 118140960795 + 1282522 * 2 ^ 59
def prefixEnd_1282522 : Nat := 4983230072969 + 3 ^ 40 * 1282522 * 2
def baseEnd_1282522 : Nat := 146344496881274746772621

theorem tailTrace_1282522 : CollatzResearch.WordTrace tailWord_1282522 prefixEnd_1282522 146344496881274746772621 := by
  unfold tailWord_1282522
  simp only [CollatzResearch.WordTrace]
  refine ⟨11694355064912326541064455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31184946839766204109505213 11694355064912326541064455)
  ·
    refine ⟨17541532597368489811596683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11694355064912326541064455 17541532597368489811596683)
    ·
      refine ⟨26312298896052734717395025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17541532597368489811596683 26312298896052734717395025)
      ·
        refine ⟨19734224172039551038046269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26312298896052734717395025 19734224172039551038046269)
        ·
          refine ⟨7400334064514831639267351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19734224172039551038046269 7400334064514831639267351)
          ·
            refine ⟨11100501096772247458901027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7400334064514831639267351 11100501096772247458901027)
            ·
              refine ⟨16650751645158371188351541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11100501096772247458901027 16650751645158371188351541)
              ·
                refine ⟨1561007966733597298907957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16650751645158371188351541 1561007966733597298907957)
                ·
                  refine ⟨146344496881274746772621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1561007966733597298907957 146344496881274746772621)
                  ·
                    rfl

theorem cell22_1282522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 5, 5].length) (baseStart_1282522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1282522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1282522 prefixEnd_1282522 := by exact prefixLift 1282522
  have htrace : WordTrace (prefixWord ++ tailWord_1282522) baseStart_1282522 baseEnd_1282522 := by
    simpa [prefixWord, tailWord_1282522, baseEnd_1282522] using wordTrace_append hprefix tailTrace_1282522
  have hstable : (prefixWord ++ tailWord_1282522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282522).length < 2 ^ (prefixWord ++ tailWord_1282522).sum := by decide
  have hdescent : baseEnd_1282522 < baseStart_1282522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282530 : List Nat := [3, 3, 3, 2, 2, 1, 1, 1, 2, 4]
def baseStart_1282530 : Nat := 118140960795 + 1282530 * 2 ^ 59
def prefixEnd_1282530 : Nat := 4983230072969 + 3 ^ 40 * 1282530 * 2
def baseEnd_1282530 : Nat := 439036229207314886117839

theorem tailTrace_1282530 : CollatzResearch.WordTrace tailWord_1282530 prefixEnd_1282530 439036229207314886117839 := by
  unfold tailWord_1282530
  simp only [CollatzResearch.WordTrace]
  refine ⟨11694428010905080882637261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31185141362413549020366029 11694428010905080882637261)
  ·
    refine ⟨4385410504089405330988973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11694428010905080882637261 4385410504089405330988973)
    ·
      refine ⟨1644528939033526999120865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4385410504089405330988973 1644528939033526999120865)
      ·
        refine ⟨1233396704275145249340649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1644528939033526999120865 1233396704275145249340649)
        ·
          refine ⟨925047528206358937005487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1233396704275145249340649 925047528206358937005487)
          ·
            refine ⟨1387571292309538405508231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 925047528206358937005487 1387571292309538405508231)
            ·
              refine ⟨2081356938464307608262347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1387571292309538405508231 2081356938464307608262347)
              ·
                refine ⟨3122035407696461412393521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2081356938464307608262347 3122035407696461412393521)
                ·
                  refine ⟨2341526555772346059295141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3122035407696461412393521 2341526555772346059295141)
                  ·
                    refine ⟨439036229207314886117839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2341526555772346059295141 439036229207314886117839)
                    ·
                      rfl

theorem cell22_1282530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_1282530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1282530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1282530 prefixEnd_1282530 := by exact prefixLift 1282530
  have htrace : WordTrace (prefixWord ++ tailWord_1282530) baseStart_1282530 baseEnd_1282530 := by
    simpa [prefixWord, tailWord_1282530, baseEnd_1282530] using wordTrace_append hprefix tailTrace_1282530
  have hstable : (prefixWord ++ tailWord_1282530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282530).length < 2 ^ (prefixWord ++ tailWord_1282530).sum := by decide
  have hdescent : baseEnd_1282530 < baseStart_1282530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282597 : List Nat := [1, 3, 1, 2, 2, 1, 4, 1, 1, 6]
def baseStart_1282597 : Nat := 118140960795 + 1282597 * 2 ^ 59
def prefixEnd_1282597 : Nat := 4983230072969 + 3 ^ 40 * 1282597 * 2
def baseEnd_1282597 : Nat := 439059164676549044692633

theorem tailTrace_1282597 : CollatzResearch.WordTrace tailWord_1282597 prefixEnd_1282597 439059164676549044692633 := by
  unfold tailWord_1282597
  simp only [CollatzResearch.WordTrace]
  refine ⟨46780155734377593973238045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31186770489585062648825363 46780155734377593973238045)
  ·
    refine ⟨17542558400391597739964267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46780155734377593973238045 17542558400391597739964267)
    ·
      refine ⟨26313837600587396609946401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17542558400391597739964267 26313837600587396609946401)
      ·
        refine ⟨19735378200440547457459801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26313837600587396609946401 19735378200440547457459801)
        ·
          refine ⟨14801533650330410593094851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19735378200440547457459801 14801533650330410593094851)
          ·
            refine ⟨22202300475495615889642277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14801533650330410593094851 22202300475495615889642277)
            ·
              refine ⟨4162931339155427979307927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22202300475495615889642277 4162931339155427979307927)
              ·
                refine ⟨6244397008733141968961891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4162931339155427979307927 6244397008733141968961891)
                ·
                  refine ⟨9366595513099712953442837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6244397008733141968961891 9366595513099712953442837)
                  ·
                    refine ⟨439059164676549044692633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9366595513099712953442837 439059164676549044692633)
                    ·
                      rfl

theorem cell22_1282597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 1, 1, 6].length) (baseStart_1282597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1282597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1282597 prefixEnd_1282597 := by exact prefixLift 1282597
  have htrace : WordTrace (prefixWord ++ tailWord_1282597) baseStart_1282597 baseEnd_1282597 := by
    simpa [prefixWord, tailWord_1282597, baseEnd_1282597] using wordTrace_append hprefix tailTrace_1282597
  have hstable : (prefixWord ++ tailWord_1282597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282597).length < 2 ^ (prefixWord ++ tailWord_1282597).sum := by decide
  have hdescent : baseEnd_1282597 < baseStart_1282597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282689 : List Nat := [1, 2, 4, 2, 1, 1, 3, 1, 2, 5]
def baseStart_1282689 : Nat := 118140960795 + 1282689 * 2 ^ 59
def prefixEnd_1282689 : Nat := 4983230072969 + 3 ^ 40 * 1282689 * 2
def baseEnd_1282689 : Nat := 439090658156691471392351

theorem tailTrace_1282689 : CollatzResearch.WordTrace tailWord_1282689 prefixEnd_1282689 439090658156691471392351 := by
  unfold tailWord_1282689
  simp only [CollatzResearch.WordTrace]
  refine ⟨46783511250044293685587121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31189007500029529123724747 46783511250044293685587121)
  ·
    refine ⟨35087633437533220264190341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46783511250044293685587121 35087633437533220264190341)
    ·
      refine ⟨6578931269537478799535689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35087633437533220264190341 6578931269537478799535689)
      ·
        refine ⟨4934198452153109099651767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6578931269537478799535689 4934198452153109099651767)
        ·
          refine ⟨7401297678229663649477651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4934198452153109099651767 7401297678229663649477651)
          ·
            refine ⟨11101946517344495474216477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7401297678229663649477651 11101946517344495474216477)
            ·
              refine ⟨4163229944004185802831179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11101946517344495474216477 4163229944004185802831179)
              ·
                refine ⟨6244844916006278704246769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4163229944004185802831179 6244844916006278704246769)
                ·
                  refine ⟨4683633687004709028185077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6244844916006278704246769 4683633687004709028185077)
                  ·
                    refine ⟨439090658156691471392351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4683633687004709028185077 439090658156691471392351)
                    ·
                      rfl

theorem cell22_1282689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_1282689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1282689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1282689 prefixEnd_1282689 := by exact prefixLift 1282689
  have htrace : WordTrace (prefixWord ++ tailWord_1282689) baseStart_1282689 baseEnd_1282689 := by
    simpa [prefixWord, tailWord_1282689, baseEnd_1282689] using wordTrace_append hprefix tailTrace_1282689
  have hstable : (prefixWord ++ tailWord_1282689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282689).length < 2 ^ (prefixWord ++ tailWord_1282689).sum := by decide
  have hdescent : baseEnd_1282689 < baseStart_1282689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282749 : List Nat := [1, 4, 1, 2, 1, 3, 1, 2, 1, 6]
def baseStart_1282749 : Nat := 118140960795 + 1282749 * 2 ^ 59
def prefixEnd_1282749 : Nat := 4983230072969 + 3 ^ 40 * 1282749 * 2
def baseEnd_1282749 : Nat := 439111197382871314892167

theorem tailTrace_1282749 : CollatzResearch.WordTrace tailWord_1282749 prefixEnd_1282749 439111197382871314892167 := by
  unfold tailWord_1282749
  simp only [CollatzResearch.WordTrace]
  refine ⟨46785699629826923932771301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31190466419884615955180867 46785699629826923932771301)
  ·
    refine ⟨8772318680592548237394619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46785699629826923932771301 8772318680592548237394619)
    ·
      refine ⟨13158478020888822356091929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8772318680592548237394619 13158478020888822356091929)
      ·
        refine ⟨9868858515666616767068947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13158478020888822356091929 9868858515666616767068947)
        ·
          refine ⟨14803287773499925150603421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9868858515666616767068947 14803287773499925150603421)
          ·
            refine ⟨5551232915062471931476283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14803287773499925150603421 5551232915062471931476283)
            ·
              refine ⟨8326849372593707897214425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5551232915062471931476283 8326849372593707897214425)
              ·
                refine ⟨6245137029445280922910819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8326849372593707897214425 6245137029445280922910819)
                ·
                  refine ⟨9367705544167921384366229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6245137029445280922910819 9367705544167921384366229)
                  ·
                    refine ⟨439111197382871314892167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9367705544167921384366229 439111197382871314892167)
                    ·
                      rfl

theorem cell22_1282749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 2, 1, 6].length) (baseStart_1282749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1282749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1282749 prefixEnd_1282749 := by exact prefixLift 1282749
  have htrace : WordTrace (prefixWord ++ tailWord_1282749) baseStart_1282749 baseEnd_1282749 := by
    simpa [prefixWord, tailWord_1282749, baseEnd_1282749] using wordTrace_append hprefix tailTrace_1282749
  have hstable : (prefixWord ++ tailWord_1282749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282749).length < 2 ^ (prefixWord ++ tailWord_1282749).sum := by decide
  have hdescent : baseEnd_1282749 < baseStart_1282749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282751 : List Nat := [1, 1, 2, 2, 2, 6, 1, 1, 1, 5]
def baseStart_1282751 : Nat := 118140960795 + 1282751 * 2 ^ 59
def prefixEnd_1282751 : Nat := 4983230072969 + 3 ^ 40 * 1282751 * 2
def baseEnd_1282751 : Nat := 439111882023743976342161

theorem tailTrace_1282751 : CollatzResearch.WordTrace tailWord_1282751 prefixEnd_1282751 439111882023743976342161 := by
  unfold tailWord_1282751
  simp only [CollatzResearch.WordTrace]
  refine ⟨46785772575819678274344107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31190515050546452182896071 46785772575819678274344107)
  ·
    refine ⟨70178658863729517411516161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46785772575819678274344107 70178658863729517411516161)
    ·
      refine ⟨52633994147797138058637121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70178658863729517411516161 52633994147797138058637121)
      ·
        refine ⟨39475495610847853543977841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52633994147797138058637121 39475495610847853543977841)
        ·
          refine ⟨29606621708135890157983381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39475495610847853543977841 29606621708135890157983381)
          ·
            refine ⟨1387810392568869851155471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 29606621708135890157983381 1387810392568869851155471)
            ·
              refine ⟨2081715588853304776733207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1387810392568869851155471 2081715588853304776733207)
              ·
                refine ⟨3122573383279957165099811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2081715588853304776733207 3122573383279957165099811)
                ·
                  refine ⟨4683860074919935747649717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3122573383279957165099811 4683860074919935747649717)
                  ·
                    refine ⟨439111882023743976342161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4683860074919935747649717 439111882023743976342161)
                    ·
                      rfl

theorem cell22_1282751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 1, 1, 5].length) (baseStart_1282751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1282751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1282751 prefixEnd_1282751 := by exact prefixLift 1282751
  have htrace : WordTrace (prefixWord ++ tailWord_1282751) baseStart_1282751 baseEnd_1282751 := by
    simpa [prefixWord, tailWord_1282751, baseEnd_1282751] using wordTrace_append hprefix tailTrace_1282751
  have hstable : (prefixWord ++ tailWord_1282751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282751).length < 2 ^ (prefixWord ++ tailWord_1282751).sum := by decide
  have hdescent : baseEnd_1282751 < baseStart_1282751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282770 : List Nat := [3, 2, 2, 2, 3, 2, 1, 3, 4]
def baseStart_1282770 : Nat := 118140960795 + 1282770 * 2 ^ 59
def prefixEnd_1282770 : Nat := 4983230072969 + 3 ^ 40 * 1282770 * 2
def baseEnd_1282770 : Nat := 146372795370678086705701

theorem tailTrace_1282770 : CollatzResearch.WordTrace tailWord_1282770 prefixEnd_1282770 146372795370678086705701 := by
  unfold tailWord_1282770
  simp only [CollatzResearch.WordTrace]
  refine ⟨11696616390687711129821441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31190977041833896346190509 11696616390687711129821441)
  ·
    refine ⟨8772462293015783347366081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11696616390687711129821441 8772462293015783347366081)
    ·
      refine ⟨6579346719761837510524561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8772462293015783347366081 6579346719761837510524561)
      ·
        refine ⟨4934510039821378132893421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6579346719761837510524561 4934510039821378132893421)
        ·
          refine ⟨1850441264933016799835033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4934510039821378132893421 1850441264933016799835033)
          ·
            refine ⟨1387830948699762599876275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1850441264933016799835033 1387830948699762599876275)
            ·
              refine ⟨2081746423049643899814413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1387830948699762599876275 2081746423049643899814413)
              ·
                refine ⟨780654908643616462430405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2081746423049643899814413 780654908643616462430405)
                ·
                  refine ⟨146372795370678086705701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 780654908643616462430405 146372795370678086705701)
                  ·
                    rfl

theorem cell22_1282770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 3, 4].length) (baseStart_1282770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1282770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1282770 prefixEnd_1282770 := by exact prefixLift 1282770
  have htrace : WordTrace (prefixWord ++ tailWord_1282770) baseStart_1282770 baseEnd_1282770 := by
    simpa [prefixWord, tailWord_1282770, baseEnd_1282770] using wordTrace_append hprefix tailTrace_1282770
  have hstable : (prefixWord ++ tailWord_1282770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282770).length < 2 ^ (prefixWord ++ tailWord_1282770).sum := by decide
  have hdescent : baseEnd_1282770 < baseStart_1282770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282794 : List Nat := [3, 1, 3, 1, 1, 1, 1, 3, 2, 6]
def baseStart_1282794 : Nat := 118140960795 + 1282794 * 2 ^ 59
def prefixEnd_1282794 : Nat := 4983230072969 + 3 ^ 40 * 1282794 * 2
def baseEnd_1282794 : Nat := 439126601802506197517029

theorem tailTrace_1282794 : CollatzResearch.WordTrace tailWord_1282794 prefixEnd_1282794 439126601802506197517029 := by
  unfold tailWord_1282794
  simp only [CollatzResearch.WordTrace]
  refine ⟨11696835228665974154539859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31191560609775931078772957 11696835228665974154539859)
  ·
    refine ⟨17545252842998961231809789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11696835228665974154539859 17545252842998961231809789)
    ·
      refine ⟨6579469816124610461928671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17545252842998961231809789 6579469816124610461928671)
      ·
        refine ⟨9869204724186915692893007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6579469816124610461928671 9869204724186915692893007)
        ·
          refine ⟨14803807086280373539339511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9869204724186915692893007 14803807086280373539339511)
          ·
            refine ⟨22205710629420560309009267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14803807086280373539339511 22205710629420560309009267)
            ·
              refine ⟨33308565944130840463513901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22205710629420560309009267 33308565944130840463513901)
              ·
                refine ⟨12490712229049065173817713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33308565944130840463513901 12490712229049065173817713)
                ·
                  refine ⟨9368034171786798880363285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12490712229049065173817713 9368034171786798880363285)
                  ·
                    refine ⟨439126601802506197517029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9368034171786798880363285 439126601802506197517029)
                    ·
                      rfl

theorem cell22_1282794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_1282794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1282794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1282794 prefixEnd_1282794 := by exact prefixLift 1282794
  have htrace : WordTrace (prefixWord ++ tailWord_1282794) baseStart_1282794 baseEnd_1282794 := by
    simpa [prefixWord, tailWord_1282794, baseEnd_1282794] using wordTrace_append hprefix tailTrace_1282794
  have hstable : (prefixWord ++ tailWord_1282794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282794).length < 2 ^ (prefixWord ++ tailWord_1282794).sum := by decide
  have hdescent : baseEnd_1282794 < baseStart_1282794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282847 : List Nat := [1, 1, 2, 4, 2, 4, 2, 2, 1, 3]
def baseStart_1282847 : Nat := 118140960795 + 1282847 * 2 ^ 59
def prefixEnd_1282847 : Nat := 4983230072969 + 3 ^ 40 * 1282847 * 2
def baseEnd_1282847 : Nat := 439144744785631725941867

theorem tailTrace_1282847 : CollatzResearch.WordTrace tailWord_1282847 prefixEnd_1282847 439144744785631725941867 := by
  unfold tailWord_1282847
  simp only [CollatzResearch.WordTrace]
  refine ⟨46789273983471886669838795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31192849322314591113225863 46789273983471886669838795)
  ·
    refine ⟨70183910975207830004758193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46789273983471886669838795 70183910975207830004758193)
    ·
      refine ⟨52637933231405872503568645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70183910975207830004758193 52637933231405872503568645)
      ·
        refine ⟨9869612480888601094419121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52637933231405872503568645 9869612480888601094419121)
        ·
          refine ⟨7402209360666450820814341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9869612480888601094419121 7402209360666450820814341)
          ·
            refine ⟨1387914255124959528902689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7402209360666450820814341 1387914255124959528902689)
            ·
              refine ⟨1040935691343719646677017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1387914255124959528902689 1040935691343719646677017)
              ·
                refine ⟨780701768507789735007763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1040935691343719646677017 780701768507789735007763)
                ·
                  refine ⟨1171052652761684602511645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 780701768507789735007763 1171052652761684602511645)
                  ·
                    refine ⟨439144744785631725941867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1171052652761684602511645 439144744785631725941867)
                    ·
                      rfl

theorem cell22_1282847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 2, 2, 1, 3].length) (baseStart_1282847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1282847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1282847 prefixEnd_1282847 := by exact prefixLift 1282847
  have htrace : WordTrace (prefixWord ++ tailWord_1282847) baseStart_1282847 baseEnd_1282847 := by
    simpa [prefixWord, tailWord_1282847, baseEnd_1282847] using wordTrace_append hprefix tailTrace_1282847
  have hstable : (prefixWord ++ tailWord_1282847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282847).length < 2 ^ (prefixWord ++ tailWord_1282847).sum := by decide
  have hdescent : baseEnd_1282847 < baseStart_1282847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282856 : List Nat := [2, 1, 5, 1, 1, 1, 1, 1, 5, 4]
def baseStart_1282856 : Nat := 118140960795 + 1282856 * 2 ^ 59
def prefixEnd_1282856 : Nat := 4983230072969 + 3 ^ 40 * 1282856 * 2
def baseEnd_1282856 : Nat := 439147825669558702466839

theorem tailTrace_1282856 : CollatzResearch.WordTrace tailWord_1282856 prefixEnd_1282856 439147825669558702466839 := by
  unfold tailWord_1282856
  simp only [CollatzResearch.WordTrace]
  refine ⟨23394801120219640603458211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31193068160292854137944281 23394801120219640603458211)
  ·
    refine ⟨35092201680329460905187317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23394801120219640603458211 35092201680329460905187317)
    ·
      refine ⟨3289893907530886959861311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35092201680329460905187317 3289893907530886959861311)
      ·
        refine ⟨4934840861296330439791967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3289893907530886959861311 4934840861296330439791967)
        ·
          refine ⟨7402261291944495659687951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4934840861296330439791967 7402261291944495659687951)
          ·
            refine ⟨11103391937916743489531927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7402261291944495659687951 11103391937916743489531927)
            ·
              refine ⟨16655087906875115234297891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11103391937916743489531927 16655087906875115234297891)
              ·
                refine ⟨24982631860312672851446837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16655087906875115234297891 24982631860312672851446837)
                ·
                  refine ⟨2342121736904313079823141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24982631860312672851446837 2342121736904313079823141)
                  ·
                    refine ⟨439147825669558702466839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2342121736904313079823141 439147825669558702466839)
                    ·
                      rfl

theorem cell22_1282856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_1282856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1282856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1282856 prefixEnd_1282856 := by exact prefixLift 1282856
  have htrace : WordTrace (prefixWord ++ tailWord_1282856) baseStart_1282856 baseEnd_1282856 := by
    simpa [prefixWord, tailWord_1282856, baseEnd_1282856] using wordTrace_append hprefix tailTrace_1282856
  have hstable : (prefixWord ++ tailWord_1282856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282856).length < 2 ^ (prefixWord ++ tailWord_1282856).sum := by decide
  have hdescent : baseEnd_1282856 < baseStart_1282856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282888 : List Nat := [2, 1, 3, 1, 1, 3, 4, 3, 4]
def baseStart_1282888 : Nat := 118140960795 + 1282888 * 2 ^ 59
def prefixEnd_1282888 : Nat := 4983230072969 + 3 ^ 40 * 1282888 * 2
def baseEnd_1282888 : Nat := 146386259974507095222247

theorem tailTrace_1282888 : CollatzResearch.WordTrace tailWord_1282888 prefixEnd_1282888 146386259974507095222247 := by
  unfold tailWord_1282888
  simp only [CollatzResearch.WordTrace]
  refine ⟨23395384688161675336040659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31193846250882233781387545 23395384688161675336040659)
  ·
    refine ⟨35093077032242513004060989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23395384688161675336040659 35093077032242513004060989)
    ·
      refine ⟨13159903887090942376522871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35093077032242513004060989 13159903887090942376522871)
      ·
        refine ⟨19739855830636413564784307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13159903887090942376522871 19739855830636413564784307)
        ·
          refine ⟨29609783745954620347176461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19739855830636413564784307 29609783745954620347176461)
          ·
            refine ⟨11103668904732982630191173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29609783745954620347176461 11103668904732982630191173)
            ·
              refine ⟨2081937919637434243160845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11103668904732982630191173 2081937919637434243160845)
              ·
                refine ⟨780726719864037841185317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2081937919637434243160845 780726719864037841185317)
                ·
                  refine ⟨146386259974507095222247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 780726719864037841185317 146386259974507095222247)
                  ·
                    rfl

theorem cell22_1282888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 3, 4].length) (baseStart_1282888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1282888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1282888 prefixEnd_1282888 := by exact prefixLift 1282888
  have htrace : WordTrace (prefixWord ++ tailWord_1282888) baseStart_1282888 baseEnd_1282888 := by
    simpa [prefixWord, tailWord_1282888, baseEnd_1282888] using wordTrace_append hprefix tailTrace_1282888
  have hstable : (prefixWord ++ tailWord_1282888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282888).length < 2 ^ (prefixWord ++ tailWord_1282888).sum := by decide
  have hdescent : baseEnd_1282888 < baseStart_1282888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282901 : List Nat := [1, 3, 2, 2, 2, 1, 2, 1, 4, 4]
def baseStart_1282901 : Nat := 118140960795 + 1282901 * 2 ^ 59
def prefixEnd_1282901 : Nat := 4983230072969 + 3 ^ 40 * 1282901 * 2
def baseEnd_1282901 : Nat := 439163230089193585091701

theorem tailTrace_1282901 : CollatzResearch.WordTrace tailWord_1282901 prefixEnd_1282901 439163230089193585091701 := by
  unfold tailWord_1282901
  simp only [CollatzResearch.WordTrace]
  refine ⟨46791243525276253892304557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31194162350184169261536371 46791243525276253892304557)
  ·
    refine ⟨17546716321978595209614209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46791243525276253892304557 17546716321978595209614209)
    ·
      refine ⟨13160037241483946407210657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17546716321978595209614209 13160037241483946407210657)
      ·
        refine ⟨9870027931112959805407993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13160037241483946407210657 9870027931112959805407993)
        ·
          refine ⟨7402520948334719854055995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9870027931112959805407993 7402520948334719854055995)
          ·
            refine ⟨11103781422502079781083993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7402520948334719854055995 11103781422502079781083993)
            ·
              refine ⟨8327836066876559835812995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11103781422502079781083993 8327836066876559835812995)
              ·
                refine ⟨12491754100314839753719493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8327836066876559835812995 12491754100314839753719493)
                ·
                  refine ⟨2342203893809032453822405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12491754100314839753719493 2342203893809032453822405)
                  ·
                    refine ⟨439163230089193585091701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2342203893809032453822405 439163230089193585091701)
                    ·
                      rfl

theorem cell22_1282901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 4, 4].length) (baseStart_1282901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1282901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1282901 prefixEnd_1282901 := by exact prefixLift 1282901
  have htrace : WordTrace (prefixWord ++ tailWord_1282901) baseStart_1282901 baseEnd_1282901 := by
    simpa [prefixWord, tailWord_1282901, baseEnd_1282901] using wordTrace_append hprefix tailTrace_1282901
  have hstable : (prefixWord ++ tailWord_1282901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282901).length < 2 ^ (prefixWord ++ tailWord_1282901).sum := by decide
  have hdescent : baseEnd_1282901 < baseStart_1282901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282903 : List Nat := [1, 1, 3, 2, 4, 2, 1, 1, 4, 3]
def baseStart_1282903 : Nat := 118140960795 + 1282903 * 2 ^ 59
def prefixEnd_1282903 : Nat := 4983230072969 + 3 ^ 40 * 1282903 * 2
def baseEnd_1282903 : Nat := 439163914730066246541695

theorem tailTrace_1282903 : CollatzResearch.WordTrace tailWord_1282903 prefixEnd_1282903 439163914730066246541695 := by
  unfold tailWord_1282903
  simp only [CollatzResearch.WordTrace]
  refine ⟨46791316471269008233877363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31194210980846005489251575 46791316471269008233877363)
  ·
    refine ⟨70186974706903512350816045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46791316471269008233877363 70186974706903512350816045)
    ·
      refine ⟨26320115515088817131556017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70186974706903512350816045 26320115515088817131556017)
      ·
        refine ⟨19740086636316612848667013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26320115515088817131556017 19740086636316612848667013)
        ·
          refine ⟨3701266244309364909125065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19740086636316612848667013 3701266244309364909125065)
          ·
            refine ⟨2775949683232023681843799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3701266244309364909125065 2775949683232023681843799)
            ·
              refine ⟨4163924524848035522765699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2775949683232023681843799 4163924524848035522765699)
              ·
                refine ⟨6245886787272053284148549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4163924524848035522765699 6245886787272053284148549)
                ·
                  refine ⟨1171103772613509990777853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6245886787272053284148549 1171103772613509990777853)
                  ·
                    refine ⟨439163914730066246541695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1171103772613509990777853 439163914730066246541695)
                    ·
                      rfl

theorem cell22_1282903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 1, 4, 3].length) (baseStart_1282903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1282903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1282903 prefixEnd_1282903 := by exact prefixLift 1282903
  have htrace : WordTrace (prefixWord ++ tailWord_1282903) baseStart_1282903 baseEnd_1282903 := by
    simpa [prefixWord, tailWord_1282903, baseEnd_1282903] using wordTrace_append hprefix tailTrace_1282903
  have hstable : (prefixWord ++ tailWord_1282903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282903).length < 2 ^ (prefixWord ++ tailWord_1282903).sum := by decide
  have hdescent : baseEnd_1282903 < baseStart_1282903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282933 : List Nat := [1, 3, 4, 1, 1, 2, 4, 6]
def baseStart_1282933 : Nat := 118140960795 + 1282933 * 2 ^ 59
def prefixEnd_1282933 : Nat := 4983230072969 + 3 ^ 40 * 1282933 * 2
def baseEnd_1282933 : Nat := 48797131593684018699067

theorem tailTrace_1282933 : CollatzResearch.WordTrace tailWord_1282933 prefixEnd_1282933 48797131593684018699067 := by
  unfold tailWord_1282933
  simp only [CollatzResearch.WordTrace]
  refine ⟨46792410661160323357469453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31194940440773548904979635 46792410661160323357469453)
  ·
    refine ⟨17547153997935121259051045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46792410661160323357469453 17547153997935121259051045)
    ·
      refine ⟨3290091374612835236072071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17547153997935121259051045 3290091374612835236072071)
      ·
        refine ⟨4935137061919252854108107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3290091374612835236072071 4935137061919252854108107)
        ·
          refine ⟨7402705592878879281162161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4935137061919252854108107 7402705592878879281162161)
          ·
            refine ⟨5552029194659159460871621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7402705592878879281162161 5552029194659159460871621)
            ·
              refine ⟨1041005473998592398913429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5552029194659159460871621 1041005473998592398913429)
              ·
                refine ⟨48797131593684018699067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1041005473998592398913429 48797131593684018699067)
                ·
                  rfl

theorem cell22_1282933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 4, 6].length) (baseStart_1282933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1282933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1282933 prefixEnd_1282933 := by exact prefixLift 1282933
  have htrace : WordTrace (prefixWord ++ tailWord_1282933) baseStart_1282933 baseEnd_1282933 := by
    simpa [prefixWord, tailWord_1282933, baseEnd_1282933] using wordTrace_append hprefix tailTrace_1282933
  have hstable : (prefixWord ++ tailWord_1282933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282933).length < 2 ^ (prefixWord ++ tailWord_1282933).sum := by decide
  have hdescent : baseEnd_1282933 < baseStart_1282933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282961 : List Nat := [1, 2, 2, 1, 1, 1, 3, 6, 5]
def baseStart_1282961 : Nat := 118140960795 + 1282961 * 2 ^ 59
def prefixEnd_1282961 : Nat := 4983230072969 + 3 ^ 40 * 1282961 * 2
def baseEnd_1282961 : Nat := 146394589771791142863839

theorem tailTrace_1282961 : CollatzResearch.WordTrace tailWord_1282961 prefixEnd_1282961 146394589771791142863839 := by
  unfold tailWord_1282961
  simp only [CollatzResearch.WordTrace]
  refine ⟨46793431905058884139488737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31195621270039256092992491 46793431905058884139488737)
  ·
    refine ⟨35095073928794163104616553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46793431905058884139488737 35095073928794163104616553)
    ·
      refine ⟨26321305446595622328462415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35095073928794163104616553 26321305446595622328462415)
      ·
        refine ⟨39481958169893433492693623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26321305446595622328462415 39481958169893433492693623)
        ·
          refine ⟨59222937254840150239040435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39481958169893433492693623 59222937254840150239040435)
          ·
            refine ⟨88834405882260225358560653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59222937254840150239040435 88834405882260225358560653)
            ·
              refine ⟨33312902205847584509460245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88834405882260225358560653 33312902205847584509460245)
              ·
                refine ⟨1561542290899105523880949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 33312902205847584509460245 1561542290899105523880949)
                ·
                  refine ⟨146394589771791142863839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1561542290899105523880949 146394589771791142863839)
                  ·
                    rfl

theorem cell22_1282961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 6, 5].length) (baseStart_1282961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1282961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1282961 prefixEnd_1282961 := by exact prefixLift 1282961
  have htrace : WordTrace (prefixWord ++ tailWord_1282961) baseStart_1282961 baseEnd_1282961 := by
    simpa [prefixWord, tailWord_1282961, baseEnd_1282961] using wordTrace_append hprefix tailTrace_1282961
  have hstable : (prefixWord ++ tailWord_1282961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282961).length < 2 ^ (prefixWord ++ tailWord_1282961).sum := by decide
  have hdescent : baseEnd_1282961 < baseStart_1282961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282965 : List Nat := [1, 3, 2, 1, 1, 6, 1, 1, 3, 3]
def baseStart_1282965 : Nat := 118140960795 + 1282965 * 2 ^ 59
def prefixEnd_1282965 : Nat := 4983230072969 + 3 ^ 40 * 1282965 * 2
def baseEnd_1282965 : Nat := 439185138597118751491505

theorem tailTrace_1282965 : CollatzResearch.WordTrace tailWord_1282965 prefixEnd_1282965 439185138597118751491505 := by
  unfold tailWord_1282965
  simp only [CollatzResearch.WordTrace]
  refine ⟨46793577797044392822634349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31195718531362928548422899 46793577797044392822634349)
  ·
    refine ⟨17547591673891647308487881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46793577797044392822634349 17547591673891647308487881)
    ·
      refine ⟨13160693755418735481365911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17547591673891647308487881 13160693755418735481365911)
      ·
        refine ⟨19741040633128103222048867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13160693755418735481365911 19741040633128103222048867)
        ·
          refine ⟨29611560949692154833073301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19741040633128103222048867 29611560949692154833073301)
          ·
            refine ⟨1388041919516819757800311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 29611560949692154833073301 1388041919516819757800311)
            ·
              refine ⟨2082062879275229636700467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1388041919516819757800311 2082062879275229636700467)
              ·
                refine ⟨3123094318912844455050701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2082062879275229636700467 3123094318912844455050701)
                ·
                  refine ⟨1171160369592316670644013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3123094318912844455050701 1171160369592316670644013)
                  ·
                    refine ⟨439185138597118751491505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1171160369592316670644013 439185138597118751491505)
                    ·
                      rfl

theorem cell22_1282965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 1, 3, 3].length) (baseStart_1282965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1282965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1282965 prefixEnd_1282965 := by exact prefixLift 1282965
  have htrace : WordTrace (prefixWord ++ tailWord_1282965) baseStart_1282965 baseEnd_1282965 := by
    simpa [prefixWord, tailWord_1282965, baseEnd_1282965] using wordTrace_append hprefix tailTrace_1282965
  have hstable : (prefixWord ++ tailWord_1282965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282965).length < 2 ^ (prefixWord ++ tailWord_1282965).sum := by decide
  have hdescent : baseEnd_1282965 < baseStart_1282965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1282976 : List Nat := [2, 1, 1, 4, 1, 1, 2, 3, 2, 5]
def baseStart_1282976 : Nat := 118140960795 + 1282976 * 2 ^ 59
def prefixEnd_1282976 : Nat := 4983230072969 + 3 ^ 40 * 1282976 * 2
def baseEnd_1282976 : Nat := 439188904121918389466471

theorem tailTrace_1282976 : CollatzResearch.WordTrace tailWord_1282976 prefixEnd_1282976 439188904121918389466471 := by
  unfold tailWord_1282976
  simp only [CollatzResearch.WordTrace]
  refine ⟨23396989500002270850642391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31195986000003027800856521 23396989500002270850642391)
  ·
    refine ⟨35095484250003406275963587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23396989500002270850642391 35095484250003406275963587)
    ·
      refine ⟨52643226375005109413945381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35095484250003406275963587 52643226375005109413945381)
      ·
        refine ⟨9870604945313458015114759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52643226375005109413945381 9870604945313458015114759)
        ·
          refine ⟨14805907417970187022672139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9870604945313458015114759 14805907417970187022672139)
          ·
            refine ⟨22208861126955280534008209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14805907417970187022672139 22208861126955280534008209)
            ·
              refine ⟨16656645845216460400506157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22208861126955280534008209 16656645845216460400506157)
              ·
                refine ⟨6246242191956172650189809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16656645845216460400506157 6246242191956172650189809)
                ·
                  refine ⟨4684681643967129487642357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6246242191956172650189809 4684681643967129487642357)
                  ·
                    refine ⟨439188904121918389466471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4684681643967129487642357 439188904121918389466471)
                    ·
                      rfl

theorem cell22_1282976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 3, 2, 5].length) (baseStart_1282976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1282976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1282976 prefixEnd_1282976 := by exact prefixLift 1282976
  have htrace : WordTrace (prefixWord ++ tailWord_1282976) baseStart_1282976 baseEnd_1282976 := by
    simpa [prefixWord, tailWord_1282976, baseEnd_1282976] using wordTrace_append hprefix tailTrace_1282976
  have hstable : (prefixWord ++ tailWord_1282976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1282976).length < 2 ^ (prefixWord ++ tailWord_1282976).sum := by decide
  have hdescent : baseEnd_1282976 < baseStart_1282976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1282976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283012 : List Nat := [2, 3, 3, 3, 1, 1, 2, 2, 5]
def baseStart_1283012 : Nat := 118140960795 + 1283012 * 2 ^ 59
def prefixEnd_1283012 : Nat := 4983230072969 + 3 ^ 40 * 1283012 * 2
def baseEnd_1283012 : Nat := 146400409219208765188787

theorem tailTrace_1283012 : CollatzResearch.WordTrace tailWord_1283012 prefixEnd_1283012 146400409219208765188787 := by
  unfold tailWord_1283012
  simp only [CollatzResearch.WordTrace]
  refine ⟨23397646013937059924797645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31196861351916079899730193 23397646013937059924797645)
  ·
    refine ⟨8774117255226397471799117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23397646013937059924797645 8774117255226397471799117)
    ·
      refine ⟨3290293970709899051924669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8774117255226397471799117 3290293970709899051924669)
      ·
        refine ⟨1233860239016212144471751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3290293970709899051924669 1233860239016212144471751)
        ·
          refine ⟨1850790358524318216707627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1233860239016212144471751 1850790358524318216707627)
          ·
            refine ⟨2776185537786477325061441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1850790358524318216707627 2776185537786477325061441)
            ·
              refine ⟨2082139153339857993796081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2776185537786477325061441 2082139153339857993796081)
              ·
                refine ⟨1561604365004893495347061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2082139153339857993796081 1561604365004893495347061)
                ·
                  refine ⟨146400409219208765188787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1561604365004893495347061 146400409219208765188787)
                  ·
                    rfl

theorem cell22_1283012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 2, 5].length) (baseStart_1283012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1283012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1283012 prefixEnd_1283012 := by exact prefixLift 1283012
  have htrace : WordTrace (prefixWord ++ tailWord_1283012) baseStart_1283012 baseEnd_1283012 := by
    simpa [prefixWord, tailWord_1283012, baseEnd_1283012] using wordTrace_append hprefix tailTrace_1283012
  have hstable : (prefixWord ++ tailWord_1283012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283012).length < 2 ^ (prefixWord ++ tailWord_1283012).sum := by decide
  have hdescent : baseEnd_1283012 < baseStart_1283012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283016 : List Nat := [2, 1, 3, 1, 6, 1, 2, 2, 1, 3]
def baseStart_1283016 : Nat := 118140960795 + 1283016 * 2 ^ 59
def prefixEnd_1283016 : Nat := 4983230072969 + 3 ^ 40 * 1283016 * 2
def baseEnd_1283016 : Nat := 439202596939371618466349

theorem tailTrace_1283016 : CollatzResearch.WordTrace tailWord_1283016 prefixEnd_1283016 439202596939371618466349 := by
  unfold tailWord_1283016
  simp only [CollatzResearch.WordTrace]
  refine ⟨23397718959929814266370451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31196958613239752355160601 23397718959929814266370451)
  ·
    refine ⟨35096578439894721399555677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23397718959929814266370451 35096578439894721399555677)
    ·
      refine ⟨13161216914960520524833379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35096578439894721399555677 13161216914960520524833379)
      ·
        refine ⟨19741825372440780787250069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13161216914960520524833379 19741825372440780787250069)
        ·
          refine ⟨925398064333161599402347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 19741825372440780787250069 925398064333161599402347)
          ·
            refine ⟨1388097096499742399103521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 925398064333161599402347 1388097096499742399103521)
            ·
              refine ⟨1041072822374806799327641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1388097096499742399103521 1041072822374806799327641)
              ·
                refine ⟨780804616781105099495731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1041072822374806799327641 780804616781105099495731)
                ·
                  refine ⟨1171206925171657649243597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 780804616781105099495731 1171206925171657649243597)
                  ·
                    refine ⟨439202596939371618466349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1171206925171657649243597 439202596939371618466349)
                    ·
                      rfl

theorem cell22_1283016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 2, 2, 1, 3].length) (baseStart_1283016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1283016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1283016 prefixEnd_1283016 := by exact prefixLift 1283016
  have htrace : WordTrace (prefixWord ++ tailWord_1283016) baseStart_1283016 baseEnd_1283016 := by
    simpa [prefixWord, tailWord_1283016, baseEnd_1283016] using wordTrace_append hprefix tailTrace_1283016
  have hstable : (prefixWord ++ tailWord_1283016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283016).length < 2 ^ (prefixWord ++ tailWord_1283016).sum := by decide
  have hdescent : baseEnd_1283016 < baseStart_1283016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283066 : List Nat := [3, 1, 1, 1, 1, 2, 1, 2, 1, 9]
def baseStart_1283066 : Nat := 118140960795 + 1283066 * 2 ^ 59
def prefixEnd_1283066 : Nat := 4983230072969 + 3 ^ 40 * 1283066 * 2
def baseEnd_1283066 : Nat := 439219712961188154716195

theorem tailTrace_1283066 : CollatzResearch.WordTrace tailWord_1283066 prefixEnd_1283066 439219712961188154716195 := by
  unfold tailWord_1283066
  simp only [CollatzResearch.WordTrace]
  refine ⟨11699315392419621768015263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31198174379785658048040701 11699315392419621768015263)
  ·
    refine ⟨17548973088629432652022895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11699315392419621768015263 17548973088629432652022895)
    ·
      refine ⟨26323459632944148978034343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17548973088629432652022895 26323459632944148978034343)
      ·
        refine ⟨39485189449416223467051515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26323459632944148978034343 39485189449416223467051515)
        ·
          refine ⟨59227784174124335200577273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39485189449416223467051515 59227784174124335200577273)
          ·
            refine ⟨44420838130593251400432955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59227784174124335200577273 44420838130593251400432955)
            ·
              refine ⟨66631257195889877100649433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44420838130593251400432955 66631257195889877100649433)
              ·
                refine ⟨49973442896917407825487075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66631257195889877100649433 49973442896917407825487075)
                ·
                  refine ⟨74960164345376111738230613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49973442896917407825487075 74960164345376111738230613)
                  ·
                    refine ⟨439219712961188154716195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 74960164345376111738230613 439219712961188154716195)
                    ·
                      rfl

theorem cell22_1283066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 1, 9].length) (baseStart_1283066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1283066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1283066 prefixEnd_1283066 := by exact prefixLift 1283066
  have htrace : WordTrace (prefixWord ++ tailWord_1283066) baseStart_1283066 baseEnd_1283066 := by
    simpa [prefixWord, tailWord_1283066, baseEnd_1283066] using wordTrace_append hprefix tailTrace_1283066
  have hstable : (prefixWord ++ tailWord_1283066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283066).length < 2 ^ (prefixWord ++ tailWord_1283066).sum := by decide
  have hdescent : baseEnd_1283066 < baseStart_1283066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283081 : List Nat := [1, 2, 1, 1, 3, 1, 1, 3, 1, 8]
def baseStart_1283081 : Nat := 118140960795 + 1283081 * 2 ^ 59
def prefixEnd_1283081 : Nat := 4983230072969 + 3 ^ 40 * 1283081 * 2
def baseEnd_1283081 : Nat := 439224847767733115591149

theorem tailTrace_1283081 : CollatzResearch.WordTrace tailWord_1283081 prefixEnd_1283081 439224847767733115591149 := by
  unfold tailWord_1283081
  simp only [CollatzResearch.WordTrace]
  refine ⟨46797808664624144633857097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31198539109749429755904731 46797808664624144633857097)
  ·
    refine ⟨35098356498468108475392823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46797808664624144633857097 35098356498468108475392823)
    ·
      refine ⟨52647534747702162713089235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35098356498468108475392823 52647534747702162713089235)
      ·
        refine ⟨78971302121553244069633853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52647534747702162713089235 78971302121553244069633853)
        ·
          refine ⟨29614238295582466526112695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78971302121553244069633853 29614238295582466526112695)
          ·
            refine ⟨44421357443373699789169043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29614238295582466526112695 44421357443373699789169043)
            ·
              refine ⟨66632036165060549683753565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44421357443373699789169043 66632036165060549683753565)
              ·
                refine ⟨24987013561897706131407587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66632036165060549683753565 24987013561897706131407587)
                ·
                  refine ⟨37480520342846559197111381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24987013561897706131407587 37480520342846559197111381)
                  ·
                    refine ⟨439224847767733115591149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 37480520342846559197111381 439224847767733115591149)
                    ·
                      rfl

theorem cell22_1283081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 8].length) (baseStart_1283081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1283081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1283081 prefixEnd_1283081 := by exact prefixLift 1283081
  have htrace : WordTrace (prefixWord ++ tailWord_1283081) baseStart_1283081 baseEnd_1283081 := by
    simpa [prefixWord, tailWord_1283081, baseEnd_1283081] using wordTrace_append hprefix tailTrace_1283081
  have hstable : (prefixWord ++ tailWord_1283081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283081).length < 2 ^ (prefixWord ++ tailWord_1283081).sum := by decide
  have hdescent : baseEnd_1283081 < baseStart_1283081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283134 : List Nat := [4, 2, 1, 3, 1, 3, 1, 1, 3, 3]
def baseStart_1283134 : Nat := 118140960795 + 1283134 * 2 ^ 59
def prefixEnd_1283134 : Nat := 4983230072969 + 3 ^ 40 * 1283134 * 2
def baseEnd_1283134 : Nat := 439242990750858644015987

theorem tailTrace_1283134 : CollatzResearch.WordTrace tailWord_1283134 prefixEnd_1283134 439242990750858644015987 := by
  unfold tailWord_1283134
  simp only [CollatzResearch.WordTrace]
  refine ⟨5849967716679016835692057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31199827822288089790357637 5849967716679016835692057)
  ·
    refine ⟨4387475787509262626769043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5849967716679016835692057 4387475787509262626769043)
    ·
      refine ⟨6581213681263893940153565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4387475787509262626769043 6581213681263893940153565)
      ·
        refine ⟨2467955130473960227557587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6581213681263893940153565 2467955130473960227557587)
        ·
          refine ⟨3701932695710940341336381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2467955130473960227557587 3701932695710940341336381)
          ·
            refine ⟨1388224760891602628001143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3701932695710940341336381 1388224760891602628001143)
            ·
              refine ⟨2082337141337403942001715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1388224760891602628001143 2082337141337403942001715)
              ·
                refine ⟨3123505712006105913002573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2082337141337403942001715 3123505712006105913002573)
                ·
                  refine ⟨1171314642002289717375965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3123505712006105913002573 1171314642002289717375965)
                  ·
                    refine ⟨439242990750858644015987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1171314642002289717375965 439242990750858644015987)
                    ·
                      rfl

theorem cell22_1283134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 1, 3, 3].length) (baseStart_1283134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1283134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1283134 prefixEnd_1283134 := by exact prefixLift 1283134
  have htrace : WordTrace (prefixWord ++ tailWord_1283134) baseStart_1283134 baseEnd_1283134 := by
    simpa [prefixWord, tailWord_1283134, baseEnd_1283134] using wordTrace_append hprefix tailTrace_1283134
  have hstable : (prefixWord ++ tailWord_1283134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283134).length < 2 ^ (prefixWord ++ tailWord_1283134).sum := by decide
  have hdescent : baseEnd_1283134 < baseStart_1283134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283177 : List Nat := [1, 2, 1, 1, 1, 7, 3, 1, 1, 4]
def baseStart_1283177 : Nat := 118140960795 + 1283177 * 2 ^ 59
def prefixEnd_1283177 : Nat := 4983230072969 + 3 ^ 40 * 1283177 * 2
def baseEnd_1283177 : Nat := 439257710529620865190855

theorem tailTrace_1283177 : CollatzResearch.WordTrace tailWord_1283177 prefixEnd_1283177 439257710529620865190855 := by
  unfold tailWord_1283177
  simp only [CollatzResearch.WordTrace]
  refine ⟨46801310072276353029351785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31200873381517568686234523 46801310072276353029351785)
  ·
    refine ⟨35100982554207264772013839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46801310072276353029351785 35100982554207264772013839)
    ·
      refine ⟨52651473831310897158020759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35100982554207264772013839 52651473831310897158020759)
      ·
        refine ⟨78977210746966345737031139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52651473831310897158020759 78977210746966345737031139)
        ·
          refine ⟨118465816120449518605546709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78977210746966345737031139 118465816120449518605546709)
          ·
            refine ⟨2776542565323035592317501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 118465816120449518605546709 2776542565323035592317501)
            ·
              refine ⟨1041203461996138347119063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2776542565323035592317501 1041203461996138347119063)
              ·
                refine ⟨1561805192994207520678595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1041203461996138347119063 1561805192994207520678595)
                ·
                  refine ⟨2342707789491311281017893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1561805192994207520678595 2342707789491311281017893)
                  ·
                    refine ⟨439257710529620865190855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2342707789491311281017893 439257710529620865190855)
                    ·
                      rfl

theorem cell22_1283177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 3, 1, 1, 4].length) (baseStart_1283177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1283177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1283177 prefixEnd_1283177 := by exact prefixLift 1283177
  have htrace : WordTrace (prefixWord ++ tailWord_1283177) baseStart_1283177 baseEnd_1283177 := by
    simpa [prefixWord, tailWord_1283177, baseEnd_1283177] using wordTrace_append hprefix tailTrace_1283177
  have hstable : (prefixWord ++ tailWord_1283177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283177).length < 2 ^ (prefixWord ++ tailWord_1283177).sum := by decide
  have hdescent : baseEnd_1283177 < baseStart_1283177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283190 : List Nat := [5, 1, 1, 2, 1, 1, 1, 2, 3, 5]
def baseStart_1283190 : Nat := 118140960795 + 1283190 * 2 ^ 59
def prefixEnd_1283190 : Nat := 4983230072969 + 3 ^ 40 * 1283190 * 2
def baseEnd_1283190 : Nat := 439262160695293164615815

theorem tailTrace_1283190 : CollatzResearch.WordTrace tailWord_1283190 prefixEnd_1283190 439262160695293164615815 := by
  unfold tailWord_1283190
  simp only [CollatzResearch.WordTrace]
  refine ⟨2925111513826828515598439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31201189480819504166383349 2925111513826828515598439)
  ·
    refine ⟨4387667270740242773397659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2925111513826828515598439 4387667270740242773397659)
    ·
      refine ⟨6581500906110364160096489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4387667270740242773397659 6581500906110364160096489)
      ·
        refine ⟨4936125679582773120072367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6581500906110364160096489 4936125679582773120072367)
        ·
          refine ⟨7404188519374159680108551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4936125679582773120072367 7404188519374159680108551)
          ·
            refine ⟨11106282779061239520162827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7404188519374159680108551 11106282779061239520162827)
            ·
              refine ⟨16659424168591859280244241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11106282779061239520162827 16659424168591859280244241)
              ·
                refine ⟨12494568126443894460183181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16659424168591859280244241 12494568126443894460183181)
                ·
                  refine ⟨4685463047416460422568693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12494568126443894460183181 4685463047416460422568693)
                  ·
                    refine ⟨439262160695293164615815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4685463047416460422568693 439262160695293164615815)
                    ·
                      rfl

theorem cell22_1283190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_1283190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1283190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1283190 prefixEnd_1283190 := by exact prefixLift 1283190
  have htrace : WordTrace (prefixWord ++ tailWord_1283190) baseStart_1283190 baseEnd_1283190 := by
    simpa [prefixWord, tailWord_1283190, baseEnd_1283190] using wordTrace_append hprefix tailTrace_1283190
  have hstable : (prefixWord ++ tailWord_1283190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283190).length < 2 ^ (prefixWord ++ tailWord_1283190).sum := by decide
  have hdescent : baseEnd_1283190 < baseStart_1283190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283192 : List Nat := [2, 1, 2, 1, 1, 1, 8, 2, 4]
def baseStart_1283192 : Nat := 118140960795 + 1283192 * 2 ^ 59
def prefixEnd_1283192 : Nat := 4983230072969 + 3 ^ 40 * 1283192 * 2
def baseEnd_1283192 : Nat := 146420948445388608688603

theorem tailTrace_1283192 : CollatzResearch.WordTrace tailWord_1283192 prefixEnd_1283192 146420948445388608688603 := by
  unfold tailWord_1283192
  simp only [CollatzResearch.WordTrace]
  refine ⟨23400928583611005295573915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31201238111481340394098553 23400928583611005295573915)
  ·
    refine ⟨35101392875416507943360873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23400928583611005295573915 35101392875416507943360873)
    ·
      refine ⟨26326044656562380957520655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35101392875416507943360873 26326044656562380957520655)
      ·
        refine ⟨39489066984843571436280983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26326044656562380957520655 39489066984843571436280983)
        ·
          refine ⟨59233600477265357154421475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39489066984843571436280983 59233600477265357154421475)
          ·
            refine ⟨88850400715898035731632213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59233600477265357154421475 88850400715898035731632213)
            ·
              refine ⟨1041215633389430106230065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 88850400715898035731632213 1041215633389430106230065)
              ·
                refine ⟨780911725042072579672549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1041215633389430106230065 780911725042072579672549)
                ·
                  refine ⟨146420948445388608688603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 780911725042072579672549 146420948445388608688603)
                  ·
                    rfl

theorem cell22_1283192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 8, 2, 4].length) (baseStart_1283192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1283192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1283192 prefixEnd_1283192 := by exact prefixLift 1283192
  have htrace : WordTrace (prefixWord ++ tailWord_1283192) baseStart_1283192 baseEnd_1283192 := by
    simpa [prefixWord, tailWord_1283192, baseEnd_1283192] using wordTrace_append hprefix tailTrace_1283192
  have hstable : (prefixWord ++ tailWord_1283192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283192).length < 2 ^ (prefixWord ++ tailWord_1283192).sum := by decide
  have hdescent : baseEnd_1283192 < baseStart_1283192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283248 : List Nat := [2, 1, 1, 1, 2, 1, 2, 5, 7]
def baseStart_1283248 : Nat := 118140960795 + 1283248 * 2 ^ 59
def prefixEnd_1283248 : Nat := 4983230072969 + 3 ^ 40 * 1283248 * 2
def baseEnd_1283248 : Nat := 146427338426866782221879

theorem tailTrace_1283248 : CollatzResearch.WordTrace tailWord_1283248 prefixEnd_1283248 146427338426866782221879 := by
  unfold tailWord_1283248
  simp only [CollatzResearch.WordTrace]
  refine ⟨23401949827509566077593199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31202599770012754770124265 23401949827509566077593199)
  ·
    refine ⟨35102924741264349116389799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23401949827509566077593199 35102924741264349116389799)
    ·
      refine ⟨52654387111896523674584699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35102924741264349116389799 52654387111896523674584699)
      ·
        refine ⟨78981580667844785511877049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52654387111896523674584699 78981580667844785511877049)
        ·
          refine ⟨59236185500883589133907787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78981580667844785511877049 59236185500883589133907787)
          ·
            refine ⟨88854278251325383700861681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59236185500883589133907787 88854278251325383700861681)
            ·
              refine ⟨66640708688494037775646261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88854278251325383700861681 66640708688494037775646261)
              ·
                refine ⟨6247566439546316041466837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 66640708688494037775646261 6247566439546316041466837)
                ·
                  refine ⟨146427338426866782221879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6247566439546316041466837 146427338426866782221879)
                  ·
                    rfl

theorem cell22_1283248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 5, 7].length) (baseStart_1283248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1283248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1283248 prefixEnd_1283248 := by exact prefixLift 1283248
  have htrace : WordTrace (prefixWord ++ tailWord_1283248) baseStart_1283248 baseEnd_1283248 := by
    simpa [prefixWord, tailWord_1283248, baseEnd_1283248] using wordTrace_append hprefix tailTrace_1283248
  have hstable : (prefixWord ++ tailWord_1283248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283248).length < 2 ^ (prefixWord ++ tailWord_1283248).sum := by decide
  have hdescent : baseEnd_1283248 < baseStart_1283248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283303 : List Nat := [1, 1, 5, 3, 2, 1, 3, 2, 1, 3]
def baseStart_1283303 : Nat := 118140960795 + 1283303 * 2 ^ 59
def prefixEnd_1283303 : Nat := 4983230072969 + 3 ^ 40 * 1283303 * 2
def baseEnd_1283303 : Nat := 439300842904598536540469

theorem tailTrace_1283303 : CollatzResearch.WordTrace tailWord_1283303 prefixEnd_1283303 439300842904598536540469 := by
  unfold tailWord_1283303
  simp only [CollatzResearch.WordTrace]
  refine ⟨46805905669819876548438563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31203937113213251032292375 46805905669819876548438563)
  ·
    refine ⟨70208858504729814822657845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46805905669819876548438563 70208858504729814822657845)
    ·
      refine ⟨6582080484818420139624173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 70208858504729814822657845 6582080484818420139624173)
      ·
        refine ⟨2468280181806907552359065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6582080484818420139624173 2468280181806907552359065)
        ·
          refine ⟨1851210136355180664269299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2468280181806907552359065 1851210136355180664269299)
          ·
            refine ⟨2776815204532770996403949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1851210136355180664269299 2776815204532770996403949)
            ·
              refine ⟨1041305701699789123651481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2776815204532770996403949 1041305701699789123651481)
              ·
                refine ⟨780979276274841842738611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1041305701699789123651481 780979276274841842738611)
                ·
                  refine ⟨1171468914412262764107917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 780979276274841842738611 1171468914412262764107917)
                  ·
                    refine ⟨439300842904598536540469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1171468914412262764107917 439300842904598536540469)
                    ·
                      rfl

theorem cell22_1283303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 3, 2, 1, 3].length) (baseStart_1283303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1283303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1283303 prefixEnd_1283303 := by exact prefixLift 1283303
  have htrace : WordTrace (prefixWord ++ tailWord_1283303) baseStart_1283303 baseEnd_1283303 := by
    simpa [prefixWord, tailWord_1283303, baseEnd_1283303] using wordTrace_append hprefix tailTrace_1283303
  have hstable : (prefixWord ++ tailWord_1283303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283303).length < 2 ^ (prefixWord ++ tailWord_1283303).sum := by decide
  have hdescent : baseEnd_1283303 < baseStart_1283303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283329 : List Nat := [1, 2, 4, 1, 1, 5, 1, 2, 1, 4]
def baseStart_1283329 : Nat := 118140960795 + 1283329 * 2 ^ 59
def prefixEnd_1283329 : Nat := 4983230072969 + 3 ^ 40 * 1283329 * 2
def baseEnd_1283329 : Nat := 439309743235943135390389

theorem tailTrace_1283329 : CollatzResearch.WordTrace tailWord_1283329 prefixEnd_1283329 439309743235943135390389 := by
  unfold tailWord_1283329
  simp only [CollatzResearch.WordTrace]
  refine ⟨46806853967725682988885041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31204569311817121992590027 46806853967725682988885041)
  ·
    refine ⟨35105140475794262241663781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46806853967725682988885041 35105140475794262241663781)
    ·
      refine ⟨6582213839211424170311959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35105140475794262241663781 6582213839211424170311959)
      ·
        refine ⟨9873320758817136255467939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6582213839211424170311959 9873320758817136255467939)
        ·
          refine ⟨14809981138225704383201909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9873320758817136255467939 14809981138225704383201909)
          ·
            refine ⟨1388435731708659785925179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14809981138225704383201909 1388435731708659785925179)
            ·
              refine ⟨2082653597562989678887769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1388435731708659785925179 2082653597562989678887769)
              ·
                refine ⟨1561990198172242259165827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2082653597562989678887769 1561990198172242259165827)
                ·
                  refine ⟨2342985297258363388748741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1561990198172242259165827 2342985297258363388748741)
                  ·
                    refine ⟨439309743235943135390389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2342985297258363388748741 439309743235943135390389)
                    ·
                      rfl

theorem cell22_1283329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 2, 1, 4].length) (baseStart_1283329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1283329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1283329 prefixEnd_1283329 := by exact prefixLift 1283329
  have htrace : WordTrace (prefixWord ++ tailWord_1283329) baseStart_1283329 baseEnd_1283329 := by
    simpa [prefixWord, tailWord_1283329, baseEnd_1283329] using wordTrace_append hprefix tailTrace_1283329
  have hstable : (prefixWord ++ tailWord_1283329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283329).length < 2 ^ (prefixWord ++ tailWord_1283329).sum := by decide
  have hdescent : baseEnd_1283329 < baseStart_1283329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283342 : List Nat := [4, 1, 1, 2, 1, 4, 1, 2, 1, 5]
def baseStart_1283342 : Nat := 118140960795 + 1283342 * 2 ^ 59
def prefixEnd_1283342 : Nat := 4983230072969 + 3 ^ 40 * 1283342 * 2
def baseEnd_1283342 : Nat := 439314193401615434815349

theorem tailTrace_1283342 : CollatzResearch.WordTrace tailWord_1283342 prefixEnd_1283342 439314193401615434815349 := by
  unfold tailWord_1283342
  simp only [CollatzResearch.WordTrace]
  refine ⟨5850916014584823276138535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31204885411119057472738853 5850916014584823276138535)
  ·
    refine ⟨8776374021877234914207803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5850916014584823276138535 8776374021877234914207803)
    ·
      refine ⟨13164561032815852371311705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8776374021877234914207803 13164561032815852371311705)
      ·
        refine ⟨9873420774611889278483779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13164561032815852371311705 9873420774611889278483779)
        ·
          refine ⟨14810131161917833917725669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9873420774611889278483779 14810131161917833917725669)
          ·
            refine ⟨2776899592859593859573563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14810131161917833917725669 2776899592859593859573563)
            ·
              refine ⟨4165349389289390789360345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2776899592859593859573563 4165349389289390789360345)
              ·
                refine ⟨3124012041967043092020259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4165349389289390789360345 3124012041967043092020259)
                ·
                  refine ⟨4686018062950564638030389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3124012041967043092020259 4686018062950564638030389)
                  ·
                    refine ⟨439314193401615434815349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4686018062950564638030389 439314193401615434815349)
                    ·
                      rfl

theorem cell22_1283342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 2, 1, 5].length) (baseStart_1283342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1283342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1283342 prefixEnd_1283342 := by exact prefixLift 1283342
  have htrace : WordTrace (prefixWord ++ tailWord_1283342) baseStart_1283342 baseEnd_1283342 := by
    simpa [prefixWord, tailWord_1283342, baseEnd_1283342] using wordTrace_append hprefix tailTrace_1283342
  have hstable : (prefixWord ++ tailWord_1283342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283342).length < 2 ^ (prefixWord ++ tailWord_1283342).sum := by decide
  have hdescent : baseEnd_1283342 < baseStart_1283342 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283400 : List Nat := [2, 1, 3, 1, 1, 2, 1, 4, 7]
def baseStart_1283400 : Nat := 118140960795 + 1283400 * 2 ^ 59
def prefixEnd_1283400 : Nat := 4983230072969 + 3 ^ 40 * 1283400 * 2
def baseEnd_1283400 : Nat := 146444682662307538955057

theorem tailTrace_1283400 : CollatzResearch.WordTrace tailWord_1283400 prefixEnd_1283400 146444682662307538955057 := by
  unfold tailWord_1283400
  simp only [CollatzResearch.WordTrace]
  refine ⟨23404721775234231057359827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31206295700312308076479769 23404721775234231057359827)
  ·
    refine ⟨35107082662851346586039741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23404721775234231057359827 35107082662851346586039741)
    ·
      refine ⟨13165155998569254969764903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35107082662851346586039741 13165155998569254969764903)
      ·
        refine ⟨19747733997853882454647355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13165155998569254969764903 19747733997853882454647355)
        ·
          refine ⟨29621600996780823681971033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19747733997853882454647355 29621600996780823681971033)
          ·
            refine ⟨22216200747585617761478275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29621600996780823681971033 22216200747585617761478275)
            ·
              refine ⟨33324301121378426642217413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22216200747585617761478275 33324301121378426642217413)
              ·
                refine ⟨6248306460258454995415765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33324301121378426642217413 6248306460258454995415765)
                ·
                  refine ⟨146444682662307538955057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6248306460258454995415765 146444682662307538955057)
                  ·
                    rfl

theorem cell22_1283400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 4, 7].length) (baseStart_1283400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1283400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1283400 prefixEnd_1283400 := by exact prefixLift 1283400
  have htrace : WordTrace (prefixWord ++ tailWord_1283400) baseStart_1283400 baseEnd_1283400 := by
    simpa [prefixWord, tailWord_1283400, baseEnd_1283400] using wordTrace_append hprefix tailTrace_1283400
  have hstable : (prefixWord ++ tailWord_1283400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283400).length < 2 ^ (prefixWord ++ tailWord_1283400).sum := by decide
  have hdescent : baseEnd_1283400 < baseStart_1283400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283417 : List Nat := [1, 2, 1, 2, 2, 2, 5, 2, 5]
def baseStart_1283417 : Nat := 118140960795 + 1283417 * 2 ^ 59
def prefixEnd_1283417 : Nat := 4983230072969 + 3 ^ 40 * 1283417 * 2
def baseEnd_1283417 : Nat := 146446622478113413063373

theorem tailTrace_1283417 : CollatzResearch.WordTrace tailWord_1283417 prefixEnd_1283417 146446622478113413063373 := by
  unfold tailWord_1283417
  simp only [CollatzResearch.WordTrace]
  refine ⟨46810063591406874018088505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31206709060937916012059003 46810063591406874018088505)
  ·
    refine ⟨35107547693555155513566379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46810063591406874018088505 35107547693555155513566379)
    ·
      refine ⟨52661321540332733270349569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35107547693555155513566379 52661321540332733270349569)
      ·
        refine ⟨39495991155249549952762177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52661321540332733270349569 39495991155249549952762177)
        ·
          refine ⟨29621993366437162464571633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39495991155249549952762177 29621993366437162464571633)
          ·
            refine ⟨22216495024827871848428725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29621993366437162464571633 22216495024827871848428725)
            ·
              refine ⟨2082796408577612985790193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22216495024827871848428725 2082796408577612985790193)
              ·
                refine ⟨1562097306433209739342645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2082796408577612985790193 1562097306433209739342645)
                ·
                  refine ⟨146446622478113413063373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1562097306433209739342645 146446622478113413063373)
                  ·
                    rfl

theorem cell22_1283417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 2, 5].length) (baseStart_1283417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1283417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1283417 prefixEnd_1283417 := by exact prefixLift 1283417
  have htrace : WordTrace (prefixWord ++ tailWord_1283417) baseStart_1283417 baseEnd_1283417 := by
    simpa [prefixWord, tailWord_1283417, baseEnd_1283417] using wordTrace_append hprefix tailTrace_1283417
  have hstable : (prefixWord ++ tailWord_1283417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283417).length < 2 ^ (prefixWord ++ tailWord_1283417).sum := by decide
  have hdescent : baseEnd_1283417 < baseStart_1283417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283464 : List Nat := [2, 1, 3, 3, 1, 2, 2, 3, 1, 4]
def baseStart_1283464 : Nat := 118140960795 + 1283464 * 2 ^ 59
def prefixEnd_1283464 : Nat := 4983230072969 + 3 ^ 40 * 1283464 * 2
def baseEnd_1283464 : Nat := 439355956494847783264975

theorem tailTrace_1283464 : CollatzResearch.WordTrace tailWord_1283464 prefixEnd_1283464 439355956494847783264975 := by
  unfold tailWord_1283464
  simp only [CollatzResearch.WordTrace]
  refine ⟨23405888911118300522524723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31207851881491067363366297 23405888911118300522524723)
  ·
    refine ⟨35108833366677450783787085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23405888911118300522524723 35108833366677450783787085)
    ·
      refine ⟨13165812512504044043920157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35108833366677450783787085 13165812512504044043920157)
      ·
        refine ⟨4937179692189016516470059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13165812512504044043920157 4937179692189016516470059)
        ·
          refine ⟨7405769538283524774705089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4937179692189016516470059 7405769538283524774705089)
          ·
            refine ⟨5554327153712643581028817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7405769538283524774705089 5554327153712643581028817)
            ·
              refine ⟨4165745365284482685771613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5554327153712643581028817 4165745365284482685771613)
              ·
                refine ⟨1562154511981681007164355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4165745365284482685771613 1562154511981681007164355)
                ·
                  refine ⟨2343231767972521510746533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1562154511981681007164355 2343231767972521510746533)
                  ·
                    refine ⟨439355956494847783264975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2343231767972521510746533 439355956494847783264975)
                    ·
                      rfl

theorem cell22_1283464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 3, 1, 4].length) (baseStart_1283464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1283464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1283464 prefixEnd_1283464 := by exact prefixLift 1283464
  have htrace : WordTrace (prefixWord ++ tailWord_1283464) baseStart_1283464 baseEnd_1283464 := by
    simpa [prefixWord, tailWord_1283464, baseEnd_1283464] using wordTrace_append hprefix tailTrace_1283464
  have hstable : (prefixWord ++ tailWord_1283464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283464).length < 2 ^ (prefixWord ++ tailWord_1283464).sum := by decide
  have hdescent : baseEnd_1283464 < baseStart_1283464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283475 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 2, 10]
def baseStart_1283475 : Nat := 118140960795 + 1283475 * 2 ^ 59
def prefixEnd_1283475 : Nat := 4983230072969 + 3 ^ 40 * 1283475 * 2
def baseEnd_1283475 : Nat := 439359722019647421239941

theorem tailTrace_1283475 : CollatzResearch.WordTrace tailWord_1283475 prefixEnd_1283475 439359722019647421239941 := by
  unfold tailWord_1283475
  simp only [CollatzResearch.WordTrace]
  refine ⟨46812179025196749923699879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31208119350131166615799919 46812179025196749923699879)
  ·
    refine ⟨70218268537795124885549819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46812179025196749923699879 70218268537795124885549819)
    ·
      refine ⟨105327402806692687328324729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70218268537795124885549819 105327402806692687328324729)
      ·
        refine ⟨78995552105019515496243547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105327402806692687328324729 78995552105019515496243547)
        ·
          refine ⟨118493328157529273244365321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78995552105019515496243547 118493328157529273244365321)
          ·
            refine ⟨88869996118146954933273991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118493328157529273244365321 88869996118146954933273991)
            ·
              refine ⟨133304994177220432399910987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88869996118146954933273991 133304994177220432399910987)
              ·
                refine ⟨199957491265830648599866481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133304994177220432399910987 199957491265830648599866481)
                ·
                  refine ⟨149968118449372986449899861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 199957491265830648599866481 149968118449372986449899861)
                  ·
                    refine ⟨439359722019647421239941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 149968118449372986449899861 439359722019647421239941)
                    ·
                      rfl

theorem cell22_1283475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 10].length) (baseStart_1283475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1283475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1283475 prefixEnd_1283475 := by exact prefixLift 1283475
  have htrace : WordTrace (prefixWord ++ tailWord_1283475) baseStart_1283475 baseEnd_1283475 := by
    simpa [prefixWord, tailWord_1283475, baseEnd_1283475] using wordTrace_append hprefix tailTrace_1283475
  have hstable : (prefixWord ++ tailWord_1283475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283475).length < 2 ^ (prefixWord ++ tailWord_1283475).sum := by decide
  have hdescent : baseEnd_1283475 < baseStart_1283475 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283492 : List Nat := [2, 3, 1, 2, 1, 1, 1, 1, 6, 4]
def baseStart_1283492 : Nat := 118140960795 + 1283492 * 2 ^ 59
def prefixEnd_1283492 : Nat := 4983230072969 + 3 ^ 40 * 1283492 * 2
def baseEnd_1283492 : Nat := 439365541467065043564889

theorem tailTrace_1283492 : CollatzResearch.WordTrace tailWord_1283492 prefixEnd_1283492 439365541467065043564889 := by
  unfold tailWord_1283492
  simp only [CollatzResearch.WordTrace]
  refine ⟨23406399533067580913534365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31208532710756774551379153 23406399533067580913534365)
  ·
    refine ⟨8777399824900342842575387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23406399533067580913534365 8777399824900342842575387)
    ·
      refine ⟨13166099737350514263863081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8777399824900342842575387 13166099737350514263863081)
      ·
        refine ⟨9874574803012885697897311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13166099737350514263863081 9874574803012885697897311)
        ·
          refine ⟨14811862204519328546845967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9874574803012885697897311 14811862204519328546845967)
          ·
            refine ⟨22217793306778992820268951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14811862204519328546845967 22217793306778992820268951)
            ·
              refine ⟨33326689960168489230403427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22217793306778992820268951 33326689960168489230403427)
              ·
                refine ⟨49990034940252733845605141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33326689960168489230403427 49990034940252733845605141)
                ·
                  refine ⟨2343282887824346899012741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 49990034940252733845605141 2343282887824346899012741)
                  ·
                    refine ⟨439365541467065043564889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2343282887824346899012741 439365541467065043564889)
                    ·
                      rfl

theorem cell22_1283492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 6, 4].length) (baseStart_1283492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1283492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1283492 prefixEnd_1283492 := by exact prefixLift 1283492
  have htrace : WordTrace (prefixWord ++ tailWord_1283492) baseStart_1283492 baseEnd_1283492 := by
    simpa [prefixWord, tailWord_1283492, baseEnd_1283492] using wordTrace_append hprefix tailTrace_1283492
  have hstable : (prefixWord ++ tailWord_1283492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283492).length < 2 ^ (prefixWord ++ tailWord_1283492).sum := by decide
  have hdescent : baseEnd_1283492 < baseStart_1283492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283509 : List Nat := [1, 3, 3, 2, 2, 1, 1, 3, 2, 4]
def baseStart_1283509 : Nat := 118140960795 + 1283509 * 2 ^ 59
def prefixEnd_1283509 : Nat := 4983230072969 + 3 ^ 40 * 1283509 * 2
def baseEnd_1283509 : Nat := 439371360914482665889837

theorem tailTrace_1283509 : CollatzResearch.WordTrace tailWord_1283509 prefixEnd_1283509 439371360914482665889837 := by
  unfold tailWord_1283509
  simp only [CollatzResearch.WordTrace]
  refine ⟨46813419107073573730437581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31208946071382382486958387 46813419107073573730437581)
  ·
    refine ⟨17555032165152590148914093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46813419107073573730437581 17555032165152590148914093)
    ·
      refine ⟨6583137061932221305842785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17555032165152590148914093 6583137061932221305842785)
      ·
        refine ⟨4937352796449165979382089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6583137061932221305842785 4937352796449165979382089)
        ·
          refine ⟨3703014597336874484536567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4937352796449165979382089 3703014597336874484536567)
          ·
            refine ⟨5554521896005311726804851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3703014597336874484536567 5554521896005311726804851)
            ·
              refine ⟨8331782844007967590207277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5554521896005311726804851 8331782844007967590207277)
              ·
                refine ⟨3124418566502987846327729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8331782844007967590207277 3124418566502987846327729)
                ·
                  refine ⟨2343313924877240884745797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3124418566502987846327729 2343313924877240884745797)
                  ·
                    refine ⟨439371360914482665889837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2343313924877240884745797 439371360914482665889837)
                    ·
                      rfl

theorem cell22_1283509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_1283509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1283509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1283509 prefixEnd_1283509 := by exact prefixLift 1283509
  have htrace : WordTrace (prefixWord ++ tailWord_1283509) baseStart_1283509 baseEnd_1283509 := by
    simpa [prefixWord, tailWord_1283509, baseEnd_1283509] using wordTrace_append hprefix tailTrace_1283509
  have hstable : (prefixWord ++ tailWord_1283509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283509).length < 2 ^ (prefixWord ++ tailWord_1283509).sum := by decide
  have hdescent : baseEnd_1283509 < baseStart_1283509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283586 : List Nat := [3, 4, 1, 2, 1, 2, 1, 1, 7]
def baseStart_1283586 : Nat := 118140960795 + 1283586 * 2 ^ 59
def prefixEnd_1283586 : Nat := 4983230072969 + 3 ^ 40 * 1283586 * 2
def baseEnd_1283586 : Nat := 146465906529360043904867

theorem tailTrace_1283586 : CollatzResearch.WordTrace tailWord_1283586 prefixEnd_1283586 146465906529360043904867 := by
  unfold tailWord_1283586
  simp only [CollatzResearch.WordTrace]
  refine ⟨11704056881948653970247653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31210818351863077253993741 11704056881948653970247653)
  ·
    refine ⟨2194510665365372619421435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11704056881948653970247653 2194510665365372619421435)
    ·
      refine ⟨3291765998048058929132153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2194510665365372619421435 3291765998048058929132153)
      ·
        refine ⟨2468824498536044196849115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3291765998048058929132153 2468824498536044196849115)
        ·
          refine ⟨3703236747804066295273673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2468824498536044196849115 3703236747804066295273673)
          ·
            refine ⟨2777427560853049721455255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3703236747804066295273673 2777427560853049721455255)
            ·
              refine ⟨4166141341279574582182883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2777427560853049721455255 4166141341279574582182883)
              ·
                refine ⟨6249212011919361873274325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4166141341279574582182883 6249212011919361873274325)
                ·
                  refine ⟨146465906529360043904867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6249212011919361873274325 146465906529360043904867)
                  ·
                    rfl

theorem cell22_1283586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_1283586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1283586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1283586 prefixEnd_1283586 := by exact prefixLift 1283586
  have htrace : WordTrace (prefixWord ++ tailWord_1283586) baseStart_1283586 baseEnd_1283586 := by
    simpa [prefixWord, tailWord_1283586, baseEnd_1283586] using wordTrace_append hprefix tailTrace_1283586
  have hstable : (prefixWord ++ tailWord_1283586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283586).length < 2 ^ (prefixWord ++ tailWord_1283586).sum := by decide
  have hdescent : baseEnd_1283586 < baseStart_1283586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283616 : List Nat := [2, 1, 1, 6, 1, 1, 1, 4, 1, 4]
def baseStart_1283616 : Nat := 118140960795 + 1283616 * 2 ^ 59
def prefixEnd_1283616 : Nat := 4983230072969 + 3 ^ 40 * 1283616 * 2
def baseEnd_1283616 : Nat := 439407989201170053464509

theorem tailTrace_1283616 : CollatzResearch.WordTrace tailWord_1283616 prefixEnd_1283616 439407989201170053464509 := by
  unfold tailWord_1283616
  simp only [CollatzResearch.WordTrace]
  refine ⟨23408660858842965502291351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31211547811790620669721801 23408660858842965502291351)
  ·
    refine ⟨35112991288264448253437027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23408660858842965502291351 35112991288264448253437027)
    ·
      refine ⟨52669486932396672380155541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35112991288264448253437027 52669486932396672380155541)
      ·
        refine ⟨2468882199956094017819791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 52669486932396672380155541 2468882199956094017819791)
        ·
          refine ⟨3703323299934141026729687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2468882199956094017819791 3703323299934141026729687)
          ·
            refine ⟨5554984949901211540094531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3703323299934141026729687 5554984949901211540094531)
            ·
              refine ⟨8332477424851817310141797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5554984949901211540094531 8332477424851817310141797)
              ·
                refine ⟨1562339517159715745651587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8332477424851817310141797 1562339517159715745651587)
                ·
                  refine ⟨2343509275739573618477381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1562339517159715745651587 2343509275739573618477381)
                  ·
                    refine ⟨439407989201170053464509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2343509275739573618477381 439407989201170053464509)
                    ·
                      rfl

theorem cell22_1283616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 4, 1, 4].length) (baseStart_1283616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1283616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1283616 prefixEnd_1283616 := by exact prefixLift 1283616
  have htrace : WordTrace (prefixWord ++ tailWord_1283616) baseStart_1283616 baseEnd_1283616 := by
    simpa [prefixWord, tailWord_1283616, baseEnd_1283616] using wordTrace_append hprefix tailTrace_1283616
  have hstable : (prefixWord ++ tailWord_1283616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283616).length < 2 ^ (prefixWord ++ tailWord_1283616).sum := by decide
  have hdescent : baseEnd_1283616 < baseStart_1283616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283719 : List Nat := [1, 1, 4, 2, 1, 3, 1, 1, 1, 7]
def baseStart_1283719 : Nat := 118140960795 + 1283719 * 2 ^ 59
def prefixEnd_1283719 : Nat := 4983230072969 + 3 ^ 40 * 1283719 * 2
def baseEnd_1283719 : Nat := 439443248206112118139193

theorem tailTrace_1283719 : CollatzResearch.WordTrace tailWord_1283719 prefixEnd_1283719 439443248206112118139193 := by
  unfold tailWord_1283719
  simp only [CollatzResearch.WordTrace]
  refine ⟨46821078436312779595582211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31214052290875186397054807 46821078436312779595582211)
  ·
    refine ⟨70231617654469169393373317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46821078436312779595582211 70231617654469169393373317)
    ·
      refine ⟨13168428310212969261257497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70231617654469169393373317 13168428310212969261257497)
      ·
        refine ⟨9876321232659726945943123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13168428310212969261257497 9876321232659726945943123)
        ·
          refine ⟨14814481848989590418914685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9876321232659726945943123 14814481848989590418914685)
          ·
            refine ⟨5555430693371096407093007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14814481848989590418914685 5555430693371096407093007)
            ·
              refine ⟨8333146040056644610639511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5555430693371096407093007 8333146040056644610639511)
              ·
                refine ⟨12499719060084966915959267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8333146040056644610639511 12499719060084966915959267)
                ·
                  refine ⟨18749578590127450373938901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12499719060084966915959267 18749578590127450373938901)
                  ·
                    refine ⟨439443248206112118139193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18749578590127450373938901 439443248206112118139193)
                    ·
                      rfl

theorem cell22_1283719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 7].length) (baseStart_1283719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1283719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1283719 prefixEnd_1283719 := by exact prefixLift 1283719
  have htrace : WordTrace (prefixWord ++ tailWord_1283719) baseStart_1283719 baseEnd_1283719 := by
    simpa [prefixWord, tailWord_1283719, baseEnd_1283719] using wordTrace_append hprefix tailTrace_1283719
  have hstable : (prefixWord ++ tailWord_1283719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283719).length < 2 ^ (prefixWord ++ tailWord_1283719).sum := by decide
  have hdescent : baseEnd_1283719 < baseStart_1283719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283742 : List Nat := [4, 3, 1, 1, 1, 3, 2, 3, 1, 3]
def baseStart_1283742 : Nat := 118140960795 + 1283742 * 2 ^ 59
def prefixEnd_1283742 : Nat := 4983230072969 + 3 ^ 40 * 1283742 * 2
def baseEnd_1283742 : Nat := 439451121576147724814123

theorem tailTrace_1283742 : CollatzResearch.WordTrace tailWord_1283742 prefixEnd_1283742 439451121576147724814123 := by
  unfold tailWord_1283742
  simp only [CollatzResearch.WordTrace]
  refine ⟨5852739664403681815458685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31214611543486303015779653 5852739664403681815458685)
  ·
    refine ⟨2194777374151380680797007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5852739664403681815458685 2194777374151380680797007)
    ·
      refine ⟨3292166061227071021195511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2194777374151380680797007 3292166061227071021195511)
      ·
        refine ⟨4938249091840606531793267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3292166061227071021195511 4938249091840606531793267)
        ·
          refine ⟨7407373637760909797689901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4938249091840606531793267 7407373637760909797689901)
          ·
            refine ⟨2777765114160341174133713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7407373637760909797689901 2777765114160341174133713)
            ·
              refine ⟨2083323835620255880600285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2777765114160341174133713 2083323835620255880600285)
              ·
                refine ⟨781246438357595955225107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2083323835620255880600285 781246438357595955225107)
                ·
                  refine ⟨1171869657536393932837661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 781246438357595955225107 1171869657536393932837661)
                  ·
                    refine ⟨439451121576147724814123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1171869657536393932837661 439451121576147724814123)
                    ·
                      rfl

theorem cell22_1283742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_1283742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1283742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1283742 prefixEnd_1283742 := by exact prefixLift 1283742
  have htrace : WordTrace (prefixWord ++ tailWord_1283742) baseStart_1283742 baseEnd_1283742 := by
    simpa [prefixWord, tailWord_1283742, baseEnd_1283742] using wordTrace_append hprefix tailTrace_1283742
  have hstable : (prefixWord ++ tailWord_1283742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283742).length < 2 ^ (prefixWord ++ tailWord_1283742).sum := by decide
  have hdescent : baseEnd_1283742 < baseStart_1283742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283871 : List Nat := [1, 1, 2, 4, 2, 1, 2, 2, 2, 5]
def baseStart_1283871 : Nat := 118140960795 + 1283871 * 2 ^ 59
def prefixEnd_1283871 : Nat := 4983230072969 + 3 ^ 40 * 1283871 * 2
def baseEnd_1283871 : Nat := 439495280912434388338727

theorem tailTrace_1283871 : CollatzResearch.WordTrace tailWord_1283871 prefixEnd_1283871 439495280912434388338727 := by
  unfold tailWord_1283871
  simp only [CollatzResearch.WordTrace]
  refine ⟨46826622331762109555115467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31217748221174739703410311 46826622331762109555115467)
  ·
    refine ⟨70239933497643164332673201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46826622331762109555115467 70239933497643164332673201)
    ·
      refine ⟨52679950123232373249504901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70239933497643164332673201 52679950123232373249504901)
      ·
        refine ⟨9877490648106069984282169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52679950123232373249504901 9877490648106069984282169)
        ·
          refine ⟨7408117986079552488211627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9877490648106069984282169 7408117986079552488211627)
          ·
            refine ⟨11112176979119328732317441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7408117986079552488211627 11112176979119328732317441)
            ·
              refine ⟨8334132734339496549238081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11112176979119328732317441 8334132734339496549238081)
              ·
                refine ⟨6250599550754622411928561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8334132734339496549238081 6250599550754622411928561)
                ·
                  refine ⟨4687949663065966808946421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6250599550754622411928561 4687949663065966808946421)
                  ·
                    refine ⟨439495280912434388338727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4687949663065966808946421 439495280912434388338727)
                    ·
                      rfl

theorem cell22_1283871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 2, 2, 5].length) (baseStart_1283871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1283871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1283871 prefixEnd_1283871 := by exact prefixLift 1283871
  have htrace : WordTrace (prefixWord ++ tailWord_1283871) baseStart_1283871 baseEnd_1283871 := by
    simpa [prefixWord, tailWord_1283871, baseEnd_1283871] using wordTrace_append hprefix tailTrace_1283871
  have hstable : (prefixWord ++ tailWord_1283871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283871).length < 2 ^ (prefixWord ++ tailWord_1283871).sum := by decide
  have hdescent : baseEnd_1283871 < baseStart_1283871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283873 : List Nat := [1, 2, 3, 2, 1, 4, 2, 2, 5]
def baseStart_1283873 : Nat := 118140960795 + 1283873 * 2 ^ 59
def prefixEnd_1283873 : Nat := 4983230072969 + 3 ^ 40 * 1283873 * 2
def baseEnd_1283873 : Nat := 146498655184435683262907

theorem tailTrace_1283873 : CollatzResearch.WordTrace tailWord_1283873 prefixEnd_1283873 146498655184435683262907 := by
  unfold tailWord_1283873
  simp only [CollatzResearch.WordTrace]
  refine ⟨46826695277754863896688273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31217796851836575931125515 46826695277754863896688273)
  ·
    refine ⟨35120021458316147922516205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46826695277754863896688273 35120021458316147922516205)
    ·
      refine ⟨13170008046868555470943577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35120021458316147922516205 13170008046868555470943577)
      ·
        refine ⟨9877506035151416603207683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13170008046868555470943577 9877506035151416603207683)
        ·
          refine ⟨14816259052727124904811525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9877506035151416603207683 14816259052727124904811525)
          ·
            refine ⟨2778048572386335919652161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14816259052727124904811525 2778048572386335919652161)
            ·
              refine ⟨2083536429289751939739121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2778048572386335919652161 2083536429289751939739121)
              ·
                refine ⟨1562652321967313954804341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2083536429289751939739121 1562652321967313954804341)
                ·
                  refine ⟨146498655184435683262907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1562652321967313954804341 146498655184435683262907)
                  ·
                    rfl

theorem cell22_1283873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 2, 5].length) (baseStart_1283873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1283873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1283873 prefixEnd_1283873 := by exact prefixLift 1283873
  have htrace : WordTrace (prefixWord ++ tailWord_1283873) baseStart_1283873 baseEnd_1283873 := by
    simpa [prefixWord, tailWord_1283873, baseEnd_1283873] using wordTrace_append hprefix tailTrace_1283873
  have hstable : (prefixWord ++ tailWord_1283873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283873).length < 2 ^ (prefixWord ++ tailWord_1283873).sum := by decide
  have hdescent : baseEnd_1283873 < baseStart_1283873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283877 : List Nat := [1, 3, 1, 2, 3, 2, 4, 2, 1, 3]
def baseStart_1283877 : Nat := 118140960795 + 1283877 * 2 ^ 59
def prefixEnd_1283877 : Nat := 4983230072969 + 3 ^ 40 * 1283877 * 2
def baseEnd_1283877 : Nat := 439497334835052372688709

theorem tailTrace_1283877 : CollatzResearch.WordTrace tailWord_1283877 prefixEnd_1283877 439497334835052372688709 := by
  unfold tailWord_1283877
  simp only [CollatzResearch.WordTrace]
  refine ⟨46826841169740372579833885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31217894113160248386555923 46826841169740372579833885)
  ·
    refine ⟨17560065438652639717437707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46826841169740372579833885 17560065438652639717437707)
    ·
      refine ⟨26340098157978959576156561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17560065438652639717437707 26340098157978959576156561)
      ·
        refine ⟨19755073618484219682117421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26340098157978959576156561 19755073618484219682117421)
        ·
          refine ⟨7408152606931582380794033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19755073618484219682117421 7408152606931582380794033)
          ·
            refine ⟨5556114455198686785595525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7408152606931582380794033 5556114455198686785595525)
            ·
              refine ⟨1041771460349753772299161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5556114455198686785595525 1041771460349753772299161)
              ·
                refine ⟨781328595262315329224371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1041771460349753772299161 781328595262315329224371)
                ·
                  refine ⟨1171992892893472993836557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 781328595262315329224371 1171992892893472993836557)
                  ·
                    refine ⟨439497334835052372688709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1171992892893472993836557 439497334835052372688709)
                    ·
                      rfl

theorem cell22_1283877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 4, 2, 1, 3].length) (baseStart_1283877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1283877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1283877 prefixEnd_1283877 := by exact prefixLift 1283877
  have htrace : WordTrace (prefixWord ++ tailWord_1283877) baseStart_1283877 baseEnd_1283877 := by
    simpa [prefixWord, tailWord_1283877, baseEnd_1283877] using wordTrace_append hprefix tailTrace_1283877
  have hstable : (prefixWord ++ tailWord_1283877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283877).length < 2 ^ (prefixWord ++ tailWord_1283877).sum := by decide
  have hdescent : baseEnd_1283877 < baseStart_1283877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283950 : List Nat := [4, 1, 2, 3, 1, 1, 3, 1, 1, 5]
def baseStart_1283950 : Nat := 118140960795 + 1283950 * 2 ^ 59
def prefixEnd_1283950 : Nat := 4983230072969 + 3 ^ 40 * 1283950 * 2
def baseEnd_1283950 : Nat := 439522324226904515613485

theorem tailTrace_1283950 : CollatzResearch.WordTrace tailWord_1283950 prefixEnd_1283950 439522324226904515613485 := by
  unfold tailWord_1283950
  simp only [CollatzResearch.WordTrace]
  refine ⟨5853687962309488255905163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31219669132317270698160869 5853687962309488255905163)
  ·
    refine ⟨8780531943464232383857745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5853687962309488255905163 8780531943464232383857745)
    ·
      refine ⟨6585398957598174287893309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8780531943464232383857745 6585398957598174287893309)
      ·
        refine ⟨2469524609099315357959991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6585398957598174287893309 2469524609099315357959991)
        ·
          refine ⟨3704286913648973036939987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2469524609099315357959991 3704286913648973036939987)
          ·
            refine ⟨5556430370473459555409981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3704286913648973036939987 5556430370473459555409981)
            ·
              refine ⟨2083661388927547333278743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5556430370473459555409981 2083661388927547333278743)
              ·
                refine ⟨3125492083391320999918115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2083661388927547333278743 3125492083391320999918115)
                ·
                  refine ⟨4688238125086981499877173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3125492083391320999918115 4688238125086981499877173)
                  ·
                    refine ⟨439522324226904515613485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4688238125086981499877173 439522324226904515613485)
                    ·
                      rfl

theorem cell22_1283950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_1283950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1283950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1283950 prefixEnd_1283950 := by exact prefixLift 1283950
  have htrace : WordTrace (prefixWord ++ tailWord_1283950) baseStart_1283950 baseEnd_1283950 := by
    simpa [prefixWord, tailWord_1283950, baseEnd_1283950] using wordTrace_append hprefix tailTrace_1283950
  have hstable : (prefixWord ++ tailWord_1283950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283950).length < 2 ^ (prefixWord ++ tailWord_1283950).sum := by decide
  have hdescent : baseEnd_1283950 < baseStart_1283950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283961 : List Nat := [1, 2, 1, 3, 2, 2, 1, 1, 2, 7]
def baseStart_1283961 : Nat := 118140960795 + 1283961 * 2 ^ 59
def prefixEnd_1283961 : Nat := 4983230072969 + 3 ^ 40 * 1283961 * 2
def baseEnd_1283961 : Nat := 439526089751704153588451

theorem tailTrace_1283961 : CollatzResearch.WordTrace tailWord_1283961 prefixEnd_1283961 439526089751704153588451 := by
  unfold tailWord_1283961
  simp only [CollatzResearch.WordTrace]
  refine ⟨46829904901436054925891737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31219936600957369950594491 46829904901436054925891737)
  ·
    refine ⟨35122428676077041194418803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46829904901436054925891737 35122428676077041194418803)
    ·
      refine ⟨52683643014115561791628205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35122428676077041194418803 52683643014115561791628205)
      ·
        refine ⟨19756366130293335671860577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52683643014115561791628205 19756366130293335671860577)
        ·
          refine ⟨14817274597720001753895433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19756366130293335671860577 14817274597720001753895433)
          ·
            refine ⟨11112955948290001315421575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14817274597720001753895433 11112955948290001315421575)
            ·
              refine ⟨16669433922435001973132363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11112955948290001315421575 16669433922435001973132363)
              ·
                refine ⟨25004150883652502959698545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16669433922435001973132363 25004150883652502959698545)
                ·
                  refine ⟨18753113162739377219773909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25004150883652502959698545 18753113162739377219773909)
                  ·
                    refine ⟨439526089751704153588451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18753113162739377219773909 439526089751704153588451)
                    ·
                      rfl

theorem cell22_1283961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 7].length) (baseStart_1283961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1283961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1283961 prefixEnd_1283961 := by exact prefixLift 1283961
  have htrace : WordTrace (prefixWord ++ tailWord_1283961) baseStart_1283961 baseEnd_1283961 := by
    simpa [prefixWord, tailWord_1283961, baseEnd_1283961] using wordTrace_append hprefix tailTrace_1283961
  have hstable : (prefixWord ++ tailWord_1283961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283961).length < 2 ^ (prefixWord ++ tailWord_1283961).sum := by decide
  have hdescent : baseEnd_1283961 < baseStart_1283961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283969 : List Nat := [1, 2, 4, 4, 1, 2, 1, 3, 4]
def baseStart_1283969 : Nat := 118140960795 + 1283969 * 2 ^ 59
def prefixEnd_1283969 : Nat := 4983230072969 + 3 ^ 40 * 1283969 * 2
def baseEnd_1283969 : Nat := 146509609438398266462809

theorem tailTrace_1283969 : CollatzResearch.WordTrace tailWord_1283969 prefixEnd_1283969 146509609438398266462809 := by
  unfold tailWord_1283969
  simp only [CollatzResearch.WordTrace]
  refine ⟨46830196685407072292182961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31220131123604714861455307 46830196685407072292182961)
  ·
    refine ⟨35122647514055304219137221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46830196685407072292182961 35122647514055304219137221)
    ·
      refine ⟨6585496408885369541088229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35122647514055304219137221 6585496408885369541088229)
      ·
        refine ⟨1234780576666006788954043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6585496408885369541088229 1234780576666006788954043)
        ·
          refine ⟨1852170864999010183431065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1234780576666006788954043 1852170864999010183431065)
          ·
            refine ⟨1389128148749257637573299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1852170864999010183431065 1389128148749257637573299)
            ·
              refine ⟨2083692223123886456359949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1389128148749257637573299 2083692223123886456359949)
              ·
                refine ⟨781384583671457421134981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2083692223123886456359949 781384583671457421134981)
                ·
                  refine ⟨146509609438398266462809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 781384583671457421134981 146509609438398266462809)
                  ·
                    rfl

theorem cell22_1283969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 3, 4].length) (baseStart_1283969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1283969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1283969 prefixEnd_1283969 := by exact prefixLift 1283969
  have htrace : WordTrace (prefixWord ++ tailWord_1283969) baseStart_1283969 baseEnd_1283969 := by
    simpa [prefixWord, tailWord_1283969, baseEnd_1283969] using wordTrace_append hprefix tailTrace_1283969
  have hstable : (prefixWord ++ tailWord_1283969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283969).length < 2 ^ (prefixWord ++ tailWord_1283969).sum := by decide
  have hdescent : baseEnd_1283969 < baseStart_1283969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283982 : List Nat := [4, 1, 1, 5, 1, 1, 1, 2, 2, 4]
def baseStart_1283982 : Nat := 118140960795 + 1283982 * 2 ^ 59
def prefixEnd_1283982 : Nat := 4983230072969 + 3 ^ 40 * 1283982 * 2
def baseEnd_1283982 : Nat := 439533278480867098813387

theorem tailTrace_1283982 : CollatzResearch.WordTrace tailWord_1283982 prefixEnd_1283982 439533278480867098813387 := by
  unfold tailWord_1283982
  simp only [CollatzResearch.WordTrace]
  refine ⟨5853833854294996939050775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31220447222906650341604133 5853833854294996939050775)
  ·
    refine ⟨8780750781442495408576163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5853833854294996939050775 8780750781442495408576163)
    ·
      refine ⟨13171126172163743112864245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8780750781442495408576163 13171126172163743112864245)
      ·
        refine ⟨1234793078640350916831023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13171126172163743112864245 1234793078640350916831023)
        ·
          refine ⟨1852189617960526375246535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1234793078640350916831023 1852189617960526375246535)
          ·
            refine ⟨2778284426940789562869803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1852189617960526375246535 2778284426940789562869803)
            ·
              refine ⟨4167426640411184344304705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2778284426940789562869803 4167426640411184344304705)
              ·
                refine ⟨3125569980308388258228529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4167426640411184344304705 3125569980308388258228529)
                ·
                  refine ⟨2344177485231291193671397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3125569980308388258228529 2344177485231291193671397)
                  ·
                    refine ⟨439533278480867098813387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2344177485231291193671397 439533278480867098813387)
                    ·
                      rfl

theorem cell22_1283982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 2, 2, 4].length) (baseStart_1283982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1283982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1283982 prefixEnd_1283982 := by exact prefixLift 1283982
  have htrace : WordTrace (prefixWord ++ tailWord_1283982) baseStart_1283982 baseEnd_1283982 := by
    simpa [prefixWord, tailWord_1283982, baseEnd_1283982] using wordTrace_append hprefix tailTrace_1283982
  have hstable : (prefixWord ++ tailWord_1283982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283982).length < 2 ^ (prefixWord ++ tailWord_1283982).sum := by decide
  have hdescent : baseEnd_1283982 < baseStart_1283982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284001 : List Nat := [1, 2, 3, 4, 3, 1, 2, 1, 2, 3]
def baseStart_1284001 : Nat := 118140960795 + 1284001 * 2 ^ 59
def prefixEnd_1284001 : Nat := 4983230072969 + 3 ^ 40 * 1284001 * 2
def baseEnd_1284001 : Nat := 439539782569157382588329

theorem tailTrace_1284001 : CollatzResearch.WordTrace tailWord_1284001 prefixEnd_1284001 439539782569157382588329 := by
  unfold tailWord_1284001
  simp only [CollatzResearch.WordTrace]
  refine ⟨46831363821291141757347857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31220909214194094504898571 46831363821291141757347857)
  ·
    refine ⟨35123522865968356318010893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46831363821291141757347857 35123522865968356318010893)
    ·
      refine ⟨13171321074738133619254085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35123522865968356318010893 13171321074738133619254085)
      ·
        refine ⟨2469622701513400053610141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13171321074738133619254085 2469622701513400053610141)
        ·
          refine ⟨926108513067525020103803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2469622701513400053610141 926108513067525020103803)
          ·
            refine ⟨1389162769601287530155705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 926108513067525020103803 1389162769601287530155705)
            ·
              refine ⟨1041872077200965647616779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1389162769601287530155705 1041872077200965647616779)
              ·
                refine ⟨1562808115801448471425169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1041872077200965647616779 1562808115801448471425169)
                ·
                  refine ⟨1172106086851086353568877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1562808115801448471425169 1172106086851086353568877)
                  ·
                    refine ⟨439539782569157382588329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1172106086851086353568877 439539782569157382588329)
                    ·
                      rfl

theorem cell22_1284001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 2, 1, 2, 3].length) (baseStart_1284001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1284001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1284001 prefixEnd_1284001 := by exact prefixLift 1284001
  have htrace : WordTrace (prefixWord ++ tailWord_1284001) baseStart_1284001 baseEnd_1284001 := by
    simpa [prefixWord, tailWord_1284001, baseEnd_1284001] using wordTrace_append hprefix tailTrace_1284001
  have hstable : (prefixWord ++ tailWord_1284001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284001).length < 2 ^ (prefixWord ++ tailWord_1284001).sum := by decide
  have hdescent : baseEnd_1284001 < baseStart_1284001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284119 : List Nat := [1, 1, 3, 5, 3, 1, 1, 1, 1, 5]
def baseStart_1284119 : Nat := 118140960795 + 1284119 * 2 ^ 59
def prefixEnd_1284119 : Nat := 4983230072969 + 3 ^ 40 * 1284119 * 2
def baseEnd_1284119 : Nat := 439580176380644408137967

theorem tailTrace_1284119 : CollatzResearch.WordTrace tailWord_1284119 prefixEnd_1284119 439580176380644408137967 := by
  unfold tailWord_1284119
  simp only [CollatzResearch.WordTrace]
  refine ⟨46835667634863647910143411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31223778423242431940095607 46835667634863647910143411)
  ·
    refine ⟨70253501452295471865215117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46835667634863647910143411 70253501452295471865215117)
    ·
      refine ⟨26345063044610801949455669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70253501452295471865215117 26345063044610801949455669)
      ·
        refine ⟨2469849660432262682761469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26345063044610801949455669 2469849660432262682761469)
        ·
          refine ⟨926193622662098506035551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2469849660432262682761469 926193622662098506035551)
          ·
            refine ⟨1389290433993147759053327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 926193622662098506035551 1389290433993147759053327)
            ·
              refine ⟨2083935650989721638579991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1389290433993147759053327 2083935650989721638579991)
              ·
                refine ⟨3125903476484582457869987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2083935650989721638579991 3125903476484582457869987)
                ·
                  refine ⟨4688855214726873686804981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3125903476484582457869987 4688855214726873686804981)
                  ·
                    refine ⟨439580176380644408137967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4688855214726873686804981 439580176380644408137967)
                    ·
                      rfl

theorem cell22_1284119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 1, 1, 5].length) (baseStart_1284119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1284119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1284119 prefixEnd_1284119 := by exact prefixLift 1284119
  have htrace : WordTrace (prefixWord ++ tailWord_1284119) baseStart_1284119 baseEnd_1284119 := by
    simpa [prefixWord, tailWord_1284119, baseEnd_1284119] using wordTrace_append hprefix tailTrace_1284119
  have hstable : (prefixWord ++ tailWord_1284119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284119).length < 2 ^ (prefixWord ++ tailWord_1284119).sum := by decide
  have hdescent : baseEnd_1284119 < baseStart_1284119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284282 : List Nat := [3, 1, 1, 1, 2, 2, 3, 3, 3, 3]
def baseStart_1284282 : Nat := 118140960795 + 1284282 * 2 ^ 59
def prefixEnd_1284282 : Nat := 4983230072969 + 3 ^ 40 * 1284282 * 2
def baseEnd_1284282 : Nat := 439635974611766316312467

theorem tailTrace_1284282 : CollatzResearch.WordTrace tailWord_1284282 prefixEnd_1284282 439635974611766316312467 := by
  unfold tailWord_1284282
  simp only [CollatzResearch.WordTrace]
  refine ⟨11710403183318281687081775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31227741822182084498884733 11710403183318281687081775)
  ·
    refine ⟨17565604774977422530622663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11710403183318281687081775 17565604774977422530622663)
    ·
      refine ⟨26348407162466133795933995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17565604774977422530622663 26348407162466133795933995)
      ·
        refine ⟨39522610743699200693900993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26348407162466133795933995 39522610743699200693900993)
        ·
          refine ⟨29641958057774400520425745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39522610743699200693900993 29641958057774400520425745)
          ·
            refine ⟨22231468543330800390319309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29641958057774400520425745 22231468543330800390319309)
            ·
              refine ⟨8336800703749050146369741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22231468543330800390319309 8336800703749050146369741)
              ·
                refine ⟨3126300263905893804888653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8336800703749050146369741 3126300263905893804888653)
                ·
                  refine ⟨1172362598964710176833245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3126300263905893804888653 1172362598964710176833245)
                  ·
                    refine ⟨439635974611766316312467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1172362598964710176833245 439635974611766316312467)
                    ·
                      rfl

theorem cell22_1284282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 3, 3, 3].length) (baseStart_1284282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1284282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1284282 prefixEnd_1284282 := by exact prefixLift 1284282
  have htrace : WordTrace (prefixWord ++ tailWord_1284282) baseStart_1284282 baseEnd_1284282 := by
    simpa [prefixWord, tailWord_1284282, baseEnd_1284282] using wordTrace_append hprefix tailTrace_1284282
  have hstable : (prefixWord ++ tailWord_1284282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284282).length < 2 ^ (prefixWord ++ tailWord_1284282).sum := by decide
  have hdescent : baseEnd_1284282 < baseStart_1284282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284333 : List Nat := [1, 5, 1, 2, 4, 1, 1, 1, 3, 3]
def baseStart_1284333 : Nat := 118140960795 + 1284333 * 2 ^ 59
def prefixEnd_1284333 : Nat := 4983230072969 + 3 ^ 40 * 1284333 * 2
def baseEnd_1284333 : Nat := 439653432954019183287311

theorem tailTrace_1284333 : CollatzResearch.WordTrace tailWord_1284333 prefixEnd_1284333 439653432954019183287311 := by
  unfold tailWord_1284333
  simp only [CollatzResearch.WordTrace]
  refine ⟨46843472856088362458433653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31228981904058908305622435 46843472856088362458433653)
  ·
    refine ⟨4391575580258283980478155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46843472856088362458433653 4391575580258283980478155)
    ·
      refine ⟨6587363370387425970717233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4391575580258283980478155 6587363370387425970717233)
      ·
        refine ⟨4940522527790569478037925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6587363370387425970717233 4940522527790569478037925)
        ·
          refine ⟨926347973960731777132111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4940522527790569478037925 926347973960731777132111)
          ·
            refine ⟨1389521960941097665698167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 926347973960731777132111 1389521960941097665698167)
            ·
              refine ⟨2084282941411646498547251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1389521960941097665698167 2084282941411646498547251)
              ·
                refine ⟨3126424412117469747820877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2084282941411646498547251 3126424412117469747820877)
                ·
                  refine ⟨1172409154544051155432829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3126424412117469747820877 1172409154544051155432829)
                  ·
                    refine ⟨439653432954019183287311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1172409154544051155432829 439653432954019183287311)
                    ·
                      rfl

theorem cell22_1284333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 1, 3, 3].length) (baseStart_1284333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1284333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1284333 prefixEnd_1284333 := by exact prefixLift 1284333
  have htrace : WordTrace (prefixWord ++ tailWord_1284333) baseStart_1284333 baseEnd_1284333 := by
    simpa [prefixWord, tailWord_1284333, baseEnd_1284333] using wordTrace_append hprefix tailTrace_1284333
  have hstable : (prefixWord ++ tailWord_1284333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284333).length < 2 ^ (prefixWord ++ tailWord_1284333).sum := by decide
  have hdescent : baseEnd_1284333 < baseStart_1284333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284387 : List Nat := [1, 1, 1, 4, 2, 2, 1, 4, 2, 4]
def baseStart_1284387 : Nat := 118140960795 + 1284387 * 2 ^ 59
def prefixEnd_1284387 : Nat := 4983230072969 + 3 ^ 40 * 1284387 * 2
def baseEnd_1284387 : Nat := 439671918257581042437145

theorem tailTrace_1284387 : CollatzResearch.WordTrace tailWord_1284387 prefixEnd_1284387 439671918257581042437145 := by
  unfold tailWord_1284387
  simp only [CollatzResearch.WordTrace]
  refine ⟨46845442397892729680899415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31230294931928486453932943 46845442397892729680899415)
  ·
    refine ⟨70268163596839094521349123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46845442397892729680899415 70268163596839094521349123)
    ·
      refine ⟨105402245395258641782023685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70268163596839094521349123 105402245395258641782023685)
      ·
        refine ⟨19762921011610995334129441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 105402245395258641782023685 19762921011610995334129441)
        ·
          refine ⟨14822190758708246500597081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19762921011610995334129441 14822190758708246500597081)
          ·
            refine ⟨11116643069031184875447811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14822190758708246500597081 11116643069031184875447811)
            ·
              refine ⟨16674964603546777313171717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11116643069031184875447811 16674964603546777313171717)
              ·
                refine ⟨3126555863165020746219697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16674964603546777313171717 3126555863165020746219697)
                ·
                  refine ⟨2344916897373765559664773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3126555863165020746219697 2344916897373765559664773)
                  ·
                    refine ⟨439671918257581042437145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2344916897373765559664773 439671918257581042437145)
                    ·
                      rfl

theorem cell22_1284387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 4, 2, 4].length) (baseStart_1284387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1284387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1284387 prefixEnd_1284387 := by exact prefixLift 1284387
  have htrace : WordTrace (prefixWord ++ tailWord_1284387) baseStart_1284387 baseEnd_1284387 := by
    simpa [prefixWord, tailWord_1284387, baseEnd_1284387] using wordTrace_append hprefix tailTrace_1284387
  have hstable : (prefixWord ++ tailWord_1284387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284387).length < 2 ^ (prefixWord ++ tailWord_1284387).sum := by decide
  have hdescent : baseEnd_1284387 < baseStart_1284387 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284451 : List Nat := [1, 1, 1, 5, 2, 1, 1, 6, 1, 3]
def baseStart_1284451 : Nat := 118140960795 + 1284451 * 2 ^ 59
def prefixEnd_1284451 : Nat := 4983230072969 + 3 ^ 40 * 1284451 * 2
def baseEnd_1284451 : Nat := 439693826765506208836949

theorem tailTrace_1284451 : CollatzResearch.WordTrace tailWord_1284451 prefixEnd_1284451 439693826765506208836949 := by
  unfold tailWord_1284451
  simp only [CollatzResearch.WordTrace]
  refine ⟨46847776669660868611229207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31231851113107245740819471 46847776669660868611229207)
  ·
    refine ⟨70271665004491302916843811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46847776669660868611229207 70271665004491302916843811)
    ·
      refine ⟨105407497506736954375265717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70271665004491302916843811 105407497506736954375265717)
      ·
        refine ⟨9881952891256589472681161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 105407497506736954375265717 9881952891256589472681161)
        ·
          refine ⟨7411464668442442104510871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9881952891256589472681161 7411464668442442104510871)
          ·
            refine ⟨11117197002663663156766307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7411464668442442104510871 11117197002663663156766307)
            ·
              refine ⟨16675795503995494735149461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11117197002663663156766307 16675795503995494735149461)
              ·
                refine ⟨781677914249788815710131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16675795503995494735149461 781677914249788815710131)
                ·
                  refine ⟨1172516871374683223565197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 781677914249788815710131 1172516871374683223565197)
                  ·
                    refine ⟨439693826765506208836949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1172516871374683223565197 439693826765506208836949)
                    ·
                      rfl

theorem cell22_1284451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 6, 1, 3].length) (baseStart_1284451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1284451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1284451 prefixEnd_1284451 := by exact prefixLift 1284451
  have htrace : WordTrace (prefixWord ++ tailWord_1284451) baseStart_1284451 baseEnd_1284451 := by
    simpa [prefixWord, tailWord_1284451, baseEnd_1284451] using wordTrace_append hprefix tailTrace_1284451
  have hstable : (prefixWord ++ tailWord_1284451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284451).length < 2 ^ (prefixWord ++ tailWord_1284451).sum := by decide
  have hdescent : baseEnd_1284451 < baseStart_1284451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284470 : List Nat := [5, 1, 1, 4, 2, 1, 2, 6]
def baseStart_1284470 : Nat := 118140960795 + 1284470 * 2 ^ 59
def prefixEnd_1284470 : Nat := 4983230072969 + 3 ^ 40 * 1284470 * 2
def baseEnd_1284470 : Nat := 48855592317088499179099

theorem tailTrace_1284470 : CollatzResearch.WordTrace tailWord_1284470 prefixEnd_1284470 48855592317088499179099 := by
  unfold tailWord_1284470
  simp only [CollatzResearch.WordTrace]
  refine ⟨2928029353537002178510679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31232313104394689904113909 2928029353537002178510679)
  ·
    refine ⟨4392044030305503267766019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2928029353537002178510679 4392044030305503267766019)
    ·
      refine ⟨6588066045458254901649029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4392044030305503267766019 6588066045458254901649029)
      ·
        refine ⟨1235262383523422794059193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6588066045458254901649029 1235262383523422794059193)
        ·
          refine ⟨926446787642567095544395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1235262383523422794059193 926446787642567095544395)
          ·
            refine ⟨1389670181463850643316593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 926446787642567095544395 1389670181463850643316593)
            ·
              refine ⟨1042252636097887982487445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1389670181463850643316593 1042252636097887982487445)
              ·
                refine ⟨48855592317088499179099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1042252636097887982487445 48855592317088499179099)
                ·
                  rfl

theorem cell22_1284470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 2, 6].length) (baseStart_1284470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1284470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1284470 prefixEnd_1284470 := by exact prefixLift 1284470
  have htrace : WordTrace (prefixWord ++ tailWord_1284470) baseStart_1284470 baseEnd_1284470 := by
    simpa [prefixWord, tailWord_1284470, baseEnd_1284470] using wordTrace_append hprefix tailTrace_1284470
  have hstable : (prefixWord ++ tailWord_1284470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284470).length < 2 ^ (prefixWord ++ tailWord_1284470).sum := by decide
  have hdescent : baseEnd_1284470 < baseStart_1284470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284586 : List Nat := [3, 1, 3, 1, 3, 1, 1, 1, 5, 3]
def baseStart_1284586 : Nat := 118140960795 + 1284586 * 2 ^ 59
def prefixEnd_1284586 : Nat := 4983230072969 + 3 ^ 40 * 1284586 * 2
def baseEnd_1284586 : Nat := 439740040024410856711535

theorem tailTrace_1284586 : CollatzResearch.WordTrace tailWord_1284586 prefixEnd_1284586 439740040024410856711535 := by
  unfold tailWord_1284586
  simp only [CollatzResearch.WordTrace]
  refine ⟨11713175131042946666848403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31235133682781191111595741 11713175131042946666848403)
  ·
    refine ⟨17569762696564420000272605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11713175131042946666848403 17569762696564420000272605)
    ·
      refine ⟨6588661011211657500102227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17569762696564420000272605 6588661011211657500102227)
      ·
        refine ⟨9882991516817486250153341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6588661011211657500102227 9882991516817486250153341)
        ·
          refine ⟨3706121818806557343807503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9882991516817486250153341 3706121818806557343807503)
          ·
            refine ⟨5559182728209836015711255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3706121818806557343807503 5559182728209836015711255)
            ·
              refine ⟨8338774092314754023566883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5559182728209836015711255 8338774092314754023566883)
              ·
                refine ⟨12508161138472131035350325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8338774092314754023566883 12508161138472131035350325)
                ·
                  refine ⟨1172640106731762284564093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12508161138472131035350325 1172640106731762284564093)
                  ·
                    refine ⟨439740040024410856711535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1172640106731762284564093 439740040024410856711535)
                    ·
                      rfl

theorem cell22_1284586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 5, 3].length) (baseStart_1284586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1284586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1284586 prefixEnd_1284586 := by exact prefixLift 1284586
  have htrace : WordTrace (prefixWord ++ tailWord_1284586) baseStart_1284586 baseEnd_1284586 := by
    simpa [prefixWord, tailWord_1284586, baseEnd_1284586] using wordTrace_append hprefix tailTrace_1284586
  have hstable : (prefixWord ++ tailWord_1284586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284586).length < 2 ^ (prefixWord ++ tailWord_1284586).sum := by decide
  have hdescent : baseEnd_1284586 < baseStart_1284586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284654 : List Nat := [4, 1, 3, 1, 4, 1, 1, 3, 1, 3]
def baseStart_1284654 : Nat := 118140960795 + 1284654 * 2 ^ 59
def prefixEnd_1284654 : Nat := 4983230072969 + 3 ^ 40 * 1284654 * 2
def baseEnd_1284654 : Nat := 439763317814081346011327

theorem tailTrace_1284654 : CollatzResearch.WordTrace tailWord_1284654 prefixEnd_1284654 439763317814081346011327 := by
  unfold tailWord_1284654
  simp only [CollatzResearch.WordTrace]
  refine ⟨5856897585990679285108627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31236787125283622853912677 5856897585990679285108627)
  ·
    refine ⟨8785346378986018927662941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5856897585990679285108627 8785346378986018927662941)
    ·
      refine ⟨3294504892119757097873603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8785346378986018927662941 3294504892119757097873603)
      ·
        refine ⟨4941757338179635646810405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3294504892119757097873603 4941757338179635646810405)
        ·
          refine ⟨926579500908681683776951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4941757338179635646810405 926579500908681683776951)
          ·
            refine ⟨1389869251363022525665427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 926579500908681683776951 1389869251363022525665427)
            ·
              refine ⟨2084803877044533788498141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1389869251363022525665427 2084803877044533788498141)
              ·
                refine ⟨781801453891700170686803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2084803877044533788498141 781801453891700170686803)
                ·
                  refine ⟨1172702180837550256030205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 781801453891700170686803 1172702180837550256030205)
                  ·
                    refine ⟨439763317814081346011327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1172702180837550256030205 439763317814081346011327)
                    ·
                      rfl

theorem cell22_1284654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_1284654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1284654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1284654 prefixEnd_1284654 := by exact prefixLift 1284654
  have htrace : WordTrace (prefixWord ++ tailWord_1284654) baseStart_1284654 baseEnd_1284654 := by
    simpa [prefixWord, tailWord_1284654, baseEnd_1284654] using wordTrace_append hprefix tailTrace_1284654
  have hstable : (prefixWord ++ tailWord_1284654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284654).length < 2 ^ (prefixWord ++ tailWord_1284654).sum := by decide
  have hdescent : baseEnd_1284654 < baseStart_1284654 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284659 : List Nat := [1, 1, 1, 2, 4, 2, 2, 1, 3, 5]
def baseStart_1284659 : Nat := 118140960795 + 1284659 * 2 ^ 59
def prefixEnd_1284659 : Nat := 4983230072969 + 3 ^ 40 * 1284659 * 2
def baseEnd_1284659 : Nat := 439765029416262999636311

theorem tailTrace_1284659 : CollatzResearch.WordTrace tailWord_1284659 prefixEnd_1284659 439765029416262999636311 := by
  unfold tailWord_1284659
  simp only [CollatzResearch.WordTrace]
  refine ⟨46855363052907320134801031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31236908701938213423200687 46855363052907320134801031)
  ·
    refine ⟨70283044579360980202201547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46855363052907320134801031 70283044579360980202201547)
    ·
      refine ⟨105424566869041470303302321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70283044579360980202201547 105424566869041470303302321)
      ·
        refine ⟨79068425151781102727476741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105424566869041470303302321 79068425151781102727476741)
        ·
          refine ⟨14825329715958956761401889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79068425151781102727476741 14825329715958956761401889)
          ·
            refine ⟨11118997286969217571051417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14825329715958956761401889 11118997286969217571051417)
            ·
              refine ⟨8339247965226913178288563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11118997286969217571051417 8339247965226913178288563)
              ·
                refine ⟨12508871947840369767432845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8339247965226913178288563 12508871947840369767432845)
                ·
                  refine ⟨4690826980440138662787317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12508871947840369767432845 4690826980440138662787317)
                  ·
                    refine ⟨439765029416262999636311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4690826980440138662787317 439765029416262999636311)
                    ·
                      rfl

theorem cell22_1284659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 3, 5].length) (baseStart_1284659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1284659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1284659 prefixEnd_1284659 := by exact prefixLift 1284659
  have htrace : WordTrace (prefixWord ++ tailWord_1284659) baseStart_1284659 baseEnd_1284659 := by
    simpa [prefixWord, tailWord_1284659, baseEnd_1284659] using wordTrace_append hprefix tailTrace_1284659
  have hstable : (prefixWord ++ tailWord_1284659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284659).length < 2 ^ (prefixWord ++ tailWord_1284659).sum := by decide
  have hdescent : baseEnd_1284659 < baseStart_1284659 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284689 : List Nat := [1, 2, 2, 1, 3, 3, 1, 9]
def baseStart_1284689 : Nat := 118140960795 + 1284689 * 2 ^ 59
def prefixEnd_1284689 : Nat := 4983230072969 + 3 ^ 40 * 1284689 * 2
def baseEnd_1284689 : Nat := 48863922114372546820691

theorem tailTrace_1284689 : CollatzResearch.WordTrace tailWord_1284689 prefixEnd_1284689 48863922114372546820691 := by
  unfold tailWord_1284689
  simp only [CollatzResearch.WordTrace]
  refine ⟨46856457242798635258393121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31237638161865756838928747 46856457242798635258393121)
  ·
    refine ⟨35142342932098976443794841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46856457242798635258393121 35142342932098976443794841)
    ·
      refine ⟨26356757199074232332846131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35142342932098976443794841 26356757199074232332846131)
      ·
        refine ⟨39535135798611348499269197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26356757199074232332846131 39535135798611348499269197)
        ·
          refine ⟨14825675924479255687225949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39535135798611348499269197 14825675924479255687225949)
          ·
            refine ⟨5559628471679720882709731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14825675924479255687225949 5559628471679720882709731)
            ·
              refine ⟨8339442707519581324064597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5559628471679720882709731 8339442707519581324064597)
              ·
                refine ⟨48863922114372546820691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8339442707519581324064597 48863922114372546820691)
                ·
                  rfl

theorem cell22_1284689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 9].length) (baseStart_1284689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1284689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1284689 prefixEnd_1284689 := by exact prefixLift 1284689
  have htrace : WordTrace (prefixWord ++ tailWord_1284689) baseStart_1284689 baseEnd_1284689 := by
    simpa [prefixWord, tailWord_1284689, baseEnd_1284689] using wordTrace_append hprefix tailTrace_1284689
  have hstable : (prefixWord ++ tailWord_1284689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284689).length < 2 ^ (prefixWord ++ tailWord_1284689).sum := by decide
  have hdescent : baseEnd_1284689 < baseStart_1284689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284704 : List Nat := [2, 1, 1, 3, 2, 1, 2, 1, 2, 7]
def baseStart_1284704 : Nat := 118140960795 + 1284704 * 2 ^ 59
def prefixEnd_1284704 : Nat := 4983230072969 + 3 ^ 40 * 1284704 * 2
def baseEnd_1284704 : Nat := 439780433835897882261173

theorem tailTrace_1284704 : CollatzResearch.WordTrace tailWord_1284704 prefixEnd_1284704 439780433835897882261173 := by
  unfold tailWord_1284704
  simp only [CollatzResearch.WordTrace]
  refine ⟨23428502168872146410094583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31238002891829528546792777 23428502168872146410094583)
  ·
    refine ⟨35142753253308219615141875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23428502168872146410094583 35142753253308219615141875)
    ·
      refine ⟨52714129879962329422712813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35142753253308219615141875 52714129879962329422712813)
      ·
        refine ⟨19767798704985873533517305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52714129879962329422712813 19767798704985873533517305)
        ·
          refine ⟨14825849028739405150137979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19767798704985873533517305 14825849028739405150137979)
          ·
            refine ⟨22238773543109107725206969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14825849028739405150137979 22238773543109107725206969)
            ·
              refine ⟨16679080157331830793905227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22238773543109107725206969 16679080157331830793905227)
              ·
                refine ⟨25018620235997746190857841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16679080157331830793905227 25018620235997746190857841)
                ·
                  refine ⟨18763965176998309643143381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25018620235997746190857841 18763965176998309643143381)
                  ·
                    refine ⟨439780433835897882261173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18763965176998309643143381 439780433835897882261173)
                    ·
                      rfl

theorem cell22_1284704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 2, 7].length) (baseStart_1284704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1284704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1284704 prefixEnd_1284704 := by exact prefixLift 1284704
  have htrace : WordTrace (prefixWord ++ tailWord_1284704) baseStart_1284704 baseEnd_1284704 := by
    simpa [prefixWord, tailWord_1284704, baseEnd_1284704] using wordTrace_append hprefix tailTrace_1284704
  have hstable : (prefixWord ++ tailWord_1284704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284704).length < 2 ^ (prefixWord ++ tailWord_1284704).sum := by decide
  have hdescent : baseEnd_1284704 < baseStart_1284704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284826 : List Nat := [3, 1, 1, 2, 2, 2, 1, 3, 1, 6]
def baseStart_1284826 : Nat := 118140960795 + 1284826 * 2 ^ 59
def prefixEnd_1284826 : Nat := 4983230072969 + 3 ^ 40 * 1284826 * 2
def baseEnd_1284826 : Nat := 439822196929130230710799

theorem tailTrace_1284826 : CollatzResearch.WordTrace tailWord_1284826 prefixEnd_1284826 439822196929130230710799 := by
  unfold tailWord_1284826
  simp only [CollatzResearch.WordTrace]
  refine ⟨11715363510825576914032583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31240969362201538437420221 11715363510825576914032583)
  ·
    refine ⟨17573045266238365371048875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11715363510825576914032583 17573045266238365371048875)
    ·
      refine ⟨26359567899357548056573313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17573045266238365371048875 26359567899357548056573313)
      ·
        refine ⟨19769675924518161042429985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26359567899357548056573313 19769675924518161042429985)
        ·
          refine ⟨14827256943388620781822489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19769675924518161042429985 14827256943388620781822489)
          ·
            refine ⟨11120442707541465586366867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14827256943388620781822489 11120442707541465586366867)
            ·
              refine ⟨16680664061312198379550301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11120442707541465586366867 16680664061312198379550301)
              ·
                refine ⟨6255249022992074392331363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16680664061312198379550301 6255249022992074392331363)
                ·
                  refine ⟨9382873534488111588497045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6255249022992074392331363 9382873534488111588497045)
                  ·
                    refine ⟨439822196929130230710799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9382873534488111588497045 439822196929130230710799)
                    ·
                      rfl

theorem cell22_1284826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 3, 1, 6].length) (baseStart_1284826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1284826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1284826 prefixEnd_1284826 := by exact prefixLift 1284826
  have htrace : WordTrace (prefixWord ++ tailWord_1284826) baseStart_1284826 baseEnd_1284826 := by
    simpa [prefixWord, tailWord_1284826, baseEnd_1284826] using wordTrace_append hprefix tailTrace_1284826
  have hstable : (prefixWord ++ tailWord_1284826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284826).length < 2 ^ (prefixWord ++ tailWord_1284826).sum := by decide
  have hdescent : baseEnd_1284826 < baseStart_1284826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284845 : List Nat := [1, 5, 1, 2, 1, 1, 2, 4, 2, 3]
def baseStart_1284845 : Nat := 118140960795 + 1284845 * 2 ^ 59
def prefixEnd_1284845 : Nat := 4983230072969 + 3 ^ 40 * 1284845 * 2
def baseEnd_1284845 : Nat := 439828701017420514485741

theorem tailTrace_1284845 : CollatzResearch.WordTrace tailWord_1284845 prefixEnd_1284845 439828701017420514485741 := by
  unfold tailWord_1284845
  simp only [CollatzResearch.WordTrace]
  refine ⟨46862147030233473901071989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31241431353488982600714659 46862147030233473901071989)
  ·
    refine ⟨4393326284084388178225499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46862147030233473901071989 4393326284084388178225499)
    ·
      refine ⟨6589989426126582267338249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4393326284084388178225499 6589989426126582267338249)
      ·
        refine ⟨4942492069594936700503687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6589989426126582267338249 4942492069594936700503687)
        ·
          refine ⟨7413738104392405050755531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4942492069594936700503687 7413738104392405050755531)
          ·
            refine ⟨11120607156588607576133297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7413738104392405050755531 11120607156588607576133297)
            ·
              refine ⟨8340455367441455682099973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11120607156588607576133297 8340455367441455682099973)
              ·
                refine ⟨1563835381395272940393745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8340455367441455682099973 1563835381395272940393745)
                ·
                  refine ⟨1172876536046454705295309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1563835381395272940393745 1172876536046454705295309)
                  ·
                    refine ⟨439828701017420514485741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1172876536046454705295309 439828701017420514485741)
                    ·
                      rfl

theorem cell22_1284845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 4, 2, 3].length) (baseStart_1284845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1284845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1284845 prefixEnd_1284845 := by exact prefixLift 1284845
  have htrace : WordTrace (prefixWord ++ tailWord_1284845) baseStart_1284845 baseEnd_1284845 := by
    simpa [prefixWord, tailWord_1284845, baseEnd_1284845] using wordTrace_append hprefix tailTrace_1284845
  have hstable : (prefixWord ++ tailWord_1284845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284845).length < 2 ^ (prefixWord ++ tailWord_1284845).sum := by decide
  have hdescent : baseEnd_1284845 < baseStart_1284845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284862 : List Nat := [4, 2, 2, 1, 2, 2, 1, 3, 2, 3]
def baseStart_1284862 : Nat := 118140960795 + 1284862 * 2 ^ 59
def prefixEnd_1284862 : Nat := 4983230072969 + 3 ^ 40 * 1284862 * 2
def baseEnd_1284862 : Nat := 439834520464838136810689

theorem tailTrace_1284862 : CollatzResearch.WordTrace tailWord_1284862 prefixEnd_1284862 439834520464838136810689 := by
  unfold tailWord_1284862
  simp only [CollatzResearch.WordTrace]
  refine ⟨5857845883896485725555105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31241844714114590536293893 5857845883896485725555105)
  ·
    refine ⟨4393384412922364294166329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5857845883896485725555105 4393384412922364294166329)
    ·
      refine ⟨3295038309691773220624747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4393384412922364294166329 3295038309691773220624747)
      ·
        refine ⟨4942557464537659830937121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3295038309691773220624747 4942557464537659830937121)
        ·
          refine ⟨3706918098403244873202841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4942557464537659830937121 3706918098403244873202841)
          ·
            refine ⟨2780188573802433654902131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3706918098403244873202841 2780188573802433654902131)
            ·
              refine ⟨4170282860703650482353197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2780188573802433654902131 4170282860703650482353197)
              ·
                refine ⟨1563856072763868930882449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4170282860703650482353197 1563856072763868930882449)
                ·
                  refine ⟨1172892054572901698161837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1563856072763868930882449 1172892054572901698161837)
                  ·
                    refine ⟨439834520464838136810689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1172892054572901698161837 439834520464838136810689)
                    ·
                      rfl

theorem cell22_1284862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_1284862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1284862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1284862 prefixEnd_1284862 := by exact prefixLift 1284862
  have htrace : WordTrace (prefixWord ++ tailWord_1284862) baseStart_1284862 baseEnd_1284862 := by
    simpa [prefixWord, tailWord_1284862, baseEnd_1284862] using wordTrace_append hprefix tailTrace_1284862
  have hstable : (prefixWord ++ tailWord_1284862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284862).length < 2 ^ (prefixWord ++ tailWord_1284862).sum := by decide
  have hdescent : baseEnd_1284862 < baseStart_1284862 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284873 : List Nat := [1, 2, 1, 1, 3, 2, 2, 4, 3, 3]
def baseStart_1284873 : Nat := 118140960795 + 1284873 * 2 ^ 59
def prefixEnd_1284873 : Nat := 4983230072969 + 3 ^ 40 * 1284873 * 2
def baseEnd_1284873 : Nat := 439838285989637774785655

theorem tailTrace_1284873 : CollatzResearch.WordTrace tailWord_1284873 prefixEnd_1284873 439838285989637774785655 := by
  unfold tailWord_1284873
  simp only [CollatzResearch.WordTrace]
  refine ⟨46863168274132034683091273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31242112182754689788727515 46863168274132034683091273)
  ·
    refine ⟨35147376205599026012318455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46863168274132034683091273 35147376205599026012318455)
    ·
      refine ⟨52721064308398539018477683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35147376205599026012318455 52721064308398539018477683)
      ·
        refine ⟨79081596462597808527716525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52721064308398539018477683 79081596462597808527716525)
        ·
          refine ⟨29655598673474178197893697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79081596462597808527716525 29655598673474178197893697)
          ·
            refine ⟨22241699005105633648420273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29655598673474178197893697 22241699005105633648420273)
            ·
              refine ⟨16681274253829225236315205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22241699005105633648420273 16681274253829225236315205)
              ·
                refine ⟨3127738922592979731809101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16681274253829225236315205 3127738922592979731809101)
                ·
                  refine ⟨1172902095972367399428413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3127738922592979731809101 1172902095972367399428413)
                  ·
                    refine ⟨439838285989637774785655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1172902095972367399428413 439838285989637774785655)
                    ·
                      rfl

theorem cell22_1284873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 4, 3, 3].length) (baseStart_1284873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1284873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1284873 prefixEnd_1284873 := by exact prefixLift 1284873
  have htrace : WordTrace (prefixWord ++ tailWord_1284873) baseStart_1284873 baseEnd_1284873 := by
    simpa [prefixWord, tailWord_1284873, baseEnd_1284873] using wordTrace_append hprefix tailTrace_1284873
  have hstable : (prefixWord ++ tailWord_1284873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284873).length < 2 ^ (prefixWord ++ tailWord_1284873).sum := by decide
  have hdescent : baseEnd_1284873 < baseStart_1284873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284909 : List Nat := [1, 5, 3, 2, 2, 1, 1, 7]
def baseStart_1284909 : Nat := 118140960795 + 1284909 * 2 ^ 59
def prefixEnd_1284909 : Nat := 4983230072969 + 3 ^ 40 * 1284909 * 2
def baseEnd_1284909 : Nat := 48872289947260631209505

theorem tailTrace_1284909 : CollatzResearch.WordTrace tailWord_1284909 prefixEnd_1284909 48872289947260631209505 := by
  unfold tailWord_1284909
  simp only [CollatzResearch.WordTrace]
  refine ⟨46864481302001612831401781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31242987534667741887601187 46864481302001612831401781)
  ·
    refine ⟨4393545122062651202943917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46864481302001612831401781 4393545122062651202943917)
    ·
      refine ⟨1647579420773494201103969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4393545122062651202943917 1647579420773494201103969)
      ·
        refine ⟨1235684565580120650827977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1647579420773494201103969 1235684565580120650827977)
        ·
          refine ⟨926763424185090488120983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1235684565580120650827977 926763424185090488120983)
          ·
            refine ⟨1390145136277635732181475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 926763424185090488120983 1390145136277635732181475)
            ·
              refine ⟨2085217704416453598272213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1390145136277635732181475 2085217704416453598272213)
              ·
                refine ⟨48872289947260631209505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2085217704416453598272213 48872289947260631209505)
                ·
                  rfl

theorem cell22_1284909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 7].length) (baseStart_1284909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1284909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1284909 prefixEnd_1284909 := by exact prefixLift 1284909
  have htrace : WordTrace (prefixWord ++ tailWord_1284909) baseStart_1284909 baseEnd_1284909 := by
    simpa [prefixWord, tailWord_1284909, baseEnd_1284909] using wordTrace_append hprefix tailTrace_1284909
  have hstable : (prefixWord ++ tailWord_1284909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284909).length < 2 ^ (prefixWord ++ tailWord_1284909).sum := by decide
  have hdescent : baseEnd_1284909 < baseStart_1284909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284941 : List Nat := [1, 6, 1, 2, 2, 1, 2, 3, 1, 3]
def baseStart_1284941 : Nat := 118140960795 + 1284941 * 2 ^ 59
def prefixEnd_1284941 : Nat := 4983230072969 + 3 ^ 40 * 1284941 * 2
def baseEnd_1284941 : Nat := 439861563779308264085447

theorem tailTrace_1284941 : CollatzResearch.WordTrace tailWord_1284941 prefixEnd_1284941 439861563779308264085447 := by
  unfold tailWord_1284941
  simp only [CollatzResearch.WordTrace]
  refine ⟨46865648437885682296566677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31243765625257121531044451 46865648437885682296566677)
  ·
    refine ⟨2196827270525891357651563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 46865648437885682296566677 2196827270525891357651563)
    ·
      refine ⟨3295240905788837036477345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2196827270525891357651563 3295240905788837036477345)
      ·
        refine ⟨2471430679341627777358009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3295240905788837036477345 2471430679341627777358009)
        ·
          refine ⟨1853573009506220833018507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2471430679341627777358009 1853573009506220833018507)
          ·
            refine ⟨2780359514259331249527761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1853573009506220833018507 2780359514259331249527761)
            ·
              refine ⟨2085269635694498437145821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2780359514259331249527761 2085269635694498437145821)
              ·
                refine ⟨781976113385436913929683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2085269635694498437145821 781976113385436913929683)
                ·
                  refine ⟨1172964170078155370894525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 781976113385436913929683 1172964170078155370894525)
                  ·
                    refine ⟨439861563779308264085447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1172964170078155370894525 439861563779308264085447)
                    ·
                      rfl

theorem cell22_1284941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_1284941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1284941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1284941 prefixEnd_1284941 := by exact prefixLift 1284941
  have htrace : WordTrace (prefixWord ++ tailWord_1284941) baseStart_1284941 baseEnd_1284941 := by
    simpa [prefixWord, tailWord_1284941, baseEnd_1284941] using wordTrace_append hprefix tailTrace_1284941
  have hstable : (prefixWord ++ tailWord_1284941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284941).length < 2 ^ (prefixWord ++ tailWord_1284941).sum := by decide
  have hdescent : baseEnd_1284941 < baseStart_1284941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284965 : List Nat := [1, 3, 1, 3, 1, 1, 4, 4, 4]
def baseStart_1284965 : Nat := 118140960795 + 1284965 * 2 ^ 59
def prefixEnd_1284965 : Nat := 4983230072969 + 3 ^ 40 * 1284965 * 2
def baseEnd_1284965 : Nat := 146623259823260067161791

theorem tailTrace_1284965 : CollatzResearch.WordTrace tailWord_1284965 prefixEnd_1284965 146623259823260067161791 := by
  unfold tailWord_1284965
  simp only [CollatzResearch.WordTrace]
  refine ⟨46866523789798734395440349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31244349193199156263626899 46866523789798734395440349)
  ·
    refine ⟨17574946421174525398290131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46866523789798734395440349 17574946421174525398290131)
    ·
      refine ⟨26362419631761788097435197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17574946421174525398290131 26362419631761788097435197)
      ·
        refine ⟨9885907361910670536538199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26362419631761788097435197 9885907361910670536538199)
        ·
          refine ⟨14828861042866005804807299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9885907361910670536538199 14828861042866005804807299)
          ·
            refine ⟨22243291564299008707210949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14828861042866005804807299 22243291564299008707210949)
            ·
              refine ⟨4170617168306064132602053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22243291564299008707210949 4170617168306064132602053)
              ·
                refine ⟨781990719057387024862885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4170617168306064132602053 781990719057387024862885)
                ·
                  refine ⟨146623259823260067161791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 781990719057387024862885 146623259823260067161791)
                  ·
                    rfl

theorem cell22_1284965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 4, 4].length) (baseStart_1284965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1284965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1284965 prefixEnd_1284965 := by exact prefixLift 1284965
  have htrace : WordTrace (prefixWord ++ tailWord_1284965) baseStart_1284965 baseEnd_1284965 := by
    simpa [prefixWord, tailWord_1284965, baseEnd_1284965] using wordTrace_append hprefix tailTrace_1284965
  have hstable : (prefixWord ++ tailWord_1284965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284965).length < 2 ^ (prefixWord ++ tailWord_1284965).sum := by decide
  have hdescent : baseEnd_1284965 < baseStart_1284965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284978 : List Nat := [3, 2, 1, 2, 1, 1, 3, 2, 1, 6]
def baseStart_1284978 : Nat := 118140960795 + 1284978 * 2 ^ 59
def prefixEnd_1284978 : Nat := 4983230072969 + 3 ^ 40 * 1284978 * 2
def baseEnd_1284978 : Nat := 439874229635452500910333

theorem tailTrace_1284978 : CollatzResearch.WordTrace tailWord_1284978 prefixEnd_1284978 439874229635452500910333 := by
  unfold tailWord_1284978
  simp only [CollatzResearch.WordTrace]
  refine ⟨11716749484687909403915897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31244665292501091743775725 11716749484687909403915897)
  ·
    refine ⟨8787562113515932052936923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11716749484687909403915897 8787562113515932052936923)
    ·
      refine ⟨13181343170273898079405385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8787562113515932052936923 13181343170273898079405385)
      ·
        refine ⟨9886007377705423559554039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13181343170273898079405385 9886007377705423559554039)
        ·
          refine ⟨14829011066558135339331059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9886007377705423559554039 14829011066558135339331059)
          ·
            refine ⟨22243516599837203008996589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14829011066558135339331059 22243516599837203008996589)
            ·
              refine ⟨8341318724938951128373721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22243516599837203008996589 8341318724938951128373721)
              ·
                refine ⟨6255989043704213346280291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8341318724938951128373721 6255989043704213346280291)
                ·
                  refine ⟨9383983565556320019420437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6255989043704213346280291 9383983565556320019420437)
                  ·
                    refine ⟨439874229635452500910333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9383983565556320019420437 439874229635452500910333)
                    ·
                      rfl

theorem cell22_1284978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 2, 1, 6].length) (baseStart_1284978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1284978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1284978 prefixEnd_1284978 := by exact prefixLift 1284978
  have htrace : WordTrace (prefixWord ++ tailWord_1284978) baseStart_1284978 baseEnd_1284978 := by
    simpa [prefixWord, tailWord_1284978, baseEnd_1284978] using wordTrace_append hprefix tailTrace_1284978
  have hstable : (prefixWord ++ tailWord_1284978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284978).length < 2 ^ (prefixWord ++ tailWord_1284978).sum := by decide
  have hdescent : baseEnd_1284978 < baseStart_1284978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285031 : List Nat := [1, 1, 6, 1, 3, 2, 2, 1, 2, 3]
def baseStart_1285031 : Nat := 118140960795 + 1285031 * 2 ^ 59
def prefixEnd_1285031 : Nat := 4983230072969 + 3 ^ 40 * 1285031 * 2
def baseEnd_1285031 : Nat := 439892372618578029335171

theorem tailTrace_1285031 : CollatzResearch.WordTrace tailWord_1285031 prefixEnd_1285031 439892372618578029335171 := by
  unfold tailWord_1285031
  simp only [CollatzResearch.WordTrace]
  refine ⟨46868931007559627667342947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31245954005039751778228631 46868931007559627667342947)
  ·
    refine ⟨70303396511339441501014421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46868931007559627667342947 70303396511339441501014421)
    ·
      refine ⟨3295471711469036320360051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 70303396511339441501014421 3295471711469036320360051)
      ·
        refine ⟨4943207567203554480540077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3295471711469036320360051 4943207567203554480540077)
        ·
          refine ⟨1853702837701332930202529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4943207567203554480540077 1853702837701332930202529)
          ·
            refine ⟨1390277128275999697651897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1853702837701332930202529 1390277128275999697651897)
            ·
              refine ⟨1042707846206999773238923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1390277128275999697651897 1042707846206999773238923)
              ·
                refine ⟨1564061769310499659858385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1042707846206999773238923 1564061769310499659858385)
                ·
                  refine ⟨1173046326982874744893789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1564061769310499659858385 1173046326982874744893789)
                  ·
                    refine ⟨439892372618578029335171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1173046326982874744893789 439892372618578029335171)
                    ·
                      rfl

theorem cell22_1285031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_1285031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1285031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1285031 prefixEnd_1285031 := by exact prefixLift 1285031
  have htrace : WordTrace (prefixWord ++ tailWord_1285031) baseStart_1285031 baseEnd_1285031 := by
    simpa [prefixWord, tailWord_1285031, baseEnd_1285031] using wordTrace_append hprefix tailTrace_1285031
  have hstable : (prefixWord ++ tailWord_1285031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285031).length < 2 ^ (prefixWord ++ tailWord_1285031).sum := by decide
  have hdescent : baseEnd_1285031 < baseStart_1285031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285076 : List Nat := [2, 4, 1, 2, 1, 2, 4, 2, 1, 3]
def baseStart_1285076 : Nat := 118140960795 + 1285076 * 2 ^ 59
def prefixEnd_1285076 : Nat := 4983230072969 + 3 ^ 40 * 1285076 * 2
def baseEnd_1285076 : Nat := 439907777038212911960033

theorem tailTrace_1285076 : CollatzResearch.WordTrace tailWord_1285076 prefixEnd_1285076 439907777038212911960033 := by
  unfold tailWord_1285076
  simp only [CollatzResearch.WordTrace]
  refine ⟨23435286146198300176365541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31247048194931066901820721 23435286146198300176365541)
  ·
    refine ⟨4394116152412181283068539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23435286146198300176365541 4394116152412181283068539)
    ·
      refine ⟨6591174228618271924602809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4394116152412181283068539 6591174228618271924602809)
      ·
        refine ⟨4943380671463703943452107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6591174228618271924602809 4943380671463703943452107)
        ·
          refine ⟨7415071007195555915178161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4943380671463703943452107 7415071007195555915178161)
          ·
            refine ⟨5561303255396666936383621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7415071007195555915178161 5561303255396666936383621)
            ·
              refine ⟨1042744360386875050571929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5561303255396666936383621 1042744360386875050571929)
              ·
                refine ⟨782058270290156287928947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1042744360386875050571929 782058270290156287928947)
                ·
                  refine ⟨1173087405435234431893421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 782058270290156287928947 1173087405435234431893421)
                  ·
                    refine ⟨439907777038212911960033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1173087405435234431893421 439907777038212911960033)
                    ·
                      rfl

theorem cell22_1285076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 4, 2, 1, 3].length) (baseStart_1285076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1285076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1285076 prefixEnd_1285076 := by exact prefixLift 1285076
  have htrace : WordTrace (prefixWord ++ tailWord_1285076) baseStart_1285076 baseEnd_1285076 := by
    simpa [prefixWord, tailWord_1285076, baseEnd_1285076] using wordTrace_append hprefix tailTrace_1285076
  have hstable : (prefixWord ++ tailWord_1285076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285076).length < 2 ^ (prefixWord ++ tailWord_1285076).sum := by decide
  have hdescent : baseEnd_1285076 < baseStart_1285076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285115 : List Nat := [1, 1, 1, 1, 1, 3, 3, 4, 4, 3]
def baseStart_1285115 : Nat := 118140960795 + 1285115 * 2 ^ 59
def prefixEnd_1285115 : Nat := 4983230072969 + 3 ^ 40 * 1285115 * 2
def baseEnd_1285115 : Nat := 439921127535229810234913

theorem tailTrace_1285115 : CollatzResearch.WordTrace tailWord_1285115 prefixEnd_1285115 439921127535229810234913 := by
  unfold tailWord_1285115
  simp only [CollatzResearch.WordTrace]
  refine ⟨46871994739255310013400799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31247996492836873342267199 46871994739255310013400799)
  ·
    refine ⟨70307992108882965020101199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46871994739255310013400799 70307992108882965020101199)
    ·
      refine ⟨105461988163324447530151799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70307992108882965020101199 105461988163324447530151799)
      ·
        refine ⟨158192982244986671295227699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105461988163324447530151799 158192982244986671295227699)
        ·
          refine ⟨237289473367480006942841549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158192982244986671295227699 237289473367480006942841549)
          ·
            refine ⟨88983552512805002603565581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 237289473367480006942841549 88983552512805002603565581)
            ·
              refine ⟨33368832192301875976337093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88983552512805002603565581 33368832192301875976337093)
              ·
                refine ⟨6256656036056601745563205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33368832192301875976337093 6256656036056601745563205)
                ·
                  refine ⟨1173123006760612827293101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6256656036056601745563205 1173123006760612827293101)
                  ·
                    refine ⟨439921127535229810234913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1173123006760612827293101 439921127535229810234913)
                    ·
                      rfl

theorem cell22_1285115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 4, 3].length) (baseStart_1285115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1285115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1285115 prefixEnd_1285115 := by exact prefixLift 1285115
  have htrace : WordTrace (prefixWord ++ tailWord_1285115) baseStart_1285115 baseEnd_1285115 := by
    simpa [prefixWord, tailWord_1285115, baseEnd_1285115] using wordTrace_append hprefix tailTrace_1285115
  have hstable : (prefixWord ++ tailWord_1285115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285115).length < 2 ^ (prefixWord ++ tailWord_1285115).sum := by decide
  have hdescent : baseEnd_1285115 < baseStart_1285115 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285132 : List Nat := [2, 2, 1, 2, 3, 3, 1, 1, 4, 3]
def baseStart_1285132 : Nat := 118140960795 + 1285132 * 2 ^ 59
def prefixEnd_1285132 : Nat := 4983230072969 + 3 ^ 40 * 1285132 * 2
def baseEnd_1285132 : Nat := 439926946982647432559861

theorem tailTrace_1285132 : CollatzResearch.WordTrace tailWord_1285132 prefixEnd_1285132 439926946982647432559861 := by
  unfold tailWord_1285132
  simp only [CollatzResearch.WordTrace]
  refine ⟨23436307390096860958384825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31248409853462481277846433 23436307390096860958384825)
  ·
    refine ⟨17577230542572645718788619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23436307390096860958384825 17577230542572645718788619)
    ·
      refine ⟨26365845813858968578182929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17577230542572645718788619 26365845813858968578182929)
      ·
        refine ⟨19774384360394226433637197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26365845813858968578182929 19774384360394226433637197)
        ·
          refine ⟨7415394135147834912613949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19774384360394226433637197 7415394135147834912613949)
          ·
            refine ⟨2780772800680438092230231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7415394135147834912613949 2780772800680438092230231)
            ·
              refine ⟨4171159201020657138345347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2780772800680438092230231 4171159201020657138345347)
              ·
                refine ⟨6256738801530985707518021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4171159201020657138345347 6256738801530985707518021)
                ·
                  refine ⟨1173138525287059820159629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6256738801530985707518021 1173138525287059820159629)
                  ·
                    refine ⟨439926946982647432559861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1173138525287059820159629 439926946982647432559861)
                    ·
                      rfl

theorem cell22_1285132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 1, 4, 3].length) (baseStart_1285132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1285132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1285132 prefixEnd_1285132 := by exact prefixLift 1285132
  have htrace : WordTrace (prefixWord ++ tailWord_1285132) baseStart_1285132 baseEnd_1285132 := by
    simpa [prefixWord, tailWord_1285132, baseEnd_1285132] using wordTrace_append hprefix tailTrace_1285132
  have hstable : (prefixWord ++ tailWord_1285132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285132).length < 2 ^ (prefixWord ++ tailWord_1285132).sum := by decide
  have hdescent : baseEnd_1285132 < baseStart_1285132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285149 : List Nat := [1, 4, 2, 2, 3, 2, 1, 1, 1, 5]
def baseStart_1285149 : Nat := 118140960795 + 1285149 * 2 ^ 59
def prefixEnd_1285149 : Nat := 4983230072969 + 3 ^ 40 * 1285149 * 2
def baseEnd_1285149 : Nat := 439932766430065054884809

theorem tailTrace_1285149 : CollatzResearch.WordTrace tailWord_1285149 prefixEnd_1285149 439932766430065054884809 := by
  unfold tailWord_1285149
  simp only [CollatzResearch.WordTrace]
  refine ⟨46873234821132133820138501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31248823214088089213425667 46873234821132133820138501)
  ·
    refine ⟨8788731528962275091275969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46873234821132133820138501 8788731528962275091275969)
    ·
      refine ⟨6591548646721706318456977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8788731528962275091275969 6591548646721706318456977)
      ·
        refine ⟨4943661485041279738842733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6591548646721706318456977 4943661485041279738842733)
        ·
          refine ⟨1853873056890479902066025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4943661485041279738842733 1853873056890479902066025)
          ·
            refine ⟨1390404792667859926549519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1853873056890479902066025 1390404792667859926549519)
            ·
              refine ⟨2085607189001789889824279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1390404792667859926549519 2085607189001789889824279)
              ·
                refine ⟨3128410783502684834736419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2085607189001789889824279 3128410783502684834736419)
                ·
                  refine ⟨4692616175254027252104629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3128410783502684834736419 4692616175254027252104629)
                  ·
                    refine ⟨439932766430065054884809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4692616175254027252104629 439932766430065054884809)
                    ·
                      rfl

theorem cell22_1285149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 1, 1, 5].length) (baseStart_1285149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1285149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1285149 prefixEnd_1285149 := by exact prefixLift 1285149
  have htrace : WordTrace (prefixWord ++ tailWord_1285149) baseStart_1285149 baseEnd_1285149 := by
    simpa [prefixWord, tailWord_1285149, baseEnd_1285149] using wordTrace_append hprefix tailTrace_1285149
  have hstable : (prefixWord ++ tailWord_1285149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285149).length < 2 ^ (prefixWord ++ tailWord_1285149).sum := by decide
  have hdescent : baseEnd_1285149 < baseStart_1285149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285162 : List Nat := [3, 1, 4, 1, 3, 1, 1, 8]
def baseStart_1285162 : Nat := 118140960795 + 1285162 * 2 ^ 59
def prefixEnd_1285162 : Nat := 4983230072969 + 3 ^ 40 * 1285162 * 2
def baseEnd_1285162 : Nat := 48881912955081928256641

theorem tailTrace_1285162 : CollatzResearch.WordTrace tailWord_1285162 prefixEnd_1285162 48881912955081928256641 := by
  unfold tailWord_1285162
  simp only [CollatzResearch.WordTrace]
  refine ⟨11718427242521259260090435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31249139313390024693574493 11718427242521259260090435)
  ·
    refine ⟨17577640863781888890135653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11718427242521259260090435 17577640863781888890135653)
    ·
      refine ⟨3295807661959104166900435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17577640863781888890135653 3295807661959104166900435)
      ·
        refine ⟨4943711492938656250350653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3295807661959104166900435 4943711492938656250350653)
        ·
          refine ⟨1853891809851996093881495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4943711492938656250350653 1853891809851996093881495)
          ·
            refine ⟨2780837714777994140822243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1853891809851996093881495 2780837714777994140822243)
            ·
              refine ⟨4171256572166991211233365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2780837714777994140822243 4171256572166991211233365)
              ·
                refine ⟨48881912955081928256641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4171256572166991211233365 48881912955081928256641)
                ·
                  rfl

theorem cell22_1285162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 8].length) (baseStart_1285162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1285162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1285162 prefixEnd_1285162 := by exact prefixLift 1285162
  have htrace : WordTrace (prefixWord ++ tailWord_1285162) baseStart_1285162 baseEnd_1285162 := by
    simpa [prefixWord, tailWord_1285162, baseEnd_1285162] using wordTrace_append hprefix tailTrace_1285162
  have hstable : (prefixWord ++ tailWord_1285162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285162).length < 2 ^ (prefixWord ++ tailWord_1285162).sum := by decide
  have hdescent : baseEnd_1285162 < baseStart_1285162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285194 : List Nat := [3, 1, 2, 1, 1, 2, 2, 6, 1, 3]
def baseStart_1285194 : Nat := 118140960795 + 1285194 * 2 ^ 59
def prefixEnd_1285194 : Nat := 4983230072969 + 3 ^ 40 * 1285194 * 2
def baseEnd_1285194 : Nat := 439948170849699937509671

theorem tailTrace_1285194 : CollatzResearch.WordTrace tailWord_1285194 prefixEnd_1285194 439948170849699937509671 := by
  unfold tailWord_1285194
  simp only [CollatzResearch.WordTrace]
  refine ⟨11718719026492276626381659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31249917403979404337017757 11718719026492276626381659)
  ·
    refine ⟨17578078539738414939572489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11718719026492276626381659 17578078539738414939572489)
    ·
      refine ⟨13183558904803811204679367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17578078539738414939572489 13183558904803811204679367)
      ·
        refine ⟨19775338357205716807019051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13183558904803811204679367 19775338357205716807019051)
        ·
          refine ⟨29663007535808575210528577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19775338357205716807019051 29663007535808575210528577)
          ·
            refine ⟨22247255651856431407896433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29663007535808575210528577 22247255651856431407896433)
            ·
              refine ⟨16685441738892323555922325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22247255651856431407896433 16685441738892323555922325)
              ·
                refine ⟨782130081510577666683859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16685441738892323555922325 782130081510577666683859)
                ·
                  refine ⟨1173195122265866500025789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 782130081510577666683859 1173195122265866500025789)
                  ·
                    refine ⟨439948170849699937509671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1173195122265866500025789 439948170849699937509671)
                    ·
                      rfl

theorem cell22_1285194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 6, 1, 3].length) (baseStart_1285194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1285194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1285194 prefixEnd_1285194 := by exact prefixLift 1285194
  have htrace : WordTrace (prefixWord ++ tailWord_1285194) baseStart_1285194 baseEnd_1285194 := by
    simpa [prefixWord, tailWord_1285194, baseEnd_1285194] using wordTrace_append hprefix tailTrace_1285194
  have hstable : (prefixWord ++ tailWord_1285194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285194).length < 2 ^ (prefixWord ++ tailWord_1285194).sum := by decide
  have hdescent : baseEnd_1285194 < baseStart_1285194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285205 : List Nat := [1, 3, 2, 2, 1, 2, 2, 1, 1, 7]
def baseStart_1285205 : Nat := 118140960795 + 1285205 * 2 ^ 59
def prefixEnd_1285205 : Nat := 4983230072969 + 3 ^ 40 * 1285205 * 2
def baseEnd_1285205 : Nat := 439951936374499575484637

theorem tailTrace_1285205 : CollatzResearch.WordTrace tailWord_1285205 prefixEnd_1285205 439951936374499575484637 := by
  unfold tailWord_1285205
  simp only [CollatzResearch.WordTrace]
  refine ⟨46875277308929255384177069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31250184872619503589451379 46875277308929255384177069)
  ·
    refine ⟨17578228990848470769066401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46875277308929255384177069 17578228990848470769066401)
    ·
      refine ⟨13183671743136353076799801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17578228990848470769066401 13183671743136353076799801)
      ·
        refine ⟨9887753807352264807599851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13183671743136353076799801 9887753807352264807599851)
        ·
          refine ⟨14831630711028397211399777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9887753807352264807599851 14831630711028397211399777)
          ·
            refine ⟨11123723033271297908549833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14831630711028397211399777 11123723033271297908549833)
            ·
              refine ⟨8342792274953473431412375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11123723033271297908549833 8342792274953473431412375)
              ·
                refine ⟨12514188412430210147118563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8342792274953473431412375 12514188412430210147118563)
                ·
                  refine ⟨18771282618645315220677845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12514188412430210147118563 18771282618645315220677845)
                  ·
                    refine ⟨439951936374499575484637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18771282618645315220677845 439951936374499575484637)
                    ·
                      rfl

theorem cell22_1285205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 7].length) (baseStart_1285205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1285205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1285205 prefixEnd_1285205 := by exact prefixLift 1285205
  have htrace : WordTrace (prefixWord ++ tailWord_1285205) baseStart_1285205 baseEnd_1285205 := by
    simpa [prefixWord, tailWord_1285205, baseEnd_1285205] using wordTrace_append hprefix tailTrace_1285205
  have hstable : (prefixWord ++ tailWord_1285205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285205).length < 2 ^ (prefixWord ++ tailWord_1285205).sum := by decide
  have hdescent : baseEnd_1285205 < baseStart_1285205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285297 : List Nat := [1, 2, 2, 5, 1, 2, 9]
def baseStart_1285297 : Nat := 118140960795 + 1285297 * 2 ^ 59
def prefixEnd_1285297 : Nat := 4983230072969 + 3 ^ 40 * 1285297 * 2
def baseEnd_1285297 : Nat := 16295682587208963043865

theorem tailTrace_1285297 : CollatzResearch.WordTrace tailWord_1285297 prefixEnd_1285297 16295682587208963043865 := by
  unfold tailWord_1285297
  simp only [CollatzResearch.WordTrace]
  refine ⟨46878632824595955096526145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31252421883063970064350763 46878632824595955096526145)
  ·
    refine ⟨35158974618446966322394609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46878632824595955096526145 35158974618446966322394609)
    ·
      refine ⟨26369230963835224741795957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35158974618446966322394609 26369230963835224741795957)
      ·
        refine ⟨2472115402859552319543371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26369230963835224741795957 2472115402859552319543371)
        ·
          refine ⟨3708173104289328479315057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2472115402859552319543371 3708173104289328479315057)
          ·
            refine ⟨2781129828216996359486293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3708173104289328479315057 2781129828216996359486293)
            ·
              refine ⟨16295682587208963043865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2781129828216996359486293 16295682587208963043865)
              ·
                rfl

theorem cell22_1285297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 9].length) (baseStart_1285297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1285297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1285297 prefixEnd_1285297 := by exact prefixLift 1285297
  have htrace : WordTrace (prefixWord ++ tailWord_1285297) baseStart_1285297 baseEnd_1285297 := by
    simpa [prefixWord, tailWord_1285297, baseEnd_1285297] using wordTrace_append hprefix tailTrace_1285297
  have hstable : (prefixWord ++ tailWord_1285297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285297).length < 2 ^ (prefixWord ++ tailWord_1285297).sum := by decide
  have hdescent : baseEnd_1285297 < baseStart_1285297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285363 : List Nat := [1, 1, 1, 2, 2, 6, 3, 2, 1, 3]
def baseStart_1285363 : Nat := 118140960795 + 1285363 * 2 ^ 59
def prefixEnd_1285363 : Nat := 4983230072969 + 3 ^ 40 * 1285363 * 2
def baseEnd_1285363 : Nat := 440006023003439830034153

theorem tailTrace_1285363 : CollatzResearch.WordTrace tailWord_1285363 prefixEnd_1285363 440006023003439830034153 := by
  unfold tailWord_1285363
  simp only [CollatzResearch.WordTrace]
  refine ⟨46881040042356848368428743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31254026694904565578952495 46881040042356848368428743)
  ·
    refine ⟨70321560063535272552643115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46881040042356848368428743 70321560063535272552643115)
    ·
      refine ⟨105482340095302908828964673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70321560063535272552643115 105482340095302908828964673)
      ·
        refine ⟨79111755071477181621723505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105482340095302908828964673 79111755071477181621723505)
        ·
          refine ⟨59333816303607886216292629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79111755071477181621723505 59333816303607886216292629)
          ·
            refine ⟨2781272639231619666388717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 59333816303607886216292629 2781272639231619666388717)
            ·
              refine ⟨1042977239711857374895769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2781272639231619666388717 1042977239711857374895769)
              ·
                refine ⟨782232929783893031171827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1042977239711857374895769 782232929783893031171827)
                ·
                  refine ⟨1173349394675839546757741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 782232929783893031171827 1173349394675839546757741)
                  ·
                    refine ⟨440006023003439830034153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1173349394675839546757741 440006023003439830034153)
                    ·
                      rfl

theorem cell22_1285363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 3, 2, 1, 3].length) (baseStart_1285363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1285363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1285363 prefixEnd_1285363 := by exact prefixLift 1285363
  have htrace : WordTrace (prefixWord ++ tailWord_1285363) baseStart_1285363 baseEnd_1285363 := by
    simpa [prefixWord, tailWord_1285363, baseEnd_1285363] using wordTrace_append hprefix tailTrace_1285363
  have hstable : (prefixWord ++ tailWord_1285363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285363).length < 2 ^ (prefixWord ++ tailWord_1285363).sum := by decide
  have hdescent : baseEnd_1285363 < baseStart_1285363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285417 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 8, 4]
def baseStart_1285417 : Nat := 118140960795 + 1285417 * 2 ^ 59
def prefixEnd_1285417 : Nat := 4983230072969 + 3 ^ 40 * 1285417 * 2
def baseEnd_1285417 : Nat := 440024508307001689183987

theorem tailTrace_1285417 : CollatzResearch.WordTrace tailWord_1285417 prefixEnd_1285417 440024508307001689183987 := by
  unfold tailWord_1285417
  simp only [CollatzResearch.WordTrace]
  refine ⟨46883009584161215590894505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31255339722774143727263003 46883009584161215590894505)
  ·
    refine ⟨35162257188120911693170879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46883009584161215590894505 35162257188120911693170879)
    ·
      refine ⟨52743385782181367539756319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35162257188120911693170879 52743385782181367539756319)
      ·
        refine ⟨79115078673272051309634479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52743385782181367539756319 79115078673272051309634479)
        ·
          refine ⟨118672618009908076964451719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79115078673272051309634479 118672618009908076964451719)
          ·
            refine ⟨178008927014862115446677579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118672618009908076964451719 178008927014862115446677579)
            ·
              refine ⟨267013390522293173170016369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178008927014862115446677579 267013390522293173170016369)
              ·
                refine ⟨200260042891719879877512277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 267013390522293173170016369 200260042891719879877512277)
                ·
                  refine ⟨2346797377637342342314597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 200260042891719879877512277 2346797377637342342314597)
                  ·
                    refine ⟨440024508307001689183987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2346797377637342342314597 440024508307001689183987)
                    ·
                      rfl

theorem cell22_1285417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 8, 4].length) (baseStart_1285417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1285417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1285417 prefixEnd_1285417 := by exact prefixLift 1285417
  have htrace : WordTrace (prefixWord ++ tailWord_1285417) baseStart_1285417 baseEnd_1285417 := by
    simpa [prefixWord, tailWord_1285417, baseEnd_1285417] using wordTrace_append hprefix tailTrace_1285417
  have hstable : (prefixWord ++ tailWord_1285417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285417).length < 2 ^ (prefixWord ++ tailWord_1285417).sum := by decide
  have hdescent : baseEnd_1285417 < baseStart_1285417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285436 : List Nat := [2, 2, 2, 2, 1, 3, 2, 3, 2, 3]
def baseStart_1285436 : Nat := 118140960795 + 1285436 * 2 ^ 59
def prefixEnd_1285436 : Nat := 4983230072969 + 3 ^ 40 * 1285436 * 2
def baseEnd_1285436 : Nat := 440031012395291972958929

theorem tailTrace_1285436 : CollatzResearch.WordTrace tailWord_1285436 prefixEnd_1285436 440031012395291972958929 := by
  unfold tailWord_1285436
  simp only [CollatzResearch.WordTrace]
  refine ⟨23441851285546190917918081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31255801714061587890557441 23441851285546190917918081)
  ·
    refine ⟨17581388464159643188438561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23441851285546190917918081 17581388464159643188438561)
    ·
      refine ⟨13186041348119732391328921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17581388464159643188438561 13186041348119732391328921)
      ·
        refine ⟨9889531011089799293496691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13186041348119732391328921 9889531011089799293496691)
        ·
          refine ⟨14834296516634698940245037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9889531011089799293496691 14834296516634698940245037)
          ·
            refine ⟨5562861193738012102591889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14834296516634698940245037 5562861193738012102591889)
            ·
              refine ⟨4172145895303509076943917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5562861193738012102591889 4172145895303509076943917)
              ·
                refine ⟨1564554710738815903853969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4172145895303509076943917 1564554710738815903853969)
                ·
                  refine ⟨1173416033054111927890477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1564554710738815903853969 1173416033054111927890477)
                  ·
                    refine ⟨440031012395291972958929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1173416033054111927890477 440031012395291972958929)
                    ·
                      rfl

theorem cell22_1285436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 3, 2, 3].length) (baseStart_1285436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1285436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1285436 prefixEnd_1285436 := by exact prefixLift 1285436
  have htrace : WordTrace (prefixWord ++ tailWord_1285436) baseStart_1285436 baseEnd_1285436 := by
    simpa [prefixWord, tailWord_1285436, baseEnd_1285436] using wordTrace_append hprefix tailTrace_1285436
  have hstable : (prefixWord ++ tailWord_1285436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285436).length < 2 ^ (prefixWord ++ tailWord_1285436).sum := by decide
  have hdescent : baseEnd_1285436 < baseStart_1285436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285464 : List Nat := [2, 1, 2, 2, 1, 1, 3, 2, 5, 3]
def baseStart_1285464 : Nat := 118140960795 + 1285464 * 2 ^ 59
def prefixEnd_1285464 : Nat := 4983230072969 + 3 ^ 40 * 1285464 * 2
def baseEnd_1285464 : Nat := 440040597367509233258843

theorem tailTrace_1285464 : CollatzResearch.WordTrace tailWord_1285464 prefixEnd_1285464 440040597367509233258843 := by
  unfold tailWord_1285464
  simp only [CollatzResearch.WordTrace]
  refine ⟨23442361907495471308927723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31256482543327295078570297 23442361907495471308927723)
  ·
    refine ⟨35163542861243206963391585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23442361907495471308927723 35163542861243206963391585)
    ·
      refine ⟨26372657145932405222543689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35163542861243206963391585 26372657145932405222543689)
      ·
        refine ⟨19779492859449303916907767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26372657145932405222543689 19779492859449303916907767)
        ·
          refine ⟨29669239289173955875361651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19779492859449303916907767 29669239289173955875361651)
          ·
            refine ⟨44503858933760933813042477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29669239289173955875361651 44503858933760933813042477)
            ·
              refine ⟨16688947100160350179890929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44503858933760933813042477 16688947100160350179890929)
              ·
                refine ⟨12516710325120262634918197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16688947100160350179890929 12516710325120262634918197)
                ·
                  refine ⟨1173441592980024622023581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12516710325120262634918197 1173441592980024622023581)
                  ·
                    refine ⟨440040597367509233258843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1173441592980024622023581 440040597367509233258843)
                    ·
                      rfl

theorem cell22_1285464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 5, 3].length) (baseStart_1285464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1285464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1285464 prefixEnd_1285464 := by exact prefixLift 1285464
  have htrace : WordTrace (prefixWord ++ tailWord_1285464) baseStart_1285464 baseEnd_1285464 := by
    simpa [prefixWord, tailWord_1285464, baseEnd_1285464] using wordTrace_append hprefix tailTrace_1285464
  have hstable : (prefixWord ++ tailWord_1285464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285464).length < 2 ^ (prefixWord ++ tailWord_1285464).sum := by decide
  have hdescent : baseEnd_1285464 < baseStart_1285464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285532 : List Nat := [2, 2, 3, 4, 2, 1, 1, 1, 3, 3]
def baseStart_1285532 : Nat := 118140960795 + 1285532 * 2 ^ 59
def prefixEnd_1285532 : Nat := 4983230072969 + 3 ^ 40 * 1285532 * 2
def baseEnd_1285532 : Nat := 440063875157179722558635

theorem tailTrace_1285532 : CollatzResearch.WordTrace tailWord_1285532 prefixEnd_1285532 440063875157179722558635 := by
  unfold tailWord_1285532
  simp only [CollatzResearch.WordTrace]
  refine ⟨23443601989372295115665425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31258135985829726820887233 23443601989372295115665425)
  ·
    refine ⟨17582701492029221336749069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23443601989372295115665425 17582701492029221336749069)
    ·
      refine ⟨6593513059510958001280901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17582701492029221336749069 6593513059510958001280901)
      ·
        refine ⟨1236283698658304625240169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6593513059510958001280901 1236283698658304625240169)
        ·
          refine ⟨927212773993728468930127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1236283698658304625240169 927212773993728468930127)
          ·
            refine ⟨1390819160990592703395191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 927212773993728468930127 1390819160990592703395191)
            ·
              refine ⟨2086228741485889055092787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1390819160990592703395191 2086228741485889055092787)
              ·
                refine ⟨3129343112228833582639181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2086228741485889055092787 3129343112228833582639181)
                ·
                  refine ⟨1173503667085812593489693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3129343112228833582639181 1173503667085812593489693)
                  ·
                    refine ⟨440063875157179722558635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1173503667085812593489693 440063875157179722558635)
                    ·
                      rfl

theorem cell22_1285532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 1, 3, 3].length) (baseStart_1285532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1285532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1285532 prefixEnd_1285532 := by exact prefixLift 1285532
  have htrace : WordTrace (prefixWord ++ tailWord_1285532) baseStart_1285532 baseEnd_1285532 := by
    simpa [prefixWord, tailWord_1285532, baseEnd_1285532] using wordTrace_append hprefix tailTrace_1285532
  have hstable : (prefixWord ++ tailWord_1285532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285532).length < 2 ^ (prefixWord ++ tailWord_1285532).sum := by decide
  have hdescent : baseEnd_1285532 < baseStart_1285532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285590 : List Nat := [5, 2, 1, 1, 1, 3, 1, 4, 4]
def baseStart_1285590 : Nat := 118140960795 + 1285590 * 2 ^ 59
def prefixEnd_1285590 : Nat := 4983230072969 + 3 ^ 40 * 1285590 * 2
def baseEnd_1285590 : Nat := 146694576580828968202819

theorem tailTrace_1285590 : CollatzResearch.WordTrace tailWord_1285590 prefixEnd_1285590 146694576580828968202819 := by
  unfold tailWord_1285590
  simp only [CollatzResearch.WordTrace]
  refine ⟨2930582463283404133558889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31259546275022977424628149 2930582463283404133558889)
  ·
    refine ⟨2197936847462553100169167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2930582463283404133558889 2197936847462553100169167)
    ·
      refine ⟨3296905271193829650253751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2197936847462553100169167 3296905271193829650253751)
      ·
        refine ⟨4945357906790744475380627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3296905271193829650253751 4945357906790744475380627)
        ·
          refine ⟨7418036860186116713070941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4945357906790744475380627 7418036860186116713070941)
          ·
            refine ⟨2781763822569793767401603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7418036860186116713070941 2781763822569793767401603)
            ·
              refine ⟨4172645733854690651102405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2781763822569793767401603 4172645733854690651102405)
              ·
                refine ⟨782371075097754497081701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4172645733854690651102405 782371075097754497081701)
                ·
                  refine ⟨146694576580828968202819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 782371075097754497081701 146694576580828968202819)
                  ·
                    rfl

theorem cell22_1285590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_1285590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1285590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1285590 prefixEnd_1285590 := by exact prefixLift 1285590
  have htrace : WordTrace (prefixWord ++ tailWord_1285590) baseStart_1285590 baseEnd_1285590 := by
    simpa [prefixWord, tailWord_1285590, baseEnd_1285590] using wordTrace_append hprefix tailTrace_1285590
  have hstable : (prefixWord ++ tailWord_1285590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285590).length < 2 ^ (prefixWord ++ tailWord_1285590).sum := by decide
  have hdescent : baseEnd_1285590 < baseStart_1285590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285601 : List Nat := [1, 2, 3, 1, 2, 5, 1, 7]
def baseStart_1285601 : Nat := 118140960795 + 1285601 * 2 ^ 59
def prefixEnd_1285601 : Nat := 4983230072969 + 3 ^ 40 * 1285601 * 2
def baseEnd_1285601 : Nat := 48898610585254060287047

theorem tailTrace_1285601 : CollatzResearch.WordTrace tailWord_1285601 prefixEnd_1285601 48898610585254060287047 := by
  unfold tailWord_1285601
  simp only [CollatzResearch.WordTrace]
  refine ⟨46889720615494615015592657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31259813743663076677061771 46889720615494615015592657)
  ·
    refine ⟨35167290461620961261694493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46889720615494615015592657 35167290461620961261694493)
    ·
      refine ⟨13187733923107860473135435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35167290461620961261694493 13187733923107860473135435)
      ·
        refine ⟨19781600884661790709703153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13187733923107860473135435 19781600884661790709703153)
        ·
          refine ⟨14836200663496343032277365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19781600884661790709703153 14836200663496343032277365)
          ·
            refine ⟨1390893812202782159276003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14836200663496343032277365 1390893812202782159276003)
            ·
              refine ⟨2086340718304173238914005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1390893812202782159276003 2086340718304173238914005)
              ·
                refine ⟨48898610585254060287047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2086340718304173238914005 48898610585254060287047)
                ·
                  rfl

theorem cell22_1285601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 7].length) (baseStart_1285601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1285601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1285601 prefixEnd_1285601 := by exact prefixLift 1285601
  have htrace : WordTrace (prefixWord ++ tailWord_1285601) baseStart_1285601 baseEnd_1285601 := by
    simpa [prefixWord, tailWord_1285601, baseEnd_1285601] using wordTrace_append hprefix tailTrace_1285601
  have hstable : (prefixWord ++ tailWord_1285601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285601).length < 2 ^ (prefixWord ++ tailWord_1285601).sum := by decide
  have hdescent : baseEnd_1285601 < baseStart_1285601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285616 : List Nat := [2, 1, 1, 1, 3, 4, 1, 1, 5, 3]
def baseStart_1285616 : Nat := 118140960795 + 1285616 * 2 ^ 59
def prefixEnd_1285616 : Nat := 4983230072969 + 3 ^ 40 * 1285616 * 2
def baseEnd_1285616 : Nat := 440092630073831503458377

theorem tailTrace_1285616 : CollatzResearch.WordTrace tailWord_1285616 prefixEnd_1285616 440092630073831503458377 := by
  unfold tailWord_1285616
  simp only [CollatzResearch.WordTrace]
  refine ⟨23445133855220136288694351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31260178473626848384925801 23445133855220136288694351)
  ·
    refine ⟨35167700782830204433041527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23445133855220136288694351 35167700782830204433041527)
    ·
      refine ⟨52751551174245306649562291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35167700782830204433041527 52751551174245306649562291)
      ·
        refine ⟨79127326761367959974343437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52751551174245306649562291 79127326761367959974343437)
        ·
          refine ⟨29672747535512984990378789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79127326761367959974343437 29672747535512984990378789)
          ·
            refine ⟨5563640162908684685696023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29672747535512984990378789 5563640162908684685696023)
            ·
              refine ⟨8345460244363027028544035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5563640162908684685696023 8345460244363027028544035)
              ·
                refine ⟨12518190366544540542816053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8345460244363027028544035 12518190366544540542816053)
                ·
                  refine ⟨1173580346863550675889005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12518190366544540542816053 1173580346863550675889005)
                  ·
                    refine ⟨440092630073831503458377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1173580346863550675889005 440092630073831503458377)
                    ·
                      rfl

theorem cell22_1285616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 5, 3].length) (baseStart_1285616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1285616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1285616 prefixEnd_1285616 := by exact prefixLift 1285616
  have htrace : WordTrace (prefixWord ++ tailWord_1285616) baseStart_1285616 baseEnd_1285616 := by
    simpa [prefixWord, tailWord_1285616, baseEnd_1285616] using wordTrace_append hprefix tailTrace_1285616
  have hstable : (prefixWord ++ tailWord_1285616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285616).length < 2 ^ (prefixWord ++ tailWord_1285616).sum := by decide
  have hdescent : baseEnd_1285616 < baseStart_1285616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285618 : List Nat := [3, 2, 1, 4, 1, 2, 3, 6]
def baseStart_1285618 : Nat := 118140960795 + 1285618 * 2 ^ 59
def prefixEnd_1285618 : Nat := 4983230072969 + 3 ^ 40 * 1285618 * 2
def baseEnd_1285618 : Nat := 48899257190522684989819

theorem tailTrace_1285618 : CollatzResearch.WordTrace tailWord_1285618 prefixEnd_1285618 48899257190522684989819 := by
  unfold tailWord_1285618
  simp only [CollatzResearch.WordTrace]
  refine ⟨11722585164108256729740377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31260227104288684612641005 11722585164108256729740377)
  ·
    refine ⟨8791938873081192547305283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11722585164108256729740377 8791938873081192547305283)
    ·
      refine ⟨13187908309621788820957925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8791938873081192547305283 13187908309621788820957925)
      ·
        refine ⟨2472732808054085403929611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13187908309621788820957925 2472732808054085403929611)
        ·
          refine ⟨3709099212081128105894417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2472732808054085403929611 3709099212081128105894417)
          ·
            refine ⟨2781824409060846079420813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3709099212081128105894417 2781824409060846079420813)
            ·
              refine ⟨1043184153397817279782805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2781824409060846079420813 1043184153397817279782805)
              ·
                refine ⟨48899257190522684989819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1043184153397817279782805 48899257190522684989819)
                ·
                  rfl

theorem cell22_1285618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 3, 6].length) (baseStart_1285618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1285618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1285618 prefixEnd_1285618 := by exact prefixLift 1285618
  have htrace : WordTrace (prefixWord ++ tailWord_1285618) baseStart_1285618 baseEnd_1285618 := by
    simpa [prefixWord, tailWord_1285618, baseEnd_1285618] using wordTrace_append hprefix tailTrace_1285618
  have hstable : (prefixWord ++ tailWord_1285618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285618).length < 2 ^ (prefixWord ++ tailWord_1285618).sum := by decide
  have hdescent : baseEnd_1285618 < baseStart_1285618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285661 : List Nat := [1, 4, 2, 2, 1, 1, 1, 3, 2, 5]
def baseStart_1285661 : Nat := 118140960795 + 1285661 * 2 ^ 59
def prefixEnd_1285661 : Nat := 4983230072969 + 3 ^ 40 * 1285661 * 2
def baseEnd_1285661 : Nat := 440108034493466386083239

theorem tailTrace_1285661 : CollatzResearch.WordTrace tailWord_1285661 prefixEnd_1285661 440108034493466386083239 := by
  unfold tailWord_1285661
  simp only [CollatzResearch.WordTrace]
  refine ⟨46891908995277245262776837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31261272663518163508517891 46891908995277245262776837)
  ·
    refine ⟨8792232936614483486770657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46891908995277245262776837 8792232936614483486770657)
    ·
      refine ⟨6594174702460862615077993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8792232936614483486770657 6594174702460862615077993)
      ·
        refine ⟨4945631026845646961308495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6594174702460862615077993 4945631026845646961308495)
        ·
          refine ⟨7418446540268470441962743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4945631026845646961308495 7418446540268470441962743)
          ·
            refine ⟨11127669810402705662944115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7418446540268470441962743 11127669810402705662944115)
            ·
              refine ⟨16691504715604058494416173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11127669810402705662944115 16691504715604058494416173)
              ·
                refine ⟨6259314268351521935406065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16691504715604058494416173 6259314268351521935406065)
                ·
                  refine ⟨4694485701263641451554549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6259314268351521935406065 4694485701263641451554549)
                  ·
                    refine ⟨440108034493466386083239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4694485701263641451554549 440108034493466386083239)
                    ·
                      rfl

theorem cell22_1285661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_1285661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1285661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1285661 prefixEnd_1285661 := by exact prefixLift 1285661
  have htrace : WordTrace (prefixWord ++ tailWord_1285661) baseStart_1285661 baseEnd_1285661 := by
    simpa [prefixWord, tailWord_1285661, baseEnd_1285661] using wordTrace_append hprefix tailTrace_1285661
  have hstable : (prefixWord ++ tailWord_1285661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285661).length < 2 ^ (prefixWord ++ tailWord_1285661).sum := by decide
  have hdescent : baseEnd_1285661 < baseStart_1285661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285708 : List Nat := [2, 2, 1, 3, 1, 5, 1, 1, 6]
def baseStart_1285708 : Nat := 118140960795 + 1285708 * 2 ^ 59
def prefixEnd_1285708 : Nat := 4983230072969 + 3 ^ 40 * 1285708 * 2
def baseEnd_1285708 : Nat := 146708041184657976719365

theorem tailTrace_1285708 : CollatzResearch.WordTrace tailWord_1285708 prefixEnd_1285708 146708041184657976719365 := by
  unfold tailWord_1285708
  simp only [CollatzResearch.WordTrace]
  refine ⟨23446811613053486144868889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31262415484071314859825185 23446811613053486144868889)
  ·
    refine ⟨17585108709790114608651667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23446811613053486144868889 17585108709790114608651667)
    ·
      refine ⟨26377663064685171912977501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17585108709790114608651667 26377663064685171912977501)
      ·
        refine ⟨9891623649256939467366563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26377663064685171912977501 9891623649256939467366563)
        ·
          refine ⟨14837435473885409201049845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9891623649256939467366563 14837435473885409201049845)
          ·
            refine ⟨1391009575676757112598423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14837435473885409201049845 1391009575676757112598423)
            ·
              refine ⟨2086514363515135668897635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1391009575676757112598423 2086514363515135668897635)
              ·
                refine ⟨3129771545272703503346453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2086514363515135668897635 3129771545272703503346453)
                ·
                  refine ⟨146708041184657976719365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3129771545272703503346453 146708041184657976719365)
                  ·
                    rfl

theorem cell22_1285708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 1, 6].length) (baseStart_1285708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1285708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1285708 prefixEnd_1285708 := by exact prefixLift 1285708
  have htrace : WordTrace (prefixWord ++ tailWord_1285708) baseStart_1285708 baseEnd_1285708 := by
    simpa [prefixWord, tailWord_1285708, baseEnd_1285708] using wordTrace_append hprefix tailTrace_1285708
  have hstable : (prefixWord ++ tailWord_1285708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285708).length < 2 ^ (prefixWord ++ tailWord_1285708).sum := by decide
  have hdescent : baseEnd_1285708 < baseStart_1285708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285738 : List Nat := [3, 1, 3, 2, 1, 2, 1, 3, 2, 4]
def baseStart_1285738 : Nat := 118140960795 + 1285738 * 2 ^ 59
def prefixEnd_1285738 : Nat := 4983230072969 + 3 ^ 40 * 1285738 * 2
def baseEnd_1285738 : Nat := 440134393167063851908003

theorem tailTrace_1285738 : CollatzResearch.WordTrace tailWord_1285738 prefixEnd_1285738 440134393167063851908003 := by
  unfold tailWord_1285738
  simp only [CollatzResearch.WordTrace]
  refine ⟨11723679353999571853332467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31263144943998858275553245 11723679353999571853332467)
  ·
    refine ⟨17585519030999357779998701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11723679353999571853332467 17585519030999357779998701)
    ·
      refine ⟨6594569636624759167499513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17585519030999357779998701 6594569636624759167499513)
      ·
        refine ⟨4945927227468569375624635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6594569636624759167499513 4945927227468569375624635)
        ·
          refine ⟨7418890841202854063436953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4945927227468569375624635 7418890841202854063436953)
          ·
            refine ⟨5564168130902140547577715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7418890841202854063436953 5564168130902140547577715)
            ·
              refine ⟨8346252196353210821366573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5564168130902140547577715 8346252196353210821366573)
              ·
                refine ⟨3129844573632454058012465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8346252196353210821366573 3129844573632454058012465)
                ·
                  refine ⟨2347383430224340543509349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3129844573632454058012465 2347383430224340543509349)
                  ·
                    refine ⟨440134393167063851908003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2347383430224340543509349 440134393167063851908003)
                    ·
                      rfl

theorem cell22_1285738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_1285738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1285738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1285738 prefixEnd_1285738 := by exact prefixLift 1285738
  have htrace : WordTrace (prefixWord ++ tailWord_1285738) baseStart_1285738 baseEnd_1285738 := by
    simpa [prefixWord, tailWord_1285738, baseEnd_1285738] using wordTrace_append hprefix tailTrace_1285738
  have hstable : (prefixWord ++ tailWord_1285738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285738).length < 2 ^ (prefixWord ++ tailWord_1285738).sum := by decide
  have hdescent : baseEnd_1285738 < baseStart_1285738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285815 : List Nat := [1, 1, 3, 1, 5, 3, 1, 2, 5]
def baseStart_1285815 : Nat := 118140960795 + 1285815 * 2 ^ 59
def prefixEnd_1285815 : Nat := 4983230072969 + 3 ^ 40 * 1285815 * 2
def baseEnd_1285815 : Nat := 146720250613553772577589

theorem tailTrace_1285815 : CollatzResearch.WordTrace tailWord_1285815 prefixEnd_1285815 146720250613553772577589 := by
  unfold tailWord_1285815
  simp only [CollatzResearch.WordTrace]
  refine ⟨46897525836719329563882899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31265017224479553042588599 46897525836719329563882899)
  ·
    refine ⟨70346288755078994345824349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46897525836719329563882899 70346288755078994345824349)
    ·
      refine ⟨26379858283154622879684131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70346288755078994345824349 26379858283154622879684131)
      ·
        refine ⟨39569787424731934319526197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26379858283154622879684131 39569787424731934319526197)
        ·
          refine ⟨3709667571068618842455581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39569787424731934319526197 3709667571068618842455581)
          ·
            refine ⟨1391125339150732065920843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3709667571068618842455581 1391125339150732065920843)
            ·
              refine ⟨2086688008726098098881265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1391125339150732065920843 2086688008726098098881265)
              ·
                refine ⟨1565016006544573574160949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2086688008726098098881265 1565016006544573574160949)
                ·
                  refine ⟨146720250613553772577589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1565016006544573574160949 146720250613553772577589)
                  ·
                    rfl

theorem cell22_1285815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 2, 5].length) (baseStart_1285815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1285815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1285815 prefixEnd_1285815 := by exact prefixLift 1285815
  have htrace : WordTrace (prefixWord ++ tailWord_1285815) baseStart_1285815 baseEnd_1285815 := by
    simpa [prefixWord, tailWord_1285815, baseEnd_1285815] using wordTrace_append hprefix tailTrace_1285815
  have hstable : (prefixWord ++ tailWord_1285815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285815).length < 2 ^ (prefixWord ++ tailWord_1285815).sum := by decide
  have hdescent : baseEnd_1285815 < baseStart_1285815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285853 : List Nat := [1, 4, 3, 3, 2, 1, 1, 3, 1, 3]
def baseStart_1285853 : Nat := 118140960795 + 1285853 * 2 ^ 59
def prefixEnd_1285853 : Nat := 4983230072969 + 3 ^ 40 * 1285853 * 2
def baseEnd_1285853 : Nat := 440173760017241885282651

theorem tailTrace_1285853 : CollatzResearch.WordTrace tailWord_1285853 prefixEnd_1285853 440173760017241885282651 := by
  unfold tailWord_1285853
  simp only [CollatzResearch.WordTrace]
  refine ⟨46898911810581662053766213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31265941207054441369177475 46898911810581662053766213)
  ·
    refine ⟨8793545964484061635081165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46898911810581662053766213 8793545964484061635081165)
    ·
      refine ⟨3297579736681523113155437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8793545964484061635081165 3297579736681523113155437)
      ·
        refine ⟨1236592401255571167433289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3297579736681523113155437 1236592401255571167433289)
        ·
          refine ⟨927444300941678375574967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1236592401255571167433289 927444300941678375574967)
          ·
            refine ⟨1391166451412517563362451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 927444300941678375574967 1391166451412517563362451)
            ·
              refine ⟨2086749677118776345043677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1391166451412517563362451 2086749677118776345043677)
              ·
                refine ⟨782531128919541129391379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2086749677118776345043677 782531128919541129391379)
                ·
                  refine ⟨1173796693379311694087069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 782531128919541129391379 1173796693379311694087069)
                  ·
                    refine ⟨440173760017241885282651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1173796693379311694087069 440173760017241885282651)
                    ·
                      rfl

theorem cell22_1285853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_1285853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1285853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1285853 prefixEnd_1285853 := by exact prefixLift 1285853
  have htrace : WordTrace (prefixWord ++ tailWord_1285853) baseStart_1285853 baseEnd_1285853 := by
    simpa [prefixWord, tailWord_1285853, baseEnd_1285853] using wordTrace_append hprefix tailTrace_1285853
  have hstable : (prefixWord ++ tailWord_1285853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285853).length < 2 ^ (prefixWord ++ tailWord_1285853).sum := by decide
  have hdescent : baseEnd_1285853 < baseStart_1285853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285873 : List Nat := [1, 2, 2, 2, 2, 3, 1, 1, 4, 4]
def baseStart_1285873 : Nat := 118140960795 + 1285873 * 2 ^ 59
def prefixEnd_1285873 : Nat := 4983230072969 + 3 ^ 40 * 1285873 * 2
def baseEnd_1285873 : Nat := 440180606425968499782589

theorem tailTrace_1285873 : CollatzResearch.WordTrace tailWord_1285873 prefixEnd_1285873 440180606425968499782589 := by
  unfold tailWord_1285873
  simp only [CollatzResearch.WordTrace]
  refine ⟨46899641270509205469494273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31266427513672803646329515 46899641270509205469494273)
  ·
    refine ⟨35174730952881904102120705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46899641270509205469494273 35174730952881904102120705)
    ·
      refine ⟨26381048214661428076590529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35174730952881904102120705 26381048214661428076590529)
      ·
        refine ⟨19785786160996071057442897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26381048214661428076590529 19785786160996071057442897)
        ·
          refine ⟨14839339620747053293082173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19785786160996071057442897 14839339620747053293082173)
          ·
            refine ⟨5564752357780144984905815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14839339620747053293082173 5564752357780144984905815)
            ·
              refine ⟨8347128536670217477358723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5564752357780144984905815 8347128536670217477358723)
              ·
                refine ⟨12520692805005326216038085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8347128536670217477358723 12520692805005326216038085)
                ·
                  refine ⟨2347629900938498665507141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12520692805005326216038085 2347629900938498665507141)
                  ·
                    refine ⟨440180606425968499782589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2347629900938498665507141 440180606425968499782589)
                    ·
                      rfl

theorem cell22_1285873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 4, 4].length) (baseStart_1285873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1285873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1285873 prefixEnd_1285873 := by exact prefixLift 1285873
  have htrace : WordTrace (prefixWord ++ tailWord_1285873) baseStart_1285873 baseEnd_1285873 := by
    simpa [prefixWord, tailWord_1285873, baseEnd_1285873] using wordTrace_append hprefix tailTrace_1285873
  have hstable : (prefixWord ++ tailWord_1285873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285873).length < 2 ^ (prefixWord ++ tailWord_1285873).sum := by decide
  have hdescent : baseEnd_1285873 < baseStart_1285873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285890 : List Nat := [3, 4, 1, 1, 1, 1, 1, 2, 4, 4]
def baseStart_1285890 : Nat := 118140960795 + 1285890 * 2 ^ 59
def prefixEnd_1285890 : Nat := 4983230072969 + 3 ^ 40 * 1285890 * 2
def baseEnd_1285890 : Nat := 440186425873386122107537

theorem tailTrace_1285890 : CollatzResearch.WordTrace tailWord_1285890 prefixEnd_1285890 440186425873386122107537 := by
  unfold tailWord_1285890
  simp only [CollatzResearch.WordTrace]
  refine ⟨11725065327861904343215781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31266840874298411581908749 11725065327861904343215781)
  ·
    refine ⟨2198449748974107064352959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11725065327861904343215781 2198449748974107064352959)
    ·
      refine ⟨3297674623461160596529439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2198449748974107064352959 3297674623461160596529439)
      ·
        refine ⟨4946511935191740894794159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3297674623461160596529439 4946511935191740894794159)
        ·
          refine ⟨7419767902787611342191239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4946511935191740894794159 7419767902787611342191239)
          ·
            refine ⟨11129651854181417013286859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7419767902787611342191239 11129651854181417013286859)
            ·
              refine ⟨16694477781272125519930289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11129651854181417013286859 16694477781272125519930289)
              ·
                refine ⟨12520858335954094139947717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16694477781272125519930289 12520858335954094139947717)
                ·
                  refine ⟨2347660937991392651240197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12520858335954094139947717 2347660937991392651240197)
                  ·
                    refine ⟨440186425873386122107537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2347660937991392651240197 440186425873386122107537)
                    ·
                      rfl

theorem cell22_1285890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_1285890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1285890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1285890 prefixEnd_1285890 := by exact prefixLift 1285890
  have htrace : WordTrace (prefixWord ++ tailWord_1285890) baseStart_1285890 baseEnd_1285890 := by
    simpa [prefixWord, tailWord_1285890, baseEnd_1285890] using wordTrace_append hprefix tailTrace_1285890
  have hstable : (prefixWord ++ tailWord_1285890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285890).length < 2 ^ (prefixWord ++ tailWord_1285890).sum := by decide
  have hdescent : baseEnd_1285890 < baseStart_1285890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285892 : List Nat := [2, 3, 2, 2, 1, 3, 1, 3, 2, 3]
def baseStart_1285892 : Nat := 118140960795 + 1285892 * 2 ^ 59
def prefixEnd_1285892 : Nat := 4983230072969 + 3 ^ 40 * 1285892 * 2
def baseEnd_1285892 : Nat := 440187110514258783557531

theorem tailTrace_1285892 : CollatzResearch.WordTrace tailWord_1285892 prefixEnd_1285892 440187110514258783557531 := by
  unfold tailWord_1285892
  simp only [CollatzResearch.WordTrace]
  refine ⟨23450167128720185857217965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31266889504960247809623953 23450167128720185857217965)
  ·
    refine ⟨8793812673270069696456737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23450167128720185857217965 8793812673270069696456737)
    ·
      refine ⟨6595359504952552272342553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8793812673270069696456737 6595359504952552272342553)
      ·
        refine ⟨4946519628714414204256915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6595359504952552272342553 4946519628714414204256915)
        ·
          refine ⟨7419779443071621306385373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4946519628714414204256915 7419779443071621306385373)
          ·
            refine ⟨2782417291151857989894515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7419779443071621306385373 2782417291151857989894515)
            ·
              refine ⟨4173625936727786984841773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2782417291151857989894515 4173625936727786984841773)
              ·
                refine ⟨1565109726272920119315665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4173625936727786984841773 1565109726272920119315665)
                ·
                  refine ⟨1173832294704690089486749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1565109726272920119315665 1173832294704690089486749)
                  ·
                    refine ⟨440187110514258783557531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1173832294704690089486749 440187110514258783557531)
                    ·
                      rfl

theorem cell22_1285892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 3, 2, 3].length) (baseStart_1285892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1285892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1285892 prefixEnd_1285892 := by exact prefixLift 1285892
  have htrace : WordTrace (prefixWord ++ tailWord_1285892) baseStart_1285892 baseEnd_1285892 := by
    simpa [prefixWord, tailWord_1285892, baseEnd_1285892] using wordTrace_append hprefix tailTrace_1285892
  have hstable : (prefixWord ++ tailWord_1285892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285892).length < 2 ^ (prefixWord ++ tailWord_1285892).sum := by decide
  have hdescent : baseEnd_1285892 < baseStart_1285892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285948 : List Nat := [2, 2, 2, 2, 1, 1, 3, 1, 1, 7]
def baseStart_1285948 : Nat := 118140960795 + 1285948 * 2 ^ 59
def prefixEnd_1285948 : Nat := 4983230072969 + 3 ^ 40 * 1285948 * 2
def baseEnd_1285948 : Nat := 440206280458693304157359

theorem tailTrace_1285948 : CollatzResearch.WordTrace tailWord_1285948 prefixEnd_1285948 440206280458693304157359 := by
  unfold tailWord_1285948
  simp only [CollatzResearch.WordTrace]
  refine ⟨23451188372618746639237249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31268251163491662185649665 23451188372618746639237249)
  ·
    refine ⟨17588391279464059979427937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23451188372618746639237249 17588391279464059979427937)
    ·
      refine ⟨13191293459598044984570953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17588391279464059979427937 13191293459598044984570953)
      ·
        refine ⟨9893470094698533738428215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13191293459598044984570953 9893470094698533738428215)
        ·
          refine ⟨14840205142047800607642323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9893470094698533738428215 14840205142047800607642323)
          ·
            refine ⟨22260307713071700911463485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14840205142047800607642323 22260307713071700911463485)
            ·
              refine ⟨8347615392401887841798807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22260307713071700911463485 8347615392401887841798807)
              ·
                refine ⟨12521423088602831762698211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8347615392401887841798807 12521423088602831762698211)
                ·
                  refine ⟨18782134632904247644047317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12521423088602831762698211 18782134632904247644047317)
                  ·
                    refine ⟨440206280458693304157359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18782134632904247644047317 440206280458693304157359)
                    ·
                      rfl

theorem cell22_1285948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 1, 7].length) (baseStart_1285948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1285948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1285948 prefixEnd_1285948 := by exact prefixLift 1285948
  have htrace : WordTrace (prefixWord ++ tailWord_1285948) baseStart_1285948 baseEnd_1285948 := by
    simpa [prefixWord, tailWord_1285948, baseEnd_1285948] using wordTrace_append hprefix tailTrace_1285948
  have hstable : (prefixWord ++ tailWord_1285948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285948).length < 2 ^ (prefixWord ++ tailWord_1285948).sum := by decide
  have hdescent : baseEnd_1285948 < baseStart_1285948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285978 : List Nat := [3, 1, 1, 2, 1, 3, 1, 2, 8]
def baseStart_1285978 : Nat := 118140960795 + 1285978 * 2 ^ 59
def prefixEnd_1285978 : Nat := 4983230072969 + 3 ^ 40 * 1285978 * 2
def baseEnd_1285978 : Nat := 146738850023927741969089

theorem tailTrace_1285978 : CollatzResearch.WordTrace tailWord_1285978 prefixEnd_1285978 146738850023927741969089 := by
  unfold tailWord_1285978
  simp only [CollatzResearch.WordTrace]
  refine ⟨11725867733782202100516647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31268980623419205601377725 11725867733782202100516647)
  ·
    refine ⟨17588801600673303150774971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11725867733782202100516647 17588801600673303150774971)
    ·
      refine ⟨26383202401009954726162457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17588801600673303150774971 26383202401009954726162457)
      ·
        refine ⟨19787401800757466044621843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26383202401009954726162457 19787401800757466044621843)
        ·
          refine ⟨29681102701136199066932765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19787401800757466044621843 29681102701136199066932765)
          ·
            refine ⟨11130413512926074650099787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29681102701136199066932765 11130413512926074650099787)
            ·
              refine ⟨16695620269389111975149681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11130413512926074650099787 16695620269389111975149681)
              ·
                refine ⟨12521715202041833981362261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16695620269389111975149681 12521715202041833981362261)
                ·
                  refine ⟨146738850023927741969089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12521715202041833981362261 146738850023927741969089)
                  ·
                    rfl

theorem cell22_1285978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 8].length) (baseStart_1285978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1285978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1285978 prefixEnd_1285978 := by exact prefixLift 1285978
  have htrace : WordTrace (prefixWord ++ tailWord_1285978) baseStart_1285978 baseEnd_1285978 := by
    simpa [prefixWord, tailWord_1285978, baseEnd_1285978] using wordTrace_append hprefix tailTrace_1285978
  have hstable : (prefixWord ++ tailWord_1285978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285978).length < 2 ^ (prefixWord ++ tailWord_1285978).sum := by decide
  have hdescent : baseEnd_1285978 < baseStart_1285978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285993 : List Nat := [1, 2, 1, 1, 1, 3, 1, 4, 3, 5]
def baseStart_1285993 : Nat := 118140960795 + 1285993 * 2 ^ 59
def prefixEnd_1285993 : Nat := 4983230072969 + 3 ^ 40 * 1285993 * 2
def baseEnd_1285993 : Nat := 440221684878328186782221

theorem tailTrace_1285993 : CollatzResearch.WordTrace tailWord_1285993 prefixEnd_1285993 440221684878328186782221 := by
  unfold tailWord_1285993
  simp only [CollatzResearch.WordTrace]
  refine ⟨46904018030074465963862633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31269345353382977309241755 46904018030074465963862633)
  ·
    refine ⟨35178013522555849472896975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46904018030074465963862633 35178013522555849472896975)
    ·
      refine ⟨52767020283833774209345463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35178013522555849472896975 52767020283833774209345463)
      ·
        refine ⟨79150530425750661314018195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52767020283833774209345463 79150530425750661314018195)
        ·
          refine ⟨118725795638625991971027293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79150530425750661314018195 118725795638625991971027293)
          ·
            refine ⟨44522173364484746989135235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 118725795638625991971027293 44522173364484746989135235)
            ·
              refine ⟨66783260046727120483702853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44522173364484746989135235 66783260046727120483702853)
              ·
                refine ⟨12521861258761335090694285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66783260046727120483702853 12521861258761335090694285)
                ·
                  refine ⟨4695697972035500659010357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12521861258761335090694285 4695697972035500659010357)
                  ·
                    refine ⟨440221684878328186782221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4695697972035500659010357 440221684878328186782221)
                    ·
                      rfl

theorem cell22_1285993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 3, 5].length) (baseStart_1285993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1285993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1285993 prefixEnd_1285993 := by exact prefixLift 1285993
  have htrace : WordTrace (prefixWord ++ tailWord_1285993) baseStart_1285993 baseEnd_1285993 := by
    simpa [prefixWord, tailWord_1285993, baseEnd_1285993] using wordTrace_append hprefix tailTrace_1285993
  have hstable : (prefixWord ++ tailWord_1285993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285993).length < 2 ^ (prefixWord ++ tailWord_1285993).sum := by decide
  have hdescent : baseEnd_1285993 < baseStart_1285993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286010 : List Nat := [3, 1, 1, 1, 1, 1, 7, 1, 1, 5]
def baseStart_1286010 : Nat := 118140960795 + 1286010 * 2 ^ 59
def prefixEnd_1286010 : Nat := 4983230072969 + 3 ^ 40 * 1286010 * 2
def baseEnd_1286010 : Nat := 440227504325745809107169

theorem tailTrace_1286010 : CollatzResearch.WordTrace tailWord_1286010 prefixEnd_1286010 440227504325745809107169 := by
  unfold tailWord_1286010
  simp only [CollatzResearch.WordTrace]
  refine ⟨11726159517753219466807871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31269758714008585244820989 11726159517753219466807871)
  ·
    refine ⟨17589239276629829200211807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11726159517753219466807871 17589239276629829200211807)
    ·
      refine ⟨26383858914944743800317711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17589239276629829200211807 26383858914944743800317711)
      ·
        refine ⟨39575788372417115700476567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26383858914944743800317711 39575788372417115700476567)
        ·
          refine ⟨59363682558625673550714851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39575788372417115700476567 59363682558625673550714851)
          ·
            refine ⟨89045523837938510326072277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59363682558625673550714851 89045523837938510326072277)
            ·
              refine ⟨2087004464951683835767319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 89045523837938510326072277 2087004464951683835767319)
              ·
                refine ⟨3130506697427525753650979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2087004464951683835767319 3130506697427525753650979)
                ·
                  refine ⟨4695760046141288630476469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3130506697427525753650979 4695760046141288630476469)
                  ·
                    refine ⟨440227504325745809107169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4695760046141288630476469 440227504325745809107169)
                    ·
                      rfl

theorem cell22_1286010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 1, 1, 5].length) (baseStart_1286010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1286010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1286010 prefixEnd_1286010 := by exact prefixLift 1286010
  have htrace : WordTrace (prefixWord ++ tailWord_1286010) baseStart_1286010 baseEnd_1286010 := by
    simpa [prefixWord, tailWord_1286010, baseEnd_1286010] using wordTrace_append hprefix tailTrace_1286010
  have hstable : (prefixWord ++ tailWord_1286010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286010).length < 2 ^ (prefixWord ++ tailWord_1286010).sum := by decide
  have hdescent : baseEnd_1286010 < baseStart_1286010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286014 : List Nat := [4, 2, 3, 1, 1, 1, 1, 4, 1, 4]
def baseStart_1286014 : Nat := 118140960795 + 1286014 * 2 ^ 59
def prefixEnd_1286014 : Nat := 4983230072969 + 3 ^ 40 * 1286014 * 2
def baseEnd_1286014 : Nat := 440228873607491132007157

theorem tailTrace_1286014 : CollatzResearch.WordTrace tailWord_1286014 prefixEnd_1286014 440228873607491132007157 := by
  unfold tailWord_1286014
  simp only [CollatzResearch.WordTrace]
  refine ⟨5863097995374798318797137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31269855975332257700251397 5863097995374798318797137)
  ·
    refine ⟨4397323496531098739097853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5863097995374798318797137 4397323496531098739097853)
    ·
      refine ⟨1648996311199162027161695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4397323496531098739097853 1648996311199162027161695)
      ·
        refine ⟨2473494466798743040742543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1648996311199162027161695 2473494466798743040742543)
        ·
          refine ⟨3710241700198114561113815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2473494466798743040742543 3710241700198114561113815)
          ·
            refine ⟨5565362550297171841670723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3710241700198114561113815 5565362550297171841670723)
            ·
              refine ⟨8348043825445757762506085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5565362550297171841670723 8348043825445757762506085)
              ·
                refine ⟨1565258217271079580469891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8348043825445757762506085 1565258217271079580469891)
                ·
                  refine ⟨2347887325906619370704837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1565258217271079580469891 2347887325906619370704837)
                  ·
                    refine ⟨440228873607491132007157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2347887325906619370704837 440228873607491132007157)
                    ·
                      rfl

theorem cell22_1286014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_1286014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1286014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1286014 prefixEnd_1286014 := by exact prefixLift 1286014
  have htrace : WordTrace (prefixWord ++ tailWord_1286014) baseStart_1286014 baseEnd_1286014 := by
    simpa [prefixWord, tailWord_1286014, baseEnd_1286014] using wordTrace_append hprefix tailTrace_1286014
  have hstable : (prefixWord ++ tailWord_1286014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286014).length < 2 ^ (prefixWord ++ tailWord_1286014).sum := by decide
  have hdescent : baseEnd_1286014 < baseStart_1286014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286025 : List Nat := [1, 2, 1, 1, 5, 1, 2, 3, 2, 4]
def baseStart_1286025 : Nat := 118140960795 + 1286025 * 2 ^ 59
def prefixEnd_1286025 : Nat := 4983230072969 + 3 ^ 40 * 1286025 * 2
def baseEnd_1286025 : Nat := 440232639132290769982123

theorem tailTrace_1286025 : CollatzResearch.WordTrace tailWord_1286025 prefixEnd_1286025 440232639132290769982123 := by
  unfold tailWord_1286025
  simp only [CollatzResearch.WordTrace]
  refine ⟨46905185165958535429027529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31270123443972356952685019 46905185165958535429027529)
  ·
    refine ⟨35178888874468901571770647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46905185165958535429027529 35178888874468901571770647)
    ·
      refine ⟨52768333311703352357655971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35178888874468901571770647 52768333311703352357655971)
      ·
        refine ⟨79152499967555028536483957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52768333311703352357655971 79152499967555028536483957)
        ·
          refine ⟨7420546871958283925295371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 79152499967555028536483957 7420546871958283925295371)
          ·
            refine ⟨11130820307937425887943057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7420546871958283925295371 11130820307937425887943057)
            ·
              refine ⟨8348115230953069415957293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11130820307937425887943057 8348115230953069415957293)
              ·
                refine ⟨3130543211607401030983985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8348115230953069415957293 3130543211607401030983985)
                ·
                  refine ⟨2347907408705550773237989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3130543211607401030983985 2347907408705550773237989)
                  ·
                    refine ⟨440232639132290769982123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2347907408705550773237989 440232639132290769982123)
                    ·
                      rfl

theorem cell22_1286025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 3, 2, 4].length) (baseStart_1286025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1286025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1286025 prefixEnd_1286025 := by exact prefixLift 1286025
  have htrace : WordTrace (prefixWord ++ tailWord_1286025) baseStart_1286025 baseEnd_1286025 := by
    simpa [prefixWord, tailWord_1286025, baseEnd_1286025] using wordTrace_append hprefix tailTrace_1286025
  have hstable : (prefixWord ++ tailWord_1286025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286025).length < 2 ^ (prefixWord ++ tailWord_1286025).sum := by decide
  have hdescent : baseEnd_1286025 < baseStart_1286025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286042 : List Nat := [3, 1, 1, 4, 2, 2, 1, 2, 2, 4]
def baseStart_1286042 : Nat := 118140960795 + 1286042 * 2 ^ 59
def prefixEnd_1286042 : Nat := 4983230072969 + 3 ^ 40 * 1286042 * 2
def baseEnd_1286042 : Nat := 440238458579708392307071

theorem tailTrace_1286042 : CollatzResearch.WordTrace tailWord_1286042 prefixEnd_1286042 440238458579708392307071 := by
  unfold tailWord_1286042
  simp only [CollatzResearch.WordTrace]
  refine ⟨11726451301724236833099095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31270536804597964888264253 11726451301724236833099095)
  ·
    refine ⟨17589676952586355249648643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11726451301724236833099095 17589676952586355249648643)
    ·
      refine ⟨26384515428879532874472965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17589676952586355249648643 26384515428879532874472965)
      ·
        refine ⟨4947096642914912413963681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26384515428879532874472965 4947096642914912413963681)
        ·
          refine ⟨3710322482186184310472761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4947096642914912413963681 3710322482186184310472761)
          ·
            refine ⟨2782741861639638232854571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3710322482186184310472761 2782741861639638232854571)
            ·
              refine ⟨4174112792459457349281857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2782741861639638232854571 4174112792459457349281857)
              ·
                refine ⟨3130584594344593011961393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4174112792459457349281857 3130584594344593011961393)
                ·
                  refine ⟨2347938445758444758971045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3130584594344593011961393 2347938445758444758971045)
                  ·
                    refine ⟨440238458579708392307071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2347938445758444758971045 440238458579708392307071)
                    ·
                      rfl

theorem cell22_1286042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 2, 2, 4].length) (baseStart_1286042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1286042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1286042 prefixEnd_1286042 := by exact prefixLift 1286042
  have htrace : WordTrace (prefixWord ++ tailWord_1286042) baseStart_1286042 baseEnd_1286042 := by
    simpa [prefixWord, tailWord_1286042, baseEnd_1286042] using wordTrace_append hprefix tailTrace_1286042
  have hstable : (prefixWord ++ tailWord_1286042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286042).length < 2 ^ (prefixWord ++ tailWord_1286042).sum := by decide
  have hdescent : baseEnd_1286042 < baseStart_1286042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286046 : List Nat := [4, 3, 1, 3, 1, 2, 1, 1, 6]
def baseStart_1286046 : Nat := 118140960795 + 1286046 * 2 ^ 59
def prefixEnd_1286046 : Nat := 4983230072969 + 3 ^ 40 * 1286046 * 2
def baseEnd_1286046 : Nat := 146746609287151238402353

theorem tailTrace_1286046 : CollatzResearch.WordTrace tailWord_1286046 prefixEnd_1286046 146746609287151238402353 := by
  unfold tailWord_1286046
  simp only [CollatzResearch.WordTrace]
  refine ⟨5863243887360307001942749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31270634065921637343694661 5863243887360307001942749)
  ·
    refine ⟨2198716457760115125728531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5863243887360307001942749 2198716457760115125728531)
    ·
      refine ⟨3298074686640172688592797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2198716457760115125728531 3298074686640172688592797)
      ·
        refine ⟨1236778007490064758222299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3298074686640172688592797 1236778007490064758222299)
        ·
          refine ⟨1855167011235097137333449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1236778007490064758222299 1855167011235097137333449)
          ·
            refine ⟨1391375258426322853000087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1855167011235097137333449 1391375258426322853000087)
            ·
              refine ⟨2087062887639484279500131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1391375258426322853000087 2087062887639484279500131)
              ·
                refine ⟨3130594331459226419250197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2087062887639484279500131 3130594331459226419250197)
                ·
                  refine ⟨146746609287151238402353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3130594331459226419250197 146746609287151238402353)
                  ·
                    rfl

theorem cell22_1286046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_1286046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1286046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1286046 prefixEnd_1286046 := by exact prefixLift 1286046
  have htrace : WordTrace (prefixWord ++ tailWord_1286046) baseStart_1286046 baseEnd_1286046 := by
    simpa [prefixWord, tailWord_1286046, baseEnd_1286046] using wordTrace_append hprefix tailTrace_1286046
  have hstable : (prefixWord ++ tailWord_1286046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286046).length < 2 ^ (prefixWord ++ tailWord_1286046).sum := by decide
  have hdescent : baseEnd_1286046 < baseStart_1286046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286106 : List Nat := [3, 1, 1, 2, 5, 1, 1, 4, 1, 3]
def baseStart_1286106 : Nat := 118140960795 + 1286106 * 2 ^ 59
def prefixEnd_1286106 : Nat := 4983230072969 + 3 ^ 40 * 1286106 * 2
def baseEnd_1286106 : Nat := 440260367087633558706875

theorem tailTrace_1286106 : CollatzResearch.WordTrace tailWord_1286106 prefixEnd_1286106 440260367087633558706875 := by
  unfold tailWord_1286106
  simp only [CollatzResearch.WordTrace]
  refine ⟨11727034869666271565681543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31272092985776724175150781 11727034869666271565681543)
  ·
    refine ⟨17590552304499407348522315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11727034869666271565681543 17590552304499407348522315)
    ·
      refine ⟨26385828456749111022783473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17590552304499407348522315 26385828456749111022783473)
      ·
        refine ⟨19789371342561833267087605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26385828456749111022783473 19789371342561833267087605)
        ·
          refine ⟨1855253563365171868789463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19789371342561833267087605 1855253563365171868789463)
          ·
            refine ⟨2782880345047757803184195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1855253563365171868789463 2782880345047757803184195)
            ·
              refine ⟨4174320517571636704776293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2782880345047757803184195 4174320517571636704776293)
              ·
                refine ⟨782685097044681882145555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4174320517571636704776293 782685097044681882145555)
                ·
                  refine ⟨1174027645567022823218333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 782685097044681882145555 1174027645567022823218333)
                  ·
                    refine ⟨440260367087633558706875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1174027645567022823218333 440260367087633558706875)
                    ·
                      rfl

theorem cell22_1286106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 4, 1, 3].length) (baseStart_1286106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1286106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1286106 prefixEnd_1286106 := by exact prefixLift 1286106
  have htrace : WordTrace (prefixWord ++ tailWord_1286106) baseStart_1286106 baseEnd_1286106 := by
    simpa [prefixWord, tailWord_1286106, baseEnd_1286106] using wordTrace_append hprefix tailTrace_1286106
  have hstable : (prefixWord ++ tailWord_1286106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286106).length < 2 ^ (prefixWord ++ tailWord_1286106).sum := by decide
  have hdescent : baseEnd_1286106 < baseStart_1286106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286108 : List Nat := [2, 2, 6, 1, 2, 1, 1, 7]
def baseStart_1286108 : Nat := 118140960795 + 1286108 * 2 ^ 59
def prefixEnd_1286108 : Nat := 4983230072969 + 3 ^ 40 * 1286108 * 2
def baseEnd_1286108 : Nat := 48917894636500691128541

theorem tailTrace_1286108 : CollatzResearch.WordTrace tailWord_1286108 prefixEnd_1286108 48917894636500691128541 := by
  unfold tailWord_1286108
  simp only [CollatzResearch.WordTrace]
  refine ⟨23454106212328920302149489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31272141616438560402865985 23454106212328920302149489)
  ·
    refine ⟨17590579659246690226612117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23454106212328920302149489 17590579659246690226612117)
    ·
      refine ⟨824558421527188604372443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 17590579659246690226612117 824558421527188604372443)
      ·
        refine ⟨1236837632290782906558665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 824558421527188604372443 1236837632290782906558665)
        ·
          refine ⟨927628224218087179918999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1236837632290782906558665 927628224218087179918999)
          ·
            refine ⟨1391442336327130769878499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 927628224218087179918999 1391442336327130769878499)
            ·
              refine ⟨2087163504490696154817749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1391442336327130769878499 2087163504490696154817749)
              ·
                refine ⟨48917894636500691128541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2087163504490696154817749 48917894636500691128541)
                ·
                  rfl

theorem cell22_1286108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 7].length) (baseStart_1286108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1286108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1286108 prefixEnd_1286108 := by exact prefixLift 1286108
  have htrace : WordTrace (prefixWord ++ tailWord_1286108) baseStart_1286108 baseEnd_1286108 := by
    simpa [prefixWord, tailWord_1286108, baseEnd_1286108] using wordTrace_append hprefix tailTrace_1286108
  have hstable : (prefixWord ++ tailWord_1286108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286108).length < 2 ^ (prefixWord ++ tailWord_1286108).sum := by decide
  have hdescent : baseEnd_1286108 < baseStart_1286108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286149 : List Nat := [1, 3, 1, 1, 2, 4, 4, 1, 1, 4]
def baseStart_1286149 : Nat := 118140960795 + 1286149 * 2 ^ 59
def prefixEnd_1286149 : Nat := 4983230072969 + 3 ^ 40 * 1286149 * 2
def baseEnd_1286149 : Nat := 440275086866395779881743

theorem tailTrace_1286149 : CollatzResearch.WordTrace tailWord_1286149 prefixEnd_1286149 440275086866395779881743 := by
  unfold tailWord_1286149
  simp only [CollatzResearch.WordTrace]
  refine ⟨46909707817509304606541501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31273138545006203071027667 46909707817509304606541501)
  ·
    refine ⟨17591140431565989227453063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46909707817509304606541501 17591140431565989227453063)
    ·
      refine ⟨26386710647348983841179595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17591140431565989227453063 26386710647348983841179595)
      ·
        refine ⟨39580065971023475761769393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26386710647348983841179595 39580065971023475761769393)
        ·
          refine ⟨29685049478267606821327045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39580065971023475761769393 29685049478267606821327045)
          ·
            refine ⟨5565946777175176278998821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29685049478267606821327045 5565946777175176278998821)
            ·
              refine ⟨1043615020720345552312279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5565946777175176278998821 1043615020720345552312279)
              ·
                refine ⟨1565422531080518328468419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1043615020720345552312279 1565422531080518328468419)
                ·
                  refine ⟨2348133796620777492702629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1565422531080518328468419 2348133796620777492702629)
                  ·
                    refine ⟨440275086866395779881743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2348133796620777492702629 440275086866395779881743)
                    ·
                      rfl

theorem cell22_1286149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 4, 1, 1, 4].length) (baseStart_1286149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1286149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1286149 prefixEnd_1286149 := by exact prefixLift 1286149
  have htrace : WordTrace (prefixWord ++ tailWord_1286149) baseStart_1286149 baseEnd_1286149 := by
    simpa [prefixWord, tailWord_1286149, baseEnd_1286149] using wordTrace_append hprefix tailTrace_1286149
  have hstable : (prefixWord ++ tailWord_1286149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286149).length < 2 ^ (prefixWord ++ tailWord_1286149).sum := by decide
  have hdescent : baseEnd_1286149 < baseStart_1286149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286175 : List Nat := [1, 1, 2, 4, 1, 2, 2, 9]
def baseStart_1286175 : Nat := 118140960795 + 1286175 * 2 ^ 59
def prefixEnd_1286175 : Nat := 4983230072969 + 3 ^ 40 * 1286175 * 2
def baseEnd_1286175 : Nat := 48920443021971153192407

theorem tailTrace_1286175 : CollatzResearch.WordTrace tailWord_1286175 prefixEnd_1286175 48920443021971153192407 := by
  unfold tailWord_1286175
  simp only [CollatzResearch.WordTrace]
  refine ⟨46910656115415111046987979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31273770743610074031325319 46910656115415111046987979)
  ·
    refine ⟨70365984173122666570481969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46910656115415111046987979 70365984173122666570481969)
    ·
      refine ⟨52774488129841999927861477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70365984173122666570481969 52774488129841999927861477)
      ·
        refine ⟨9895216524345374986474027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52774488129841999927861477 9895216524345374986474027)
        ·
          refine ⟨14842824786518062479711041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9895216524345374986474027 14842824786518062479711041)
          ·
            refine ⟨11132118589888546859783281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14842824786518062479711041 11132118589888546859783281)
            ·
              refine ⟨8349088942416410144837461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11132118589888546859783281 8349088942416410144837461)
              ·
                refine ⟨48920443021971153192407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8349088942416410144837461 48920443021971153192407)
                ·
                  rfl

theorem cell22_1286175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 9].length) (baseStart_1286175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1286175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1286175 prefixEnd_1286175 := by exact prefixLift 1286175
  have htrace : WordTrace (prefixWord ++ tailWord_1286175) baseStart_1286175 baseEnd_1286175 := by
    simpa [prefixWord, tailWord_1286175, baseEnd_1286175] using wordTrace_append hprefix tailTrace_1286175
  have hstable : (prefixWord ++ tailWord_1286175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286175).length < 2 ^ (prefixWord ++ tailWord_1286175).sum := by decide
  have hdescent : baseEnd_1286175 < baseStart_1286175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286192 : List Nat := [2, 1, 1, 1, 2, 5, 4, 6]
def baseStart_1286192 : Nat := 118140960795 + 1286192 * 2 ^ 59
def prefixEnd_1286192 : Nat := 4983230072969 + 3 ^ 40 * 1286192 * 2
def baseEnd_1286192 : Nat := 48921089627239777895179

theorem tailTrace_1286192 : CollatzResearch.WordTrace tailWord_1286192 prefixEnd_1286192 48921089627239777895179 := by
  unfold tailWord_1286192
  simp only [CollatzResearch.WordTrace]
  refine ⟨23455638078176761475178415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31274184104235681966904553 23455638078176761475178415)
  ·
    refine ⟨35183457117265142212767623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23455638078176761475178415 35183457117265142212767623)
    ·
      refine ⟨52775185675897713319151435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35183457117265142212767623 52775185675897713319151435)
      ·
        refine ⟨79162778513846569978727153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52775185675897713319151435 79162778513846569978727153)
        ·
          refine ⟨59372083885384927484045365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79162778513846569978727153 59372083885384927484045365)
          ·
            refine ⟨5566132864254836951629253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 59372083885384927484045365 5566132864254836951629253)
            ·
              refine ⟨1043649912047781928430485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5566132864254836951629253 1043649912047781928430485)
              ·
                refine ⟨48921089627239777895179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1043649912047781928430485 48921089627239777895179)
                ·
                  rfl

theorem cell22_1286192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 4, 6].length) (baseStart_1286192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1286192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1286192 prefixEnd_1286192 := by exact prefixLift 1286192
  have htrace : WordTrace (prefixWord ++ tailWord_1286192) baseStart_1286192 baseEnd_1286192 := by
    simpa [prefixWord, tailWord_1286192, baseEnd_1286192] using wordTrace_append hprefix tailTrace_1286192
  have hstable : (prefixWord ++ tailWord_1286192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286192).length < 2 ^ (prefixWord ++ tailWord_1286192).sum := by decide
  have hdescent : baseEnd_1286192 < baseStart_1286192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286207 : List Nat := [1, 1, 2, 2, 3, 1, 2, 2, 5, 3]
def baseStart_1286207 : Nat := 118140960795 + 1286207 * 2 ^ 59
def prefixEnd_1286207 : Nat := 4983230072969 + 3 ^ 40 * 1286207 * 2
def baseEnd_1286207 : Nat := 440294941451702961931565

theorem tailTrace_1286207 : CollatzResearch.WordTrace tailWord_1286207 prefixEnd_1286207 440294941451702961931565 := by
  unfold tailWord_1286207
  simp only [CollatzResearch.WordTrace]
  refine ⟨46911823251299180512152875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31274548834199453674768583 46911823251299180512152875)
  ·
    refine ⟨70367734876948770768229313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46911823251299180512152875 70367734876948770768229313)
    ·
      refine ⟨52775801157711578076171985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70367734876948770768229313 52775801157711578076171985)
      ·
        refine ⟨39581850868283683557128989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52775801157711578076171985 39581850868283683557128989)
        ·
          refine ⟨14843194075606381333923371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39581850868283683557128989 14843194075606381333923371)
          ·
            refine ⟨22264791113409572000885057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14843194075606381333923371 22264791113409572000885057)
            ·
              refine ⟨16698593335057179000663793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22264791113409572000885057 16698593335057179000663793)
              ·
                refine ⟨12523945001292884250497845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16698593335057179000663793 12523945001292884250497845)
                ·
                  refine ⟨1174119843871207898484173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12523945001292884250497845 1174119843871207898484173)
                  ·
                    refine ⟨440294941451702961931565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1174119843871207898484173 440294941451702961931565)
                    ·
                      rfl

theorem cell22_1286207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 5, 3].length) (baseStart_1286207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1286207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1286207 prefixEnd_1286207 := by exact prefixLift 1286207
  have htrace : WordTrace (prefixWord ++ tailWord_1286207) baseStart_1286207 baseEnd_1286207 := by
    simpa [prefixWord, tailWord_1286207, baseEnd_1286207] using wordTrace_append hprefix tailTrace_1286207
  have hstable : (prefixWord ++ tailWord_1286207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286207).length < 2 ^ (prefixWord ++ tailWord_1286207).sum := by decide
  have hdescent : baseEnd_1286207 < baseStart_1286207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286230 : List Nat := [5, 2, 2, 1, 1, 1, 4, 1, 2, 3]
def baseStart_1286230 : Nat := 118140960795 + 1286230 * 2 ^ 59
def prefixEnd_1286230 : Nat := 4983230072969 + 3 ^ 40 * 1286230 * 2
def baseEnd_1286230 : Nat := 440302814821738568606495

theorem tailTrace_1286230 : CollatzResearch.WordTrace tailWord_1286230 prefixEnd_1286230 440302814821738568606495 := by
  unfold tailWord_1286230
  simp only [CollatzResearch.WordTrace]
  refine ⟨2932041383138490965015009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31275108086810570293493429 2932041383138490965015009)
  ·
    refine ⟨2199031037353868223761257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2932041383138490965015009 2199031037353868223761257)
    ·
      refine ⟨1649273278015401167820943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2199031037353868223761257 1649273278015401167820943)
      ·
        refine ⟨2473909917023101751731415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1649273278015401167820943 2473909917023101751731415)
        ·
          refine ⟨3710864875534652627597123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2473909917023101751731415 3710864875534652627597123)
          ·
            refine ⟨5566297313301978941395685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3710864875534652627597123 5566297313301978941395685)
            ·
              refine ⟨1043680746244121051511691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5566297313301978941395685 1043680746244121051511691)
              ·
                refine ⟨1565521119366181577267537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1043680746244121051511691 1565521119366181577267537)
                ·
                  refine ⟨1174140839524636182950653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1565521119366181577267537 1174140839524636182950653)
                  ·
                    refine ⟨440302814821738568606495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1174140839524636182950653 440302814821738568606495)
                    ·
                      rfl

theorem cell22_1286230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_1286230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1286230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1286230 prefixEnd_1286230 := by exact prefixLift 1286230
  have htrace : WordTrace (prefixWord ++ tailWord_1286230) baseStart_1286230 baseEnd_1286230 := by
    simpa [prefixWord, tailWord_1286230, baseEnd_1286230] using wordTrace_append hprefix tailTrace_1286230
  have hstable : (prefixWord ++ tailWord_1286230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286230).length < 2 ^ (prefixWord ++ tailWord_1286230).sum := by decide
  have hdescent : baseEnd_1286230 < baseStart_1286230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286327 : List Nat := [1, 1, 3, 1, 4, 3, 9]
def baseStart_1286327 : Nat := 118140960795 + 1286327 * 2 ^ 59
def prefixEnd_1286327 : Nat := 4983230072969 + 3 ^ 40 * 1286327 * 2
def baseEnd_1286327 : Nat := 16308741477928246256711

theorem tailTrace_1286327 : CollatzResearch.WordTrace tailWord_1286327 prefixEnd_1286327 16308741477928246256711 := by
  unfold tailWord_1286327
  simp only [CollatzResearch.WordTrace]
  refine ⟨46916200010864441006521235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31277466673909627337680823 46916200010864441006521235)
  ·
    refine ⟨70374300016296661509781853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46916200010864441006521235 70374300016296661509781853)
    ·
      refine ⟨26390362506111248066168195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70374300016296661509781853 26390362506111248066168195)
      ·
        refine ⟨39585543759166872099252293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26390362506111248066168195 39585543759166872099252293)
        ·
          refine ⟨7422289454843788518609805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39585543759166872099252293 7422289454843788518609805)
          ·
            refine ⟨2783358545566420694478677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7422289454843788518609805 2783358545566420694478677)
            ·
              refine ⟨16308741477928246256711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2783358545566420694478677 16308741477928246256711)
              ·
                rfl

theorem cell22_1286327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 9].length) (baseStart_1286327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1286327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1286327 prefixEnd_1286327 := by exact prefixLift 1286327
  have htrace : WordTrace (prefixWord ++ tailWord_1286327) baseStart_1286327 baseEnd_1286327 := by
    simpa [prefixWord, tailWord_1286327, baseEnd_1286327] using wordTrace_append hprefix tailTrace_1286327
  have hstable : (prefixWord ++ tailWord_1286327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286327).length < 2 ^ (prefixWord ++ tailWord_1286327).sum := by decide
  have hdescent : baseEnd_1286327 < baseStart_1286327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286348 : List Nat := [2, 2, 1, 6, 1, 2, 1, 1, 1, 5]
def baseStart_1286348 : Nat := 118140960795 + 1286348 * 2 ^ 59
def prefixEnd_1286348 : Nat := 4983230072969 + 3 ^ 40 * 1286348 * 2
def baseEnd_1286348 : Nat := 440343208633225594156133

theorem tailTrace_1286348 : CollatzResearch.WordTrace tailWord_1286348 prefixEnd_1286348 440343208633225594156133 := by
  unfold tailWord_1286348
  simp only [CollatzResearch.WordTrace]
  refine ⟨23458482971894180796517849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31277977295858907728690465 23458482971894180796517849)
  ·
    refine ⟨17593862228920635597388387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23458482971894180796517849 17593862228920635597388387)
    ·
      refine ⟨26390793343380953396082581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17593862228920635597388387 26390793343380953396082581)
      ·
        refine ⟨1237068437970982190441371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 26390793343380953396082581 1237068437970982190441371)
        ·
          refine ⟨1855602656956473285662057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1237068437970982190441371 1855602656956473285662057)
          ·
            refine ⟨1391701992717354964246543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1855602656956473285662057 1391701992717354964246543)
            ·
              refine ⟨2087552989076032446369815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1391701992717354964246543 2087552989076032446369815)
              ·
                refine ⟨3131329483614048669554723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2087552989076032446369815 3131329483614048669554723)
                ·
                  refine ⟨4696994225421073004332085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3131329483614048669554723 4696994225421073004332085)
                  ·
                    refine ⟨440343208633225594156133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4696994225421073004332085 440343208633225594156133)
                    ·
                      rfl

theorem cell22_1286348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 1, 1, 5].length) (baseStart_1286348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1286348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1286348 prefixEnd_1286348 := by exact prefixLift 1286348
  have htrace : WordTrace (prefixWord ++ tailWord_1286348) baseStart_1286348 baseEnd_1286348 := by
    simpa [prefixWord, tailWord_1286348, baseEnd_1286348] using wordTrace_append hprefix tailTrace_1286348
  have hstable : (prefixWord ++ tailWord_1286348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286348).length < 2 ^ (prefixWord ++ tailWord_1286348).sum := by decide
  have hdescent : baseEnd_1286348 < baseStart_1286348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286451 : List Nat := [1, 1, 1, 2, 5, 1, 3, 4, 4]
def baseStart_1286451 : Nat := 118140960795 + 1286451 * 2 ^ 59
def prefixEnd_1286451 : Nat := 4983230072969 + 3 ^ 40 * 1286451 * 2
def baseEnd_1286451 : Nat := 146792822546055886276939

theorem tailTrace_1286451 : CollatzResearch.WordTrace tailWord_1286451 prefixEnd_1286451 146792822546055886276939 := by
  unfold tailWord_1286451
  simp only [CollatzResearch.WordTrace]
  refine ⟨46920722662415210184035207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31280481774943473456023471 46920722662415210184035207)
  ·
    refine ⟨70381083993622815276052811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46920722662415210184035207 70381083993622815276052811)
    ·
      refine ⟨105571625990434222914079217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70381083993622815276052811 105571625990434222914079217)
      ·
        refine ⟨79178719492825667185559413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105571625990434222914079217 79178719492825667185559413)
        ·
          refine ⟨7423004952452406298646195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 79178719492825667185559413 7423004952452406298646195)
          ·
            refine ⟨11134507428678609447969293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7423004952452406298646195 11134507428678609447969293)
            ·
              refine ⟨4175440285754478542988485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11134507428678609447969293 4175440285754478542988485)
              ·
                refine ⟨782895053578964726810341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4175440285754478542988485 782895053578964726810341)
                ·
                  refine ⟨146792822546055886276939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 782895053578964726810341 146792822546055886276939)
                  ·
                    rfl

theorem cell22_1286451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 4, 4].length) (baseStart_1286451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1286451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1286451 prefixEnd_1286451 := by exact prefixLift 1286451
  have htrace : WordTrace (prefixWord ++ tailWord_1286451) baseStart_1286451 baseEnd_1286451 := by
    simpa [prefixWord, tailWord_1286451, baseEnd_1286451] using wordTrace_append hprefix tailTrace_1286451
  have hstable : (prefixWord ++ tailWord_1286451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286451).length < 2 ^ (prefixWord ++ tailWord_1286451).sum := by decide
  have hdescent : baseEnd_1286451 < baseStart_1286451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286468 : List Nat := [2, 3, 4, 1, 2, 1, 1, 2, 6]
def baseStart_1286468 : Nat := 118140960795 + 1286468 * 2 ^ 59
def prefixEnd_1286468 : Nat := 4983230072969 + 3 ^ 40 * 1286468 * 2
def baseEnd_1286468 : Nat := 146794762361861760385255

theorem tailTrace_1286468 : CollatzResearch.WordTrace tailWord_1286468 prefixEnd_1286468 146794762361861760385255 := by
  unfold tailWord_1286468
  simp only [CollatzResearch.WordTrace]
  refine ⟨23460671351676811043702029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31280895135569081391602705 23460671351676811043702029)
  ·
    refine ⟨8797751756878804141388261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23460671351676811043702029 8797751756878804141388261)
    ·
      refine ⟨1649578454414775776510299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8797751756878804141388261 1649578454414775776510299)
      ·
        refine ⟨2474367681622163664765449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1649578454414775776510299 2474367681622163664765449)
        ·
          refine ⟨1855775761216622748574087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2474367681622163664765449 1855775761216622748574087)
          ·
            refine ⟨2783663641824934122861131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1855775761216622748574087 2783663641824934122861131)
            ·
              refine ⟨4175495462737401184291697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2783663641824934122861131 4175495462737401184291697)
              ·
                refine ⟨3131621597053050888218773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4175495462737401184291697 3131621597053050888218773)
                ·
                  refine ⟨146794762361861760385255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3131621597053050888218773 146794762361861760385255)
                  ·
                    rfl

theorem cell22_1286468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 2, 6].length) (baseStart_1286468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1286468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1286468 prefixEnd_1286468 := by exact prefixLift 1286468
  have htrace : WordTrace (prefixWord ++ tailWord_1286468) baseStart_1286468 baseEnd_1286468 := by
    simpa [prefixWord, tailWord_1286468, baseEnd_1286468] using wordTrace_append hprefix tailTrace_1286468
  have hstable : (prefixWord ++ tailWord_1286468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286468).length < 2 ^ (prefixWord ++ tailWord_1286468).sum := by decide
  have hdescent : baseEnd_1286468 < baseStart_1286468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286481 : List Nat := [1, 2, 2, 1, 4, 2, 3, 1, 2, 4]
def baseStart_1286481 : Nat := 118140960795 + 1286481 * 2 ^ 59
def prefixEnd_1286481 : Nat := 4983230072969 + 3 ^ 40 * 1286481 * 2
def baseEnd_1286481 : Nat := 440388737251257580580725

theorem tailTrace_1286481 : CollatzResearch.WordTrace tailWord_1286481 prefixEnd_1286481 440388737251257580580725 := by
  unfold tailWord_1286481
  simp only [CollatzResearch.WordTrace]
  refine ⟨46921816852306525307627297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31281211234871016871751531 46921816852306525307627297)
  ·
    refine ⟨35191362639229893980720473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46921816852306525307627297 35191362639229893980720473)
    ·
      refine ⟨26393521979422420485540355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35191362639229893980720473 26393521979422420485540355)
      ·
        refine ⟨39590282969133630728310533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26393521979422420485540355 39590282969133630728310533)
        ·
          refine ⟨7423178056712555761558225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39590282969133630728310533 7423178056712555761558225)
          ·
            refine ⟨5567383542534416821168669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7423178056712555761558225 5567383542534416821168669)
            ·
              refine ⟨2087768828450406307938251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5567383542534416821168669 2087768828450406307938251)
              ·
                refine ⟨3131653242675609461907377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2087768828450406307938251 3131653242675609461907377)
                ·
                  refine ⟨2348739932006707096430533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3131653242675609461907377 2348739932006707096430533)
                  ·
                    refine ⟨440388737251257580580725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2348739932006707096430533 440388737251257580580725)
                    ·
                      rfl

theorem cell22_1286481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 1, 2, 4].length) (baseStart_1286481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1286481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1286481 prefixEnd_1286481 := by exact prefixLift 1286481
  have htrace : WordTrace (prefixWord ++ tailWord_1286481) baseStart_1286481 baseEnd_1286481 := by
    simpa [prefixWord, tailWord_1286481, baseEnd_1286481] using wordTrace_append hprefix tailTrace_1286481
  have hstable : (prefixWord ++ tailWord_1286481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286481).length < 2 ^ (prefixWord ++ tailWord_1286481).sum := by decide
  have hdescent : baseEnd_1286481 < baseStart_1286481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286558 : List Nat := [4, 3, 1, 2, 1, 1, 2, 1, 7]
def baseStart_1286558 : Nat := 118140960795 + 1286558 * 2 ^ 59
def prefixEnd_1286558 : Nat := 4983230072969 + 3 ^ 40 * 1286558 * 2
def baseEnd_1286558 : Nat := 146805031974951682135163

theorem tailTrace_1286558 : CollatzResearch.WordTrace tailWord_1286558 prefixEnd_1286558 146805031974951682135163 := by
  unfold tailWord_1286558
  simp only [CollatzResearch.WordTrace]
  refine ⟨5865578159128445932272541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31283083515351711638786885 5865578159128445932272541)
  ·
    refine ⟨2199591809673167224602203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5865578159128445932272541 2199591809673167224602203)
    ·
      refine ⟨3299387714509750836903305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2199591809673167224602203 3299387714509750836903305)
      ·
        refine ⟨2474540785882313127677479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3299387714509750836903305 2474540785882313127677479)
        ·
          refine ⟨3711811178823469691516219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2474540785882313127677479 3711811178823469691516219)
          ·
            refine ⟨5567716768235204537274329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3711811178823469691516219 5567716768235204537274329)
            ·
              refine ⟨4175787576176403402955747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5567716768235204537274329 4175787576176403402955747)
              ·
                refine ⟨6263681364264605104433621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4175787576176403402955747 6263681364264605104433621)
                ·
                  refine ⟨146805031974951682135163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6263681364264605104433621 146805031974951682135163)
                  ·
                    rfl

theorem cell22_1286558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_1286558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1286558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1286558 prefixEnd_1286558 := by exact prefixLift 1286558
  have htrace : WordTrace (prefixWord ++ tailWord_1286558) baseStart_1286558 baseEnd_1286558 := by
    simpa [prefixWord, tailWord_1286558, baseEnd_1286558] using wordTrace_append hprefix tailTrace_1286558
  have hstable : (prefixWord ++ tailWord_1286558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286558).length < 2 ^ (prefixWord ++ tailWord_1286558).sum := by decide
  have hdescent : baseEnd_1286558 < baseStart_1286558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286562 : List Nat := [3, 3, 1, 2, 1, 1, 5, 2, 1, 3]
def baseStart_1286562 : Nat := 118140960795 + 1286562 * 2 ^ 59
def prefixEnd_1286562 : Nat := 4983230072969 + 3 ^ 40 * 1286562 * 2
def baseEnd_1286562 : Nat := 440416465206600369305477

theorem tailTrace_1286562 : CollatzResearch.WordTrace tailWord_1286562 prefixEnd_1286562 440416465206600369305477 := by
  unfold tailWord_1286562
  simp only [CollatzResearch.WordTrace]
  refine ⟨11731192791253269035331485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31283180776675384094217293 11731192791253269035331485)
  ·
    refine ⟨4399197296719975888249307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11731192791253269035331485 4399197296719975888249307)
    ·
      refine ⟨6598795945079963832373961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4399197296719975888249307 6598795945079963832373961)
      ·
        refine ⟨4949096958809972874280471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6598795945079963832373961 4949096958809972874280471)
        ·
          refine ⟨7423645438214959311420707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4949096958809972874280471 7423645438214959311420707)
          ·
            refine ⟨11135468157322438967131061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7423645438214959311420707 11135468157322438967131061)
            ·
              refine ⟨1043950139748978653168537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11135468157322438967131061 1043950139748978653168537)
              ·
                refine ⟨782962604811733989876403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1043950139748978653168537 782962604811733989876403)
                ·
                  refine ⟨1174443907217600984814605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 782962604811733989876403 1174443907217600984814605)
                  ·
                    refine ⟨440416465206600369305477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1174443907217600984814605 440416465206600369305477)
                    ·
                      rfl

theorem cell22_1286562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 5, 2, 1, 3].length) (baseStart_1286562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1286562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1286562 prefixEnd_1286562 := by exact prefixLift 1286562
  have htrace : WordTrace (prefixWord ++ tailWord_1286562) baseStart_1286562 baseEnd_1286562 := by
    simpa [prefixWord, tailWord_1286562, baseEnd_1286562] using wordTrace_append hprefix tailTrace_1286562
  have hstable : (prefixWord ++ tailWord_1286562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286562).length < 2 ^ (prefixWord ++ tailWord_1286562).sum := by decide
  have hdescent : baseEnd_1286562 < baseStart_1286562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286588 : List Nat := [2, 2, 2, 4, 1, 2, 1, 1, 3, 4]
def baseStart_1286588 : Nat := 118140960795 + 1286588 * 2 ^ 59
def prefixEnd_1286588 : Nat := 4983230072969 + 3 ^ 40 * 1286588 * 2
def baseEnd_1286588 : Nat := 440425365537944968155397

theorem tailTrace_1286588 : CollatzResearch.WordTrace tailWord_1286588 prefixEnd_1286588 440425365537944968155397 := by
  unfold tailWord_1286588
  simp only [CollatzResearch.WordTrace]
  refine ⟨23462859731459441290886209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31283812975279255054514945 23462859731459441290886209)
  ·
    refine ⟨17597144798594580968164657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23462859731459441290886209 17597144798594580968164657)
    ·
      refine ⟨13197858598945935726123493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17597144798594580968164657 13197858598945935726123493)
      ·
        refine ⟨2474598487302362948648155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13197858598945935726123493 2474598487302362948648155)
        ·
          refine ⟨3711897730953544422972233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2474598487302362948648155 3711897730953544422972233)
          ·
            refine ⟨2783923298215158317229175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3711897730953544422972233 2783923298215158317229175)
            ·
              refine ⟨4175884947322737475843763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2783923298215158317229175 4175884947322737475843763)
              ·
                refine ⟨6263827420984106213765645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4175884947322737475843763 6263827420984106213765645)
                ·
                  refine ⟨2348935282869039830162117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6263827420984106213765645 2348935282869039830162117)
                  ·
                    refine ⟨440425365537944968155397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2348935282869039830162117 440425365537944968155397)
                    ·
                      rfl

theorem cell22_1286588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 1, 3, 4].length) (baseStart_1286588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1286588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1286588 prefixEnd_1286588 := by exact prefixLift 1286588
  have htrace : WordTrace (prefixWord ++ tailWord_1286588) baseStart_1286588 baseEnd_1286588 := by
    simpa [prefixWord, tailWord_1286588, baseEnd_1286588] using wordTrace_append hprefix tailTrace_1286588
  have hstable : (prefixWord ++ tailWord_1286588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286588).length < 2 ^ (prefixWord ++ tailWord_1286588).sum := by decide
  have hdescent : baseEnd_1286588 < baseStart_1286588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286601 : List Nat := [1, 2, 1, 1, 2, 1, 4, 1, 6, 3]
def baseStart_1286601 : Nat := 118140960795 + 1286601 * 2 ^ 59
def prefixEnd_1286601 : Nat := 4983230072969 + 3 ^ 40 * 1286601 * 2
def baseEnd_1286601 : Nat := 440429815703617267580357

theorem tailTrace_1286601 : CollatzResearch.WordTrace tailWord_1286601 prefixEnd_1286601 440429815703617267580357 := by
  unfold tailWord_1286601
  simp only [CollatzResearch.WordTrace]
  refine ⟨46926193611871785801995657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31284129074581190534663771 46926193611871785801995657)
  ·
    refine ⟨35194645208903839351496743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46926193611871785801995657 35194645208903839351496743)
    ·
      refine ⟨52791967813355759027245115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35194645208903839351496743 52791967813355759027245115)
      ·
        refine ⟨79187951720033638540867673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52791967813355759027245115 79187951720033638540867673)
        ·
          refine ⟨59390963790025228905650755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79187951720033638540867673 59390963790025228905650755)
          ·
            refine ⟨89086445685037843358476133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59390963790025228905650755 89086445685037843358476133)
            ·
              refine ⟨16703708565944595629714275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 89086445685037843358476133 16703708565944595629714275)
              ·
                refine ⟨25055562848916893444571413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16703708565944595629714275 25055562848916893444571413)
                ·
                  refine ⟨1174479508542979380214285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 25055562848916893444571413 1174479508542979380214285)
                  ·
                    refine ⟨440429815703617267580357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1174479508542979380214285 440429815703617267580357)
                    ·
                      rfl

theorem cell22_1286601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 6, 3].length) (baseStart_1286601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1286601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1286601 prefixEnd_1286601 := by exact prefixLift 1286601
  have htrace : WordTrace (prefixWord ++ tailWord_1286601) baseStart_1286601 baseEnd_1286601 := by
    simpa [prefixWord, tailWord_1286601, baseEnd_1286601] using wordTrace_append hprefix tailTrace_1286601
  have hstable : (prefixWord ++ tailWord_1286601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286601).length < 2 ^ (prefixWord ++ tailWord_1286601).sum := by decide
  have hdescent : baseEnd_1286601 < baseStart_1286601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286669 : List Nat := [1, 7, 1, 1, 1, 1, 3, 2, 2, 3]
def baseStart_1286669 : Nat := 118140960795 + 1286669 * 2 ^ 59
def prefixEnd_1286669 : Nat := 4983230072969 + 3 ^ 40 * 1286669 * 2
def baseEnd_1286669 : Nat := 440453093493287756880149

theorem tailTrace_1286669 : CollatzResearch.WordTrace tailWord_1286669 prefixEnd_1286669 440453093493287756880149 := by
  unfold tailWord_1286669
  simp only [CollatzResearch.WordTrace]
  refine ⟨46928673775625433415471061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31285782517083622276980707 46928673775625433415471061)
  ·
    refine ⟨1099890791616221095675103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 46928673775625433415471061 1099890791616221095675103)
    ·
      refine ⟨1649836187424331643512655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1099890791616221095675103 1649836187424331643512655)
      ·
        refine ⟨2474754281136497465268983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1649836187424331643512655 2474754281136497465268983)
        ·
          refine ⟨3712131421704746197903475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2474754281136497465268983 3712131421704746197903475)
          ·
            refine ⟨5568197132557119296855213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3712131421704746197903475 5568197132557119296855213)
            ·
              refine ⟨2088073924708919736320705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5568197132557119296855213 2088073924708919736320705)
              ·
                refine ⟨1566055443531689802240529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2088073924708919736320705 1566055443531689802240529)
                ·
                  refine ⟨1174541582648767351680397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1566055443531689802240529 1174541582648767351680397)
                  ·
                    refine ⟨440453093493287756880149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1174541582648767351680397 440453093493287756880149)
                    ·
                      rfl

theorem cell22_1286669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_1286669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1286669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1286669 prefixEnd_1286669 := by exact prefixLift 1286669
  have htrace : WordTrace (prefixWord ++ tailWord_1286669) baseStart_1286669 baseEnd_1286669 := by
    simpa [prefixWord, tailWord_1286669, baseEnd_1286669] using wordTrace_append hprefix tailTrace_1286669
  have hstable : (prefixWord ++ tailWord_1286669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286669).length < 2 ^ (prefixWord ++ tailWord_1286669).sum := by decide
  have hdescent : baseEnd_1286669 < baseStart_1286669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286680 : List Nat := [2, 1, 2, 3, 3, 2, 2, 1, 3, 3]
def baseStart_1286680 : Nat := 118140960795 + 1286680 * 2 ^ 59
def prefixEnd_1286680 : Nat := 4983230072969 + 3 ^ 40 * 1286680 * 2
def baseEnd_1286680 : Nat := 440456859018087394855115

theorem tailTrace_1286680 : CollatzResearch.WordTrace tailWord_1286680 prefixEnd_1286680 440456859018087394855115 := by
  unfold tailWord_1286680
  simp only [CollatzResearch.WordTrace]
  refine ⟨23464537489292791147060747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31286049985723721529414329 23464537489292791147060747)
  ·
    refine ⟨35196806233939186720591121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23464537489292791147060747 35196806233939186720591121)
    ·
      refine ⟨26397604675454390040443341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35196806233939186720591121 26397604675454390040443341)
      ·
        refine ⟨9899101753295396265166253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26397604675454390040443341 9899101753295396265166253)
        ·
          refine ⟨3712163157485773599437345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9899101753295396265166253 3712163157485773599437345)
          ·
            refine ⟨2784122368114330199578009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3712163157485773599437345 2784122368114330199578009)
            ·
              refine ⟨2088091776085747649683507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2784122368114330199578009 2088091776085747649683507)
              ·
                refine ⟨3132137664128621474525261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2088091776085747649683507 3132137664128621474525261)
                ·
                  refine ⟨1174551624048233052946973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3132137664128621474525261 1174551624048233052946973)
                  ·
                    refine ⟨440456859018087394855115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1174551624048233052946973 440456859018087394855115)
                    ·
                      rfl

theorem cell22_1286680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 1, 3, 3].length) (baseStart_1286680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1286680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1286680 prefixEnd_1286680 := by exact prefixLift 1286680
  have htrace : WordTrace (prefixWord ++ tailWord_1286680) baseStart_1286680 baseEnd_1286680 := by
    simpa [prefixWord, tailWord_1286680, baseEnd_1286680] using wordTrace_append hprefix tailTrace_1286680
  have hstable : (prefixWord ++ tailWord_1286680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286680).length < 2 ^ (prefixWord ++ tailWord_1286680).sum := by decide
  have hdescent : baseEnd_1286680 < baseStart_1286680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286736 : List Nat := [2, 1, 1, 1, 1, 3, 2, 1, 5, 5]
def baseStart_1286736 : Nat := 118140960795 + 1286736 * 2 ^ 59
def prefixEnd_1286736 : Nat := 4983230072969 + 3 ^ 40 * 1286736 * 2
def baseEnd_1286736 : Nat := 440476028962521915454943

theorem tailTrace_1286736 : CollatzResearch.WordTrace tailWord_1286736 prefixEnd_1286736 440476028962521915454943 := by
  unfold tailWord_1286736
  simp only [CollatzResearch.WordTrace]
  refine ⟨23465558733191351929080031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31287411644255135905440041 23465558733191351929080031)
  ·
    refine ⟨35198338099787027893620047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23465558733191351929080031 35198338099787027893620047)
    ·
      refine ⟨52797507149680541840430071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35198338099787027893620047 52797507149680541840430071)
      ·
        refine ⟨79196260724520812760645107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52797507149680541840430071 79196260724520812760645107)
        ·
          refine ⟨118794391086781219140967661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79196260724520812760645107 118794391086781219140967661)
          ·
            refine ⟨44547896657542957177862873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 118794391086781219140967661 44547896657542957177862873)
            ·
              refine ⟨33410922493157217883397155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44547896657542957177862873 33410922493157217883397155)
              ·
                refine ⟨50116383739735826825095733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33410922493157217883397155 50116383739735826825095733)
                ·
                  refine ⟨4698410975600233764852725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50116383739735826825095733 4698410975600233764852725)
                  ·
                    refine ⟨440476028962521915454943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4698410975600233764852725 440476028962521915454943)
                    ·
                      rfl

theorem cell22_1286736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 5, 5].length) (baseStart_1286736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1286736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1286736 prefixEnd_1286736 := by exact prefixLift 1286736
  have htrace : WordTrace (prefixWord ++ tailWord_1286736) baseStart_1286736 baseEnd_1286736 := by
    simpa [prefixWord, tailWord_1286736, baseEnd_1286736] using wordTrace_append hprefix tailTrace_1286736
  have hstable : (prefixWord ++ tailWord_1286736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286736).length < 2 ^ (prefixWord ++ tailWord_1286736).sum := by decide
  have hdescent : baseEnd_1286736 < baseStart_1286736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286751 : List Nat := [1, 1, 2, 3, 1, 1, 1, 3, 3, 6]
def baseStart_1286751 : Nat := 118140960795 + 1286751 * 2 ^ 59
def prefixEnd_1286751 : Nat := 4983230072969 + 3 ^ 40 * 1286751 * 2
def baseEnd_1286751 : Nat := 440481163769066876329897

theorem tailTrace_1286751 : CollatzResearch.WordTrace tailWord_1286751 prefixEnd_1286751 440481163769066876329897 := by
  unfold tailWord_1286751
  simp only [CollatzResearch.WordTrace]
  refine ⟨46931664561328361419956107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31287776374218907613304071 46931664561328361419956107)
  ·
    refine ⟨70397496841992542129934161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46931664561328361419956107 70397496841992542129934161)
    ·
      refine ⟨52798122631494406597450621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70397496841992542129934161 52798122631494406597450621)
      ·
        refine ⟨19799295986810402474043983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52798122631494406597450621 19799295986810402474043983)
        ·
          refine ⟨29698943980215603711065975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19799295986810402474043983 29698943980215603711065975)
          ·
            refine ⟨44548415970323405566598963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29698943980215603711065975 44548415970323405566598963)
            ·
              refine ⟨66822623955485108349898445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44548415970323405566598963 66822623955485108349898445)
              ·
                refine ⟨25058483983306915631211917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66822623955485108349898445 25058483983306915631211917)
                ·
                  refine ⟨9396931493740093361704469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25058483983306915631211917 9396931493740093361704469)
                  ·
                    refine ⟨440481163769066876329897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9396931493740093361704469 440481163769066876329897)
                    ·
                      rfl

theorem cell22_1286751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 3, 6].length) (baseStart_1286751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1286751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1286751 prefixEnd_1286751 := by exact prefixLift 1286751
  have htrace : WordTrace (prefixWord ++ tailWord_1286751) baseStart_1286751 baseEnd_1286751 := by
    simpa [prefixWord, tailWord_1286751, baseEnd_1286751] using wordTrace_append hprefix tailTrace_1286751
  have hstable : (prefixWord ++ tailWord_1286751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286751).length < 2 ^ (prefixWord ++ tailWord_1286751).sum := by decide
  have hdescent : baseEnd_1286751 < baseStart_1286751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286757 : List Nat := [1, 3, 1, 3, 4, 2, 1, 2, 1, 4]
def baseStart_1286757 : Nat := 118140960795 + 1286757 * 2 ^ 59
def prefixEnd_1286757 : Nat := 4983230072969 + 3 ^ 40 * 1286757 * 2
def baseEnd_1286757 : Nat := 440483217691684860679879

theorem tailTrace_1286757 : CollatzResearch.WordTrace tailWord_1286757 prefixEnd_1286757 440483217691684860679879 := by
  unfold tailWord_1286757
  simp only [CollatzResearch.WordTrace]
  refine ⟨46931883399306624444674525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31287922266204416296449683 46931883399306624444674525)
  ·
    refine ⟨17599456274739984166752947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46931883399306624444674525 17599456274739984166752947)
    ·
      refine ⟨26399184412109976250129421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17599456274739984166752947 26399184412109976250129421)
      ·
        refine ⟨9899694154541241093798533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26399184412109976250129421 9899694154541241093798533)
        ·
          refine ⟨1856192653976482705087225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9899694154541241093798533 1856192653976482705087225)
          ·
            refine ⟨1392144490482362028815419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1856192653976482705087225 1392144490482362028815419)
            ·
              refine ⟨2088216735723543043223129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1392144490482362028815419 2088216735723543043223129)
              ·
                refine ⟨1566162551792657282417347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2088216735723543043223129 1566162551792657282417347)
                ·
                  refine ⟨2349243827688985923626021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1566162551792657282417347 2349243827688985923626021)
                  ·
                    refine ⟨440483217691684860679879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2349243827688985923626021 440483217691684860679879)
                    ·
                      rfl

theorem cell22_1286757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 2, 1, 4].length) (baseStart_1286757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1286757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1286757 prefixEnd_1286757 := by exact prefixLift 1286757
  have htrace : WordTrace (prefixWord ++ tailWord_1286757) baseStart_1286757 baseEnd_1286757 := by
    simpa [prefixWord, tailWord_1286757, baseEnd_1286757] using wordTrace_append hprefix tailTrace_1286757
  have hstable : (prefixWord ++ tailWord_1286757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286757).length < 2 ^ (prefixWord ++ tailWord_1286757).sum := by decide
  have hdescent : baseEnd_1286757 < baseStart_1286757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286770 : List Nat := [3, 2, 1, 2, 4, 1, 1, 2, 1, 5]
def baseStart_1286770 : Nat := 118140960795 + 1286770 * 2 ^ 59
def prefixEnd_1286770 : Nat := 4983230072969 + 3 ^ 40 * 1286770 * 2
def baseEnd_1286770 : Nat := 440487667857357160104839

theorem tailTrace_1286770 : CollatzResearch.WordTrace tailWord_1286770 prefixEnd_1286770 440487667857357160104839 := by
  unfold tailWord_1286770
  simp only [CollatzResearch.WordTrace]
  refine ⟨11733089387064881916224441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31288238365506351776598509 11733089387064881916224441)
  ·
    refine ⟨8799817040298661437168331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11733089387064881916224441 8799817040298661437168331)
    ·
      refine ⟨13199725560447992155752497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8799817040298661437168331 13199725560447992155752497)
      ·
        refine ⟨9899794170335994116814373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13199725560447992155752497 9899794170335994116814373)
        ·
          refine ⟨1856211406937998896902695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9899794170335994116814373 1856211406937998896902695)
          ·
            refine ⟨2784317110406998345354043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1856211406937998896902695 2784317110406998345354043)
            ·
              refine ⟨4176475665610497518031065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2784317110406998345354043 4176475665610497518031065)
              ·
                refine ⟨3132356749207873138523299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4176475665610497518031065 3132356749207873138523299)
                ·
                  refine ⟨4698535123811809707784949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3132356749207873138523299 4698535123811809707784949)
                  ·
                    refine ⟨440487667857357160104839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4698535123811809707784949 440487667857357160104839)
                    ·
                      rfl

theorem cell22_1286770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 2, 1, 5].length) (baseStart_1286770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1286770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1286770 prefixEnd_1286770 := by exact prefixLift 1286770
  have htrace : WordTrace (prefixWord ++ tailWord_1286770) baseStart_1286770 baseEnd_1286770 := by
    simpa [prefixWord, tailWord_1286770, baseEnd_1286770] using wordTrace_append hprefix tailTrace_1286770
  have hstable : (prefixWord ++ tailWord_1286770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286770).length < 2 ^ (prefixWord ++ tailWord_1286770).sum := by decide
  have hdescent : baseEnd_1286770 < baseStart_1286770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286774 : List Nat := [5, 1, 1, 2, 3, 1, 3, 1, 1, 4]
def baseStart_1286774 : Nat := 118140960795 + 1286774 * 2 ^ 59
def prefixEnd_1286774 : Nat := 4983230072969 + 3 ^ 40 * 1286774 * 2
def baseEnd_1286774 : Nat := 440489037139102483004827

theorem tailTrace_1286774 : CollatzResearch.WordTrace tailWord_1286774 prefixEnd_1286774 440489037139102483004827 := by
  unfold tailWord_1286774
  simp only [CollatzResearch.WordTrace]
  refine ⟨2933281465015314771752711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31288335626830024232028917 2933281465015314771752711)
  ·
    refine ⟨4399922197522972157629067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2933281465015314771752711 4399922197522972157629067)
    ·
      refine ⟨6599883296284458236443601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4399922197522972157629067 6599883296284458236443601)
      ·
        refine ⟨4949912472213343677332701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6599883296284458236443601 4949912472213343677332701)
        ·
          refine ⟨1856217177080003878999763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4949912472213343677332701 1856217177080003878999763)
          ·
            refine ⟨2784325765620005818499645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1856217177080003878999763 2784325765620005818499645)
            ·
              refine ⟨1044122162107502181937367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2784325765620005818499645 1044122162107502181937367)
              ·
                refine ⟨1566183243161253272906051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1044122162107502181937367 1566183243161253272906051)
                ·
                  refine ⟨2349274864741879909359077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1566183243161253272906051 2349274864741879909359077)
                  ·
                    refine ⟨440489037139102483004827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2349274864741879909359077 440489037139102483004827)
                    ·
                      rfl

theorem cell22_1286774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 3, 1, 1, 4].length) (baseStart_1286774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1286774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1286774 prefixEnd_1286774 := by exact prefixLift 1286774
  have htrace : WordTrace (prefixWord ++ tailWord_1286774) baseStart_1286774 baseEnd_1286774 := by
    simpa [prefixWord, tailWord_1286774, baseEnd_1286774] using wordTrace_append hprefix tailTrace_1286774
  have hstable : (prefixWord ++ tailWord_1286774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286774).length < 2 ^ (prefixWord ++ tailWord_1286774).sum := by decide
  have hdescent : baseEnd_1286774 < baseStart_1286774 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286838 : List Nat := [5, 1, 3, 1, 3, 1, 1, 2, 2, 3]
def baseStart_1286838 : Nat := 118140960795 + 1286838 * 2 ^ 59
def prefixEnd_1286838 : Nat := 4983230072969 + 3 ^ 40 * 1286838 * 2
def baseEnd_1286838 : Nat := 440510945647027649404631

theorem tailTrace_1286838 : CollatzResearch.WordTrace tailWord_1286838 prefixEnd_1286838 440510945647027649404631 := by
  unfold tailWord_1286838
  simp only [CollatzResearch.WordTrace]
  refine ⟨2933427357000823454898323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31289891808008783518915445 2933427357000823454898323)
  ·
    refine ⟨4400141035501235182347485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2933427357000823454898323 4400141035501235182347485)
    ·
      refine ⟨1650052888312963193380307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4400141035501235182347485 1650052888312963193380307)
      ·
        refine ⟨2475079332469444790070461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1650052888312963193380307 2475079332469444790070461)
        ·
          refine ⟨928154749676041796276423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2475079332469444790070461 928154749676041796276423)
          ·
            refine ⟨1392232124514062694414635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 928154749676041796276423 1392232124514062694414635)
            ·
              refine ⟨2088348186771094041621953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1392232124514062694414635 2088348186771094041621953)
              ·
                refine ⟨1566261140078320531216465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2088348186771094041621953 1566261140078320531216465)
                ·
                  refine ⟨1174695855058740398412349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1566261140078320531216465 1174695855058740398412349)
                  ·
                    refine ⟨440510945647027649404631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1174695855058740398412349 440510945647027649404631)
                    ·
                      rfl

theorem cell22_1286838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_1286838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1286838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1286838 prefixEnd_1286838 := by exact prefixLift 1286838
  have htrace : WordTrace (prefixWord ++ tailWord_1286838) baseStart_1286838 baseEnd_1286838 := by
    simpa [prefixWord, tailWord_1286838, baseEnd_1286838] using wordTrace_append hprefix tailTrace_1286838
  have hstable : (prefixWord ++ tailWord_1286838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286838).length < 2 ^ (prefixWord ++ tailWord_1286838).sum := by decide
  have hdescent : baseEnd_1286838 < baseStart_1286838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286845 : List Nat := [1, 4, 1, 2, 1, 3, 3, 2, 5]
def baseStart_1286845 : Nat := 118140960795 + 1286845 * 2 ^ 59
def prefixEnd_1286845 : Nat := 4983230072969 + 3 ^ 40 * 1286845 * 2
def baseEnd_1286845 : Nat := 146837780630027321493203

theorem tailTrace_1286845 : CollatzResearch.WordTrace tailWord_1286845 prefixEnd_1286845 146837780630027321493203 := by
  unfold tailWord_1286845
  simp only [CollatzResearch.WordTrace]
  refine ⟨46935093022987815473877989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31290062015325210315918659 46935093022987815473877989)
  ·
    refine ⟨8800329941810215401352123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46935093022987815473877989 8800329941810215401352123)
    ·
      refine ⟨13200494912715323102028185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8800329941810215401352123 13200494912715323102028185)
      ·
        refine ⟨9900371184536492326521139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13200494912715323102028185 9900371184536492326521139)
        ·
          refine ⟨14850556776804738489781709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9900371184536492326521139 14850556776804738489781709)
          ·
            refine ⟨5568958791301776933668141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14850556776804738489781709 5568958791301776933668141)
            ·
              refine ⟨2088359546738166350125553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5568958791301776933668141 2088359546738166350125553)
              ·
                refine ⟨1566269660053624762594165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2088359546738166350125553 1566269660053624762594165)
                ·
                  refine ⟨146837780630027321493203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1566269660053624762594165 146837780630027321493203)
                  ·
                    rfl

theorem cell22_1286845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 2, 5].length) (baseStart_1286845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1286845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1286845 prefixEnd_1286845 := by exact prefixLift 1286845
  have htrace : WordTrace (prefixWord ++ tailWord_1286845) baseStart_1286845 baseEnd_1286845 := by
    simpa [prefixWord, tailWord_1286845, baseEnd_1286845] using wordTrace_append hprefix tailTrace_1286845
  have hstable : (prefixWord ++ tailWord_1286845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286845).length < 2 ^ (prefixWord ++ tailWord_1286845).sum := by decide
  have hdescent : baseEnd_1286845 < baseStart_1286845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286860 : List Nat := [2, 2, 1, 5, 1, 1, 2, 1, 2, 5]
def baseStart_1286860 : Nat := 118140960795 + 1286860 * 2 ^ 59
def prefixEnd_1286860 : Nat := 4983230072969 + 3 ^ 40 * 1286860 * 2
def baseEnd_1286860 : Nat := 440518476696626925354563

theorem tailTrace_1286860 : CollatzResearch.WordTrace tailWord_1286860 prefixEnd_1286860 440518476696626925354563 := by
  unfold tailWord_1286860
  simp only [CollatzResearch.WordTrace]
  refine ⟨23467820058966736517837017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31290426745288982023782689 23467820058966736517837017)
  ·
    refine ⟨17600865044225052388377763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23467820058966736517837017 17600865044225052388377763)
    ·
      refine ⟨26401297566337578582566645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17600865044225052388377763 26401297566337578582566645)
      ·
        refine ⟨2475121646844147992115623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26401297566337578582566645 2475121646844147992115623)
        ·
          refine ⟨3712682470266221988173435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2475121646844147992115623 3712682470266221988173435)
          ·
            refine ⟨5569023705399332982260153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3712682470266221988173435 5569023705399332982260153)
            ·
              refine ⟨4176767779049499736695115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5569023705399332982260153 4176767779049499736695115)
              ·
                refine ⟨6265151668574249605042673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4176767779049499736695115 6265151668574249605042673)
                ·
                  refine ⟨4698863751430687203782005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6265151668574249605042673 4698863751430687203782005)
                  ·
                    refine ⟨440518476696626925354563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4698863751430687203782005 440518476696626925354563)
                    ·
                      rfl

theorem cell22_1286860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 1, 2, 5].length) (baseStart_1286860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1286860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1286860 prefixEnd_1286860 := by exact prefixLift 1286860
  have htrace : WordTrace (prefixWord ++ tailWord_1286860) baseStart_1286860 baseEnd_1286860 := by
    simpa [prefixWord, tailWord_1286860, baseEnd_1286860] using wordTrace_append hprefix tailTrace_1286860
  have hstable : (prefixWord ++ tailWord_1286860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286860).length < 2 ^ (prefixWord ++ tailWord_1286860).sum := by decide
  have hdescent : baseEnd_1286860 < baseStart_1286860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286862 : List Nat := [4, 1, 1, 1, 3, 3, 3, 1, 5]
def baseStart_1286862 : Nat := 118140960795 + 1286862 * 2 ^ 59
def prefixEnd_1286862 : Nat := 4983230072969 + 3 ^ 40 * 1286862 * 2
def baseEnd_1286862 : Nat := 146839720445833195601519

theorem tailTrace_1286862 : CollatzResearch.WordTrace tailWord_1286862 prefixEnd_1286862 146839720445833195601519 := by
  unfold tailWord_1286862
  simp only [CollatzResearch.WordTrace]
  refine ⟨5866964132990778422155855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31290475375950818251497893 5866964132990778422155855)
  ·
    refine ⟨8800446199486167633233783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5866964132990778422155855 8800446199486167633233783)
    ·
      refine ⟨13200669299229251449850675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8800446199486167633233783 13200669299229251449850675)
      ·
        refine ⟨19801003948843877174776013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13200669299229251449850675 19801003948843877174776013)
        ·
          refine ⟨7425376480816453940541005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19801003948843877174776013 7425376480816453940541005)
          ·
            refine ⟨2784516180306170227702877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7425376480816453940541005 2784516180306170227702877)
            ·
              refine ⟨1044193567614813835388579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2784516180306170227702877 1044193567614813835388579)
              ·
                refine ⟨1566290351422220753082869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1044193567614813835388579 1566290351422220753082869)
                ·
                  refine ⟨146839720445833195601519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1566290351422220753082869 146839720445833195601519)
                  ·
                    rfl

theorem cell22_1286862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 3, 1, 5].length) (baseStart_1286862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1286862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1286862 prefixEnd_1286862 := by exact prefixLift 1286862
  have htrace : WordTrace (prefixWord ++ tailWord_1286862) baseStart_1286862 baseEnd_1286862 := by
    simpa [prefixWord, tailWord_1286862, baseEnd_1286862] using wordTrace_append hprefix tailTrace_1286862
  have hstable : (prefixWord ++ tailWord_1286862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286862).length < 2 ^ (prefixWord ++ tailWord_1286862).sum := by decide
  have hdescent : baseEnd_1286862 < baseStart_1286862 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286873 : List Nat := [1, 2, 1, 2, 3, 2, 1, 4, 6]
def baseStart_1286873 : Nat := 118140960795 + 1286873 * 2 ^ 59
def prefixEnd_1286873 : Nat := 4983230072969 + 3 ^ 40 * 1286873 * 2
def baseEnd_1286873 : Nat := 146840975620766408259841

theorem tailTrace_1286873 : CollatzResearch.WordTrace tailWord_1286873 prefixEnd_1286873 146840975620766408259841 := by
  unfold tailWord_1286873
  simp only [CollatzResearch.WordTrace]
  refine ⟨46936114266886376255897273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31290742844590917503931515 46936114266886376255897273)
  ·
    refine ⟨35202085700164782191922955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46936114266886376255897273 35202085700164782191922955)
    ·
      refine ⟨52803128550247173287884433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35202085700164782191922955 52803128550247173287884433)
      ·
        refine ⟨39602346412685379965913325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52803128550247173287884433 39602346412685379965913325)
        ·
          refine ⟨14850879904757017487217497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39602346412685379965913325 14850879904757017487217497)
          ·
            refine ⟨11138159928567763115413123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14850879904757017487217497 11138159928567763115413123)
            ·
              refine ⟨16707239892851644673119685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11138159928567763115413123 16707239892851644673119685)
              ·
                refine ⟨3132607479909683376209941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16707239892851644673119685 3132607479909683376209941)
                ·
                  refine ⟨146840975620766408259841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3132607479909683376209941 146840975620766408259841)
                  ·
                    rfl

theorem cell22_1286873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 4, 6].length) (baseStart_1286873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1286873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1286873 prefixEnd_1286873 := by exact prefixLift 1286873
  have htrace : WordTrace (prefixWord ++ tailWord_1286873) baseStart_1286873 baseEnd_1286873 := by
    simpa [prefixWord, tailWord_1286873, baseEnd_1286873] using wordTrace_append hprefix tailTrace_1286873
  have hstable : (prefixWord ++ tailWord_1286873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286873).length < 2 ^ (prefixWord ++ tailWord_1286873).sum := by decide
  have hdescent : baseEnd_1286873 < baseStart_1286873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286900 : List Nat := [2, 6, 1, 1, 2, 1, 3, 2, 1, 3]
def baseStart_1286900 : Nat := 118140960795 + 1286900 * 2 ^ 59
def prefixEnd_1286900 : Nat := 4983230072969 + 3 ^ 40 * 1286900 * 2
def baseEnd_1286900 : Nat := 440532169514080154354441

theorem tailTrace_1286900 : CollatzResearch.WordTrace tailWord_1286900 prefixEnd_1286900 440532169514080154354441 := by
  unfold tailWord_1286900
  simp only [CollatzResearch.WordTrace]
  refine ⟨23468549518894279933565077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31291399358525706578086769 23468549518894279933565077)
  ·
    refine ⟨1100088258698169371885863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 23468549518894279933565077 1100088258698169371885863)
    ·
      refine ⟨1650132388047254057828795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1100088258698169371885863 1650132388047254057828795)
      ·
        refine ⟨2475198582070881086743193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1650132388047254057828795 2475198582070881086743193)
        ·
          refine ⟨1856398936553160815057395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2475198582070881086743193 1856398936553160815057395)
          ·
            refine ⟨2784598404829741222586093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1856398936553160815057395 2784598404829741222586093)
            ·
              refine ⟨1044224401811152958469785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2784598404829741222586093 1044224401811152958469785)
              ·
                refine ⟨783168301358364718852339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1044224401811152958469785 783168301358364718852339)
                ·
                  refine ⟨1174752452037547078278509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 783168301358364718852339 1174752452037547078278509)
                  ·
                    refine ⟨440532169514080154354441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1174752452037547078278509 440532169514080154354441)
                    ·
                      rfl

theorem cell22_1286900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_1286900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1286900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1286900 prefixEnd_1286900 := by exact prefixLift 1286900
  have htrace : WordTrace (prefixWord ++ tailWord_1286900) baseStart_1286900 baseEnd_1286900 := by
    simpa [prefixWord, tailWord_1286900, baseEnd_1286900] using wordTrace_append hprefix tailTrace_1286900
  have hstable : (prefixWord ++ tailWord_1286900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286900).length < 2 ^ (prefixWord ++ tailWord_1286900).sum := by decide
  have hdescent : baseEnd_1286900 < baseStart_1286900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286922 : List Nat := [3, 1, 2, 2, 1, 2, 3, 3, 2, 3]
def baseStart_1286922 : Nat := 118140960795 + 1286922 * 2 ^ 59
def prefixEnd_1286922 : Nat := 4983230072969 + 3 ^ 40 * 1286922 * 2
def baseEnd_1286922 : Nat := 440539700563679430304373

theorem tailTrace_1286922 : CollatzResearch.WordTrace tailWord_1286922 prefixEnd_1286922 440539700563679430304373 := by
  unfold tailWord_1286922
  simp only [CollatzResearch.WordTrace]
  refine ⟨11734475360927214406107755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31291934295805905082954013 11734475360927214406107755)
  ·
    refine ⟨17601713041390821609161633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11734475360927214406107755 17601713041390821609161633)
    ·
      refine ⟨13201284781043116206871225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17601713041390821609161633 13201284781043116206871225)
      ·
        refine ⟨9900963585782337155153419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13201284781043116206871225 9900963585782337155153419)
        ·
          refine ⟨14851445378673505732730129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9900963585782337155153419 14851445378673505732730129)
          ·
            refine ⟨11138584034005129299547597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14851445378673505732730129 11138584034005129299547597)
            ·
              refine ⟨4176969012751923487330349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11138584034005129299547597 4176969012751923487330349)
              ·
                refine ⟨1566363379781971307748881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4176969012751923487330349 1566363379781971307748881)
                ·
                  refine ⟨1174772534836478480811661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1566363379781971307748881 1174772534836478480811661)
                  ·
                    refine ⟨440539700563679430304373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1174772534836478480811661 440539700563679430304373)
                    ·
                      rfl

theorem cell22_1286922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 3, 2, 3].length) (baseStart_1286922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1286922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1286922 prefixEnd_1286922 := by exact prefixLift 1286922
  have htrace : WordTrace (prefixWord ++ tailWord_1286922) baseStart_1286922 baseEnd_1286922 := by
    simpa [prefixWord, tailWord_1286922, baseEnd_1286922] using wordTrace_append hprefix tailTrace_1286922
  have hstable : (prefixWord ++ tailWord_1286922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286922).length < 2 ^ (prefixWord ++ tailWord_1286922).sum := by decide
  have hdescent : baseEnd_1286922 < baseStart_1286922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286965 : List Nat := [1, 3, 3, 1, 3, 1, 1, 1, 2, 6]
def baseStart_1286965 : Nat := 118140960795 + 1286965 * 2 ^ 59
def prefixEnd_1286965 : Nat := 4983230072969 + 3 ^ 40 * 1286965 * 2
def baseEnd_1286965 : Nat := 440554420342441651479241

theorem tailTrace_1286965 : CollatzResearch.WordTrace tailWord_1286965 prefixEnd_1286965 440554420342441651479241 := by
  unfold tailWord_1286965
  simp only [CollatzResearch.WordTrace]
  refine ⟨46939469782553075968246349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31292979855035383978830899 46939469782553075968246349)
  ·
    refine ⟨17602301168457403488092381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46939469782553075968246349 17602301168457403488092381)
    ·
      refine ⟨6600862938171526308034643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17602301168457403488092381 6600862938171526308034643)
      ·
        refine ⟨9901294407257289462051965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6600862938171526308034643 9901294407257289462051965)
        ·
          refine ⟨3712985402721483548269487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9901294407257289462051965 3712985402721483548269487)
          ·
            refine ⟨5569478104082225322404231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3712985402721483548269487 5569478104082225322404231)
            ·
              refine ⟨8354217156123337983606347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5569478104082225322404231 8354217156123337983606347)
              ·
                refine ⟨12531325734185006975409521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8354217156123337983606347 12531325734185006975409521)
                ·
                  refine ⟨9398494300638755231557141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12531325734185006975409521 9398494300638755231557141)
                  ·
                    refine ⟨440554420342441651479241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9398494300638755231557141 440554420342441651479241)
                    ·
                      rfl

theorem cell22_1286965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_1286965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1286965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1286965 prefixEnd_1286965 := by exact prefixLift 1286965
  have htrace : WordTrace (prefixWord ++ tailWord_1286965) baseStart_1286965 baseEnd_1286965 := by
    simpa [prefixWord, tailWord_1286965, baseEnd_1286965] using wordTrace_append hprefix tailTrace_1286965
  have hstable : (prefixWord ++ tailWord_1286965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286965).length < 2 ^ (prefixWord ++ tailWord_1286965).sum := by decide
  have hdescent : baseEnd_1286965 < baseStart_1286965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287025 : List Nat := [1, 2, 2, 2, 1, 4, 1, 3, 6]
def baseStart_1287025 : Nat := 118140960795 + 1287025 * 2 ^ 59
def prefixEnd_1287025 : Nat := 4983230072969 + 3 ^ 40 * 1287025 * 2
def baseEnd_1287025 : Nat := 146858319856207164993019

theorem tailTrace_1287025 : CollatzResearch.WordTrace tailWord_1287025 prefixEnd_1287025 146858319856207164993019 := by
  unfold tailWord_1287025
  simp only [CollatzResearch.WordTrace]
  refine ⟨46941658162335706215430529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31294438774890470810287019 46941658162335706215430529)
  ·
    refine ⟨35206243621751779661572897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46941658162335706215430529 35206243621751779661572897)
    ·
      refine ⟨26404682716313834746179673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35206243621751779661572897 26404682716313834746179673)
      ·
        refine ⟨19803512037235376059634755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26404682716313834746179673 19803512037235376059634755)
        ·
          refine ⟨29705268055853064089452133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19803512037235376059634755 29705268055853064089452133)
          ·
            refine ⟨5569737760472449516772275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29705268055853064089452133 5569737760472449516772275)
            ·
              refine ⟨8354606640708674275158413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5569737760472449516772275 8354606640708674275158413)
              ·
                refine ⟨3132977490265752853184405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8354606640708674275158413 3132977490265752853184405)
                ·
                  refine ⟨146858319856207164993019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3132977490265752853184405 146858319856207164993019)
                  ·
                    rfl

theorem cell22_1287025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 3, 6].length) (baseStart_1287025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1287025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1287025 prefixEnd_1287025 := by exact prefixLift 1287025
  have htrace : WordTrace (prefixWord ++ tailWord_1287025) baseStart_1287025 baseEnd_1287025 := by
    simpa [prefixWord, tailWord_1287025, baseEnd_1287025] using wordTrace_append hprefix tailTrace_1287025
  have hstable : (prefixWord ++ tailWord_1287025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287025).length < 2 ^ (prefixWord ++ tailWord_1287025).sum := by decide
  have hdescent : baseEnd_1287025 < baseStart_1287025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287040 : List Nat := [2, 1, 1, 2, 1, 2, 2, 5, 1, 5]
def baseStart_1287040 : Nat := 118140960795 + 1287040 * 2 ^ 59
def prefixEnd_1287040 : Nat := 4983230072969 + 3 ^ 40 * 1287040 * 2
def baseEnd_1287040 : Nat := 440580094375166455854011

theorem tailTrace_1287040 : CollatzResearch.WordTrace tailWord_1287040 prefixEnd_1287040 440580094375166455854011 := by
  unfold tailWord_1287040
  simp only [CollatzResearch.WordTrace]
  refine ⟨23471102628640681888613287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31294803504854242518151049 23471102628640681888613287)
  ·
    refine ⟨35206653942961022832919931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23471102628640681888613287 35206653942961022832919931)
    ·
      refine ⟨52809980914441534249379897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35206653942961022832919931 52809980914441534249379897)
      ·
        refine ⟨39607485685831150687034923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52809980914441534249379897 39607485685831150687034923)
        ·
          refine ⟨59411228528746726030552385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39607485685831150687034923 59411228528746726030552385)
          ·
            refine ⟨44558421396560044522914289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59411228528746726030552385 44558421396560044522914289)
            ·
              refine ⟨33418816047420033392185717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44558421396560044522914289 33418816047420033392185717)
              ·
                refine ⟨3133014004445628130517411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33418816047420033392185717 3133014004445628130517411)
                ·
                  refine ⟨4699521006668442195776117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3133014004445628130517411 4699521006668442195776117)
                  ·
                    refine ⟨440580094375166455854011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4699521006668442195776117 440580094375166455854011)
                    ·
                      rfl

theorem cell22_1287040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 5, 1, 5].length) (baseStart_1287040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1287040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1287040 prefixEnd_1287040 := by exact prefixLift 1287040
  have htrace : WordTrace (prefixWord ++ tailWord_1287040) baseStart_1287040 baseEnd_1287040 := by
    simpa [prefixWord, tailWord_1287040, baseEnd_1287040] using wordTrace_append hprefix tailTrace_1287040
  have hstable : (prefixWord ++ tailWord_1287040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287040).length < 2 ^ (prefixWord ++ tailWord_1287040).sum := by decide
  have hdescent : baseEnd_1287040 < baseStart_1287040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287074 : List Nat := [3, 3, 1, 2, 2, 1, 2, 1, 4, 3]
def baseStart_1287074 : Nat := 118140960795 + 1287074 * 2 ^ 59
def prefixEnd_1287074 : Nat := 4983230072969 + 3 ^ 40 * 1287074 * 2
def baseEnd_1287074 : Nat := 440591733270001700503907

theorem tailTrace_1287074 : CollatzResearch.WordTrace tailWord_1287074 prefixEnd_1287074 440591733270001700503907 := by
  unfold tailWord_1287074
  simp only [CollatzResearch.WordTrace]
  refine ⟨11735861334789546895991069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31295630226105458389309517 11735861334789546895991069)
  ·
    refine ⟨4400948000546080085996651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11735861334789546895991069 4400948000546080085996651)
    ·
      refine ⟨6601422000819120128994977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4400948000546080085996651 6601422000819120128994977)
      ·
        refine ⟨4951066500614340096746233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6601422000819120128994977 4951066500614340096746233)
        ·
          refine ⟨3713299875460755072559675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4951066500614340096746233 3713299875460755072559675)
          ·
            refine ⟨5569949813191132608839513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3713299875460755072559675 5569949813191132608839513)
            ·
              refine ⟨4177462359893349456629635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5569949813191132608839513 4177462359893349456629635)
              ·
                refine ⟨6266193539840024184944453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4177462359893349456629635 6266193539840024184944453)
                ·
                  refine ⟨1174911288720004534677085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6266193539840024184944453 1174911288720004534677085)
                  ·
                    refine ⟨440591733270001700503907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1174911288720004534677085 440591733270001700503907)
                    ·
                      rfl

theorem cell22_1287074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 1, 4, 3].length) (baseStart_1287074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1287074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1287074 prefixEnd_1287074 := by exact prefixLift 1287074
  have htrace : WordTrace (prefixWord ++ tailWord_1287074) baseStart_1287074 baseEnd_1287074 := by
    simpa [prefixWord, tailWord_1287074, baseEnd_1287074] using wordTrace_append hprefix tailTrace_1287074
  have hstable : (prefixWord ++ tailWord_1287074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287074).length < 2 ^ (prefixWord ++ tailWord_1287074).sum := by decide
  have hdescent : baseEnd_1287074 < baseStart_1287074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287179 : List Nat := [1, 1, 1, 1, 6, 3, 1, 3, 1, 4]
def baseStart_1287179 : Nat := 118140960795 + 1287179 * 2 ^ 59
def prefixEnd_1287179 : Nat := 4983230072969 + 3 ^ 40 * 1287179 * 2
def baseEnd_1287179 : Nat := 440627676915816426628585

theorem tailTrace_1287179 : CollatzResearch.WordTrace tailWord_1287179 prefixEnd_1287179 440627676915816426628585 := by
  unfold tailWord_1287179
  simp only [CollatzResearch.WordTrace]
  refine ⟨46947275003777790516536591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31298183335851860344357727 46947275003777790516536591)
  ·
    refine ⟨70420912505666685774804887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46947275003777790516536591 70420912505666685774804887)
    ·
      refine ⟨105631368758500028662207331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70420912505666685774804887 105631368758500028662207331)
      ·
        refine ⟨158447053137750042993310997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105631368758500028662207331 158447053137750042993310997)
        ·
          refine ⟨7427205615832033265311453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 158447053137750042993310997 7427205615832033265311453)
          ·
            refine ⟨2785202105937012474491795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7427205615832033265311453 2785202105937012474491795)
            ·
              refine ⟨4177803158905518711737693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2785202105937012474491795 4177803158905518711737693)
              ·
                refine ⟨1566676184589569516901635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4177803158905518711737693 1566676184589569516901635)
                ·
                  refine ⟨2350014276884354275352453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1566676184589569516901635 2350014276884354275352453)
                  ·
                    refine ⟨440627676915816426628585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2350014276884354275352453 440627676915816426628585)
                    ·
                      rfl

theorem cell22_1287179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 3, 1, 4].length) (baseStart_1287179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1287179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1287179 prefixEnd_1287179 := by exact prefixLift 1287179
  have htrace : WordTrace (prefixWord ++ tailWord_1287179) baseStart_1287179 baseEnd_1287179 := by
    simpa [prefixWord, tailWord_1287179, baseEnd_1287179] using wordTrace_append hprefix tailTrace_1287179
  have hstable : (prefixWord ++ tailWord_1287179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287179).length < 2 ^ (prefixWord ++ tailWord_1287179).sum := by decide
  have hdescent : baseEnd_1287179 < baseStart_1287179 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287194 : List Nat := [3, 1, 1, 3, 1, 2, 1, 6, 4]
def baseStart_1287194 : Nat := 118140960795 + 1287194 * 2 ^ 59
def prefixEnd_1287194 : Nat := 4983230072969 + 3 ^ 40 * 1287194 * 2
def baseEnd_1287194 : Nat := 146877603907453795834513

theorem tailTrace_1287194 : CollatzResearch.WordTrace tailWord_1287194 prefixEnd_1287194 146877603907453795834513 := by
  unfold tailWord_1287194
  simp only [CollatzResearch.WordTrace]
  refine ⟨11736955524680862019583159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31298548065815632052221757 11736955524680862019583159)
  ·
    refine ⟨17605433287021293029374739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11736955524680862019583159 17605433287021293029374739)
    ·
      refine ⟨26408149930531939544062109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17605433287021293029374739 26408149930531939544062109)
      ·
        refine ⟨9903056223949477329023291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26408149930531939544062109 9903056223949477329023291)
        ·
          refine ⟨14854584335924215993534937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9903056223949477329023291 14854584335924215993534937)
          ·
            refine ⟨11140938251943161995151203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14854584335924215993534937 11140938251943161995151203)
            ·
              refine ⟨16711407377914742992726805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11140938251943161995151203 16711407377914742992726805)
              ·
                refine ⟨783347220839753577784069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16711407377914742992726805 783347220839753577784069)
                ·
                  refine ⟨146877603907453795834513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 783347220839753577784069 146877603907453795834513)
                  ·
                    rfl

theorem cell22_1287194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 6, 4].length) (baseStart_1287194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1287194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1287194 prefixEnd_1287194 := by exact prefixLift 1287194
  have htrace : WordTrace (prefixWord ++ tailWord_1287194) baseStart_1287194 baseEnd_1287194 := by
    simpa [prefixWord, tailWord_1287194, baseEnd_1287194] using wordTrace_append hprefix tailTrace_1287194
  have hstable : (prefixWord ++ tailWord_1287194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287194).length < 2 ^ (prefixWord ++ tailWord_1287194).sum := by decide
  have hdescent : baseEnd_1287194 < baseStart_1287194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287301 : List Nat := [1, 3, 1, 1, 6, 1, 2, 2, 5]
def baseStart_1287301 : Nat := 118140960795 + 1287301 * 2 ^ 59
def prefixEnd_1287301 : Nat := 4983230072969 + 3 ^ 40 * 1287301 * 2
def baseEnd_1287301 : Nat := 146889813336349591692737

theorem tailTrace_1287301 : CollatzResearch.WordTrace tailWord_1287301 prefixEnd_1287301 146889813336349591692737 := by
  unfold tailWord_1287301
  simp only [CollatzResearch.WordTrace]
  refine ⟨46951724709335805352477757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31301149806223870234985171 46951724709335805352477757)
  ·
    refine ⟨17606896766000927007179159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46951724709335805352477757 17606896766000927007179159)
    ·
      refine ⟨26410345149001390510768739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17606896766000927007179159 26410345149001390510768739)
      ·
        refine ⟨39615517723502085766153109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26410345149001390510768739 39615517723502085766153109)
        ·
          refine ⟨1856977393289160270288427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 39615517723502085766153109 1856977393289160270288427)
          ·
            refine ⟨2785466089933740405432641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1856977393289160270288427 2785466089933740405432641)
            ·
              refine ⟨2089099567450305304074481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2785466089933740405432641 2089099567450305304074481)
              ·
                refine ⟨1566824675587728978055861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2089099567450305304074481 1566824675587728978055861)
                ·
                  refine ⟨146889813336349591692737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1566824675587728978055861 146889813336349591692737)
                  ·
                    rfl

theorem cell22_1287301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 2, 5].length) (baseStart_1287301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1287301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1287301 prefixEnd_1287301 := by exact prefixLift 1287301
  have htrace : WordTrace (prefixWord ++ tailWord_1287301) baseStart_1287301 baseEnd_1287301 := by
    simpa [prefixWord, tailWord_1287301, baseEnd_1287301] using wordTrace_append hprefix tailTrace_1287301
  have hstable : (prefixWord ++ tailWord_1287301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287301).length < 2 ^ (prefixWord ++ tailWord_1287301).sum := by decide
  have hdescent : baseEnd_1287301 < baseStart_1287301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287305 : List Nat := [1, 2, 1, 1, 4, 5, 2, 2, 1, 3]
def baseStart_1287305 : Nat := 118140960795 + 1287305 * 2 ^ 59
def prefixEnd_1287305 : Nat := 4983230072969 + 3 ^ 40 * 1287305 * 2
def baseEnd_1287305 : Nat := 440670809290794097978199

theorem tailTrace_1287305 : CollatzResearch.WordTrace tailWord_1287305 prefixEnd_1287305 440670809290794097978199 := by
  unfold tailWord_1287305
  simp only [CollatzResearch.WordTrace]
  refine ⟨46951870601321314035623369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31301247067547542690415579 46951870601321314035623369)
  ·
    refine ⟨35213902950990985526717527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46951870601321314035623369 35213902950990985526717527)
    ·
      refine ⟨52820854426486478290076291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35213902950990985526717527 52820854426486478290076291)
      ·
        refine ⟨79231281639729717435114437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52820854426486478290076291 79231281639729717435114437)
        ·
          refine ⟨14855865307449322019083957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79231281639729717435114437 14855865307449322019083957)
          ·
            refine ⟨1392737372573373939289121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14855865307449322019083957 1392737372573373939289121)
            ·
              refine ⟨1044553029430030454466841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1392737372573373939289121 1044553029430030454466841)
              ·
                refine ⟨783414772072522840850131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1044553029430030454466841 783414772072522840850131)
                ·
                  refine ⟨1175122158108784261275197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 783414772072522840850131 1175122158108784261275197)
                  ·
                    refine ⟨440670809290794097978199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1175122158108784261275197 440670809290794097978199)
                    ·
                      rfl

theorem cell22_1287305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 2, 2, 1, 3].length) (baseStart_1287305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1287305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1287305 prefixEnd_1287305 := by exact prefixLift 1287305
  have htrace : WordTrace (prefixWord ++ tailWord_1287305) baseStart_1287305 baseEnd_1287305 := by
    simpa [prefixWord, tailWord_1287305, baseEnd_1287305] using wordTrace_append hprefix tailTrace_1287305
  have hstable : (prefixWord ++ tailWord_1287305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287305).length < 2 ^ (prefixWord ++ tailWord_1287305).sum := by decide
  have hdescent : baseEnd_1287305 < baseStart_1287305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287329 : List Nat := [1, 2, 3, 3, 1, 1, 3, 2, 6]
def baseStart_1287329 : Nat := 118140960795 + 1287329 * 2 ^ 59
def prefixEnd_1287329 : Nat := 4983230072969 + 3 ^ 40 * 1287329 * 2
def baseEnd_1287329 : Nat := 146893008327088678459375

theorem tailTrace_1287329 : CollatzResearch.WordTrace tailWord_1287329 prefixEnd_1287329 146893008327088678459375 := by
  unfold tailWord_1287329
  simp only [CollatzResearch.WordTrace]
  refine ⟨46952745953234366134497041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31301830635489577422998027 46952745953234366134497041)
  ·
    refine ⟨35214559464925774600872781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46952745953234366134497041 35214559464925774600872781)
    ·
      refine ⟨13205459799347165475327293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35214559464925774600872781 13205459799347165475327293)
      ·
        refine ⟨4952047424755187053247735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13205459799347165475327293 4952047424755187053247735)
        ·
          refine ⟨7428071137132780579871603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4952047424755187053247735 7428071137132780579871603)
          ·
            refine ⟨11142106705699170869807405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7428071137132780579871603 11142106705699170869807405)
            ·
              refine ⟨4178290014637189076177777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11142106705699170869807405 4178290014637189076177777)
              ·
                refine ⟨3133717510977891807133333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4178290014637189076177777 3133717510977891807133333)
                ·
                  refine ⟨146893008327088678459375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3133717510977891807133333 146893008327088678459375)
                  ·
                    rfl

theorem cell22_1287329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 2, 6].length) (baseStart_1287329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1287329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1287329 prefixEnd_1287329 := by exact prefixLift 1287329
  have htrace : WordTrace (prefixWord ++ tailWord_1287329) baseStart_1287329 baseEnd_1287329 := by
    simpa [prefixWord, tailWord_1287329, baseEnd_1287329] using wordTrace_append hprefix tailTrace_1287329
  have hstable : (prefixWord ++ tailWord_1287329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287329).length < 2 ^ (prefixWord ++ tailWord_1287329).sum := by decide
  have hdescent : baseEnd_1287329 < baseStart_1287329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287344 : List Nat := [2, 1, 1, 1, 2, 1, 2, 3, 6, 3]
def baseStart_1287344 : Nat := 118140960795 + 1287344 * 2 ^ 59
def prefixEnd_1287344 : Nat := 4983230072969 + 3 ^ 40 * 1287344 * 2
def baseEnd_1287344 : Nat := 440684159787810996253079

theorem tailTrace_1287344 : CollatzResearch.WordTrace tailWord_1287344 prefixEnd_1287344 440684159787810996253079 := by
  unfold tailWord_1287344
  simp only [CollatzResearch.WordTrace]
  refine ⟨23476646524090011848146543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31302195365453349130862057 23476646524090011848146543)
  ·
    refine ⟨35214969786135017772219815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23476646524090011848146543 35214969786135017772219815)
    ·
      refine ⟨52822454679202526658329723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35214969786135017772219815 52822454679202526658329723)
      ·
        refine ⟨79233682018803789987494585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52822454679202526658329723 79233682018803789987494585)
        ·
          refine ⟨59425261514102842490620939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79233682018803789987494585 59425261514102842490620939)
          ·
            refine ⟨89137892271154263735931409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59425261514102842490620939 89137892271154263735931409)
            ·
              refine ⟨66853419203365697801948557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89137892271154263735931409 66853419203365697801948557)
              ·
                refine ⟨25070032201262136675730709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66853419203365697801948557 25070032201262136675730709)
                ·
                  refine ⟨1175157759434162656674877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 25070032201262136675730709 1175157759434162656674877)
                  ·
                    refine ⟨440684159787810996253079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1175157759434162656674877 440684159787810996253079)
                    ·
                      rfl

theorem cell22_1287344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 6, 3].length) (baseStart_1287344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1287344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1287344 prefixEnd_1287344 := by exact prefixLift 1287344
  have htrace : WordTrace (prefixWord ++ tailWord_1287344) baseStart_1287344 baseEnd_1287344 := by
    simpa [prefixWord, tailWord_1287344, baseEnd_1287344] using wordTrace_append hprefix tailTrace_1287344
  have hstable : (prefixWord ++ tailWord_1287344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287344).length < 2 ^ (prefixWord ++ tailWord_1287344).sum := by decide
  have hdescent : baseEnd_1287344 < baseStart_1287344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287346 : List Nat := [3, 2, 1, 1, 1, 4, 1, 5, 4]
def baseStart_1287346 : Nat := 118140960795 + 1287346 * 2 ^ 59
def prefixEnd_1287346 : Nat := 4983230072969 + 3 ^ 40 * 1287346 * 2
def baseEnd_1287346 : Nat := 146894948142894552567691

theorem tailTrace_1287346 : CollatzResearch.WordTrace tailWord_1287346 prefixEnd_1287346 146894948142894552567691 := by
  unfold tailWord_1287346
  simp only [CollatzResearch.WordTrace]
  refine ⟨11738341498543194509466473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31302243996115185358577261 11738341498543194509466473)
  ·
    refine ⟨8803756123907395882099855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11738341498543194509466473 8803756123907395882099855)
    ·
      refine ⟨13205634185861093823149783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8803756123907395882099855 13205634185861093823149783)
      ·
        refine ⟨19808451278791640734724675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13205634185861093823149783 19808451278791640734724675)
        ·
          refine ⟨29712676918187461102087013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19808451278791640734724675 29712676918187461102087013)
          ·
            refine ⟨5571126922160148956641315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29712676918187461102087013 5571126922160148956641315)
            ·
              refine ⟨8356690383240223434961973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5571126922160148956641315 8356690383240223434961973)
              ·
                refine ⟨783439723428770947027685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8356690383240223434961973 783439723428770947027685)
                ·
                  refine ⟨146894948142894552567691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 783439723428770947027685 146894948142894552567691)
                  ·
                    rfl

theorem cell22_1287346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 5, 4].length) (baseStart_1287346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1287346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1287346 prefixEnd_1287346 := by exact prefixLift 1287346
  have htrace : WordTrace (prefixWord ++ tailWord_1287346) baseStart_1287346 baseEnd_1287346 := by
    simpa [prefixWord, tailWord_1287346, baseEnd_1287346] using wordTrace_append hprefix tailTrace_1287346
  have hstable : (prefixWord ++ tailWord_1287346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287346).length < 2 ^ (prefixWord ++ tailWord_1287346).sum := by decide
  have hdescent : baseEnd_1287346 < baseStart_1287346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287359 : List Nat := [1, 1, 2, 2, 2, 2, 2, 4, 2, 4]
def baseStart_1287359 : Nat := 118140960795 + 1287359 * 2 ^ 59
def prefixEnd_1287359 : Nat := 4983230072969 + 3 ^ 40 * 1287359 * 2
def baseEnd_1287359 : Nat := 440689294594355957128033

theorem tailTrace_1287359 : CollatzResearch.WordTrace tailWord_1287359 prefixEnd_1287359 440689294594355957128033 := by
  unfold tailWord_1287359
  simp only [CollatzResearch.WordTrace]
  refine ⟨46953840143125681258089131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31302560095417120838726087 46953840143125681258089131)
  ·
    refine ⟨70430760214688521887133697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46953840143125681258089131 70430760214688521887133697)
    ·
      refine ⟨52823070161016391415350273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70430760214688521887133697 52823070161016391415350273)
      ·
        refine ⟨39617302620762293561512705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52823070161016391415350273 39617302620762293561512705)
        ·
          refine ⟨29712976965571720171134529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39617302620762293561512705 29712976965571720171134529)
          ·
            refine ⟨22284732724178790128350897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29712976965571720171134529 22284732724178790128350897)
            ·
              refine ⟨16713549543134092596263173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22284732724178790128350897 16713549543134092596263173)
              ·
                refine ⟨3133790539337642361799345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16713549543134092596263173 3133790539337642361799345)
                ·
                  refine ⟨2350342904503231771349509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3133790539337642361799345 2350342904503231771349509)
                  ·
                    refine ⟨440689294594355957128033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2350342904503231771349509 440689294594355957128033)
                    ·
                      rfl

theorem cell22_1287359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4, 2, 4].length) (baseStart_1287359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1287359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1287359 prefixEnd_1287359 := by exact prefixLift 1287359
  have htrace : WordTrace (prefixWord ++ tailWord_1287359) baseStart_1287359 baseEnd_1287359 := by
    simpa [prefixWord, tailWord_1287359, baseEnd_1287359] using wordTrace_append hprefix tailTrace_1287359
  have hstable : (prefixWord ++ tailWord_1287359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287359).length < 2 ^ (prefixWord ++ tailWord_1287359).sum := by decide
  have hdescent : baseEnd_1287359 < baseStart_1287359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287406 : List Nat := [4, 1, 2, 1, 1, 1, 2, 2, 5, 3]
def baseStart_1287406 : Nat := 118140960795 + 1287406 * 2 ^ 59
def prefixEnd_1287406 : Nat := 4983230072969 + 3 ^ 40 * 1287406 * 2
def baseEnd_1287406 : Nat := 440705383654863501202889

theorem tailTrace_1287406 : CollatzResearch.WordTrace tailWord_1287406 prefixEnd_1287406 440705383654863501202889 := by
  unfold tailWord_1287406
  simp only [CollatzResearch.WordTrace]
  refine ⟨5869444296744426035631259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31303702915970272190033381 5869444296744426035631259)
  ·
    refine ⟨8804166445116639053446889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5869444296744426035631259 8804166445116639053446889)
    ·
      refine ⟨6603124833837479290085167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8804166445116639053446889 6603124833837479290085167)
      ·
        refine ⟨9904687250756218935127751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6603124833837479290085167 9904687250756218935127751)
        ·
          refine ⟨14857030876134328402691627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9904687250756218935127751 14857030876134328402691627)
          ·
            refine ⟨22285546314201492604037441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14857030876134328402691627 22285546314201492604037441)
            ·
              refine ⟨16714159735651119453028081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22285546314201492604037441 16714159735651119453028081)
              ·
                refine ⟨12535619801738339589771061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16714159735651119453028081 12535619801738339589771061)
                ·
                  refine ⟨1175214356412969336541037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12535619801738339589771061 1175214356412969336541037)
                  ·
                    refine ⟨440705383654863501202889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1175214356412969336541037 440705383654863501202889)
                    ·
                      rfl

theorem cell22_1287406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 5, 3].length) (baseStart_1287406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1287406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1287406 prefixEnd_1287406 := by exact prefixLift 1287406
  have htrace : WordTrace (prefixWord ++ tailWord_1287406) baseStart_1287406 baseEnd_1287406 := by
    simpa [prefixWord, tailWord_1287406, baseEnd_1287406] using wordTrace_append hprefix tailTrace_1287406
  have hstable : (prefixWord ++ tailWord_1287406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287406).length < 2 ^ (prefixWord ++ tailWord_1287406).sum := by decide
  have hdescent : baseEnd_1287406 < baseStart_1287406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287423 : List Nat := [1, 1, 2, 2, 1, 7, 1, 1, 3, 3]
def baseStart_1287423 : Nat := 118140960795 + 1287423 * 2 ^ 59
def prefixEnd_1287423 : Nat := 4983230072969 + 3 ^ 40 * 1287423 * 2
def baseEnd_1287423 : Nat := 440711203102281123527837

theorem tailTrace_1287423 : CollatzResearch.WordTrace tailWord_1287423 prefixEnd_1287423 440711203102281123527837 := by
  unfold tailWord_1287423
  simp only [CollatzResearch.WordTrace]
  refine ⟨46956174414893820188418923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31304116276595880125612615 46956174414893820188418923)
  ·
    refine ⟨70434261622340730282628385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46956174414893820188418923 70434261622340730282628385)
    ·
      refine ⟨52825696216755547711971289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70434261622340730282628385 52825696216755547711971289)
      ·
        refine ⟨39619272162566660783978467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52825696216755547711971289 39619272162566660783978467)
        ·
          refine ⟨59428908243849991175967701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39619272162566660783978467 59428908243849991175967701)
          ·
            refine ⟨1392865036965234168186743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 59428908243849991175967701 1392865036965234168186743)
            ·
              refine ⟨2089297555447851252280115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1392865036965234168186743 2089297555447851252280115)
              ·
                refine ⟨3133946333171776878420173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2089297555447851252280115 3133946333171776878420173)
                ·
                  refine ⟨1175229874939416329407565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3133946333171776878420173 1175229874939416329407565)
                  ·
                    refine ⟨440711203102281123527837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1175229874939416329407565 440711203102281123527837)
                    ·
                      rfl

theorem cell22_1287423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 1, 3, 3].length) (baseStart_1287423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1287423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1287423 prefixEnd_1287423 := by exact prefixLift 1287423
  have htrace : WordTrace (prefixWord ++ tailWord_1287423) baseStart_1287423 baseEnd_1287423 := by
    simpa [prefixWord, tailWord_1287423, baseEnd_1287423] using wordTrace_append hprefix tailTrace_1287423
  have hstable : (prefixWord ++ tailWord_1287423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287423).length < 2 ^ (prefixWord ++ tailWord_1287423).sum := by decide
  have hdescent : baseEnd_1287423 < baseStart_1287423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287434 : List Nat := [3, 1, 2, 2, 1, 1, 1, 3, 1, 7]
def baseStart_1287434 : Nat := 118140960795 + 1287434 * 2 ^ 59
def prefixEnd_1287434 : Nat := 4983230072969 + 3 ^ 40 * 1287434 * 2
def baseEnd_1287434 : Nat := 440714968627080761502803

theorem tailTrace_1287434 : CollatzResearch.WordTrace tailWord_1287434 prefixEnd_1287434 440714968627080761502803 := by
  unfold tailWord_1287434
  simp only [CollatzResearch.WordTrace]
  refine ⟨11739143904463492266767339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31304383745235979378046237 11739143904463492266767339)
  ·
    refine ⟨17608715856695238400151009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11739143904463492266767339 17608715856695238400151009)
    ·
      refine ⟨13206536892521428800113257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17608715856695238400151009 13206536892521428800113257)
      ·
        refine ⟨9904902669391071600084943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13206536892521428800113257 9904902669391071600084943)
        ·
          refine ⟨14857354004086607400127415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9904902669391071600084943 14857354004086607400127415)
          ·
            refine ⟨22286031006129911100191123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14857354004086607400127415 22286031006129911100191123)
            ·
              refine ⟨33429046509194866650286685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22286031006129911100191123 33429046509194866650286685)
              ·
                refine ⟨12535892440948074993857507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33429046509194866650286685 12535892440948074993857507)
                ·
                  refine ⟨18803838661422112490786261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12535892440948074993857507 18803838661422112490786261)
                  ·
                    refine ⟨440714968627080761502803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18803838661422112490786261 440714968627080761502803)
                    ·
                      rfl

theorem cell22_1287434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 1, 7].length) (baseStart_1287434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1287434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1287434 prefixEnd_1287434 := by exact prefixLift 1287434
  have htrace : WordTrace (prefixWord ++ tailWord_1287434) baseStart_1287434 baseEnd_1287434 := by
    simpa [prefixWord, tailWord_1287434, baseEnd_1287434] using wordTrace_append hprefix tailTrace_1287434
  have hstable : (prefixWord ++ tailWord_1287434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287434).length < 2 ^ (prefixWord ++ tailWord_1287434).sum := by decide
  have hdescent : baseEnd_1287434 < baseStart_1287434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287436 : List Nat := [2, 2, 1, 2, 2, 4, 1, 3, 5]
def baseStart_1287436 : Nat := 118140960795 + 1287436 * 2 ^ 59
def prefixEnd_1287436 : Nat := 4983230072969 + 3 ^ 40 * 1287436 * 2
def baseEnd_1287436 : Nat := 146905217755984474317599

theorem tailTrace_1287436 : CollatzResearch.WordTrace tailWord_1287436 prefixEnd_1287436 146905217755984474317599 := by
  unfold tailWord_1287436
  simp only [CollatzResearch.WordTrace]
  refine ⟨23478324281923361704321081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31304432375897815605761441 23478324281923361704321081)
  ·
    refine ⟨17608743211442521278240811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23478324281923361704321081 17608743211442521278240811)
    ·
      refine ⟨26413114817163781917361217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17608743211442521278240811 26413114817163781917361217)
      ·
        refine ⟨19809836112872836438020913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26413114817163781917361217 19809836112872836438020913)
        ·
          refine ⟨14857377084654627328515685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19809836112872836438020913 14857377084654627328515685)
          ·
            refine ⟨2785758203372742624096691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14857377084654627328515685 2785758203372742624096691)
            ·
              refine ⟨4178637305059113936145037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2785758203372742624096691 4178637305059113936145037)
              ·
                refine ⟨1566988989397167726054389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4178637305059113936145037 1566988989397167726054389)
                ·
                  refine ⟨146905217755984474317599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1566988989397167726054389 146905217755984474317599)
                  ·
                    rfl

theorem cell22_1287436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 3, 5].length) (baseStart_1287436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1287436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1287436 prefixEnd_1287436 := by exact prefixLift 1287436
  have htrace : WordTrace (prefixWord ++ tailWord_1287436) baseStart_1287436 baseEnd_1287436 := by
    simpa [prefixWord, tailWord_1287436, baseEnd_1287436] using wordTrace_append hprefix tailTrace_1287436
  have hstable : (prefixWord ++ tailWord_1287436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287436).length < 2 ^ (prefixWord ++ tailWord_1287436).sum := by decide
  have hdescent : baseEnd_1287436 < baseStart_1287436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287496 : List Nat := [2, 1, 3, 1, 1, 2, 1, 2, 6, 3]
def baseStart_1287496 : Nat := 118140960795 + 1287496 * 2 ^ 59
def prefixEnd_1287496 : Nat := 4983230072969 + 3 ^ 40 * 1287496 * 2
def baseEnd_1287496 : Nat := 440736192494133266452613

theorem tailTrace_1287496 : CollatzResearch.WordTrace tailWord_1287496 prefixEnd_1287496 440736192494133266452613 := by
  unfold tailWord_1287496
  simp only [CollatzResearch.WordTrace]
  refine ⟨23479418471814676827913171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31305891295752902437217561 23479418471814676827913171)
  ·
    refine ⟨35219127707722015241869757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23479418471814676827913171 35219127707722015241869757)
    ·
      refine ⟨13207172890395755715701159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35219127707722015241869757 13207172890395755715701159)
      ·
        refine ⟨19810759335593633573551739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13207172890395755715701159 19810759335593633573551739)
        ·
          refine ⟨29716139003390450360327609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19810759335593633573551739 29716139003390450360327609)
          ·
            refine ⟨22287104252542837770245707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29716139003390450360327609 22287104252542837770245707)
            ·
              refine ⟨33430656378814256655368561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22287104252542837770245707 33430656378814256655368561)
              ·
                refine ⟨25072992284110692491526421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33430656378814256655368561 25072992284110692491526421)
                ·
                  refine ⟨1175296513317688710540301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 25072992284110692491526421 1175296513317688710540301)
                  ·
                    refine ⟨440736192494133266452613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1175296513317688710540301 440736192494133266452613)
                    ·
                      rfl

theorem cell22_1287496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 6, 3].length) (baseStart_1287496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1287496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1287496 prefixEnd_1287496 := by exact prefixLift 1287496
  have htrace : WordTrace (prefixWord ++ tailWord_1287496) baseStart_1287496 baseEnd_1287496 := by
    simpa [prefixWord, tailWord_1287496, baseEnd_1287496] using wordTrace_append hprefix tailTrace_1287496
  have hstable : (prefixWord ++ tailWord_1287496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287496).length < 2 ^ (prefixWord ++ tailWord_1287496).sum := by decide
  have hdescent : baseEnd_1287496 < baseStart_1287496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287511 : List Nat := [1, 1, 3, 2, 3, 3, 1, 1, 1, 6]
def baseStart_1287511 : Nat := 118140960795 + 1287511 * 2 ^ 59
def prefixEnd_1287511 : Nat := 4983230072969 + 3 ^ 40 * 1287511 * 2
def baseEnd_1287511 : Nat := 440741327300678227327567

theorem tailTrace_1287511 : CollatzResearch.WordTrace tailWord_1287511 prefixEnd_1287511 440741327300678227327567 := by
  unfold tailWord_1287511
  simp only [CollatzResearch.WordTrace]
  refine ⟨46959384038575011217622387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31306256025716674145081591 46959384038575011217622387)
  ·
    refine ⟨70439076057862516826433581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46959384038575011217622387 70439076057862516826433581)
    ·
      refine ⟨26414653521698443809912593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70439076057862516826433581 26414653521698443809912593)
      ·
        refine ⟨19810990141273832857434445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26414653521698443809912593 19810990141273832857434445)
        ·
          refine ⟨7429121302977687321537917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19810990141273832857434445 7429121302977687321537917)
          ·
            refine ⟨2785920488616632745576719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7429121302977687321537917 2785920488616632745576719)
            ·
              refine ⟨4178880732924949118365079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2785920488616632745576719 4178880732924949118365079)
              ·
                refine ⟨6268321099387423677547619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4178880732924949118365079 6268321099387423677547619)
                ·
                  refine ⟨9402481649081135516321429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6268321099387423677547619 9402481649081135516321429)
                  ·
                    refine ⟨440741327300678227327567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9402481649081135516321429 440741327300678227327567)
                    ·
                      rfl

theorem cell22_1287511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 1, 1, 6].length) (baseStart_1287511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1287511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1287511 prefixEnd_1287511 := by exact prefixLift 1287511
  have htrace : WordTrace (prefixWord ++ tailWord_1287511) baseStart_1287511 baseEnd_1287511 := by
    simpa [prefixWord, tailWord_1287511, baseEnd_1287511] using wordTrace_append hprefix tailTrace_1287511
  have hstable : (prefixWord ++ tailWord_1287511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287511).length < 2 ^ (prefixWord ++ tailWord_1287511).sum := by decide
  have hdescent : baseEnd_1287511 < baseStart_1287511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287530 : List Nat := [3, 1, 3, 3, 2, 1, 1, 1, 4, 3]
def baseStart_1287530 : Nat := 118140960795 + 1287530 * 2 ^ 59
def prefixEnd_1287530 : Nat := 4983230072969 + 3 ^ 40 * 1287530 * 2
def baseEnd_1287530 : Nat := 440747831388968511102509

theorem tailTrace_1287530 : CollatzResearch.WordTrace tailWord_1287530 prefixEnd_1287530 440747831388968511102509 := by
  unfold tailWord_1287530
  simp only [CollatzResearch.WordTrace]
  refine ⟨11740019256376544365641011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31306718017004118308376029 11740019256376544365641011)
  ·
    refine ⟨17610028884564816548461517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11740019256376544365641011 17610028884564816548461517)
    ·
      refine ⟨6603760831711806205673069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17610028884564816548461517 6603760831711806205673069)
      ·
        refine ⟨2476410311891927327127401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6603760831711806205673069 2476410311891927327127401)
        ·
          refine ⟨1857307733918945495345551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2476410311891927327127401 1857307733918945495345551)
          ·
            refine ⟨2785961600878418243018327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1857307733918945495345551 2785961600878418243018327)
            ·
              refine ⟨4178942401317627364527491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2785961600878418243018327 4178942401317627364527491)
              ·
                refine ⟨6268413601976441046791237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4178942401317627364527491 6268413601976441046791237)
                ·
                  refine ⟨1175327550370582696273357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6268413601976441046791237 1175327550370582696273357)
                  ·
                    refine ⟨440747831388968511102509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1175327550370582696273357 440747831388968511102509)
                    ·
                      rfl

theorem cell22_1287530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 1, 4, 3].length) (baseStart_1287530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1287530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1287530 prefixEnd_1287530 := by exact prefixLift 1287530
  have htrace : WordTrace (prefixWord ++ tailWord_1287530) baseStart_1287530 baseEnd_1287530 := by
    simpa [prefixWord, tailWord_1287530, baseEnd_1287530] using wordTrace_append hprefix tailTrace_1287530
  have hstable : (prefixWord ++ tailWord_1287530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287530).length < 2 ^ (prefixWord ++ tailWord_1287530).sum := by decide
  have hdescent : baseEnd_1287530 < baseStart_1287530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287605 : List Nat := [1, 3, 3, 2, 2, 1, 4, 1, 5]
def baseStart_1287605 : Nat := 118140960795 + 1287605 * 2 ^ 59
def prefixEnd_1287605 : Nat := 4983230072969 + 3 ^ 40 * 1287605 * 2
def baseEnd_1287605 : Nat := 146924501807231105159093

theorem tailTrace_1287605 : CollatzResearch.WordTrace tailWord_1287605 prefixEnd_1287605 146924501807231105159093 := by
  unfold tailWord_1287605
  simp only [CollatzResearch.WordTrace]
  refine ⟨46962812500234465271544269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31308541666822976847696179 46962812500234465271544269)
  ·
    refine ⟨17611054687587924476829101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46962812500234465271544269 17611054687587924476829101)
    ·
      refine ⟨6604145507845471678810913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17611054687587924476829101 6604145507845471678810913)
      ·
        refine ⟨4953109130884103759108185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6604145507845471678810913 4953109130884103759108185)
        ·
          refine ⟨3714831848163077819331139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4953109130884103759108185 3714831848163077819331139)
          ·
            refine ⟨5572247772244616728996709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3714831848163077819331139 5572247772244616728996709)
            ·
              refine ⟨1044796457295865636686883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5572247772244616728996709 1044796457295865636686883)
              ·
                refine ⟨1567194685943798455030325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1044796457295865636686883 1567194685943798455030325)
                ·
                  refine ⟨146924501807231105159093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1567194685943798455030325 146924501807231105159093)
                  ·
                    rfl

theorem cell22_1287605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 4, 1, 5].length) (baseStart_1287605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1287605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1287605 prefixEnd_1287605 := by exact prefixLift 1287605
  have htrace : WordTrace (prefixWord ++ tailWord_1287605) baseStart_1287605 baseEnd_1287605 := by
    simpa [prefixWord, tailWord_1287605, baseEnd_1287605] using wordTrace_append hprefix tailTrace_1287605
  have hstable : (prefixWord ++ tailWord_1287605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287605).length < 2 ^ (prefixWord ++ tailWord_1287605).sum := by decide
  have hdescent : baseEnd_1287605 < baseStart_1287605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287616 : List Nat := [2, 1, 1, 2, 3, 1, 2, 4, 6]
def baseStart_1287616 : Nat := 118140960795 + 1287616 * 2 ^ 59
def prefixEnd_1287616 : Nat := 4983230072969 + 3 ^ 40 * 1287616 * 2
def baseEnd_1287616 : Nat := 146925756982164317817415

theorem tailTrace_1287616 : CollatzResearch.WordTrace tailWord_1287616 prefixEnd_1287616 146925756982164317817415 := by
  unfold tailWord_1287616
  simp only [CollatzResearch.WordTrace]
  refine ⟨23481606851597307075097351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31308809135463076100129801 23481606851597307075097351)
  ·
    refine ⟨35222410277395960612646027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23481606851597307075097351 35222410277395960612646027)
    ·
      refine ⟨52833615416093940918969041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35222410277395960612646027 52833615416093940918969041)
      ·
        refine ⟨39625211562070455689226781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52833615416093940918969041 39625211562070455689226781)
        ·
          refine ⟨14859454335776420883460043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39625211562070455689226781 14859454335776420883460043)
          ·
            refine ⟨22289181503664631325190065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14859454335776420883460043 22289181503664631325190065)
            ·
              refine ⟨16716886127748473493892549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22289181503664631325190065 16716886127748473493892549)
              ·
                refine ⟨3134416148952838780104853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16716886127748473493892549 3134416148952838780104853)
                ·
                  refine ⟨146925756982164317817415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3134416148952838780104853 146925756982164317817415)
                  ·
                    rfl

theorem cell22_1287616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 4, 6].length) (baseStart_1287616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1287616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1287616 prefixEnd_1287616 := by exact prefixLift 1287616
  have htrace : WordTrace (prefixWord ++ tailWord_1287616) baseStart_1287616 baseEnd_1287616 := by
    simpa [prefixWord, tailWord_1287616, baseEnd_1287616] using wordTrace_append hprefix tailTrace_1287616
  have hstable : (prefixWord ++ tailWord_1287616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287616).length < 2 ^ (prefixWord ++ tailWord_1287616).sum := by decide
  have hdescent : baseEnd_1287616 < baseStart_1287616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
