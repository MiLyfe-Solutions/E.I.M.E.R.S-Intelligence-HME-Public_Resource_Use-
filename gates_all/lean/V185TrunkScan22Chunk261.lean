import V185TrunkScan22Chunk260

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2328391 : List Nat := [1, 1, 4, 1, 2, 1, 2, 4, 2, 4]
def baseStart_2328391 : Nat := 118140960795 + 2328391 * 2 ^ 59
def prefixEnd_2328391 : Nat := 4983230072969 + 3 ^ 40 * 2328391 * 2
def baseEnd_2328391 : Nat := 797055823068603262136287

theorem tailTrace_2328391 : CollatzResearch.WordTrace tailWord_2328391 prefixEnd_2328391 797055823068603262136287 := by
  unfold tailWord_2328391
  simp only [CollatzResearch.WordTrace]
  refine ⟨84923396507644539368777027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56615597671763026245851351 84923396507644539368777027)
  ·
    refine ⟨127385094761466809053165541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84923396507644539368777027 127385094761466809053165541)
    ·
      refine ⟨23884705267775026697468539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 127385094761466809053165541 23884705267775026697468539)
      ·
        refine ⟨35827057901662540046202809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23884705267775026697468539 35827057901662540046202809)
        ·
          refine ⟨26870293426246905034652107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35827057901662540046202809 26870293426246905034652107)
          ·
            refine ⟨40305440139370357551978161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26870293426246905034652107 40305440139370357551978161)
            ·
              refine ⟨30229080104527768163983621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40305440139370357551978161 30229080104527768163983621)
              ·
                refine ⟨5667952519598956530746929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30229080104527768163983621 5667952519598956530746929)
                ·
                  refine ⟨4250964389699217398060197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5667952519598956530746929 4250964389699217398060197)
                  ·
                    refine ⟨797055823068603262136287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4250964389699217398060197 797055823068603262136287)
                    ·
                      rfl

theorem cell22_2328391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 4, 2, 4].length) (baseStart_2328391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2328391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2328391 prefixEnd_2328391 := by exact prefixLift 2328391
  have htrace : WordTrace (prefixWord ++ tailWord_2328391) baseStart_2328391 baseEnd_2328391 := by
    simpa [prefixWord, tailWord_2328391, baseEnd_2328391] using wordTrace_append hprefix tailTrace_2328391
  have hstable : (prefixWord ++ tailWord_2328391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328391).length < 2 ^ (prefixWord ++ tailWord_2328391).sum := by decide
  have hdescent : baseEnd_2328391 < baseStart_2328391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328410 : List Nat := [3, 1, 1, 2, 1, 3, 5, 1, 2, 3]
def baseStart_2328410 : Nat := 118140960795 + 2328410 * 2 ^ 59
def prefixEnd_2328410 : Nat := 4983230072969 + 3 ^ 40 * 2328410 * 2
def baseEnd_2328410 : Nat := 797062327156893545911229

theorem tailTrace_2328410 : CollatzResearch.WordTrace tailWord_2328410 prefixEnd_2328410 797062327156893545911229 := by
  unfold tailWord_2328410
  simp only [CollatzResearch.WordTrace]
  refine ⟨21231022373643926403429671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56616059663050470409145789 21231022373643926403429671)
  ·
    refine ⟨31846533560465889605144507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21231022373643926403429671 31846533560465889605144507)
    ·
      refine ⟨47769800340698834407716761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31846533560465889605144507 47769800340698834407716761)
      ·
        refine ⟨35827350255524125805787571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47769800340698834407716761 35827350255524125805787571)
        ·
          refine ⟨53741025383286188708681357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35827350255524125805787571 53741025383286188708681357)
          ·
            refine ⟨20152884518732320765755509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53741025383286188708681357 20152884518732320765755509)
            ·
              refine ⟨1889332923631155071789579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20152884518732320765755509 1889332923631155071789579)
              ·
                refine ⟨2833999385446732607684369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1889332923631155071789579 2833999385446732607684369)
                ·
                  refine ⟨2125499539085049455763277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2833999385446732607684369 2125499539085049455763277)
                  ·
                    refine ⟨797062327156893545911229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2125499539085049455763277 797062327156893545911229)
                    ·
                      rfl

theorem cell22_2328410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 5, 1, 2, 3].length) (baseStart_2328410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2328410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2328410 prefixEnd_2328410 := by exact prefixLift 2328410
  have htrace : WordTrace (prefixWord ++ tailWord_2328410) baseStart_2328410 baseEnd_2328410 := by
    simpa [prefixWord, tailWord_2328410, baseEnd_2328410] using wordTrace_append hprefix tailTrace_2328410
  have hstable : (prefixWord ++ tailWord_2328410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328410).length < 2 ^ (prefixWord ++ tailWord_2328410).sum := by decide
  have hdescent : baseEnd_2328410 < baseStart_2328410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328451 : List Nat := [1, 1, 1, 3, 4, 2, 2, 1, 7]
def baseStart_2328451 : Nat := 118140960795 + 2328451 * 2 ^ 59
def prefixEnd_2328451 : Nat := 4983230072969 + 3 ^ 40 * 2328451 * 2
def baseEnd_2328451 : Nat := 265692120764927701878701

theorem tailTrace_2328451 : CollatzResearch.WordTrace tailWord_2328451 prefixEnd_2328451 265692120764927701878701 := by
  unfold tailWord_2328451
  simp only [CollatzResearch.WordTrace]
  refine ⟨84925584887427169615961207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56617056591618113077307471 84925584887427169615961207)
  ·
    refine ⟨127388377331140754423941811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84925584887427169615961207 127388377331140754423941811)
    ·
      refine ⟨191082565996711131635912717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127388377331140754423941811 191082565996711131635912717)
      ·
        refine ⟨71655962248766674363467269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 191082565996711131635912717 71655962248766674363467269)
        ·
          refine ⟨13435492921643751443150113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71655962248766674363467269 13435492921643751443150113)
          ·
            refine ⟨10076619691232813582362585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13435492921643751443150113 10076619691232813582362585)
            ·
              refine ⟨7557464768424610186771939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10076619691232813582362585 7557464768424610186771939)
              ·
                refine ⟨11336197152636915280157909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7557464768424610186771939 11336197152636915280157909)
                ·
                  refine ⟨265692120764927701878701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11336197152636915280157909 265692120764927701878701)
                  ·
                    rfl

theorem cell22_2328451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 1, 7].length) (baseStart_2328451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2328451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2328451 prefixEnd_2328451 := by exact prefixLift 2328451
  have htrace : WordTrace (prefixWord ++ tailWord_2328451) baseStart_2328451 baseEnd_2328451 := by
    simpa [prefixWord, tailWord_2328451, baseEnd_2328451] using wordTrace_append hprefix tailTrace_2328451
  have hstable : (prefixWord ++ tailWord_2328451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328451).length < 2 ^ (prefixWord ++ tailWord_2328451).sum := by decide
  have hdescent : baseEnd_2328451 < baseStart_2328451 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328498 : List Nat := [3, 2, 1, 1, 1, 1, 1, 7, 1, 4]
def baseStart_2328498 : Nat := 118140960795 + 2328498 * 2 ^ 59
def prefixEnd_2328498 : Nat := 4983230072969 + 3 ^ 40 * 2328498 * 2
def baseEnd_2328498 : Nat := 797092451355290649710959

theorem tailTrace_2328498 : CollatzResearch.WordTrace tailWord_2328498 prefixEnd_2328498 797092451355290649710959 := by
  unfold tailWord_2328498
  simp only [CollatzResearch.WordTrace]
  refine ⟨21231824779564224160730537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56618199412171264428614765 21231824779564224160730537)
  ·
    refine ⟨15923868584673168120547903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21231824779564224160730537 15923868584673168120547903)
    ·
      refine ⟨23885802877009752180821855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15923868584673168120547903 23885802877009752180821855)
      ·
        refine ⟨35828704315514628271232783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23885802877009752180821855 35828704315514628271232783)
        ·
          refine ⟨53743056473271942406849175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35828704315514628271232783 53743056473271942406849175)
          ·
            refine ⟨80614584709907913610273763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53743056473271942406849175 80614584709907913610273763)
            ·
              refine ⟨120921877064861870415410645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80614584709907913610273763 120921877064861870415410645)
              ·
                refine ⟨2834106493707700087861187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 120921877064861870415410645 2834106493707700087861187)
                ·
                  refine ⟨4251159740561550131791781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2834106493707700087861187 4251159740561550131791781)
                  ·
                    refine ⟨797092451355290649710959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4251159740561550131791781 797092451355290649710959)
                    ·
                      rfl

theorem cell22_2328498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 7, 1, 4].length) (baseStart_2328498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2328498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2328498 prefixEnd_2328498 := by exact prefixLift 2328498
  have htrace : WordTrace (prefixWord ++ tailWord_2328498) baseStart_2328498 baseEnd_2328498 := by
    simpa [prefixWord, tailWord_2328498, baseEnd_2328498] using wordTrace_append hprefix tailTrace_2328498
  have hstable : (prefixWord ++ tailWord_2328498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328498).length < 2 ^ (prefixWord ++ tailWord_2328498).sum := by decide
  have hdescent : baseEnd_2328498 < baseStart_2328498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328511 : List Nat := [1, 1, 2, 2, 2, 1, 3, 2, 3, 5]
def baseStart_2328511 : Nat := 118140960795 + 2328511 * 2 ^ 59
def prefixEnd_2328511 : Nat := 4983230072969 + 3 ^ 40 * 2328511 * 2
def baseEnd_2328511 : Nat := 797096901520962949135919

theorem tailTrace_2328511 : CollatzResearch.WordTrace tailWord_2328511 prefixEnd_2328511 797096901520962949135919 := by
  unfold tailWord_2328511
  simp only [CollatzResearch.WordTrace]
  refine ⟨84927773267209799863145387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56618515511473199908763591 84927773267209799863145387)
  ·
    refine ⟨127391659900814699794718081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84927773267209799863145387 127391659900814699794718081)
    ·
      refine ⟨95543744925611024846038561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127391659900814699794718081 95543744925611024846038561)
      ·
        refine ⟨71657808694208268634528921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95543744925611024846038561 71657808694208268634528921)
        ·
          refine ⟨53743356520656201475896691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71657808694208268634528921 53743356520656201475896691)
          ·
            refine ⟨80615034780984302213845037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53743356520656201475896691 80615034780984302213845037)
            ·
              refine ⟨30230638042869113330191889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80615034780984302213845037 30230638042869113330191889)
              ·
                refine ⟨22672978532151834997643917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30230638042869113330191889 22672978532151834997643917)
                ·
                  refine ⟨8502366949556938124116469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22672978532151834997643917 8502366949556938124116469)
                  ·
                    refine ⟨797096901520962949135919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8502366949556938124116469 797096901520962949135919)
                    ·
                      rfl

theorem cell22_2328511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 3, 5].length) (baseStart_2328511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2328511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2328511 prefixEnd_2328511 := by exact prefixLift 2328511
  have htrace : WordTrace (prefixWord ++ tailWord_2328511) baseStart_2328511 baseEnd_2328511 := by
    simpa [prefixWord, tailWord_2328511, baseEnd_2328511] using wordTrace_append hprefix tailTrace_2328511
  have hstable : (prefixWord ++ tailWord_2328511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328511).length < 2 ^ (prefixWord ++ tailWord_2328511).sum := by decide
  have hdescent : baseEnd_2328511 < baseStart_2328511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328530 : List Nat := [3, 2, 2, 3, 2, 1, 1, 2, 6]
def baseStart_2328530 : Nat := 118140960795 + 2328530 * 2 ^ 59
def prefixEnd_2328530 : Nat := 4983230072969 + 3 ^ 40 * 2328530 * 2
def baseEnd_2328530 : Nat := 265701135203084410970287

theorem tailTrace_2328530 : CollatzResearch.WordTrace tailWord_2328530 prefixEnd_2328530 265701135203084410970287 := by
  unfold tailWord_2328530
  simp only [CollatzResearch.WordTrace]
  refine ⟨21232116563535241527021761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56618977502760644072058029 21232116563535241527021761)
  ·
    refine ⟨15924087422651431145266321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21232116563535241527021761 15924087422651431145266321)
    ·
      refine ⟨11943065566988573358949741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15924087422651431145266321 11943065566988573358949741)
      ·
        refine ⟨4478649587620715009606153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11943065566988573358949741 4478649587620715009606153)
        ·
          refine ⟨3358987190715536257204615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4478649587620715009606153 3358987190715536257204615)
          ·
            refine ⟨5038480786073304385806923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3358987190715536257204615 5038480786073304385806923)
            ·
              refine ⟨7557721179109956578710385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5038480786073304385806923 7557721179109956578710385)
              ·
                refine ⟨5668290884332467434032789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7557721179109956578710385 5668290884332467434032789)
                ·
                  refine ⟨265701135203084410970287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5668290884332467434032789 265701135203084410970287)
                  ·
                    rfl

theorem cell22_2328530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 2, 6].length) (baseStart_2328530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2328530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2328530 prefixEnd_2328530 := by exact prefixLift 2328530
  have htrace : WordTrace (prefixWord ++ tailWord_2328530) baseStart_2328530 baseEnd_2328530 := by
    simpa [prefixWord, tailWord_2328530, baseEnd_2328530] using wordTrace_append hprefix tailTrace_2328530
  have hstable : (prefixWord ++ tailWord_2328530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328530).length < 2 ^ (prefixWord ++ tailWord_2328530).sum := by decide
  have hdescent : baseEnd_2328530 < baseStart_2328530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328543 : List Nat := [1, 1, 2, 3, 4, 2, 1, 1, 1, 6]
def baseStart_2328543 : Nat := 118140960795 + 2328543 * 2 ^ 59
def prefixEnd_2328543 : Nat := 4983230072969 + 3 ^ 40 * 2328543 * 2
def baseEnd_2328543 : Nat := 797107855774925532335821

theorem tailTrace_2328543 : CollatzResearch.WordTrace tailWord_2328543 prefixEnd_2328543 797107855774925532335821 := by
  unfold tailWord_2328543
  simp only [CollatzResearch.WordTrace]
  refine ⟨84928940403093869328310283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56619293602062579552206855 84928940403093869328310283)
  ·
    refine ⟨127393410604640803992465425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84928940403093869328310283 127393410604640803992465425)
    ·
      refine ⟨95545057953480602994349069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127393410604640803992465425 95545057953480602994349069)
      ·
        refine ⟨35829396732555226122880901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95545057953480602994349069 35829396732555226122880901)
        ·
          refine ⟨6718011887354104898040169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35829396732555226122880901 6718011887354104898040169)
          ·
            refine ⟨5038508915515578673530127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6718011887354104898040169 5038508915515578673530127)
            ·
              refine ⟨7557763373273368010295191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5038508915515578673530127 7557763373273368010295191)
              ·
                refine ⟨11336645059910052015442787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7557763373273368010295191 11336645059910052015442787)
                ·
                  refine ⟨17004967589865078023164181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11336645059910052015442787 17004967589865078023164181)
                  ·
                    refine ⟨797107855774925532335821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17004967589865078023164181 797107855774925532335821)
                    ·
                      rfl

theorem cell22_2328543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 1, 1, 6].length) (baseStart_2328543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2328543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2328543 prefixEnd_2328543 := by exact prefixLift 2328543
  have htrace : WordTrace (prefixWord ++ tailWord_2328543) baseStart_2328543 baseEnd_2328543 := by
    simpa [prefixWord, tailWord_2328543, baseEnd_2328543] using wordTrace_append hprefix tailTrace_2328543
  have hstable : (prefixWord ++ tailWord_2328543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328543).length < 2 ^ (prefixWord ++ tailWord_2328543).sum := by decide
  have hdescent : baseEnd_2328543 < baseStart_2328543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328556 : List Nat := [2, 2, 1, 1, 2, 1, 1, 2, 1, 9]
def baseStart_2328556 : Nat := 118140960795 + 2328556 * 2 ^ 59
def prefixEnd_2328556 : Nat := 4983230072969 + 3 ^ 40 * 2328556 * 2
def baseEnd_2328556 : Nat := 797112305940597831760781

theorem tailTrace_2328556 : CollatzResearch.WordTrace tailWord_2328556 prefixEnd_2328556 797112305940597831760781 := by
  unfold tailWord_2328556
  simp only [CollatzResearch.WordTrace]
  refine ⟨42464707276023386274266761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56619609701364515032355681 42464707276023386274266761)
  ·
    refine ⟨31848530457017539705700071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42464707276023386274266761 31848530457017539705700071)
    ·
      refine ⟨47772795685526309558550107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31848530457017539705700071 47772795685526309558550107)
      ·
        refine ⟨71659193528289464337825161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47772795685526309558550107 71659193528289464337825161)
        ·
          refine ⟨53744395146217098253368871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71659193528289464337825161 53744395146217098253368871)
          ·
            refine ⟨80616592719325647380053307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53744395146217098253368871 80616592719325647380053307)
            ·
              refine ⟨120924889078988471070079961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80616592719325647380053307 120924889078988471070079961)
              ·
                refine ⟨90693666809241353302559971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 120924889078988471070079961 90693666809241353302559971)
                ·
                  refine ⟨136040500213862029953839957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90693666809241353302559971 136040500213862029953839957)
                  ·
                    refine ⟨797112305940597831760781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 136040500213862029953839957 797112305940597831760781)
                    ·
                      rfl

theorem cell22_2328556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 9].length) (baseStart_2328556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2328556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2328556 prefixEnd_2328556 := by exact prefixLift 2328556
  have htrace : WordTrace (prefixWord ++ tailWord_2328556) baseStart_2328556 baseEnd_2328556 := by
    simpa [prefixWord, tailWord_2328556, baseEnd_2328556] using wordTrace_append hprefix tailTrace_2328556
  have hstable : (prefixWord ++ tailWord_2328556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328556).length < 2 ^ (prefixWord ++ tailWord_2328556).sum := by decide
  have hdescent : baseEnd_2328556 < baseStart_2328556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328558 : List Nat := [4, 1, 2, 1, 3, 2, 9]
def baseStart_2328558 : Nat := 118140960795 + 2328558 * 2 ^ 59
def prefixEnd_2328558 : Nat := 4983230072969 + 3 ^ 40 * 2328558 * 2
def baseEnd_2328558 : Nat := 29522703354869277526325

theorem tailTrace_2328558 : CollatzResearch.WordTrace tailWord_2328558 prefixEnd_2328558 29522703354869277526325 := by
  unfold tailWord_2328558
  simp only [CollatzResearch.WordTrace]
  refine ⟨10616185937254940861263291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56619658332026351260070885 10616185937254940861263291)
  ·
    refine ⟨15924278905882411291894937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10616185937254940861263291 15924278905882411291894937)
    ·
      refine ⟨11943209179411808468921203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15924278905882411291894937 11943209179411808468921203)
      ·
        refine ⟨17914813769117712703381805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11943209179411808468921203 17914813769117712703381805)
        ·
          refine ⟨6718055163419142263768177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17914813769117712703381805 6718055163419142263768177)
          ·
            refine ⟨5038541372564356697826133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6718055163419142263768177 5038541372564356697826133)
            ·
              refine ⟨29522703354869277526325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5038541372564356697826133 29522703354869277526325)
              ·
                rfl

theorem cell22_2328558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 9].length) (baseStart_2328558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2328558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2328558 prefixEnd_2328558 := by exact prefixLift 2328558
  have htrace : WordTrace (prefixWord ++ tailWord_2328558) baseStart_2328558 baseEnd_2328558 := by
    simpa [prefixWord, tailWord_2328558, baseEnd_2328558] using wordTrace_append hprefix tailTrace_2328558
  have hstable : (prefixWord ++ tailWord_2328558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328558).length < 2 ^ (prefixWord ++ tailWord_2328558).sum := by decide
  have hdescent : baseEnd_2328558 < baseStart_2328558 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328571 : List Nat := [1, 1, 1, 1, 1, 3, 4, 1, 1, 8]
def baseStart_2328571 : Nat := 118140960795 + 2328571 * 2 ^ 59
def prefixEnd_2328571 : Nat := 4983230072969 + 3 ^ 40 * 2328571 * 2
def baseEnd_2328571 : Nat := 797117440747142792635735

theorem tailTrace_2328571 : CollatzResearch.WordTrace tailWord_2328571 prefixEnd_2328571 797117440747142792635735 := by
  unfold tailWord_2328571
  simp only [CollatzResearch.WordTrace]
  refine ⟨84929961646992430110329567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56619974431328286740219711 84929961646992430110329567)
  ·
    refine ⟨127394942470488645165494351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84929961646992430110329567 127394942470488645165494351)
    ·
      refine ⟨191092413705732967748241527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127394942470488645165494351 191092413705732967748241527)
      ·
        refine ⟨286638620558599451622362291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191092413705732967748241527 286638620558599451622362291)
        ·
          refine ⟨429957930837899177433543437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 286638620558599451622362291 429957930837899177433543437)
          ·
            refine ⟨161234224064212191537578789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 429957930837899177433543437 161234224064212191537578789)
            ·
              refine ⟨30231417012039785913296023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 161234224064212191537578789 30231417012039785913296023)
              ·
                refine ⟨45347125518059678869944035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30231417012039785913296023 45347125518059678869944035)
                ·
                  refine ⟨68020688277089518304916053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45347125518059678869944035 68020688277089518304916053)
                  ·
                    refine ⟨797117440747142792635735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 68020688277089518304916053 797117440747142792635735)
                    ·
                      rfl

theorem cell22_2328571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 8].length) (baseStart_2328571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2328571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2328571 prefixEnd_2328571 := by exact prefixLift 2328571
  have htrace : WordTrace (prefixWord ++ tailWord_2328571) baseStart_2328571 baseEnd_2328571 := by
    simpa [prefixWord, tailWord_2328571, baseEnd_2328571] using wordTrace_append hprefix tailTrace_2328571
  have hstable : (prefixWord ++ tailWord_2328571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328571).length < 2 ^ (prefixWord ++ tailWord_2328571).sum := by decide
  have hdescent : baseEnd_2328571 < baseStart_2328571 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328590 : List Nat := [4, 1, 1, 2, 2, 1, 1, 4, 3, 3]
def baseStart_2328590 : Nat := 118140960795 + 2328590 * 2 ^ 59
def prefixEnd_2328590 : Nat := 4983230072969 + 3 ^ 40 * 2328590 * 2
def baseEnd_2328590 : Nat := 797123944835433076410677

theorem tailTrace_2328590 : CollatzResearch.WordTrace tailWord_2328590 prefixEnd_2328590 797123944835433076410677 := by
  unfold tailWord_2328590
  simp only [CollatzResearch.WordTrace]
  refine ⟨10616331829240449544408903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56620436422615730903514149 10616331829240449544408903)
  ·
    refine ⟨15924497743860674316613355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10616331829240449544408903 15924497743860674316613355)
    ·
      refine ⟨23886746615791011474920033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15924497743860674316613355 23886746615791011474920033)
      ·
        refine ⟨17915059961843258606190025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23886746615791011474920033 17915059961843258606190025)
        ·
          refine ⟨13436294971382443954642519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17915059961843258606190025 13436294971382443954642519)
          ·
            refine ⟨20154442457073665931963779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13436294971382443954642519 20154442457073665931963779)
            ·
              refine ⟨30231663685610498897945669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20154442457073665931963779 30231663685610498897945669)
              ·
                refine ⟨5668436941051968543364813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30231663685610498897945669 5668436941051968543364813)
                ·
                  refine ⟨2125663852894488203761805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5668436941051968543364813 2125663852894488203761805)
                  ·
                    refine ⟨797123944835433076410677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2125663852894488203761805 797123944835433076410677)
                    ·
                      rfl

theorem cell22_2328590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 4, 3, 3].length) (baseStart_2328590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2328590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2328590 prefixEnd_2328590 := by exact prefixLift 2328590
  have htrace : WordTrace (prefixWord ++ tailWord_2328590) baseStart_2328590 baseEnd_2328590 := by
    simpa [prefixWord, tailWord_2328590, baseEnd_2328590] using wordTrace_append hprefix tailTrace_2328590
  have hstable : (prefixWord ++ tailWord_2328590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328590).length < 2 ^ (prefixWord ++ tailWord_2328590).sum := by decide
  have hdescent : baseEnd_2328590 < baseStart_2328590 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328624 : List Nat := [2, 1, 1, 1, 2, 6, 3, 2, 1, 3]
def baseStart_2328624 : Nat := 118140960795 + 2328624 * 2 ^ 59
def prefixEnd_2328624 : Nat := 4983230072969 + 3 ^ 40 * 2328624 * 2
def baseEnd_2328624 : Nat := 797135583730268321060573

theorem tailTrace_2328624 : CollatzResearch.WordTrace tailWord_2328624 prefixEnd_2328624 797135583730268321060573 := by
  unfold tailWord_2328624
  simp only [CollatzResearch.WordTrace]
  refine ⟨42465947357900210081004463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56621263143866946774672617 42465947357900210081004463)
  ·
    refine ⟨63698921036850315121506695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42465947357900210081004463 63698921036850315121506695)
    ·
      refine ⟨95548381555275472682260043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63698921036850315121506695 95548381555275472682260043)
      ·
        refine ⟨143322572332913209023390065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95548381555275472682260043 143322572332913209023390065)
        ·
          refine ⟨107491929249684906767542549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143322572332913209023390065 107491929249684906767542549)
          ·
            refine ⟨5038684183578980004728557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 107491929249684906767542549 5038684183578980004728557)
            ·
              refine ⟨1889506568842117501773209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5038684183578980004728557 1889506568842117501773209)
              ·
                refine ⟨1417129926631588126329907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1889506568842117501773209 1417129926631588126329907)
                ·
                  refine ⟨2125694889947382189494861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1417129926631588126329907 2125694889947382189494861)
                  ·
                    refine ⟨797135583730268321060573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2125694889947382189494861 797135583730268321060573)
                    ·
                      rfl

theorem cell22_2328624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 3, 2, 1, 3].length) (baseStart_2328624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2328624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2328624 prefixEnd_2328624 := by exact prefixLift 2328624
  have htrace : WordTrace (prefixWord ++ tailWord_2328624) baseStart_2328624 baseEnd_2328624 := by
    simpa [prefixWord, tailWord_2328624, baseEnd_2328624] using wordTrace_append hprefix tailTrace_2328624
  have hstable : (prefixWord ++ tailWord_2328624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328624).length < 2 ^ (prefixWord ++ tailWord_2328624).sum := by decide
  have hdescent : baseEnd_2328624 < baseStart_2328624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328663 : List Nat := [1, 1, 3, 2, 2, 1, 3, 1, 3, 5]
def baseStart_2328663 : Nat := 118140960795 + 2328663 * 2 ^ 59
def prefixEnd_2328663 : Nat := 4983230072969 + 3 ^ 40 * 2328663 * 2
def baseEnd_2328663 : Nat := 797148934227285219335453

theorem tailTrace_2328663 : CollatzResearch.WordTrace tailWord_2328663 prefixEnd_2328663 797148934227285219335453 := by
  unfold tailWord_2328663
  simp only [CollatzResearch.WordTrace]
  refine ⟨84933317162659129822678643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56622211441772753215119095 84933317162659129822678643)
  ·
    refine ⟨127399975743988694734017965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84933317162659129822678643 127399975743988694734017965)
    ·
      refine ⟨47774990903995760525256737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127399975743988694734017965 47774990903995760525256737)
      ·
        refine ⟨35831243177996820393942553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47774990903995760525256737 35831243177996820393942553)
        ·
          refine ⟨26873432383497615295456915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35831243177996820393942553 26873432383497615295456915)
          ·
            refine ⟨40310148575246422943185373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26873432383497615295456915 40310148575246422943185373)
            ·
              refine ⟨15116305715717408603694515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40310148575246422943185373 15116305715717408603694515)
              ·
                refine ⟨22674458573576112905541773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15116305715717408603694515 22674458573576112905541773)
                ·
                  refine ⟨8502921965091042339578165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22674458573576112905541773 8502921965091042339578165)
                  ·
                    refine ⟨797148934227285219335453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8502921965091042339578165 797148934227285219335453)
                    ·
                      rfl

theorem cell22_2328663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 3, 5].length) (baseStart_2328663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2328663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2328663 prefixEnd_2328663 := by exact prefixLift 2328663
  have htrace : WordTrace (prefixWord ++ tailWord_2328663) baseStart_2328663 baseEnd_2328663 := by
    simpa [prefixWord, tailWord_2328663, baseEnd_2328663] using wordTrace_append hprefix tailTrace_2328663
  have hstable : (prefixWord ++ tailWord_2328663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328663).length < 2 ^ (prefixWord ++ tailWord_2328663).sum := by decide
  have hdescent : baseEnd_2328663 < baseStart_2328663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328665 : List Nat := [1, 2, 1, 2, 2, 1, 4, 5, 4]
def baseStart_2328665 : Nat := 118140960795 + 2328665 * 2 ^ 59
def prefixEnd_2328665 : Nat := 4983230072969 + 3 ^ 40 * 2328665 * 2
def baseEnd_2328665 : Nat := 265716539622719293595149

theorem tailTrace_2328665 : CollatzResearch.WordTrace tailWord_2328665 prefixEnd_2328665 265716539622719293595149 := by
  unfold tailWord_2328665
  simp only [CollatzResearch.WordTrace]
  refine ⟨84933390108651884164251449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56622260072434589442834299 84933390108651884164251449)
  ·
    refine ⟨63700042581488913123188587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84933390108651884164251449 63700042581488913123188587)
    ·
      refine ⟨95550063872233369684782881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63700042581488913123188587 95550063872233369684782881)
      ·
        refine ⟨71662547904175027263587161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95550063872233369684782881 71662547904175027263587161)
        ·
          refine ⟨53746910928131270447690371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71662547904175027263587161 53746910928131270447690371)
          ·
            refine ⟨80620366392196905671535557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53746910928131270447690371 80620366392196905671535557)
            ·
              refine ⟨15116318698536919813412917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 80620366392196905671535557 15116318698536919813412917)
              ·
                refine ⟨1417154877987836232507461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15116318698536919813412917 1417154877987836232507461)
                ·
                  refine ⟨265716539622719293595149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1417154877987836232507461 265716539622719293595149)
                  ·
                    rfl

theorem cell22_2328665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 5, 4].length) (baseStart_2328665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2328665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2328665 prefixEnd_2328665 := by exact prefixLift 2328665
  have htrace : WordTrace (prefixWord ++ tailWord_2328665) baseStart_2328665 baseEnd_2328665 := by
    simpa [prefixWord, tailWord_2328665, baseEnd_2328665] using wordTrace_append hprefix tailTrace_2328665
  have hstable : (prefixWord ++ tailWord_2328665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328665).length < 2 ^ (prefixWord ++ tailWord_2328665).sum := by decide
  have hdescent : baseEnd_2328665 < baseStart_2328665 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328697 : List Nat := [1, 2, 1, 3, 4, 1, 2, 3, 2, 3]
def baseStart_2328697 : Nat := 118140960795 + 2328697 * 2 ^ 59
def prefixEnd_2328697 : Nat := 4983230072969 + 3 ^ 40 * 2328697 * 2
def baseEnd_2328697 : Nat := 797160573122120463985349

theorem tailTrace_2328697 : CollatzResearch.WordTrace tailWord_2328697 prefixEnd_2328697 797160573122120463985349 := by
  unfold tailWord_2328697
  simp only [CollatzResearch.WordTrace]
  refine ⟨84934557244535953629416345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56623038163023969086277563 84934557244535953629416345)
  ·
    refine ⟨63700917933401965222062259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84934557244535953629416345 63700917933401965222062259)
    ·
      refine ⟨95551376900102947833093389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63700917933401965222062259 95551376900102947833093389)
      ·
        refine ⟨35831766337538605437410021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95551376900102947833093389 35831766337538605437410021)
        ·
          refine ⟨6718456188288488519514379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35831766337538605437410021 6718456188288488519514379)
          ·
            refine ⟨10077684282432732779271569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6718456188288488519514379 10077684282432732779271569)
            ·
              refine ⟨7558263211824549584453677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10077684282432732779271569 7558263211824549584453677)
              ·
                refine ⟨2834348704434206094170129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7558263211824549584453677 2834348704434206094170129)
                ·
                  refine ⟨2125761528325654570627597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2834348704434206094170129 2125761528325654570627597)
                  ·
                    refine ⟨797160573122120463985349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2125761528325654570627597 797160573122120463985349)
                    ·
                      rfl

theorem cell22_2328697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 3, 2, 3].length) (baseStart_2328697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2328697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2328697 prefixEnd_2328697 := by exact prefixLift 2328697
  have htrace : WordTrace (prefixWord ++ tailWord_2328697) baseStart_2328697 baseEnd_2328697 := by
    simpa [prefixWord, tailWord_2328697, baseEnd_2328697] using wordTrace_append hprefix tailTrace_2328697
  have hstable : (prefixWord ++ tailWord_2328697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328697).length < 2 ^ (prefixWord ++ tailWord_2328697).sum := by decide
  have hdescent : baseEnd_2328697 < baseStart_2328697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328712 : List Nat := [2, 1, 3, 4, 1, 1, 3, 1, 2, 4]
def baseStart_2328712 : Nat := 118140960795 + 2328712 * 2 ^ 59
def prefixEnd_2328712 : Nat := 4983230072969 + 3 ^ 40 * 2328712 * 2
def baseEnd_2328712 : Nat := 797165707928665424860303

theorem tailTrace_2328712 : CollatzResearch.WordTrace tailWord_2328712 prefixEnd_2328712 797165707928665424860303 := by
  unfold tailWord_2328712
  simp only [CollatzResearch.WordTrace]
  refine ⟨42467552169740805595606195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56623402892987740794141593 42467552169740805595606195)
  ·
    refine ⟨63701328254611208393409293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42467552169740805595606195 63701328254611208393409293)
    ·
      refine ⟨23887998095479203147528485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63701328254611208393409293 23887998095479203147528485)
      ·
        refine ⟨4478999642902350590161591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23887998095479203147528485 4478999642902350590161591)
        ·
          refine ⟨6718499464353525885242387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4478999642902350590161591 6718499464353525885242387)
          ·
            refine ⟨10077749196530288827863581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6718499464353525885242387 10077749196530288827863581)
            ·
              refine ⟨3779155948698858310448843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10077749196530288827863581 3779155948698858310448843)
              ·
                refine ⟨5668733923048287465673265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3779155948698858310448843 5668733923048287465673265)
                ·
                  refine ⟨4251550442286215599254949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5668733923048287465673265 4251550442286215599254949)
                  ·
                    refine ⟨797165707928665424860303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4251550442286215599254949 797165707928665424860303)
                    ·
                      rfl

theorem cell22_2328712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 1, 2, 4].length) (baseStart_2328712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2328712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2328712 prefixEnd_2328712 := by exact prefixLift 2328712
  have htrace : WordTrace (prefixWord ++ tailWord_2328712) baseStart_2328712 baseEnd_2328712 := by
    simpa [prefixWord, tailWord_2328712, baseEnd_2328712] using wordTrace_append hprefix tailTrace_2328712
  have hstable : (prefixWord ++ tailWord_2328712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328712).length < 2 ^ (prefixWord ++ tailWord_2328712).sum := by decide
  have hdescent : baseEnd_2328712 < baseStart_2328712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328725 : List Nat := [1, 3, 2, 1, 1, 1, 3, 2, 5, 3]
def baseStart_2328725 : Nat := 118140960795 + 2328725 * 2 ^ 59
def prefixEnd_2328725 : Nat := 4983230072969 + 3 ^ 40 * 2328725 * 2
def baseEnd_2328725 : Nat := 797170158094337724285263

theorem tailTrace_2328725 : CollatzResearch.WordTrace tailWord_2328725 prefixEnd_2328725 797170158094337724285263 := by
  unfold tailWord_2328725
  simp only [CollatzResearch.WordTrace]
  refine ⟨84935578488434514411435629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56623718992289676274290419 84935578488434514411435629)
  ·
    refine ⟨31850841933162942904288361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84935578488434514411435629 31850841933162942904288361)
    ·
      refine ⟨23888131449872207178216271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31850841933162942904288361 23888131449872207178216271)
      ·
        refine ⟨35832197174808310767324407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23888131449872207178216271 35832197174808310767324407)
        ·
          refine ⟨53748295762212466150986611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35832197174808310767324407 53748295762212466150986611)
          ·
            refine ⟨80622443643318699226479917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53748295762212466150986611 80622443643318699226479917)
            ·
              refine ⟨30233416366244512209929969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80622443643318699226479917 30233416366244512209929969)
              ·
                refine ⟨22675062274683384157447477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30233416366244512209929969 22675062274683384157447477)
                ·
                  refine ⟨2125787088251567264760701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22675062274683384157447477 2125787088251567264760701)
                  ·
                    refine ⟨797170158094337724285263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2125787088251567264760701 797170158094337724285263)
                    ·
                      rfl

theorem cell22_2328725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 5, 3].length) (baseStart_2328725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2328725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2328725 prefixEnd_2328725 := by exact prefixLift 2328725
  have htrace : WordTrace (prefixWord ++ tailWord_2328725) baseStart_2328725 baseEnd_2328725 := by
    simpa [prefixWord, tailWord_2328725, baseEnd_2328725] using wordTrace_append hprefix tailTrace_2328725
  have hstable : (prefixWord ++ tailWord_2328725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328725).length < 2 ^ (prefixWord ++ tailWord_2328725).sum := by decide
  have hdescent : baseEnd_2328725 < baseStart_2328725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328836 : List Nat := [2, 3, 2, 2, 3, 1, 3, 1, 1, 4]
def baseStart_2328836 : Nat := 118140960795 + 2328836 * 2 ^ 59
def prefixEnd_2328836 : Nat := 4983230072969 + 3 ^ 40 * 2328836 * 2
def baseEnd_2328836 : Nat := 797208155662770434759923

theorem tailTrace_2328836 : CollatzResearch.WordTrace tailWord_2328836 prefixEnd_2328836 797208155662770434759923 := by
  unfold tailWord_2328836
  simp only [CollatzResearch.WordTrace]
  refine ⟨42469813495516190184363181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56626417994021586912484241 42469813495516190184363181)
  ·
    refine ⟨15926180060818571319136193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42469813495516190184363181 15926180060818571319136193)
    ·
      refine ⟨11944635045613928489352145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15926180060818571319136193 11944635045613928489352145)
      ·
        refine ⟨8958476284210446367014109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11944635045613928489352145 8958476284210446367014109)
        ·
          refine ⟨3359428606578917387630291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8958476284210446367014109 3359428606578917387630291)
          ·
            refine ⟨5039142909868376081445437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3359428606578917387630291 5039142909868376081445437)
            ·
              refine ⟨1889678591200641030542039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5039142909868376081445437 1889678591200641030542039)
              ·
                refine ⟨2834517886800961545813059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1889678591200641030542039 2834517886800961545813059)
                ·
                  refine ⟨4251776830201442318719589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2834517886800961545813059 4251776830201442318719589)
                  ·
                    refine ⟨797208155662770434759923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4251776830201442318719589 797208155662770434759923)
                    ·
                      rfl

theorem cell22_2328836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 3, 1, 1, 4].length) (baseStart_2328836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2328836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2328836 prefixEnd_2328836 := by exact prefixLift 2328836
  have htrace : WordTrace (prefixWord ++ tailWord_2328836) baseStart_2328836 baseEnd_2328836 := by
    simpa [prefixWord, tailWord_2328836, baseEnd_2328836] using wordTrace_append hprefix tailTrace_2328836
  have hstable : (prefixWord ++ tailWord_2328836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328836).length < 2 ^ (prefixWord ++ tailWord_2328836).sum := by decide
  have hdescent : baseEnd_2328836 < baseStart_2328836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328849 : List Nat := [1, 2, 2, 1, 1, 6, 2, 2, 2, 3]
def baseStart_2328849 : Nat := 118140960795 + 2328849 * 2 ^ 59
def prefixEnd_2328849 : Nat := 4983230072969 + 3 ^ 40 * 2328849 * 2
def baseEnd_2328849 : Nat := 797212605828442734184883

theorem tailTrace_2328849 : CollatzResearch.WordTrace tailWord_2328849 prefixEnd_2328849 797212605828442734184883 := by
  unfold tailWord_2328849
  simp only [CollatzResearch.WordTrace]
  refine ⟨84940101139985283588949601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56626734093323522392633067 84940101139985283588949601)
  ·
    refine ⟨63705075854988962691712201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84940101139985283588949601 63705075854988962691712201)
    ·
      refine ⟨47778806891241722018784151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63705075854988962691712201 47778806891241722018784151)
      ·
        refine ⟨71668210336862583028176227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47778806891241722018784151 71668210336862583028176227)
        ·
          refine ⟨107502315505293874542264341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71668210336862583028176227 107502315505293874542264341)
          ·
            refine ⟨5039171039310650369168641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 107502315505293874542264341 5039171039310650369168641)
            ·
              refine ⟨3779378279482987776876481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5039171039310650369168641 3779378279482987776876481)
              ·
                refine ⟨2834533709612240832657361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3779378279482987776876481 2834533709612240832657361)
                ·
                  refine ⟨2125900282209180624493021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2834533709612240832657361 2125900282209180624493021)
                  ·
                    refine ⟨797212605828442734184883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2125900282209180624493021 797212605828442734184883)
                    ·
                      rfl

theorem cell22_2328849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 2, 2, 3].length) (baseStart_2328849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2328849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2328849 prefixEnd_2328849 := by exact prefixLift 2328849
  have htrace : WordTrace (prefixWord ++ tailWord_2328849) baseStart_2328849 baseEnd_2328849 := by
    simpa [prefixWord, tailWord_2328849, baseEnd_2328849] using wordTrace_append hprefix tailTrace_2328849
  have hstable : (prefixWord ++ tailWord_2328849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328849).length < 2 ^ (prefixWord ++ tailWord_2328849).sum := by decide
  have hdescent : baseEnd_2328849 < baseStart_2328849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328860 : List Nat := [2, 2, 3, 1, 1, 1, 1, 2, 2, 7]
def baseStart_2328860 : Nat := 118140960795 + 2328860 * 2 ^ 59
def prefixEnd_2328860 : Nat := 4983230072969 + 3 ^ 40 * 2328860 * 2
def baseEnd_2328860 : Nat := 797216371353242372159849

theorem tailTrace_2328860 : CollatzResearch.WordTrace tailWord_2328860 prefixEnd_2328860 797216371353242372159849 := by
  unfold tailWord_2328860
  simp only [CollatzResearch.WordTrace]
  refine ⟨42470251171472716233800017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56627001561963621645066689 42470251171472716233800017)
  ·
    refine ⟨31852688378604537175350013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42470251171472716233800017 31852688378604537175350013)
    ·
      refine ⟨11944758141976701440756255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31852688378604537175350013 11944758141976701440756255)
      ·
        refine ⟨17917137212965052161134383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11944758141976701440756255 17917137212965052161134383)
        ·
          refine ⟨26875705819447578241701575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17917137212965052161134383 26875705819447578241701575)
          ·
            refine ⟨40313558729171367362552363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26875705819447578241701575 40313558729171367362552363)
            ·
              refine ⟨60470338093757051043828545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40313558729171367362552363 60470338093757051043828545)
              ·
                refine ⟨45352753570317788282871409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60470338093757051043828545 45352753570317788282871409)
                ·
                  refine ⟨34014565177738341212153557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45352753570317788282871409 34014565177738341212153557)
                  ·
                    refine ⟨797216371353242372159849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34014565177738341212153557 797216371353242372159849)
                    ·
                      rfl

theorem cell22_2328860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_2328860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2328860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2328860 prefixEnd_2328860 := by exact prefixLift 2328860
  have htrace : WordTrace (prefixWord ++ tailWord_2328860) baseStart_2328860 baseEnd_2328860 := by
    simpa [prefixWord, tailWord_2328860, baseEnd_2328860] using wordTrace_append hprefix tailTrace_2328860
  have hstable : (prefixWord ++ tailWord_2328860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328860).length < 2 ^ (prefixWord ++ tailWord_2328860).sum := by decide
  have hdescent : baseEnd_2328860 < baseStart_2328860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328881 : List Nat := [1, 2, 2, 3, 5, 1, 1, 1, 2, 4]
def baseStart_2328881 : Nat := 118140960795 + 2328881 * 2 ^ 59
def prefixEnd_2328881 : Nat := 4983230072969 + 3 ^ 40 * 2328881 * 2
def baseEnd_2328881 : Nat := 797223560082405317384785

theorem tailTrace_2328881 : CollatzResearch.WordTrace tailWord_2328881 prefixEnd_2328881 797223560082405317384785 := by
  unfold tailWord_2328881
  simp only [CollatzResearch.WordTrace]
  refine ⟨84941268275869353054114497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56627512183912902036076331 84941268275869353054114497)
  ·
    refine ⟨63705951206902014790585873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84941268275869353054114497 63705951206902014790585873)
    ·
      refine ⟨47779463405176511092939405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63705951206902014790585873 47779463405176511092939405)
      ·
        refine ⟨17917298776941191659852277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47779463405176511092939405 17917298776941191659852277)
        ·
          refine ⟨1679746760338236718111151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17917298776941191659852277 1679746760338236718111151)
          ·
            refine ⟨2519620140507355077166727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1679746760338236718111151 2519620140507355077166727)
            ·
              refine ⟨3779430210761032615750091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2519620140507355077166727 3779430210761032615750091)
              ·
                refine ⟨5669145316141548923625137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3779430210761032615750091 5669145316141548923625137)
                ·
                  refine ⟨4251858987106161692718853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5669145316141548923625137 4251858987106161692718853)
                  ·
                    refine ⟨797223560082405317384785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4251858987106161692718853 797223560082405317384785)
                    ·
                      rfl

theorem cell22_2328881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 1, 2, 4].length) (baseStart_2328881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2328881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2328881 prefixEnd_2328881 := by exact prefixLift 2328881
  have htrace : WordTrace (prefixWord ++ tailWord_2328881) baseStart_2328881 baseEnd_2328881 := by
    simpa [prefixWord, tailWord_2328881, baseEnd_2328881] using wordTrace_append hprefix tailTrace_2328881
  have hstable : (prefixWord ++ tailWord_2328881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328881).length < 2 ^ (prefixWord ++ tailWord_2328881).sum := by decide
  have hdescent : baseEnd_2328881 < baseStart_2328881 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328900 : List Nat := [2, 3, 4, 1, 3, 1, 1, 2, 2, 3]
def baseStart_2328900 : Nat := 118140960795 + 2328900 * 2 ^ 59
def prefixEnd_2328900 : Nat := 4983230072969 + 3 ^ 40 * 2328900 * 2
def baseEnd_2328900 : Nat := 797230064170695601159727

theorem tailTrace_2328900 : CollatzResearch.WordTrace tailWord_2328900 prefixEnd_2328900 797230064170695601159727 := by
  unfold tailWord_2328900
  simp only [CollatzResearch.WordTrace]
  refine ⟨42470980631400259649528077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56627974175200346199370769 42470980631400259649528077)
  ·
    refine ⟨15926617736775097368573029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42470980631400259649528077 15926617736775097368573029)
    ·
      refine ⟨2986240825645330756607443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15926617736775097368573029 2986240825645330756607443)
      ·
        refine ⟨4479361238467996134911165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2986240825645330756607443 4479361238467996134911165)
        ·
          refine ⟨1679760464425498550591687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4479361238467996134911165 1679760464425498550591687)
          ·
            refine ⟨2519640696638247825887531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1679760464425498550591687 2519640696638247825887531)
            ·
              refine ⟨3779461044957371738831297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2519640696638247825887531 3779461044957371738831297)
              ·
                refine ⟨2834595783718028804123473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3779461044957371738831297 2834595783718028804123473)
                ·
                  refine ⟨2125946837788521603092605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2834595783718028804123473 2125946837788521603092605)
                  ·
                    refine ⟨797230064170695601159727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2125946837788521603092605 797230064170695601159727)
                    ·
                      rfl

theorem cell22_2328900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_2328900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2328900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2328900 prefixEnd_2328900 := by exact prefixLift 2328900
  have htrace : WordTrace (prefixWord ++ tailWord_2328900) baseStart_2328900 baseEnd_2328900 := by
    simpa [prefixWord, tailWord_2328900, baseEnd_2328900] using wordTrace_append hprefix tailTrace_2328900
  have hstable : (prefixWord ++ tailWord_2328900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328900).length < 2 ^ (prefixWord ++ tailWord_2328900).sum := by decide
  have hdescent : baseEnd_2328900 < baseStart_2328900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328920 : List Nat := [2, 1, 2, 2, 1, 1, 2, 1, 2, 8]
def baseStart_2328920 : Nat := 118140960795 + 2328920 * 2 ^ 59
def prefixEnd_2328920 : Nat := 4983230072969 + 3 ^ 40 * 2328920 * 2
def baseEnd_2328920 : Nat := 797236910579422215659665

theorem tailTrace_2328920 : CollatzResearch.WordTrace tailWord_2328920 prefixEnd_2328920 797236910579422215659665 := by
  unfold tailWord_2328920
  simp only [CollatzResearch.WordTrace]
  refine ⟨42471345361364031357392107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56628460481818708476522809 42471345361364031357392107)
  ·
    refine ⟨63707018042046047036088161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42471345361364031357392107 63707018042046047036088161)
    ·
      refine ⟨47780263531534535277066121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63707018042046047036088161 47780263531534535277066121)
      ·
        refine ⟨35835197648650901457799591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47780263531534535277066121 35835197648650901457799591)
        ·
          refine ⟨53752796472976352186699387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35835197648650901457799591 53752796472976352186699387)
          ·
            refine ⟨80629194709464528280049081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53752796472976352186699387 80629194709464528280049081)
            ·
              refine ⟨60471896032098396210036811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80629194709464528280049081 60471896032098396210036811)
              ·
                refine ⟨90707844048147594315055217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60471896032098396210036811 90707844048147594315055217)
                ·
                  refine ⟨68030883036110695736291413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 90707844048147594315055217 68030883036110695736291413)
                  ·
                    refine ⟨797236910579422215659665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 68030883036110695736291413 797236910579422215659665)
                    ·
                      rfl

theorem cell22_2328920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 2, 8].length) (baseStart_2328920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2328920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2328920 prefixEnd_2328920 := by exact prefixLift 2328920
  have htrace : WordTrace (prefixWord ++ tailWord_2328920) baseStart_2328920 baseEnd_2328920 := by
    simpa [prefixWord, tailWord_2328920, baseEnd_2328920] using wordTrace_append hprefix tailTrace_2328920
  have hstable : (prefixWord ++ tailWord_2328920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328920).length < 2 ^ (prefixWord ++ tailWord_2328920).sum := by decide
  have hdescent : baseEnd_2328920 < baseStart_2328920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328962 : List Nat := [3, 4, 2, 1, 2, 1, 3, 2, 1, 3]
def baseStart_2328962 : Nat := 118140960795 + 2328962 * 2 ^ 59
def prefixEnd_2328962 : Nat := 4983230072969 + 3 ^ 40 * 2328962 * 2
def baseEnd_2328962 : Nat := 797251288037748106109537

theorem tailTrace_2328962 : CollatzResearch.WordTrace tailWord_2328962 prefixEnd_2328962 797251288037748106109537 := by
  unfold tailWord_2328962
  simp only [CollatzResearch.WordTrace]
  refine ⟨21236055647143975971953285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56629481725717269258542093 21236055647143975971953285)
  ·
    refine ⟨3981760433839495494741241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21236055647143975971953285 3981760433839495494741241)
    ·
      refine ⟨2986320325379621621055931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3981760433839495494741241 2986320325379621621055931)
      ·
        refine ⟨4479480488069432431583897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2986320325379621621055931 4479480488069432431583897)
        ·
          refine ⟨3359610366052074323687923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4479480488069432431583897 3359610366052074323687923)
          ·
            refine ⟨5039415549078111485531885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3359610366052074323687923 5039415549078111485531885)
            ·
              refine ⟨1889780830904291807074457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5039415549078111485531885 1889780830904291807074457)
              ·
                refine ⟨1417335623178218855305843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1889780830904291807074457 1417335623178218855305843)
                ·
                  refine ⟨2126003434767328282958765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1417335623178218855305843 2126003434767328282958765)
                  ·
                    refine ⟨797251288037748106109537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2126003434767328282958765 797251288037748106109537)
                    ·
                      rfl

theorem cell22_2328962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_2328962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2328962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2328962 prefixEnd_2328962 := by exact prefixLift 2328962
  have htrace : WordTrace (prefixWord ++ tailWord_2328962) baseStart_2328962 baseEnd_2328962 := by
    simpa [prefixWord, tailWord_2328962, baseEnd_2328962] using wordTrace_append hprefix tailTrace_2328962
  have hstable : (prefixWord ++ tailWord_2328962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328962).length < 2 ^ (prefixWord ++ tailWord_2328962).sum := by decide
  have hdescent : baseEnd_2328962 < baseStart_2328962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328969 : List Nat := [1, 2, 1, 1, 6, 3, 1, 1, 6]
def baseStart_2328969 : Nat := 118140960795 + 2328969 * 2 ^ 59
def prefixEnd_2328969 : Nat := 4983230072969 + 3 ^ 40 * 2328969 * 2
def baseEnd_2328969 : Nat := 265751228093600807061505

theorem tailTrace_2328969 : CollatzResearch.WordTrace tailWord_2328969 prefixEnd_2328969 265751228093600807061505 := by
  unfold tailWord_2328969
  simp only [CollatzResearch.WordTrace]
  refine ⟨84944477899550544083317961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56629651933033696055545307 84944477899550544083317961)
  ·
    refine ⟨63708358424662908062488471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84944477899550544083317961 63708358424662908062488471)
    ·
      refine ⟨95562537636994362093732707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63708358424662908062488471 95562537636994362093732707)
      ·
        refine ⟨143343806455491543140599061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95562537636994362093732707 143343806455491543140599061)
        ·
          refine ⟨6719240927601166084715581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 143343806455491543140599061 6719240927601166084715581)
          ·
            refine ⟨2519715347850437281768343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6719240927601166084715581 2519715347850437281768343)
            ·
              refine ⟨3779573021775655922652515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2519715347850437281768343 3779573021775655922652515)
              ·
                refine ⟨5669359532663483883978773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3779573021775655922652515 5669359532663483883978773)
                ·
                  refine ⟨265751228093600807061505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5669359532663483883978773 265751228093600807061505)
                  ·
                    rfl

theorem cell22_2328969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 1, 6].length) (baseStart_2328969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2328969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2328969 prefixEnd_2328969 := by exact prefixLift 2328969
  have htrace : WordTrace (prefixWord ++ tailWord_2328969) baseStart_2328969 baseEnd_2328969 := by
    simpa [prefixWord, tailWord_2328969, baseEnd_2328969] using wordTrace_append hprefix tailTrace_2328969
  have hstable : (prefixWord ++ tailWord_2328969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328969).length < 2 ^ (prefixWord ++ tailWord_2328969).sum := by decide
  have hdescent : baseEnd_2328969 < baseStart_2328969 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328999 : List Nat := [1, 1, 6, 1, 1, 2, 1, 3, 2, 4]
def baseStart_2328999 : Nat := 118140960795 + 2328999 * 2 ^ 59
def prefixEnd_2328999 : Nat := 4983230072969 + 3 ^ 40 * 2328999 * 2
def baseEnd_2328999 : Nat := 797263953893892342934423

theorem tailTrace_2328999 : CollatzResearch.WordTrace tailWord_2328999 prefixEnd_2328999 797263953893892342934423 := by
  unfold tailWord_2328999
  simp only [CollatzResearch.WordTrace]
  refine ⟨84945572089441859206910051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56630381392961239471273367 84945572089441859206910051)
  ·
    refine ⟨127418358134162788810365077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84945572089441859206910051 127418358134162788810365077)
    ·
      refine ⟨5972735537538880725485863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 127418358134162788810365077 5972735537538880725485863)
      ·
        refine ⟨8959103306308321088228795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5972735537538880725485863 8959103306308321088228795)
        ·
          refine ⟨13438654959462481632343193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8959103306308321088228795 13438654959462481632343193)
          ·
            refine ⟨10078991219596861224257395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13438654959462481632343193 10078991219596861224257395)
            ·
              refine ⟨15118486829395291836386093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10078991219596861224257395 15118486829395291836386093)
              ·
                refine ⟨5669432561023234438644785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15118486829395291836386093 5669432561023234438644785)
                ·
                  refine ⟨4252074420767425828983589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5669432561023234438644785 4252074420767425828983589)
                  ·
                    refine ⟨797263953893892342934423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4252074420767425828983589 797263953893892342934423)
                    ·
                      rfl

theorem cell22_2328999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_2328999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2328999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2328999 prefixEnd_2328999 := by exact prefixLift 2328999
  have htrace : WordTrace (prefixWord ++ tailWord_2328999) baseStart_2328999 baseEnd_2328999 := by
    simpa [prefixWord, tailWord_2328999, baseEnd_2328999] using wordTrace_append hprefix tailTrace_2328999
  have hstable : (prefixWord ++ tailWord_2328999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328999).length < 2 ^ (prefixWord ++ tailWord_2328999).sum := by decide
  have hdescent : baseEnd_2328999 < baseStart_2328999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2329057 : List Nat := [1, 2, 3, 1, 2, 2, 1, 2, 1, 7]
def baseStart_2329057 : Nat := 118140960795 + 2329057 * 2 ^ 59
def prefixEnd_2329057 : Nat := 4983230072969 + 3 ^ 40 * 2329057 * 2
def baseEnd_2329057 : Nat := 797283808479199524984245

theorem tailTrace_2329057 : CollatzResearch.WordTrace tailWord_2329057 prefixEnd_2329057 797283808479199524984245 := by
  unfold tailWord_2329057
  simp only [CollatzResearch.WordTrace]
  refine ⟨84947687523231735112521425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56631791682154490075014283 84947687523231735112521425)
  ·
    refine ⟨63710765642423801334391069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84947687523231735112521425 63710765642423801334391069)
    ·
      refine ⟨23891537115908925500396651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63710765642423801334391069 23891537115908925500396651)
      ·
        refine ⟨35837305673863388250594977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23891537115908925500396651 35837305673863388250594977)
        ·
          refine ⟨26877979255397541187946233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35837305673863388250594977 26877979255397541187946233)
          ·
            refine ⟨20158484441548155890959675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26877979255397541187946233 20158484441548155890959675)
            ·
              refine ⟨30237726662322233836439513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20158484441548155890959675 30237726662322233836439513)
              ·
                refine ⟨22678294996741675377329635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30237726662322233836439513 22678294996741675377329635)
                ·
                  refine ⟨34017442495112513065994453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22678294996741675377329635 34017442495112513065994453)
                  ·
                    refine ⟨797283808479199524984245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34017442495112513065994453 797283808479199524984245)
                    ·
                      rfl

theorem cell22_2329057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 7].length) (baseStart_2329057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2329057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2329057 prefixEnd_2329057 := by exact prefixLift 2329057
  have htrace : WordTrace (prefixWord ++ tailWord_2329057) baseStart_2329057 baseEnd_2329057 := by
    simpa [prefixWord, tailWord_2329057, baseEnd_2329057] using wordTrace_append hprefix tailTrace_2329057
  have hstable : (prefixWord ++ tailWord_2329057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2329057).length < 2 ^ (prefixWord ++ tailWord_2329057).sum := by decide
  have hdescent : baseEnd_2329057 < baseStart_2329057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2329057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2329063 : List Nat := [1, 1, 5, 2, 1, 1, 4, 3, 1, 3]
def baseStart_2329063 : Nat := 118140960795 + 2329063 * 2 ^ 59
def prefixEnd_2329063 : Nat := 4983230072969 + 3 ^ 40 * 2329063 * 2
def baseEnd_2329063 : Nat := 797285862401817509334227

theorem tailTrace_2329063 : CollatzResearch.WordTrace tailWord_2329063 prefixEnd_2329063 797285862401817509334227 := by
  unfold tailWord_2329063
  simp only [CollatzResearch.WordTrace]
  refine ⟨84947906361209998137239843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56631937574139998758159895 84947906361209998137239843)
  ·
    refine ⟨127421859541814997205859765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84947906361209998137239843 127421859541814997205859765)
    ·
      refine ⟨11945799332045155988049353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 127421859541814997205859765 11945799332045155988049353)
      ·
        refine ⟨8959349499033866991037015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11945799332045155988049353 8959349499033866991037015)
        ·
          refine ⟨13439024248550800486555523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8959349499033866991037015 13439024248550800486555523)
          ·
            refine ⟨20158536372826200729833285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13439024248550800486555523 20158536372826200729833285)
            ·
              refine ⟨3779725569904912636843741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20158536372826200729833285 3779725569904912636843741)
              ·
                refine ⟨1417397088714342238816403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3779725569904912636843741 1417397088714342238816403)
                ·
                  refine ⟨2126095633071513358224605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1417397088714342238816403 2126095633071513358224605)
                  ·
                    refine ⟨797285862401817509334227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2126095633071513358224605 797285862401817509334227)
                    ·
                      rfl

theorem cell22_2329063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 3, 1, 3].length) (baseStart_2329063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2329063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2329063 prefixEnd_2329063 := by exact prefixLift 2329063
  have htrace : WordTrace (prefixWord ++ tailWord_2329063) baseStart_2329063 baseEnd_2329063 := by
    simpa [prefixWord, tailWord_2329063, baseEnd_2329063] using wordTrace_append hprefix tailTrace_2329063
  have hstable : (prefixWord ++ tailWord_2329063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2329063).length < 2 ^ (prefixWord ++ tailWord_2329063).sum := by decide
  have hdescent : baseEnd_2329063 < baseStart_2329063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2329063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2329147 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 3, 9]
def baseStart_2329147 : Nat := 118140960795 + 2329147 * 2 ^ 59
def prefixEnd_2329147 : Nat := 4983230072969 + 3 ^ 40 * 2329147 * 2
def baseEnd_2329147 : Nat := 797314617318469290233969

theorem tailTrace_2329147 : CollatzResearch.WordTrace tailWord_2329147 prefixEnd_2329147 797314617318469290233969 := by
  unfold tailWord_2329147
  simp only [CollatzResearch.WordTrace]
  refine ⟨84950970092905680483297695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56633980061937120322198463 84950970092905680483297695)
  ·
    refine ⟨127426455139358520724946543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84950970092905680483297695 127426455139358520724946543)
    ·
      refine ⟨191139682709037781087419815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127426455139358520724946543 191139682709037781087419815)
      ·
        refine ⟨286709524063556671631129723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191139682709037781087419815 286709524063556671631129723)
        ·
          refine ⟨430064286095335007446694585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 286709524063556671631129723 430064286095335007446694585)
          ·
            refine ⟨322548214571501255585020939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 430064286095335007446694585 322548214571501255585020939)
            ·
              refine ⟨483822321857251883377531409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 322548214571501255585020939 483822321857251883377531409)
              ·
                refine ⟨362866741392938912533148557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 483822321857251883377531409 362866741392938912533148557)
                ·
                  refine ⟨136075028022352092199930709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 362866741392938912533148557 136075028022352092199930709)
                  ·
                    refine ⟨797314617318469290233969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 136075028022352092199930709 797314617318469290233969)
                    ·
                      rfl

theorem cell22_2329147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 9].length) (baseStart_2329147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2329147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2329147 prefixEnd_2329147 := by exact prefixLift 2329147
  have htrace : WordTrace (prefixWord ++ tailWord_2329147) baseStart_2329147 baseEnd_2329147 := by
    simpa [prefixWord, tailWord_2329147, baseEnd_2329147] using wordTrace_append hprefix tailTrace_2329147
  have hstable : (prefixWord ++ tailWord_2329147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2329147).length < 2 ^ (prefixWord ++ tailWord_2329147).sum := by decide
  have hdescent : baseEnd_2329147 < baseStart_2329147 := by decide
  rcases family_descends (prefixWord ++ tailWord_2329147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2329149 : List Nat := [1, 4, 1, 3, 2, 1, 1, 9]
def baseStart_2329149 : Nat := 118140960795 + 2329149 * 2 ^ 59
def prefixEnd_2329149 : Nat := 4983230072969 + 3 ^ 40 * 2329149 * 2
def baseEnd_2329149 : Nat := 88590589106593550187107

theorem tailTrace_2329149 : CollatzResearch.WordTrace tailWord_2329149 prefixEnd_2329149 88590589106593550187107 := by
  unfold tailWord_2329149
  simp only [CollatzResearch.WordTrace]
  refine ⟨84951043038898434824870501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56634028692598956549913667 84951043038898434824870501)
  ·
    refine ⟨15928320569793456529663219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84951043038898434824870501 15928320569793456529663219)
    ·
      refine ⟨23892480854690184794494829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15928320569793456529663219 23892480854690184794494829)
      ·
        refine ⟨8959680320508819297935561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23892480854690184794494829 8959680320508819297935561)
        ·
          refine ⟨6719760240381614473451671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8959680320508819297935561 6719760240381614473451671)
          ·
            refine ⟨10079640360572421710177507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6719760240381614473451671 10079640360572421710177507)
            ·
              refine ⟨15119460540858632565266261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10079640360572421710177507 15119460540858632565266261)
              ·
                refine ⟨88590589106593550187107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15119460540858632565266261 88590589106593550187107)
                ·
                  rfl

theorem cell22_2329149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 9].length) (baseStart_2329149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2329149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2329149 prefixEnd_2329149 := by exact prefixLift 2329149
  have htrace : WordTrace (prefixWord ++ tailWord_2329149) baseStart_2329149 baseEnd_2329149 := by
    simpa [prefixWord, tailWord_2329149, baseEnd_2329149] using wordTrace_append hprefix tailTrace_2329149
  have hstable : (prefixWord ++ tailWord_2329149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2329149).length < 2 ^ (prefixWord ++ tailWord_2329149).sum := by decide
  have hdescent : baseEnd_2329149 < baseStart_2329149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2329149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2329153 : List Nat := [1, 2, 5, 1, 1, 3, 1, 3, 2, 3]
def baseStart_2329153 : Nat := 118140960795 + 2329153 * 2 ^ 59
def prefixEnd_2329153 : Nat := 4983230072969 + 3 ^ 40 * 2329153 * 2
def baseEnd_2329153 : Nat := 797316671241087274583951

theorem tailTrace_2329153 : CollatzResearch.WordTrace tailWord_2329153 prefixEnd_2329153 797316671241087274583951 := by
  unfold tailWord_2329153
  simp only [CollatzResearch.WordTrace]
  refine ⟨84951188930883943508016113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56634125953922629005344075 84951188930883943508016113)
  ·
    refine ⟨63713391698162957631012085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84951188930883943508016113 63713391698162957631012085)
    ·
      refine ⟨5973130471702777277907383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 63713391698162957631012085 5973130471702777277907383)
      ·
        refine ⟨8959695707554165916861075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5973130471702777277907383 8959695707554165916861075)
        ·
          refine ⟨13439543561331248875291613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8959695707554165916861075 13439543561331248875291613)
          ·
            refine ⟨5039828835499218328234355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13439543561331248875291613 5039828835499218328234355)
            ·
              refine ⟨7559743253248827492351533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5039828835499218328234355 7559743253248827492351533)
              ·
                refine ⟨2834903719968310309631825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7559743253248827492351533 2834903719968310309631825)
                ·
                  refine ⟨2126177789976232732223869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2834903719968310309631825 2126177789976232732223869)
                  ·
                    refine ⟨797316671241087274583951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2126177789976232732223869 797316671241087274583951)
                    ·
                      rfl

theorem cell22_2329153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_2329153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2329153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2329153 prefixEnd_2329153 := by exact prefixLift 2329153
  have htrace : WordTrace (prefixWord ++ tailWord_2329153) baseStart_2329153 baseEnd_2329153 := by
    simpa [prefixWord, tailWord_2329153, baseEnd_2329153] using wordTrace_append hprefix tailTrace_2329153
  have hstable : (prefixWord ++ tailWord_2329153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2329153).length < 2 ^ (prefixWord ++ tailWord_2329153).sum := by decide
  have hdescent : baseEnd_2329153 < baseStart_2329153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2329153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2329209 : List Nat := [1, 2, 1, 3, 3, 2, 1, 1, 1, 7]
def baseStart_2329209 : Nat := 118140960795 + 2329209 * 2 ^ 59
def prefixEnd_2329209 : Nat := 4983230072969 + 3 ^ 40 * 2329209 * 2
def baseEnd_2329209 : Nat := 797335841185521795183779

theorem tailTrace_2329209 : CollatzResearch.WordTrace tailWord_2329209 prefixEnd_2329209 797335841185521795183779 := by
  unfold tailWord_2329209
  simp only [CollatzResearch.WordTrace]
  refine ⟨84953231418681065072054681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56635487612454043381369787 84953231418681065072054681)
  ·
    refine ⟨63714923564010798804041011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84953231418681065072054681 63714923564010798804041011)
    ·
      refine ⟨95572385346016198206061517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63714923564010798804041011 95572385346016198206061517)
      ·
        refine ⟨35839644504756074327273069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95572385346016198206061517 35839644504756074327273069)
        ·
          refine ⟨13439866689283527872727401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35839644504756074327273069 13439866689283527872727401)
          ·
            refine ⟨10079900016962645904545551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13439866689283527872727401 10079900016962645904545551)
            ·
              refine ⟨15119850025443968856818327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10079900016962645904545551 15119850025443968856818327)
              ·
                refine ⟨22679775038165953285227491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15119850025443968856818327 22679775038165953285227491)
                ·
                  refine ⟨34019662557248929927841237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22679775038165953285227491 34019662557248929927841237)
                  ·
                    refine ⟨797335841185521795183779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34019662557248929927841237 797335841185521795183779)
                    ·
                      rfl

theorem cell22_2329209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 7].length) (baseStart_2329209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2329209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2329209 prefixEnd_2329209 := by exact prefixLift 2329209
  have htrace : WordTrace (prefixWord ++ tailWord_2329209) baseStart_2329209 baseEnd_2329209 := by
    simpa [prefixWord, tailWord_2329209, baseEnd_2329209] using wordTrace_append hprefix tailTrace_2329209
  have hstable : (prefixWord ++ tailWord_2329209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2329209).length < 2 ^ (prefixWord ++ tailWord_2329209).sum := by decide
  have hdescent : baseEnd_2329209 < baseStart_2329209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2329209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2329239 : List Nat := [1, 1, 3, 3, 2, 1, 1, 2, 8]
def baseStart_2329239 : Nat := 118140960795 + 2329239 * 2 ^ 59
def prefixEnd_2329239 : Nat := 4983230072969 + 3 ^ 40 * 2329239 * 2
def baseEnd_2329239 : Nat := 265782036932870572311229

theorem tailTrace_2329239 : CollatzResearch.WordTrace tailWord_2329239 prefixEnd_2329239 265782036932870572311229 := by
  unfold tailWord_2329239
  simp only [CollatzResearch.WordTrace]
  refine ⟨84954325608572380195646771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56636217072381586797097847 84954325608572380195646771)
  ·
    refine ⟨127431488412858570293470157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84954325608572380195646771 127431488412858570293470157)
    ·
      refine ⟨47786808154821963860051309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127431488412858570293470157 47786808154821963860051309)
      ·
        refine ⟨17920053058058236447519241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47786808154821963860051309 17920053058058236447519241)
        ·
          refine ⟨13440039793543677335639431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17920053058058236447519241 13440039793543677335639431)
          ·
            refine ⟨20160059690315516003459147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13440039793543677335639431 20160059690315516003459147)
            ·
              refine ⟨30240089535473274005188721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20160059690315516003459147 30240089535473274005188721)
              ·
                refine ⟨22680067151604955503891541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30240089535473274005188721 22680067151604955503891541)
                ·
                  refine ⟨265782036932870572311229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22680067151604955503891541 265782036932870572311229)
                  ·
                    rfl

theorem cell22_2329239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 8].length) (baseStart_2329239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2329239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2329239 prefixEnd_2329239 := by exact prefixLift 2329239
  have htrace : WordTrace (prefixWord ++ tailWord_2329239) baseStart_2329239 baseEnd_2329239 := by
    simpa [prefixWord, tailWord_2329239, baseEnd_2329239] using wordTrace_append hprefix tailTrace_2329239
  have hstable : (prefixWord ++ tailWord_2329239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2329239).length < 2 ^ (prefixWord ++ tailWord_2329239).sum := by decide
  have hdescent : baseEnd_2329239 < baseStart_2329239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2329239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2329241 : List Nat := [1, 2, 1, 2, 1, 2, 5, 3, 1, 4]
def baseStart_2329241 : Nat := 118140960795 + 2329241 * 2 ^ 59
def prefixEnd_2329241 : Nat := 4983230072969 + 3 ^ 40 * 2329241 * 2
def baseEnd_2329241 : Nat := 797346795439484378383681

theorem tailTrace_2329241 : CollatzResearch.WordTrace tailWord_2329241 prefixEnd_2329241 797346795439484378383681 := by
  unfold tailWord_2329241
  simp only [CollatzResearch.WordTrace]
  refine ⟨84954398554565134537219577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56636265703043423024813051 84954398554565134537219577)
  ·
    refine ⟨63715798915923850902914683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84954398554565134537219577 63715798915923850902914683)
    ·
      refine ⟨95573698373885776354372025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63715798915923850902914683 95573698373885776354372025)
      ·
        refine ⟨71680273780414332265779019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95573698373885776354372025 71680273780414332265779019)
        ·
          refine ⟨107520410670621498398668529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71680273780414332265779019 107520410670621498398668529)
          ·
            refine ⟨80640308002966123799001397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107520410670621498398668529 80640308002966123799001397)
            ·
              refine ⟨7560028875278074106156381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 80640308002966123799001397 7560028875278074106156381)
              ·
                refine ⟨2835010828229277789808643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7560028875278074106156381 2835010828229277789808643)
                ·
                  refine ⟨4252516242343916684712965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2835010828229277789808643 4252516242343916684712965)
                  ·
                    refine ⟨797346795439484378383681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4252516242343916684712965 797346795439484378383681)
                    ·
                      rfl

theorem cell22_2329241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 3, 1, 4].length) (baseStart_2329241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2329241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2329241 prefixEnd_2329241 := by exact prefixLift 2329241
  have htrace : WordTrace (prefixWord ++ tailWord_2329241) baseStart_2329241 baseEnd_2329241 := by
    simpa [prefixWord, tailWord_2329241, baseEnd_2329241] using wordTrace_append hprefix tailTrace_2329241
  have hstable : (prefixWord ++ tailWord_2329241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2329241).length < 2 ^ (prefixWord ++ tailWord_2329241).sum := by decide
  have hdescent : baseEnd_2329241 < baseStart_2329241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2329241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2329290 : List Nat := [3, 1, 2, 1, 4, 3, 1, 3, 4]
def baseStart_2329290 : Nat := 118140960795 + 2329290 * 2 ^ 59
def prefixEnd_2329290 : Nat := 4983230072969 + 3 ^ 40 * 2329290 * 2
def baseEnd_2329290 : Nat := 265787856380288194636177

theorem tailTrace_2329290 : CollatzResearch.WordTrace tailWord_2329290 prefixEnd_2329290 265787856380288194636177 := by
  unfold tailWord_2329290
  simp only [CollatzResearch.WordTrace]
  refine ⟨21239046432846903976438331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56637457154258410603835549 21239046432846903976438331)
  ·
    refine ⟨31858569649270355964657497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21239046432846903976438331 31858569649270355964657497)
    ·
      refine ⟨23893927236952766973493123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31858569649270355964657497 23893927236952766973493123)
      ·
        refine ⟨35840890855429150460239685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23893927236952766973493123 35840890855429150460239685)
        ·
          refine ⟨6720167035392965711294941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35840890855429150460239685 6720167035392965711294941)
          ·
            refine ⟨2520062638272362141735603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6720167035392965711294941 2520062638272362141735603)
            ·
              refine ⟨3780093957408543212603405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2520062638272362141735603 3780093957408543212603405)
              ·
                refine ⟨1417535234028203704726277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3780093957408543212603405 1417535234028203704726277)
                ·
                  refine ⟨265787856380288194636177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1417535234028203704726277 265787856380288194636177)
                  ·
                    rfl

theorem cell22_2329290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 3, 4].length) (baseStart_2329290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2329290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2329290 prefixEnd_2329290 := by exact prefixLift 2329290
  have htrace : WordTrace (prefixWord ++ tailWord_2329290) baseStart_2329290 baseEnd_2329290 := by
    simpa [prefixWord, tailWord_2329290, baseEnd_2329290] using wordTrace_append hprefix tailTrace_2329290
  have hstable : (prefixWord ++ tailWord_2329290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2329290).length < 2 ^ (prefixWord ++ tailWord_2329290).sum := by decide
  have hdescent : baseEnd_2329290 < baseStart_2329290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2329290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2329367 : List Nat := [1, 1, 3, 4, 3, 1, 1, 4, 1, 3]
def baseStart_2329367 : Nat := 118140960795 + 2329367 * 2 ^ 59
def prefixEnd_2329367 : Nat := 4983230072969 + 3 ^ 40 * 2329367 * 2
def baseEnd_2329367 : Nat := 797389927814462049733295

theorem tailTrace_2329367 : CollatzResearch.WordTrace tailWord_2329367 prefixEnd_2329367 797389927814462049733295 := by
  unfold tailWord_2329367
  simp only [CollatzResearch.WordTrace]
  refine ⟨84958994152108658056306355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56639329434739105370870903 84958994152108658056306355)
  ·
    refine ⟨127438491228162987084459533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84958994152108658056306355 127438491228162987084459533)
    ·
      refine ⟨47789434210561120156672325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127438491228162987084459533 47789434210561120156672325)
      ·
        refine ⟨8960518914480210029376061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47789434210561120156672325 8960518914480210029376061)
        ·
          refine ⟨3360194592930078761016023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8960518914480210029376061 3360194592930078761016023)
          ·
            refine ⟨5040291889395118141524035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3360194592930078761016023 5040291889395118141524035)
            ·
              refine ⟨7560437834092677212286053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5040291889395118141524035 7560437834092677212286053)
              ·
                refine ⟨1417582093892376977303635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7560437834092677212286053 1417582093892376977303635)
                ·
                  refine ⟨2126373140838565465955453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1417582093892376977303635 2126373140838565465955453)
                  ·
                    refine ⟨797389927814462049733295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2126373140838565465955453 797389927814462049733295)
                    ·
                      rfl

theorem cell22_2329367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 4, 1, 3].length) (baseStart_2329367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2329367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2329367 prefixEnd_2329367 := by exact prefixLift 2329367
  have htrace : WordTrace (prefixWord ++ tailWord_2329367) baseStart_2329367 baseEnd_2329367 := by
    simpa [prefixWord, tailWord_2329367, baseEnd_2329367] using wordTrace_append hprefix tailTrace_2329367
  have hstable : (prefixWord ++ tailWord_2329367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2329367).length < 2 ^ (prefixWord ++ tailWord_2329367).sum := by decide
  have hdescent : baseEnd_2329367 < baseStart_2329367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2329367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2329378 : List Nat := [3, 3, 1, 1, 2, 3, 1, 1, 2, 5]
def baseStart_2329378 : Nat := 118140960795 + 2329378 * 2 ^ 59
def prefixEnd_2329378 : Nat := 4983230072969 + 3 ^ 40 * 2329378 * 2
def baseEnd_2329378 : Nat := 797393693339261687708261

theorem tailTrace_2329378 : CollatzResearch.WordTrace tailWord_2329378 prefixEnd_2329378 797393693339261687708261 := by
  unfold tailWord_2329378
  simp only [CollatzResearch.WordTrace]
  refine ⟨21239848838767201733739197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56639596903379204623304525 21239848838767201733739197)
  ·
    refine ⟨7964943314537700650152199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21239848838767201733739197 7964943314537700650152199)
    ·
      refine ⟨11947414971806550975228299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7964943314537700650152199 11947414971806550975228299)
      ·
        refine ⟨17921122457709826462842449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11947414971806550975228299 17921122457709826462842449)
        ·
          refine ⟨13440841843282369847131837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17921122457709826462842449 13440841843282369847131837)
          ·
            refine ⟨5040315691230888692674439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13440841843282369847131837 5040315691230888692674439)
            ·
              refine ⟨7560473536846333039011659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5040315691230888692674439 7560473536846333039011659)
              ·
                refine ⟨11340710305269499558517489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7560473536846333039011659 11340710305269499558517489)
                ·
                  refine ⟨8505532728952124668888117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11340710305269499558517489 8505532728952124668888117)
                  ·
                    refine ⟨797393693339261687708261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8505532728952124668888117 797393693339261687708261)
                    ·
                      rfl

theorem cell22_2329378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_2329378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2329378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2329378 prefixEnd_2329378 := by exact prefixLift 2329378
  have htrace : WordTrace (prefixWord ++ tailWord_2329378) baseStart_2329378 baseEnd_2329378 := by
    simpa [prefixWord, tailWord_2329378, baseEnd_2329378] using wordTrace_append hprefix tailTrace_2329378
  have hstable : (prefixWord ++ tailWord_2329378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2329378).length < 2 ^ (prefixWord ++ tailWord_2329378).sum := by decide
  have hdescent : baseEnd_2329378 < baseStart_2329378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2329378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2329393 : List Nat := [1, 2, 2, 3, 2, 1, 2, 4, 1, 4]
def baseStart_2329393 : Nat := 118140960795 + 2329393 * 2 ^ 59
def prefixEnd_2329393 : Nat := 4983230072969 + 3 ^ 40 * 2329393 * 2
def baseEnd_2329393 : Nat := 797398828145806648583215

theorem tailTrace_2329393 : CollatzResearch.WordTrace tailWord_2329393 prefixEnd_2329393 797398828145806648583215 := by
  unfold tailWord_2329393
  simp only [CollatzResearch.WordTrace]
  refine ⟨84959942450014464496752833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56639961633342976331168555 84959942450014464496752833)
  ·
    refine ⟨63719956837510848372564625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84959942450014464496752833 63719956837510848372564625)
    ·
      refine ⟨47789967628133136279423469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63719956837510848372564625 47789967628133136279423469)
      ·
        refine ⟨17921237860549926104783801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47789967628133136279423469 17921237860549926104783801)
        ·
          refine ⟨13440928395412444578587851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17921237860549926104783801 13440928395412444578587851)
          ·
            refine ⟨20161392593118666867881777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13440928395412444578587851 20161392593118666867881777)
            ·
              refine ⟨15121044444839000150911333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20161392593118666867881777 15121044444839000150911333)
              ·
                refine ⟨2835195833407312528295875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15121044444839000150911333 2835195833407312528295875)
                ·
                  refine ⟨4252793750110968792443813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2835195833407312528295875 4252793750110968792443813)
                  ·
                    refine ⟨797398828145806648583215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4252793750110968792443813 797398828145806648583215)
                    ·
                      rfl

theorem cell22_2329393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 4, 1, 4].length) (baseStart_2329393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2329393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2329393 prefixEnd_2329393 := by exact prefixLift 2329393
  have htrace : WordTrace (prefixWord ++ tailWord_2329393) baseStart_2329393 baseEnd_2329393 := by
    simpa [prefixWord, tailWord_2329393, baseEnd_2329393] using wordTrace_append hprefix tailTrace_2329393
  have hstable : (prefixWord ++ tailWord_2329393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2329393).length < 2 ^ (prefixWord ++ tailWord_2329393).sum := by decide
  have hdescent : baseEnd_2329393 < baseStart_2329393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2329393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2329414 : List Nat := [6, 1, 1, 2, 2, 2, 1, 2, 5]
def baseStart_2329414 : Nat := 118140960795 + 2329414 * 2 ^ 59
def prefixEnd_2329414 : Nat := 4983230072969 + 3 ^ 40 * 2329414 * 2
def baseEnd_2329414 : Nat := 265802005624989864602717

theorem tailTrace_2329414 : CollatzResearch.WordTrace tailWord_2329414 prefixEnd_2329414 265802005624989864602717 := by
  unfold tailWord_2329414
  simp only [CollatzResearch.WordTrace]
  refine ⟨2655022136966824533852103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 56640472255292256722178197 2655022136966824533852103)
  ·
    refine ⟨3982533205450236800778155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2655022136966824533852103 3982533205450236800778155)
    ·
      refine ⟨5973799808175355201167233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3982533205450236800778155 5973799808175355201167233)
      ·
        refine ⟨4480349856131516400875425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5973799808175355201167233 4480349856131516400875425)
        ·
          refine ⟨3360262392098637300656569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4480349856131516400875425 3360262392098637300656569)
          ·
            refine ⟨2520196794073977975492427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3360262392098637300656569 2520196794073977975492427)
            ·
              refine ⟨3780295191110966963238641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2520196794073977975492427 3780295191110966963238641)
              ·
                refine ⟨2835221393333225222428981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3780295191110966963238641 2835221393333225222428981)
                ·
                  refine ⟨265802005624989864602717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2835221393333225222428981 265802005624989864602717)
                  ·
                    rfl

theorem cell22_2329414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_2329414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2329414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2329414 prefixEnd_2329414 := by exact prefixLift 2329414
  have htrace : WordTrace (prefixWord ++ tailWord_2329414) baseStart_2329414 baseEnd_2329414 := by
    simpa [prefixWord, tailWord_2329414, baseEnd_2329414] using wordTrace_append hprefix tailTrace_2329414
  have hstable : (prefixWord ++ tailWord_2329414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2329414).length < 2 ^ (prefixWord ++ tailWord_2329414).sum := by decide
  have hdescent : baseEnd_2329414 < baseStart_2329414 := by decide
  rcases family_descends (prefixWord ++ tailWord_2329414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2329466 : List Nat := [3, 1, 1, 1, 1, 1, 3, 2, 1, 8]
def baseStart_2329466 : Nat := 118140960795 + 2329466 * 2 ^ 59
def prefixEnd_2329466 : Nat := 4983230072969 + 3 ^ 40 * 2329466 * 2
def baseEnd_2329466 : Nat := 797423817537658791507991

theorem tailTrace_2329466 : CollatzResearch.WordTrace tailWord_2329466 prefixEnd_2329466 797423817537658791507991 := by
  unfold tailWord_2329466
  simp only [CollatzResearch.WordTrace]
  refine ⟨21240651244687499491040063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56641736652499998642773501 21240651244687499491040063)
  ·
    refine ⟨31860976867031249236560095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21240651244687499491040063 31860976867031249236560095)
    ·
      refine ⟨47791465300546873854840143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31860976867031249236560095 47791465300546873854840143)
      ·
        refine ⟨71687197950820310782260215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47791465300546873854840143 71687197950820310782260215)
        ·
          refine ⟨107530796926230466173390323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71687197950820310782260215 107530796926230466173390323)
          ·
            refine ⟨161296195389345699260085485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107530796926230466173390323 161296195389345699260085485)
            ·
              refine ⟨60486073271004637222532057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 161296195389345699260085485 60486073271004637222532057)
              ·
                refine ⟨45364554953253477916899043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60486073271004637222532057 45364554953253477916899043)
                ·
                  refine ⟨68046832429880216875348565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45364554953253477916899043 68046832429880216875348565)
                  ·
                    refine ⟨797423817537658791507991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 68046832429880216875348565 797423817537658791507991)
                    ·
                      rfl

theorem cell22_2329466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 1, 8].length) (baseStart_2329466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2329466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2329466 prefixEnd_2329466 := by exact prefixLift 2329466
  have htrace : WordTrace (prefixWord ++ tailWord_2329466) baseStart_2329466 baseEnd_2329466 := by
    simpa [prefixWord, tailWord_2329466, baseEnd_2329466] using wordTrace_append hprefix tailTrace_2329466
  have hstable : (prefixWord ++ tailWord_2329466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2329466).length < 2 ^ (prefixWord ++ tailWord_2329466).sum := by decide
  have hdescent : baseEnd_2329466 < baseStart_2329466 := by decide
  rcases family_descends (prefixWord ++ tailWord_2329466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2329468 : List Nat := [2, 2, 2, 1, 1, 1, 1, 4, 5, 3]
def baseStart_2329468 : Nat := 118140960795 + 2329468 * 2 ^ 59
def prefixEnd_2329468 : Nat := 4983230072969 + 3 ^ 40 * 2329468 * 2
def baseEnd_2329468 : Nat := 797424502178531452957985

theorem tailTrace_2329468 : CollatzResearch.WordTrace tailWord_2329468 prefixEnd_2329468 797424502178531452957985 := by
  unfold tailWord_2329468
  simp only [CollatzResearch.WordTrace]
  refine ⟨42481338962371376152866529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56641785283161834870488705 42481338962371376152866529)
  ·
    refine ⟨31861004221778532114649897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42481338962371376152866529 31861004221778532114649897)
    ·
      refine ⟨23895753166333899085987423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31861004221778532114649897 23895753166333899085987423)
      ·
        refine ⟨35843629749500848628981135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23895753166333899085987423 35843629749500848628981135)
        ·
          refine ⟨53765444624251272943471703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35843629749500848628981135 53765444624251272943471703)
          ·
            refine ⟨80648166936376909415207555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53765444624251272943471703 80648166936376909415207555)
            ·
              refine ⟨120972250404565364122811333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80648166936376909415207555 120972250404565364122811333)
              ·
                refine ⟨22682296950856005773027125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 120972250404565364122811333 22682296950856005773027125)
                ·
                  refine ⟨2126465339142750541221293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22682296950856005773027125 2126465339142750541221293)
                  ·
                    refine ⟨797424502178531452957985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2126465339142750541221293 797424502178531452957985)
                    ·
                      rfl

theorem cell22_2329468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 5, 3].length) (baseStart_2329468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2329468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2329468 prefixEnd_2329468 := by exact prefixLift 2329468
  have htrace : WordTrace (prefixWord ++ tailWord_2329468) baseStart_2329468 baseEnd_2329468 := by
    simpa [prefixWord, tailWord_2329468, baseEnd_2329468] using wordTrace_append hprefix tailTrace_2329468
  have hstable : (prefixWord ++ tailWord_2329468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2329468).length < 2 ^ (prefixWord ++ tailWord_2329468).sum := by decide
  have hdescent : baseEnd_2329468 < baseStart_2329468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2329468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2329575 : List Nat := [1, 1, 5, 2, 2, 1, 2, 2, 1, 5]
def baseStart_2329575 : Nat := 118140960795 + 2329575 * 2 ^ 59
def prefixEnd_2329575 : Nat := 4983230072969 + 3 ^ 40 * 2329575 * 2
def baseEnd_2329575 : Nat := 797461130465218840532657

theorem tailTrace_2329575 : CollatzResearch.WordTrace tailWord_2329575 prefixEnd_2329575 797461130465218840532657 := by
  unfold tailWord_2329575
  simp only [CollatzResearch.WordTrace]
  refine ⟨84966580535355109579878179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56644387023570073053252119 84966580535355109579878179)
  ·
    refine ⟨127449870803032664369817269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84966580535355109579878179 127449870803032664369817269)
    ·
      refine ⟨11948425387784312284670369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 127449870803032664369817269 11948425387784312284670369)
      ·
        refine ⟨8961319040838234213502777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11948425387784312284670369 8961319040838234213502777)
        ·
          refine ⟨6720989280628675660127083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8961319040838234213502777 6720989280628675660127083)
          ·
            refine ⟨10081483920943013490190625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6720989280628675660127083 10081483920943013490190625)
            ·
              refine ⟨7561112940707260117642969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10081483920943013490190625 7561112940707260117642969)
              ·
                refine ⟨5670834705530445088232227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7561112940707260117642969 5670834705530445088232227)
                ·
                  refine ⟨8506252058295667632348341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5670834705530445088232227 8506252058295667632348341)
                  ·
                    refine ⟨797461130465218840532657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8506252058295667632348341 797461130465218840532657)
                    ·
                      rfl

theorem cell22_2329575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_2329575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2329575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2329575 prefixEnd_2329575 := by exact prefixLift 2329575
  have htrace : WordTrace (prefixWord ++ tailWord_2329575) baseStart_2329575 baseEnd_2329575 := by
    simpa [prefixWord, tailWord_2329575, baseEnd_2329575] using wordTrace_append hprefix tailTrace_2329575
  have hstable : (prefixWord ++ tailWord_2329575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2329575).length < 2 ^ (prefixWord ++ tailWord_2329575).sum := by decide
  have hdescent : baseEnd_2329575 < baseStart_2329575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2329575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2329650 : List Nat := [3, 2, 1, 1, 2, 2, 2, 4, 5]
def baseStart_2329650 : Nat := 118140960795 + 2329650 * 2 ^ 59
def prefixEnd_2329650 : Nat := 4983230072969 + 3 ^ 40 * 2329650 * 2
def baseEnd_2329650 : Nat := 265828934832647881635809

theorem tailTrace_2329650 : CollatzResearch.WordTrace tailWord_2329650 prefixEnd_2329650 265828934832647881635809 := by
  unfold tailWord_2329650
  simp only [CollatzResearch.WordTrace]
  refine ⟨21242329002520849347214601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56646210673388931592572269 21242329002520849347214601)
  ·
    refine ⟨15931746751890637010410951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21242329002520849347214601 15931746751890637010410951)
    ·
      refine ⟨23897620127835955515616427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15931746751890637010410951 23897620127835955515616427)
      ·
        refine ⟨35846430191753933273424641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23897620127835955515616427 35846430191753933273424641)
        ·
          refine ⟨26884822643815449955068481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35846430191753933273424641 26884822643815449955068481)
          ·
            refine ⟨20163616982861587466301361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26884822643815449955068481 20163616982861587466301361)
            ·
              refine ⟨15122712737146190599726021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20163616982861587466301361 15122712737146190599726021)
              ·
                refine ⟨2835508638214910737448629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15122712737146190599726021 2835508638214910737448629)
                ·
                  refine ⟨265828934832647881635809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2835508638214910737448629 265828934832647881635809)
                  ·
                    rfl

theorem cell22_2329650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 4, 5].length) (baseStart_2329650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2329650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2329650 prefixEnd_2329650 := by exact prefixLift 2329650
  have htrace : WordTrace (prefixWord ++ tailWord_2329650) baseStart_2329650 baseEnd_2329650 := by
    simpa [prefixWord, tailWord_2329650, baseEnd_2329650] using wordTrace_append hprefix tailTrace_2329650
  have hstable : (prefixWord ++ tailWord_2329650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2329650).length < 2 ^ (prefixWord ++ tailWord_2329650).sum := by decide
  have hdescent : baseEnd_2329650 < baseStart_2329650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2329650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2329654 : List Nat := [5, 1, 2, 1, 1, 2, 3, 1, 3, 3]
def baseStart_2329654 : Nat := 118140960795 + 2329654 * 2 ^ 59
def prefixEnd_2329654 : Nat := 4983230072969 + 3 ^ 40 * 2329654 * 2
def baseEnd_2329654 : Nat := 797488173779688967807415

theorem tailTrace_2329654 : CollatzResearch.WordTrace tailWord_2329654 prefixEnd_2329654 797488173779688967807415 := by
  unfold tailWord_2329654
  simp only [CollatzResearch.WordTrace]
  refine ⟨5310591368879306629500251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 56646307934712604048002677 5310591368879306629500251)
  ·
    refine ⟨7965887053318959944250377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5310591368879306629500251 7965887053318959944250377)
    ·
      refine ⟨5974415289989219958187783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7965887053318959944250377 5974415289989219958187783)
      ·
        refine ⟨8961622934983829937281675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5974415289989219958187783 8961622934983829937281675)
        ·
          refine ⟨13442434402475744905922513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8961622934983829937281675 13442434402475744905922513)
          ·
            refine ⟨10081825801856808679441885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13442434402475744905922513 10081825801856808679441885)
            ·
              refine ⟨3780684675696303254790707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10081825801856808679441885 3780684675696303254790707)
              ·
                refine ⟨5671027013544454882186061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3780684675696303254790707 5671027013544454882186061)
                ·
                  refine ⟨2126635130079170580819773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5671027013544454882186061 2126635130079170580819773)
                  ·
                    refine ⟨797488173779688967807415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2126635130079170580819773 797488173779688967807415)
                    ·
                      rfl

theorem cell22_2329654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_2329654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2329654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2329654 prefixEnd_2329654 := by exact prefixLift 2329654
  have htrace : WordTrace (prefixWord ++ tailWord_2329654) baseStart_2329654 baseEnd_2329654 := by
    simpa [prefixWord, tailWord_2329654, baseEnd_2329654] using wordTrace_append hprefix tailTrace_2329654
  have hstable : (prefixWord ++ tailWord_2329654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2329654).length < 2 ^ (prefixWord ++ tailWord_2329654).sum := by decide
  have hdescent : baseEnd_2329654 < baseStart_2329654 := by decide
  rcases family_descends (prefixWord ++ tailWord_2329654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2329663 : List Nat := [1, 1, 2, 2, 3, 1, 1, 1, 2, 8]
def baseStart_2329663 : Nat := 118140960795 + 2329663 * 2 ^ 59
def prefixEnd_2329663 : Nat := 4983230072969 + 3 ^ 40 * 2329663 * 2
def baseEnd_2329663 : Nat := 797491254663615944332387

theorem tailTrace_2329663 : CollatzResearch.WordTrace tailWord_2329663 prefixEnd_2329663 797491254663615944332387 := by
  unfold tailWord_2329663
  simp only [CollatzResearch.WordTrace]
  refine ⟨84969790159036300609081643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56646526772690867072721095 84969790159036300609081643)
  ·
    refine ⟨127454685238554450913622465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84969790159036300609081643 127454685238554450913622465)
    ·
      refine ⟨95591013928915838185216849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127454685238554450913622465 95591013928915838185216849)
      ·
        refine ⟨71693260446686878638912637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95591013928915838185216849 71693260446686878638912637)
        ·
          refine ⟨26884972667507579489592239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71693260446686878638912637 26884972667507579489592239)
          ·
            refine ⟨40327459001261369234388359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26884972667507579489592239 40327459001261369234388359)
            ·
              refine ⟨60491188501892053851582539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40327459001261369234388359 60491188501892053851582539)
              ·
                refine ⟨90736782752838080777373809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60491188501892053851582539 90736782752838080777373809)
                ·
                  refine ⟨68052587064628560583030357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 90736782752838080777373809 68052587064628560583030357)
                  ·
                    refine ⟨797491254663615944332387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 68052587064628560583030357 797491254663615944332387)
                    ·
                      rfl

theorem cell22_2329663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 8].length) (baseStart_2329663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2329663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2329663 prefixEnd_2329663 := by exact prefixLift 2329663
  have htrace : WordTrace (prefixWord ++ tailWord_2329663) baseStart_2329663 baseEnd_2329663 := by
    simpa [prefixWord, tailWord_2329663, baseEnd_2329663] using wordTrace_append hprefix tailTrace_2329663
  have hstable : (prefixWord ++ tailWord_2329663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2329663).length < 2 ^ (prefixWord ++ tailWord_2329663).sum := by decide
  have hdescent : baseEnd_2329663 < baseStart_2329663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2329663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2329712 : List Nat := [2, 1, 1, 1, 5, 1, 3, 4, 4]
def baseStart_2329712 : Nat := 118140960795 + 2329712 * 2 ^ 59
def prefixEnd_2329712 : Nat := 4983230072969 + 3 ^ 40 * 2329712 * 2
def baseEnd_2329712 : Nat := 265836009454998716619079

theorem tailTrace_2329712 : CollatzResearch.WordTrace tailWord_2329712 prefixEnd_2329712 265836009454998716619079 := by
  unfold tailWord_2329712
  simp only [CollatzResearch.WordTrace]
  refine ⟨42485788667929390988807695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56647718223905854651743593 42485788667929390988807695)
  ·
    refine ⟨63728683001894086483211543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42485788667929390988807695 63728683001894086483211543)
    ·
      refine ⟨95593024502841129724817315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63728683001894086483211543 95593024502841129724817315)
      ·
        refine ⟨143389536754261694587225973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95593024502841129724817315 143389536754261694587225973)
        ·
          refine ⟨13442769070712033867552435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 143389536754261694587225973 13442769070712033867552435)
          ·
            refine ⟨20164153606068050801328653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13442769070712033867552435 20164153606068050801328653)
            ·
              refine ⟨7561557602275519050498245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20164153606068050801328653 7561557602275519050498245)
              ·
                refine ⟨1417792050426659821968421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7561557602275519050498245 1417792050426659821968421)
                ·
                  refine ⟨265836009454998716619079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1417792050426659821968421 265836009454998716619079)
                  ·
                    rfl

theorem cell22_2329712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 4, 4].length) (baseStart_2329712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2329712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2329712 prefixEnd_2329712 := by exact prefixLift 2329712
  have htrace : WordTrace (prefixWord ++ tailWord_2329712) baseStart_2329712 baseEnd_2329712 := by
    simpa [prefixWord, tailWord_2329712, baseEnd_2329712] using wordTrace_append hprefix tailTrace_2329712
  have hstable : (prefixWord ++ tailWord_2329712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2329712).length < 2 ^ (prefixWord ++ tailWord_2329712).sum := by decide
  have hdescent : baseEnd_2329712 < baseStart_2329712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2329712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2329725 : List Nat := [1, 4, 1, 1, 3, 1, 2, 2, 1, 6]
def baseStart_2329725 : Nat := 118140960795 + 2329725 * 2 ^ 59
def prefixEnd_2329725 : Nat := 4983230072969 + 3 ^ 40 * 2329725 * 2
def baseEnd_2329725 : Nat := 797512478530668449282197

theorem tailTrace_2329725 : CollatzResearch.WordTrace tailWord_2329725 prefixEnd_2329725 797512478530668449282197 := by
  unfold tailWord_2329725
  simp only [CollatzResearch.WordTrace]
  refine ⟨84972051484811685197838629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56648034323207790131892419 84972051484811685197838629)
  ·
    refine ⟨15932259653402190974594743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84972051484811685197838629 15932259653402190974594743)
    ·
      refine ⟨23898389480103286461892115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15932259653402190974594743 23898389480103286461892115)
      ·
        refine ⟨35847584220154929692838173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23898389480103286461892115 35847584220154929692838173)
        ·
          refine ⟨13442844082558098634814315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35847584220154929692838173 13442844082558098634814315)
          ·
            refine ⟨20164266123837147952221473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13442844082558098634814315 20164266123837147952221473)
            ·
              refine ⟨15123199592877860964166105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20164266123837147952221473 15123199592877860964166105)
              ·
                refine ⟨11342399694658395723124579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15123199592877860964166105 11342399694658395723124579)
                ·
                  refine ⟨17013599541987593584686869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11342399694658395723124579 17013599541987593584686869)
                  ·
                    refine ⟨797512478530668449282197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17013599541987593584686869 797512478530668449282197)
                    ·
                      rfl

theorem cell22_2329725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 2, 1, 6].length) (baseStart_2329725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2329725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2329725 prefixEnd_2329725 := by exact prefixLift 2329725
  have htrace : WordTrace (prefixWord ++ tailWord_2329725) baseStart_2329725 baseEnd_2329725 := by
    simpa [prefixWord, tailWord_2329725, baseEnd_2329725] using wordTrace_append hprefix tailTrace_2329725
  have hstable : (prefixWord ++ tailWord_2329725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2329725).length < 2 ^ (prefixWord ++ tailWord_2329725).sum := by decide
  have hdescent : baseEnd_2329725 < baseStart_2329725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2329725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2329742 : List Nat := [4, 1, 1, 3, 2, 2, 1, 1, 1, 6]
def baseStart_2329742 : Nat := 118140960795 + 2329742 * 2 ^ 59
def prefixEnd_2329742 : Nat := 4983230072969 + 3 ^ 40 * 2329742 * 2
def baseEnd_2329742 : Nat := 797518297978086071607145

theorem tailTrace_2329742 : CollatzResearch.WordTrace tailWord_2329742 prefixEnd_2329742 797518297978086071607145 := by
  unfold tailWord_2329742
  simp only [CollatzResearch.WordTrace]
  refine ⟨10621583940718762137650935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56648447683833398067471653 10621583940718762137650935)
  ·
    refine ⟨15932375911078143206476403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10621583940718762137650935 15932375911078143206476403)
    ·
      refine ⟨23898563866617214809714605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15932375911078143206476403 23898563866617214809714605)
      ·
        refine ⟨8961961449981455553642977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23898563866617214809714605 8961961449981455553642977)
        ·
          refine ⟨6721471087486091665232233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8961961449981455553642977 6721471087486091665232233)
          ·
            refine ⟨5041103315614568748924175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6721471087486091665232233 5041103315614568748924175)
            ·
              refine ⟨7561654973421853123386263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5041103315614568748924175 7561654973421853123386263)
              ·
                refine ⟨11342482460132779685079395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7561654973421853123386263 11342482460132779685079395)
                ·
                  refine ⟨17013723690199169527619093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11342482460132779685079395 17013723690199169527619093)
                  ·
                    refine ⟨797518297978086071607145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17013723690199169527619093 797518297978086071607145)
                    ·
                      rfl

theorem cell22_2329742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 1, 1, 6].length) (baseStart_2329742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2329742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2329742 prefixEnd_2329742 := by exact prefixLift 2329742
  have htrace : WordTrace (prefixWord ++ tailWord_2329742) baseStart_2329742 baseEnd_2329742 := by
    simpa [prefixWord, tailWord_2329742, baseEnd_2329742] using wordTrace_append hprefix tailTrace_2329742
  have hstable : (prefixWord ++ tailWord_2329742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2329742).length < 2 ^ (prefixWord ++ tailWord_2329742).sum := by decide
  have hdescent : baseEnd_2329742 < baseStart_2329742 := by decide
  rcases family_descends (prefixWord ++ tailWord_2329742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2329800 : List Nat := [2, 1, 3, 1, 2, 1, 2, 2, 1, 7]
def baseStart_2329800 : Nat := 118140960795 + 2329800 * 2 ^ 59
def prefixEnd_2329800 : Nat := 4983230072969 + 3 ^ 40 * 2329800 * 2
def baseEnd_2329800 : Nat := 797538152563393253656967

theorem tailTrace_2329800 : CollatzResearch.WordTrace tailWord_2329800 prefixEnd_2329800 797538152563393253656967 := by
  unfold tailWord_2329800
  simp only [CollatzResearch.WordTrace]
  refine ⟨42487393479769986503409427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56649857973026648671212569 42487393479769986503409427)
  ·
    refine ⟨63731090219654979755114141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42487393479769986503409427 63731090219654979755114141)
    ·
      refine ⟨23899158832370617408167803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63731090219654979755114141 23899158832370617408167803)
      ·
        refine ⟨35848738248555926112251705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23899158832370617408167803 35848738248555926112251705)
        ·
          refine ⟨26886553686416944584188779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35848738248555926112251705 26886553686416944584188779)
          ·
            refine ⟨40329830529625416876283169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26886553686416944584188779 40329830529625416876283169)
            ·
              refine ⟨30247372897219062657212377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40329830529625416876283169 30247372897219062657212377)
              ·
                refine ⟨22685529672914296992909283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30247372897219062657212377 22685529672914296992909283)
                ·
                  refine ⟨34028294509371445489363925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22685529672914296992909283 34028294509371445489363925)
                  ·
                    refine ⟨797538152563393253656967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34028294509371445489363925 797538152563393253656967)
                    ·
                      rfl

theorem cell22_2329800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 1, 7].length) (baseStart_2329800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2329800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2329800 prefixEnd_2329800 := by exact prefixLift 2329800
  have htrace : WordTrace (prefixWord ++ tailWord_2329800) baseStart_2329800 baseEnd_2329800 := by
    simpa [prefixWord, tailWord_2329800, baseEnd_2329800] using wordTrace_append hprefix tailTrace_2329800
  have hstable : (prefixWord ++ tailWord_2329800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2329800).length < 2 ^ (prefixWord ++ tailWord_2329800).sum := by decide
  have hdescent : baseEnd_2329800 < baseStart_2329800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2329800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2329832 : List Nat := [2, 1, 4, 1, 2, 1, 2, 2, 3, 4]
def baseStart_2329832 : Nat := 118140960795 + 2329832 * 2 ^ 59
def prefixEnd_2329832 : Nat := 4983230072969 + 3 ^ 40 * 2329832 * 2
def baseEnd_2329832 : Nat := 797549106817355836856869

theorem tailTrace_2329832 : CollatzResearch.WordTrace tailWord_2329832 prefixEnd_2329832 797549106817355836856869 := by
  unfold tailWord_2329832
  simp only [CollatzResearch.WordTrace]
  refine ⟨42487977047712021235991875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56650636063616028314655833 42487977047712021235991875)
  ·
    refine ⟨63731965571568031853987813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42487977047712021235991875 63731965571568031853987813)
    ·
      refine ⟨11949743544669005972622715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63731965571568031853987813 11949743544669005972622715)
      ·
        refine ⟨17924615317003508958934073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11949743544669005972622715 17924615317003508958934073)
        ·
          refine ⟨13443461487752631719200555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17924615317003508958934073 13443461487752631719200555)
          ·
            refine ⟨20165192231628947578800833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13443461487752631719200555 20165192231628947578800833)
            ·
              refine ⟨15123894173721710684100625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20165192231628947578800833 15123894173721710684100625)
              ·
                refine ⟨11342920630291283013075469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15123894173721710684100625 11342920630291283013075469)
                ·
                  refine ⟨4253595236359231129903301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11342920630291283013075469 4253595236359231129903301)
                  ·
                    refine ⟨797549106817355836856869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4253595236359231129903301 797549106817355836856869)
                    ·
                      rfl

theorem cell22_2329832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_2329832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2329832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2329832 prefixEnd_2329832 := by exact prefixLift 2329832
  have htrace : WordTrace (prefixWord ++ tailWord_2329832) baseStart_2329832 baseEnd_2329832 := by
    simpa [prefixWord, tailWord_2329832, baseEnd_2329832] using wordTrace_append hprefix tailTrace_2329832
  have hstable : (prefixWord ++ tailWord_2329832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2329832).length < 2 ^ (prefixWord ++ tailWord_2329832).sum := by decide
  have hdescent : baseEnd_2329832 < baseStart_2329832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2329832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2329874 : List Nat := [3, 2, 4, 2, 2, 1, 2, 2, 1, 3]
def baseStart_2329874 : Nat := 118140960795 + 2329874 * 2 ^ 59
def prefixEnd_2329874 : Nat := 4983230072969 + 3 ^ 40 * 2329874 * 2
def baseEnd_2329874 : Nat := 797563484275681727306741

theorem tailTrace_2329874 : CollatzResearch.WordTrace tailWord_2329874 prefixEnd_2329874 797563484275681727306741 := by
  unfold tailWord_2329874
  simp only [CollatzResearch.WordTrace]
  refine ⟨21244371490317970911253169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56651657307514589096675117 21244371490317970911253169)
  ·
    refine ⟨15933278617738478183439877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21244371490317970911253169 15933278617738478183439877)
    ·
      refine ⟨2987489740825964659394977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15933278617738478183439877 2987489740825964659394977)
      ·
        refine ⟨2240617305619473494546233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2987489740825964659394977 2240617305619473494546233)
        ·
          refine ⟨1680462979214605120909675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2240617305619473494546233 1680462979214605120909675)
          ·
            refine ⟨2520694468821907681364513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1680462979214605120909675 2520694468821907681364513)
            ·
              refine ⟨1890520851616430761023385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2520694468821907681364513 1890520851616430761023385)
              ·
                refine ⟨1417890638712323070767539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1890520851616430761023385 1417890638712323070767539)
                ·
                  refine ⟨2126835958068484606151309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1417890638712323070767539 2126835958068484606151309)
                  ·
                    refine ⟨797563484275681727306741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2126835958068484606151309 797563484275681727306741)
                    ·
                      rfl

theorem cell22_2329874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_2329874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2329874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2329874 prefixEnd_2329874 := by exact prefixLift 2329874
  have htrace : WordTrace (prefixWord ++ tailWord_2329874) baseStart_2329874 baseEnd_2329874 := by
    simpa [prefixWord, tailWord_2329874, baseEnd_2329874] using wordTrace_append hprefix tailTrace_2329874
  have hstable : (prefixWord ++ tailWord_2329874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2329874).length < 2 ^ (prefixWord ++ tailWord_2329874).sum := by decide
  have hdescent : baseEnd_2329874 < baseStart_2329874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2329874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2329896 : List Nat := [2, 1, 5, 1, 2, 1, 2, 3, 2, 3]
def baseStart_2329896 : Nat := 118140960795 + 2329896 * 2 ^ 59
def prefixEnd_2329896 : Nat := 4983230072969 + 3 ^ 40 * 2329896 * 2
def baseEnd_2329896 : Nat := 797571015325281003256673

theorem tailTrace_2329896 : CollatzResearch.WordTrace tailWord_2329896 prefixEnd_2329896 797571015325281003256673 := by
  unfold tailWord_2329896
  simp only [CollatzResearch.WordTrace]
  refine ⟨42489144183596090701156771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56652192244794787601542361 42489144183596090701156771)
  ·
    refine ⟨63733716275394136051735157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42489144183596090701156771 63733716275394136051735157)
    ·
      refine ⟨5975035900818200254850171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 63733716275394136051735157 5975035900818200254850171)
      ·
        refine ⟨8962553851227300382275257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5975035900818200254850171 8962553851227300382275257)
        ·
          refine ⟨6721915388420475286706443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8962553851227300382275257 6721915388420475286706443)
          ·
            refine ⟨10082873082630712930059665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6721915388420475286706443 10082873082630712930059665)
            ·
              refine ⟨7562154811973034697544749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10082873082630712930059665 7562154811973034697544749)
              ·
                refine ⟨2835808054489888011579281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7562154811973034697544749 2835808054489888011579281)
                ·
                  refine ⟨2126856040867416008684461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2835808054489888011579281 2126856040867416008684461)
                  ·
                    refine ⟨797571015325281003256673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2126856040867416008684461 797571015325281003256673)
                    ·
                      rfl

theorem cell22_2329896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_2329896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2329896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2329896 prefixEnd_2329896 := by exact prefixLift 2329896
  have htrace : WordTrace (prefixWord ++ tailWord_2329896) baseStart_2329896 baseEnd_2329896 := by
    simpa [prefixWord, tailWord_2329896, baseEnd_2329896] using wordTrace_append hprefix tailTrace_2329896
  have hstable : (prefixWord ++ tailWord_2329896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2329896).length < 2 ^ (prefixWord ++ tailWord_2329896).sum := by decide
  have hdescent : baseEnd_2329896 < baseStart_2329896 := by decide
  rcases family_descends (prefixWord ++ tailWord_2329896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2329909 : List Nat := [1, 3, 3, 1, 2, 3, 3, 6]
def baseStart_2329909 : Nat := 118140960795 + 2329909 * 2 ^ 59
def prefixEnd_2329909 : Nat := 4983230072969 + 3 ^ 40 * 2329909 * 2
def baseEnd_2329909 : Nat := 88619496165661478075737

theorem tailTrace_2329909 : CollatzResearch.WordTrace tailWord_2329909 prefixEnd_2329909 88619496165661478075737 := by
  unfold tailWord_2329909
  simp only [CollatzResearch.WordTrace]
  refine ⟨84978762516145084622536781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56652508344096723081691187 84978762516145084622536781)
  ·
    refine ⟨31867035943554406733451293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84978762516145084622536781 31867035943554406733451293)
    ·
      refine ⟨11950138478832902525044235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31867035943554406733451293 11950138478832902525044235)
      ·
        refine ⟨17925207718249353787566353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11950138478832902525044235 17925207718249353787566353)
        ·
          refine ⟨13443905788687015340674765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17925207718249353787566353 13443905788687015340674765)
          ·
            refine ⟨5041464670757630752753037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13443905788687015340674765 5041464670757630752753037)
            ·
              refine ⟨1890549251534111532282389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5041464670757630752753037 1890549251534111532282389)
              ·
                refine ⟨88619496165661478075737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1890549251534111532282389 88619496165661478075737)
                ·
                  rfl

theorem cell22_2329909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 3, 6].length) (baseStart_2329909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2329909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2329909 prefixEnd_2329909 := by exact prefixLift 2329909
  have htrace : WordTrace (prefixWord ++ tailWord_2329909) baseStart_2329909 baseEnd_2329909 := by
    simpa [prefixWord, tailWord_2329909, baseEnd_2329909] using wordTrace_append hprefix tailTrace_2329909
  have hstable : (prefixWord ++ tailWord_2329909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2329909).length < 2 ^ (prefixWord ++ tailWord_2329909).sum := by decide
  have hdescent : baseEnd_2329909 < baseStart_2329909 := by decide
  rcases family_descends (prefixWord ++ tailWord_2329909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2329937 : List Nat := [1, 2, 2, 1, 4, 1, 3, 1, 7]
def baseStart_2329937 : Nat := 118140960795 + 2329937 * 2 ^ 59
def prefixEnd_2329937 : Nat := 4983230072969 + 3 ^ 40 * 2329937 * 2
def baseEnd_2329937 : Nat := 265861683487723520993849

theorem tailTrace_2329937 : CollatzResearch.WordTrace tailWord_2329937 prefixEnd_2329937 265861683487723520993849 := by
  unfold tailWord_2329937
  simp only [CollatzResearch.WordTrace]
  refine ⟨84979783760043645404556065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56653189173362430269704043 84979783760043645404556065)
  ·
    refine ⟨63734837820032734053417049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84979783760043645404556065 63734837820032734053417049)
    ·
      refine ⟨47801128365024550540062787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63734837820032734053417049 47801128365024550540062787)
      ·
        refine ⟨71701692547536825810094181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47801128365024550540062787 71701692547536825810094181)
        ·
          refine ⟨13444067352663154839392659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71701692547536825810094181 13444067352663154839392659)
          ·
            refine ⟨20166101028994732259088989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13444067352663154839392659 20166101028994732259088989)
            ·
              refine ⟨7562287885873024597158371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20166101028994732259088989 7562287885873024597158371)
              ·
                refine ⟨11343431828809536895737557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7562287885873024597158371 11343431828809536895737557)
                ·
                  refine ⟨265861683487723520993849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11343431828809536895737557 265861683487723520993849)
                  ·
                    rfl

theorem cell22_2329937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 1, 7].length) (baseStart_2329937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2329937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2329937 prefixEnd_2329937 := by exact prefixLift 2329937
  have htrace : WordTrace (prefixWord ++ tailWord_2329937) baseStart_2329937 baseEnd_2329937 := by
    simpa [prefixWord, tailWord_2329937, baseEnd_2329937] using wordTrace_append hprefix tailTrace_2329937
  have hstable : (prefixWord ++ tailWord_2329937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2329937).length < 2 ^ (prefixWord ++ tailWord_2329937).sum := by decide
  have hdescent : baseEnd_2329937 < baseStart_2329937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2329937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2329941 : List Nat := [1, 3, 2, 2, 3, 2, 2, 1, 3, 3]
def baseStart_2329941 : Nat := 118140960795 + 2329941 * 2 ^ 59
def prefixEnd_2329941 : Nat := 4983230072969 + 3 ^ 40 * 2329941 * 2
def baseEnd_2329941 : Nat := 797586419744915885881535

theorem tailTrace_2329941 : CollatzResearch.WordTrace tailWord_2329941 prefixEnd_2329941 797586419744915885881535 := by
  unfold tailWord_2329941
  simp only [CollatzResearch.WordTrace]
  refine ⟨84979929652029154087701677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56653286434686102725134451 84979929652029154087701677)
  ·
    refine ⟨31867473619510932782888129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84979929652029154087701677 31867473619510932782888129)
    ·
      refine ⟨23900605214633199587166097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31867473619510932782888129 23900605214633199587166097)
      ·
        refine ⟨17925453910974899690374573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23900605214633199587166097 17925453910974899690374573)
        ·
          refine ⟨6722045216615587383890465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17925453910974899690374573 6722045216615587383890465)
          ·
            refine ⟨5041533912461690537917849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6722045216615587383890465 5041533912461690537917849)
            ·
              refine ⟨3781150434346267903438387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5041533912461690537917849 3781150434346267903438387)
              ·
                refine ⟨5671725651519401855157581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3781150434346267903438387 5671725651519401855157581)
                ·
                  refine ⟨2126897119319775695684093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5671725651519401855157581 2126897119319775695684093)
                  ·
                    refine ⟨797586419744915885881535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2126897119319775695684093 797586419744915885881535)
                    ·
                      rfl

theorem cell22_2329941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 1, 3, 3].length) (baseStart_2329941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2329941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2329941 prefixEnd_2329941 := by exact prefixLift 2329941
  have htrace : WordTrace (prefixWord ++ tailWord_2329941) baseStart_2329941 baseEnd_2329941 := by
    simpa [prefixWord, tailWord_2329941, baseEnd_2329941] using wordTrace_append hprefix tailTrace_2329941
  have hstable : (prefixWord ++ tailWord_2329941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2329941).length < 2 ^ (prefixWord ++ tailWord_2329941).sum := by decide
  have hdescent : baseEnd_2329941 < baseStart_2329941 := by decide
  rcases family_descends (prefixWord ++ tailWord_2329941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2330018 : List Nat := [3, 3, 1, 2, 1, 4, 1, 2, 1, 4]
def baseStart_2330018 : Nat := 118140960795 + 2330018 * 2 ^ 59
def prefixEnd_2330018 : Nat := 4983230072969 + 3 ^ 40 * 2330018 * 2
def baseEnd_2330018 : Nat := 797612778418513351706299

theorem tailTrace_2330018 : CollatzResearch.WordTrace tailWord_2330018 prefixEnd_2330018 797612778418513351706299 := by
  unfold tailWord_2330018
  simp only [CollatzResearch.WordTrace]
  refine ⟨21245684518187549059563677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56655158715166797492169805 21245684518187549059563677)
  ·
    refine ⟨7967131694320330897336379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21245684518187549059563677 7967131694320330897336379)
    ·
      refine ⟨11950697541480496346004569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7967131694320330897336379 11950697541480496346004569)
      ·
        refine ⟨8963023156110372259503427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11950697541480496346004569 8963023156110372259503427)
        ·
          refine ⟨13444534734165558389255141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8963023156110372259503427 13444534734165558389255141)
          ·
            refine ⟨2520850262656042197985339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13444534734165558389255141 2520850262656042197985339)
            ·
              refine ⟨3781275393984063296978009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2520850262656042197985339 3781275393984063296978009)
              ·
                refine ⟨2835956545488047472733507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3781275393984063296978009 2835956545488047472733507)
                ·
                  refine ⟨4253934818232071209100261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2835956545488047472733507 4253934818232071209100261)
                  ·
                    refine ⟨797612778418513351706299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4253934818232071209100261 797612778418513351706299)
                    ·
                      rfl

theorem cell22_2330018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 2, 1, 4].length) (baseStart_2330018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2330018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2330018 prefixEnd_2330018 := by exact prefixLift 2330018
  have htrace : WordTrace (prefixWord ++ tailWord_2330018) baseStart_2330018 baseEnd_2330018 := by
    simpa [prefixWord, tailWord_2330018, baseEnd_2330018] using wordTrace_append hprefix tailTrace_2330018
  have hstable : (prefixWord ++ tailWord_2330018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2330018).length < 2 ^ (prefixWord ++ tailWord_2330018).sum := by decide
  have hdescent : baseEnd_2330018 < baseStart_2330018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2330018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2330044 : List Nat := [2, 2, 2, 4, 2, 10]
def baseStart_2330044 : Nat := 118140960795 + 2330044 * 2 ^ 59
def prefixEnd_2330044 : Nat := 4983230072969 + 3 ^ 40 * 2330044 * 2
def baseEnd_2330044 : Nat := 9847181219134048772299

theorem tailTrace_2330044 : CollatzResearch.WordTrace tailWord_2330044 prefixEnd_2330044 9847181219134048772299 := by
  unfold tailWord_2330044
  simp only [CollatzResearch.WordTrace]
  refine ⟨42491843185328001339350593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56655790913770668452467457 42491843185328001339350593)
  ·
    refine ⟨31868882388996001004512945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42491843185328001339350593 31868882388996001004512945)
    ·
      refine ⟨23901661791747000753384709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31868882388996001004512945 23901661791747000753384709)
      ·
        refine ⟨4481561585952562641259633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23901661791747000753384709 4481561585952562641259633)
        ·
          refine ⟨3361171189464421980944725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4481561585952562641259633 3361171189464421980944725)
          ·
            refine ⟨9847181219134048772299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3361171189464421980944725 9847181219134048772299)
            ·
              rfl

theorem cell22_2330044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 10].length) (baseStart_2330044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2330044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2330044 prefixEnd_2330044 := by exact prefixLift 2330044
  have htrace : WordTrace (prefixWord ++ tailWord_2330044) baseStart_2330044 baseEnd_2330044 := by
    simpa [prefixWord, tailWord_2330044, baseEnd_2330044] using wordTrace_append hprefix tailTrace_2330044
  have hstable : (prefixWord ++ tailWord_2330044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2330044).length < 2 ^ (prefixWord ++ tailWord_2330044).sum := by decide
  have hdescent : baseEnd_2330044 < baseStart_2330044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2330044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2330104 : List Nat := [2, 1, 2, 1, 1, 5, 1, 2, 2, 5]
def baseStart_2330104 : Nat := 118140960795 + 2330104 * 2 ^ 59
def prefixEnd_2330104 : Nat := 4983230072969 + 3 ^ 40 * 2330104 * 2
def baseEnd_2330104 : Nat := 797642217976037794056035

theorem tailTrace_2330104 : CollatzResearch.WordTrace tailWord_2330104 prefixEnd_2330104 797642217976037794056035 := by
  unfold tailWord_2330104
  simp only [CollatzResearch.WordTrace]
  refine ⟨42492937375219316462942683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56657249833625755283923577 42492937375219316462942683)
  ·
    refine ⟨63739406062828974694414025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42492937375219316462942683 63739406062828974694414025)
    ·
      refine ⟨47804554547121731020810519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63739406062828974694414025 47804554547121731020810519)
      ·
        refine ⟨71706831820682596531215779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47804554547121731020810519 71706831820682596531215779)
        ·
          refine ⟨107560247731023894796823669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71706831820682596531215779 107560247731023894796823669)
          ·
            refine ⟨10083773224783490137202219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 107560247731023894796823669 10083773224783490137202219)
            ·
              refine ⟨15125659837175235205803329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10083773224783490137202219 15125659837175235205803329)
              ·
                refine ⟨11344244877881426404352497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15125659837175235205803329 11344244877881426404352497)
                ·
                  refine ⟨8508183658411069803264373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11344244877881426404352497 8508183658411069803264373)
                  ·
                    refine ⟨797642217976037794056035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8508183658411069803264373 797642217976037794056035)
                    ·
                      rfl

theorem cell22_2330104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 2, 2, 5].length) (baseStart_2330104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2330104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2330104 prefixEnd_2330104 := by exact prefixLift 2330104
  have htrace : WordTrace (prefixWord ++ tailWord_2330104) baseStart_2330104 baseEnd_2330104 := by
    simpa [prefixWord, tailWord_2330104, baseEnd_2330104] using wordTrace_append hprefix tailTrace_2330104
  have hstable : (prefixWord ++ tailWord_2330104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2330104).length < 2 ^ (prefixWord ++ tailWord_2330104).sum := by decide
  have hdescent : baseEnd_2330104 < baseStart_2330104 := by decide
  rcases family_descends (prefixWord ++ tailWord_2330104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2330123 : List Nat := [1, 1, 1, 1, 8, 1, 3, 1, 5]
def baseStart_2330123 : Nat := 118140960795 + 2330123 * 2 ^ 59
def prefixEnd_2330123 : Nat := 4983230072969 + 3 ^ 40 * 2330123 * 2
def baseEnd_2330123 : Nat := 265882907354776025943659

theorem tailTrace_2330123 : CollatzResearch.WordTrace tailWord_2330123 prefixEnd_2330123 265882907354776025943659 := by
  unfold tailWord_2330123
  simp only [CollatzResearch.WordTrace]
  refine ⟨84986567737369799170827023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56657711824913199447218015 84986567737369799170827023)
  ·
    refine ⟨127479851606054698756240535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84986567737369799170827023 127479851606054698756240535)
    ·
      refine ⟨191219777409082048134360803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127479851606054698756240535 191219777409082048134360803)
      ·
        refine ⟨286829666113623072201541205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191219777409082048134360803 286829666113623072201541205)
        ·
          refine ⟨3361285149769020377361811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 286829666113623072201541205 3361285149769020377361811)
          ·
            refine ⟨5041927724653530566042717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3361285149769020377361811 5041927724653530566042717)
            ·
              refine ⟨1890722896745073962266019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5041927724653530566042717 1890722896745073962266019)
              ·
                refine ⟨2836084345117610943399029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1890722896745073962266019 2836084345117610943399029)
                ·
                  refine ⟨265882907354776025943659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2836084345117610943399029 265882907354776025943659)
                  ·
                    rfl

theorem cell22_2330123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 3, 1, 5].length) (baseStart_2330123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2330123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2330123 prefixEnd_2330123 := by exact prefixLift 2330123
  have htrace : WordTrace (prefixWord ++ tailWord_2330123) baseStart_2330123 baseEnd_2330123 := by
    simpa [prefixWord, tailWord_2330123, baseEnd_2330123] using wordTrace_append hprefix tailTrace_2330123
  have hstable : (prefixWord ++ tailWord_2330123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2330123).length < 2 ^ (prefixWord ++ tailWord_2330123).sum := by decide
  have hdescent : baseEnd_2330123 < baseStart_2330123 := by decide
  rcases family_descends (prefixWord ++ tailWord_2330123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2330149 : List Nat := [1, 3, 1, 2, 2, 1, 1, 3, 3, 5]
def baseStart_2330149 : Nat := 118140960795 + 2330149 * 2 ^ 59
def prefixEnd_2330149 : Nat := 4983230072969 + 3 ^ 40 * 2330149 * 2
def baseEnd_2330149 : Nat := 797657622395672676680897

theorem tailTrace_2330149 : CollatzResearch.WordTrace tailWord_2330149 prefixEnd_2330149 797657622395672676680897 := by
  unfold tailWord_2330149
  simp only [CollatzResearch.WordTrace]
  refine ⟨84987516035275605611273501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56658344023517070407515667 84987516035275605611273501)
  ·
    refine ⟨31870318513228352104227563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84987516035275605611273501 31870318513228352104227563)
    ·
      refine ⟨47805477769842528156341345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31870318513228352104227563 47805477769842528156341345)
      ·
        refine ⟨35854108327381896117256009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47805477769842528156341345 35854108327381896117256009)
        ·
          refine ⟨26890581245536422087942007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35854108327381896117256009 26890581245536422087942007)
          ·
            refine ⟨40335871868304633131913011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26890581245536422087942007 40335871868304633131913011)
            ·
              refine ⟨60503807802456949697869517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40335871868304633131913011 60503807802456949697869517)
              ·
                refine ⟨22688927925921356136701069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60503807802456949697869517 22688927925921356136701069)
                ·
                  refine ⟨8508347972220508551262901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22688927925921356136701069 8508347972220508551262901)
                  ·
                    refine ⟨797657622395672676680897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8508347972220508551262901 797657622395672676680897)
                    ·
                      rfl

theorem cell22_2330149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 3, 5].length) (baseStart_2330149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2330149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2330149 prefixEnd_2330149 := by exact prefixLift 2330149
  have htrace : WordTrace (prefixWord ++ tailWord_2330149) baseStart_2330149 baseEnd_2330149 := by
    simpa [prefixWord, tailWord_2330149, baseEnd_2330149] using wordTrace_append hprefix tailTrace_2330149
  have hstable : (prefixWord ++ tailWord_2330149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2330149).length < 2 ^ (prefixWord ++ tailWord_2330149).sum := by decide
  have hdescent : baseEnd_2330149 < baseStart_2330149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2330149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2330226 : List Nat := [3, 2, 1, 2, 3, 1, 1, 1, 2, 6]
def baseStart_2330226 : Nat := 118140960795 + 2330226 * 2 ^ 59
def prefixEnd_2330226 : Nat := 4983230072969 + 3 ^ 40 * 2330226 * 2
def baseEnd_2330226 : Nat := 797683981069270142505661

theorem tailTrace_2330226 : CollatzResearch.WordTrace tailWord_2330226 prefixEnd_2330226 797683981069270142505661 := by
  unfold tailWord_2330226
  simp only [CollatzResearch.WordTrace]
  refine ⟨21247581113999161940456633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56660216303997765174551021 21247581113999161940456633)
  ·
    refine ⟨15935685835499371455342475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21247581113999161940456633 15935685835499371455342475)
    ·
      refine ⟨23903528753249057183013713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15935685835499371455342475 23903528753249057183013713)
      ·
        refine ⟨17927646564936792887260285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23903528753249057183013713 17927646564936792887260285)
        ·
          refine ⟨6722867461851297332722607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17927646564936792887260285 6722867461851297332722607)
          ·
            refine ⟨10084301192776945999083911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6722867461851297332722607 10084301192776945999083911)
            ·
              refine ⟨15126451789165418998625867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10084301192776945999083911 15126451789165418998625867)
              ·
                refine ⟨22689677683748128497938801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15126451789165418998625867 22689677683748128497938801)
                ·
                  refine ⟨17017258262811096373454101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22689677683748128497938801 17017258262811096373454101)
                  ·
                    refine ⟨797683981069270142505661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17017258262811096373454101 797683981069270142505661)
                    ·
                      rfl

theorem cell22_2330226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 2, 6].length) (baseStart_2330226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2330226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2330226 prefixEnd_2330226 := by exact prefixLift 2330226
  have htrace : WordTrace (prefixWord ++ tailWord_2330226) baseStart_2330226 baseEnd_2330226 := by
    simpa [prefixWord, tailWord_2330226, baseEnd_2330226] using wordTrace_append hprefix tailTrace_2330226
  have hstable : (prefixWord ++ tailWord_2330226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2330226).length < 2 ^ (prefixWord ++ tailWord_2330226).sum := by decide
  have hdescent : baseEnd_2330226 < baseStart_2330226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2330226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2330318 : List Nat := [4, 1, 1, 1, 3, 1, 1, 1, 6, 3]
def baseStart_2330318 : Nat := 118140960795 + 2330318 * 2 ^ 59
def prefixEnd_2330318 : Nat := 4983230072969 + 3 ^ 40 * 2330318 * 2
def baseEnd_2330318 : Nat := 797715474549412569205379

theorem tailTrace_2330318 : CollatzResearch.WordTrace tailWord_2330318 prefixEnd_2330318 797715474549412569205379 := by
  unfold tailWord_2330318
  simp only [CollatzResearch.WordTrace]
  refine ⟨10624209996457918434271951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56662453314442231649450405 10624209996457918434271951)
  ·
    refine ⟨15936314994686877651407927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10624209996457918434271951 15936314994686877651407927)
    ·
      refine ⟨23904472492030316477111891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15936314994686877651407927 23904472492030316477111891)
      ·
        refine ⟨35856708738045474715667837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23904472492030316477111891 35856708738045474715667837)
        ·
          refine ⟨13446265776767053018375439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35856708738045474715667837 13446265776767053018375439)
          ·
            refine ⟨20169398665150579527563159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13446265776767053018375439 20169398665150579527563159)
            ·
              refine ⟨30254097997725869291344739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20169398665150579527563159 30254097997725869291344739)
              ·
                refine ⟨45381146996588803937017109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30254097997725869291344739 45381146996588803937017109)
                ·
                  refine ⟨2127241265465100184547677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 45381146996588803937017109 2127241265465100184547677)
                  ·
                    refine ⟨797715474549412569205379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2127241265465100184547677 797715474549412569205379)
                    ·
                      rfl

theorem cell22_2330318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 6, 3].length) (baseStart_2330318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2330318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2330318 prefixEnd_2330318 := by exact prefixLift 2330318
  have htrace : WordTrace (prefixWord ++ tailWord_2330318) baseStart_2330318 baseEnd_2330318 := by
    simpa [prefixWord, tailWord_2330318, baseEnd_2330318] using wordTrace_append hprefix tailTrace_2330318
  have hstable : (prefixWord ++ tailWord_2330318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2330318).length < 2 ^ (prefixWord ++ tailWord_2330318).sum := by decide
  have hdescent : baseEnd_2330318 < baseStart_2330318 := by decide
  rcases family_descends (prefixWord ++ tailWord_2330318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2330337 : List Nat := [1, 2, 3, 1, 5, 1, 3, 2, 4]
def baseStart_2330337 : Nat := 118140960795 + 2330337 * 2 ^ 59
def prefixEnd_2330337 : Nat := 4983230072969 + 3 ^ 40 * 2330337 * 2
def baseEnd_2330337 : Nat := 265907326212567617660107

theorem tailTrace_2330337 : CollatzResearch.WordTrace tailWord_2330337 prefixEnd_2330337 265907326212567617660107 := by
  unfold tailWord_2330337
  simp only [CollatzResearch.WordTrace]
  refine ⟨84994372958594513719117265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56662915305729675812744843 84994372958594513719117265)
  ·
    refine ⟨63745779718945885289337949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84994372958594513719117265 63745779718945885289337949)
    ·
      refine ⟨23904667394604706983501731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63745779718945885289337949 23904667394604706983501731)
      ·
        refine ⟨35857001091907060475252597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23904667394604706983501731 35857001091907060475252597)
        ·
          refine ⟨3361593852366286919554931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35857001091907060475252597 3361593852366286919554931)
          ·
            refine ⟨5042390778549430379332397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3361593852366286919554931 5042390778549430379332397)
            ·
              refine ⟨1890896541956036392249649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5042390778549430379332397 1890896541956036392249649)
              ·
                refine ⟨1418172406467027294187237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1890896541956036392249649 1418172406467027294187237)
                ·
                  refine ⟨265907326212567617660107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1418172406467027294187237 265907326212567617660107)
                  ·
                    rfl

theorem cell22_2330337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 3, 2, 4].length) (baseStart_2330337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2330337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2330337 prefixEnd_2330337 := by exact prefixLift 2330337
  have htrace : WordTrace (prefixWord ++ tailWord_2330337) baseStart_2330337 baseEnd_2330337 := by
    simpa [prefixWord, tailWord_2330337, baseEnd_2330337] using wordTrace_append hprefix tailTrace_2330337
  have hstable : (prefixWord ++ tailWord_2330337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2330337).length < 2 ^ (prefixWord ++ tailWord_2330337).sum := by decide
  have hdescent : baseEnd_2330337 < baseStart_2330337 := by decide
  rcases family_descends (prefixWord ++ tailWord_2330337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2330388 : List Nat := [2, 4, 4, 1, 1, 2, 2, 2, 4]
def baseStart_2330388 : Nat := 118140960795 + 2330388 * 2 ^ 59
def prefixEnd_2330388 : Nat := 4983230072969 + 3 ^ 40 * 2330388 * 2
def baseEnd_2330388 : Nat := 265913145659985239985055

theorem tailTrace_2330388 : CollatzResearch.WordTrace tailWord_2330388 prefixEnd_2330388 265913145659985239985055 := by
  unfold tailWord_2330388
  simp only [CollatzResearch.WordTrace]
  refine ⟨42498116540704874714611909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56664155387606499619482545 42498116540704874714611909)
  ·
    refine ⟨7968396851382164008989733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42498116540704874714611909 7968396851382164008989733)
    ·
      refine ⟨1494074409634155751685575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7968396851382164008989733 1494074409634155751685575)
      ·
        refine ⟨2241111614451233627528363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1494074409634155751685575 2241111614451233627528363)
        ·
          refine ⟨3361667421676850441292545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2241111614451233627528363 3361667421676850441292545)
          ·
            refine ⟨2521250566257637830969409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3361667421676850441292545 2521250566257637830969409)
            ·
              refine ⟨1890937924693228373227057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2521250566257637830969409 1890937924693228373227057)
              ·
                refine ⟨1418203443519921279920293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1890937924693228373227057 1418203443519921279920293)
                ·
                  refine ⟨265913145659985239985055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1418203443519921279920293 265913145659985239985055)
                  ·
                    rfl

theorem cell22_2330388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 2, 2, 4].length) (baseStart_2330388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2330388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2330388 prefixEnd_2330388 := by exact prefixLift 2330388
  have htrace : WordTrace (prefixWord ++ tailWord_2330388) baseStart_2330388 baseEnd_2330388 := by
    simpa [prefixWord, tailWord_2330388, baseEnd_2330388] using wordTrace_append hprefix tailTrace_2330388
  have hstable : (prefixWord ++ tailWord_2330388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2330388).length < 2 ^ (prefixWord ++ tailWord_2330388).sum := by decide
  have hdescent : baseEnd_2330388 < baseStart_2330388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2330388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2330408 : List Nat := [2, 1, 5, 1, 1, 2, 1, 1, 1, 7]
def baseStart_2330408 : Nat := 118140960795 + 2330408 * 2 ^ 59
def prefixEnd_2330408 : Nat := 4983230072969 + 3 ^ 40 * 2330408 * 2
def baseEnd_2330408 : Nat := 797746283388682334455103

theorem tailTrace_2330408 : CollatzResearch.WordTrace tailWord_2330408 prefixEnd_2330408 797746283388682334455103 := by
  unfold tailWord_2330408
  simp only [CollatzResearch.WordTrace]
  refine ⟨42498481270668646422475939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56664641694224861896634585 42498481270668646422475939)
  ·
    refine ⟨63747721906002969633713909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42498481270668646422475939 63747721906002969633713909)
    ·
      refine ⟨5976348928687778403160679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 63747721906002969633713909 5976348928687778403160679)
      ·
        refine ⟨8964523393031667604741019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5976348928687778403160679 8964523393031667604741019)
        ·
          refine ⟨13446785089547501407111529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8964523393031667604741019 13446785089547501407111529)
          ·
            refine ⟨10085088817160626055333647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13446785089547501407111529 10085088817160626055333647)
            ·
              refine ⟨15127633225740939083000471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10085088817160626055333647 15127633225740939083000471)
              ·
                refine ⟨22691449838611408624500707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15127633225740939083000471 22691449838611408624500707)
                ·
                  refine ⟨34037174757917112936751061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22691449838611408624500707 34037174757917112936751061)
                  ·
                    refine ⟨797746283388682334455103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34037174757917112936751061 797746283388682334455103)
                    ·
                      rfl

theorem cell22_2330408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_2330408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2330408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2330408 prefixEnd_2330408 := by exact prefixLift 2330408
  have htrace : WordTrace (prefixWord ++ tailWord_2330408) baseStart_2330408 baseEnd_2330408 := by
    simpa [prefixWord, tailWord_2330408, baseEnd_2330408] using wordTrace_append hprefix tailTrace_2330408
  have hstable : (prefixWord ++ tailWord_2330408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2330408).length < 2 ^ (prefixWord ++ tailWord_2330408).sum := by decide
  have hdescent : baseEnd_2330408 < baseStart_2330408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2330408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2330440 : List Nat := [2, 1, 3, 1, 1, 5, 1, 3, 1, 4]
def baseStart_2330440 : Nat := 118140960795 + 2330440 * 2 ^ 59
def prefixEnd_2330440 : Nat := 4983230072969 + 3 ^ 40 * 2330440 * 2
def baseEnd_2330440 : Nat := 797757237642644917655005

theorem tailTrace_2330440 : CollatzResearch.WordTrace tailWord_2330440 prefixEnd_2330440 797757237642644917655005 := by
  unfold tailWord_2330440
  simp only [CollatzResearch.WordTrace]
  refine ⟨42499064838610681155058387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56665419784814241540077849 42499064838610681155058387)
  ·
    refine ⟨63748597257916021732587581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42499064838610681155058387 63748597257916021732587581)
    ·
      refine ⟨23905723971718508149720343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63748597257916021732587581 23905723971718508149720343)
      ·
        refine ⟨35858585957577762224580515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23905723971718508149720343 35858585957577762224580515)
        ·
          refine ⟨53787878936366643336870773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35858585957577762224580515 53787878936366643336870773)
          ·
            refine ⟨5042613650284372812831635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53787878936366643336870773 5042613650284372812831635)
            ·
              refine ⟨7563920475426559219247453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5042613650284372812831635 7563920475426559219247453)
              ·
                refine ⟨2836470178284959707217795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7563920475426559219247453 2836470178284959707217795)
                ·
                  refine ⟨4254705267427439560826693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2836470178284959707217795 4254705267427439560826693)
                  ·
                    refine ⟨797757237642644917655005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4254705267427439560826693 797757237642644917655005)
                    ·
                      rfl

theorem cell22_2330440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 3, 1, 4].length) (baseStart_2330440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2330440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2330440 prefixEnd_2330440 := by exact prefixLift 2330440
  have htrace : WordTrace (prefixWord ++ tailWord_2330440) baseStart_2330440 baseEnd_2330440 := by
    simpa [prefixWord, tailWord_2330440, baseEnd_2330440] using wordTrace_append hprefix tailTrace_2330440
  have hstable : (prefixWord ++ tailWord_2330440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2330440).length < 2 ^ (prefixWord ++ tailWord_2330440).sum := by decide
  have hdescent : baseEnd_2330440 < baseStart_2330440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2330440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2330455 : List Nat := [1, 1, 3, 2, 5, 1, 2, 1, 6]
def baseStart_2330455 : Nat := 118140960795 + 2330455 * 2 ^ 59
def prefixEnd_2330455 : Nat := 4983230072969 + 3 ^ 40 * 2330455 * 2
def baseEnd_2330455 : Nat := 265920790816396626176653

theorem tailTrace_2330455 : CollatzResearch.WordTrace tailWord_2330455 prefixEnd_2330455 265920790816396626176653 := by
  unfold tailWord_2330455
  simp only [CollatzResearch.WordTrace]
  refine ⟨84998676772167019871912819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56665784514778013247941879 84998676772167019871912819)
  ·
    refine ⟨127498015158250529807869229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84998676772167019871912819 127498015158250529807869229)
    ·
      refine ⟨47811755684343948677950961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127498015158250529807869229 47811755684343948677950961)
      ·
        refine ⟨35858816763257961508463221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47811755684343948677950961 35858816763257961508463221)
        ·
          refine ⟨3361764071555433891418427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35858816763257961508463221 3361764071555433891418427)
          ·
            refine ⟨5042646107333150837127641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3361764071555433891418427 5042646107333150837127641)
            ·
              refine ⟨3781984580499863127845731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5042646107333150837127641 3781984580499863127845731)
              ·
                refine ⟨5672976870749794691768597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3781984580499863127845731 5672976870749794691768597)
                ·
                  refine ⟨265920790816396626176653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5672976870749794691768597 265920790816396626176653)
                  ·
                    rfl

theorem cell22_2330455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 1, 6].length) (baseStart_2330455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2330455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2330455 prefixEnd_2330455 := by exact prefixLift 2330455
  have htrace : WordTrace (prefixWord ++ tailWord_2330455) baseStart_2330455 baseEnd_2330455 := by
    simpa [prefixWord, tailWord_2330455, baseEnd_2330455] using wordTrace_append hprefix tailTrace_2330455
  have hstable : (prefixWord ++ tailWord_2330455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2330455).length < 2 ^ (prefixWord ++ tailWord_2330455).sum := by decide
  have hdescent : baseEnd_2330455 < baseStart_2330455 := by decide
  rcases family_descends (prefixWord ++ tailWord_2330455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2330474 : List Nat := [3, 1, 3, 4, 1, 1, 2, 2, 1, 4]
def baseStart_2330474 : Nat := 118140960795 + 2330474 * 2 ^ 59
def prefixEnd_2330474 : Nat := 4983230072969 + 3 ^ 40 * 2330474 * 2
def baseEnd_2330474 : Nat := 797768876537480162304901

theorem tailTrace_2330474 : CollatzResearch.WordTrace tailWord_2330474 prefixEnd_2330474 797768876537480162304901 := by
  unfold tailWord_2330474
  simp only [CollatzResearch.WordTrace]
  refine ⟨21249842439774546529213619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56666246506065457411236317 21249842439774546529213619)
  ·
    refine ⟨31874763659661819793820429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21249842439774546529213619 31874763659661819793820429)
    ·
      refine ⟨11953036372373182422682661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31874763659661819793820429 11953036372373182422682661)
      ·
        refine ⟨2241194319819971704252999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11953036372373182422682661 2241194319819971704252999)
        ·
          refine ⟨3361791479729957556379499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2241194319819971704252999 3361791479729957556379499)
          ·
            refine ⟨5042687219594936334569249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3361791479729957556379499 5042687219594936334569249)
            ·
              refine ⟨3782015414696202250926937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5042687219594936334569249 3782015414696202250926937)
              ·
                refine ⟨2836511561022151688195203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3782015414696202250926937 2836511561022151688195203)
                ·
                  refine ⟨4254767341533227532292805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2836511561022151688195203 4254767341533227532292805)
                  ·
                    refine ⟨797768876537480162304901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4254767341533227532292805 797768876537480162304901)
                    ·
                      rfl

theorem cell22_2330474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 2, 1, 4].length) (baseStart_2330474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2330474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2330474 prefixEnd_2330474 := by exact prefixLift 2330474
  have htrace : WordTrace (prefixWord ++ tailWord_2330474) baseStart_2330474 baseEnd_2330474 := by
    simpa [prefixWord, tailWord_2330474, baseEnd_2330474] using wordTrace_append hprefix tailTrace_2330474
  have hstable : (prefixWord ++ tailWord_2330474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2330474).length < 2 ^ (prefixWord ++ tailWord_2330474).sum := by decide
  have hdescent : baseEnd_2330474 < baseStart_2330474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2330474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2330485 : List Nat := [1, 3, 4, 1, 1, 1, 2, 3, 2, 4]
def baseStart_2330485 : Nat := 118140960795 + 2330485 * 2 ^ 59
def prefixEnd_2330485 : Nat := 4983230072969 + 3 ^ 40 * 2330485 * 2
def baseEnd_2330485 : Nat := 797772642062279800279867

theorem tailTrace_2330485 : CollatzResearch.WordTrace tailWord_2330485 prefixEnd_2330485 797772642062279800279867 := by
  unfold tailWord_2330485
  simp only [CollatzResearch.WordTrace]
  refine ⟨84999770962058334995504909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56666513974705556663669939 84999770962058334995504909)
  ·
    refine ⟨31874914110771875623314341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84999770962058334995504909 31874914110771875623314341)
    ·
      refine ⟨5976546395769726679371439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31874914110771875623314341 5976546395769726679371439)
      ·
        refine ⟨8964819593654590019057159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5976546395769726679371439 8964819593654590019057159)
        ·
          refine ⟨13447229390481885028585739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8964819593654590019057159 13447229390481885028585739)
          ·
            refine ⟨20170844085722827542878609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13447229390481885028585739 20170844085722827542878609)
            ·
              refine ⟨15128133064292120657158957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20170844085722827542878609 15128133064292120657158957)
              ·
                refine ⟨5673049899109545246434609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15128133064292120657158957 5673049899109545246434609)
                ·
                  refine ⟨4254787424332158934825957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5673049899109545246434609 4254787424332158934825957)
                  ·
                    refine ⟨797772642062279800279867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4254787424332158934825957 797772642062279800279867)
                    ·
                      rfl

theorem cell22_2330485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_2330485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2330485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2330485 prefixEnd_2330485 := by exact prefixLift 2330485
  have htrace : WordTrace (prefixWord ++ tailWord_2330485) baseStart_2330485 baseEnd_2330485 := by
    simpa [prefixWord, tailWord_2330485, baseEnd_2330485] using wordTrace_append hprefix tailTrace_2330485
  have hstable : (prefixWord ++ tailWord_2330485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2330485).length < 2 ^ (prefixWord ++ tailWord_2330485).sum := by decide
  have hdescent : baseEnd_2330485 < baseStart_2330485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2330485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2330607 : List Nat := [1, 1, 2, 1, 4, 2, 4, 3, 4]
def baseStart_2330607 : Nat := 118140960795 + 2330607 * 2 ^ 59
def prefixEnd_2330607 : Nat := 4983230072969 + 3 ^ 40 * 2330607 * 2
def baseEnd_2330607 : Nat := 265938135051837382909831

theorem tailTrace_2330607 : CollatzResearch.WordTrace tailWord_2330607 prefixEnd_2330607 265938135051837382909831 := by
  unfold tailWord_2330607
  simp only [CollatzResearch.WordTrace]
  refine ⟨85004220667616349831446075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56669480445077566554297383 85004220667616349831446075)
  ·
    refine ⟨127506331001424524747169113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85004220667616349831446075 127506331001424524747169113)
    ·
      refine ⟨95629748251068393560376835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127506331001424524747169113 95629748251068393560376835)
      ·
        refine ⟨143444622376602590340565253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95629748251068393560376835 143444622376602590340565253)
        ·
          refine ⟨26895866695612985688855985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 143444622376602590340565253 26895866695612985688855985)
          ·
            refine ⟨20171900021709739266641989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26895866695612985688855985 20171900021709739266641989)
            ·
              refine ⟨3782231254070576112495373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20171900021709739266641989 3782231254070576112495373)
              ·
                refine ⟨1418336720276466042185765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3782231254070576112495373 1418336720276466042185765)
                ·
                  refine ⟨265938135051837382909831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1418336720276466042185765 265938135051837382909831)
                  ·
                    rfl

theorem cell22_2330607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 3, 4].length) (baseStart_2330607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2330607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2330607 prefixEnd_2330607 := by exact prefixLift 2330607
  have htrace : WordTrace (prefixWord ++ tailWord_2330607) baseStart_2330607 baseEnd_2330607 := by
    simpa [prefixWord, tailWord_2330607, baseEnd_2330607] using wordTrace_append hprefix tailTrace_2330607
  have hstable : (prefixWord ++ tailWord_2330607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2330607).length < 2 ^ (prefixWord ++ tailWord_2330607).sum := by decide
  have hdescent : baseEnd_2330607 < baseStart_2330607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2330607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2330620 : List Nat := [2, 2, 2, 1, 2, 2, 2, 1, 4, 4]
def baseStart_2330620 : Nat := 118140960795 + 2330620 * 2 ^ 59
def prefixEnd_2330620 : Nat := 4983230072969 + 3 ^ 40 * 2330620 * 2
def baseEnd_2330620 : Nat := 797818855321184448154453

theorem tailTrace_2330620 : CollatzResearch.WordTrace tailWord_2330620 prefixEnd_2330620 797818855321184448154453 := by
  unfold tailWord_2330620
  simp only [CollatzResearch.WordTrace]
  refine ⟨42502347408284626525834657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56669796544379502034446209 42502347408284626525834657)
  ·
    refine ⟨31876760556213469894375993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42502347408284626525834657 31876760556213469894375993)
    ·
      refine ⟨23907570417160102420781995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31876760556213469894375993 23907570417160102420781995)
      ·
        refine ⟨35861355625740153631172993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23907570417160102420781995 35861355625740153631172993)
        ·
          refine ⟨26896016719305115223379745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35861355625740153631172993 26896016719305115223379745)
          ·
            refine ⟨20172012539478836417534809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26896016719305115223379745 20172012539478836417534809)
            ·
              refine ⟨15129009404609127313151107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20172012539478836417534809 15129009404609127313151107)
              ·
                refine ⟨22693514106913690969726661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15129009404609127313151107 22693514106913690969726661)
                ·
                  refine ⟨4255033895046317056823749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22693514106913690969726661 4255033895046317056823749)
                  ·
                    refine ⟨797818855321184448154453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4255033895046317056823749 797818855321184448154453)
                    ·
                      rfl

theorem cell22_2330620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 4, 4].length) (baseStart_2330620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2330620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2330620 prefixEnd_2330620 := by exact prefixLift 2330620
  have htrace : WordTrace (prefixWord ++ tailWord_2330620) baseStart_2330620 baseEnd_2330620 := by
    simpa [prefixWord, tailWord_2330620, baseEnd_2330620] using wordTrace_append hprefix tailTrace_2330620
  have hstable : (prefixWord ++ tailWord_2330620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2330620).length < 2 ^ (prefixWord ++ tailWord_2330620).sum := by decide
  have hdescent : baseEnd_2330620 < baseStart_2330620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2330620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2330630 : List Nat := [6, 2, 1, 2, 1, 1, 3, 1, 5]
def baseStart_2330630 : Nat := 118140960795 + 2330630 * 2 ^ 59
def prefixEnd_2330630 : Nat := 4983230072969 + 3 ^ 40 * 2330630 * 2
def baseEnd_2330630 : Nat := 265940759508515918468141

theorem tailTrace_2330630 : CollatzResearch.WordTrace tailWord_2330630 prefixEnd_2330630 265940759508515918468141 := by
  unfold tailWord_2330630
  simp only [CollatzResearch.WordTrace]
  refine ⟨2656408110829157023735417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 56670039697688683173022229 2656408110829157023735417)
  ·
    refine ⟨1992306083121867767801563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2656408110829157023735417 1992306083121867767801563)
    ·
      refine ⟨2988459124682801651702345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1992306083121867767801563 2988459124682801651702345)
      ·
        refine ⟨2241344343512101238776759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2988459124682801651702345 2241344343512101238776759)
        ·
          refine ⟨3362016515268151858165139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2241344343512101238776759 3362016515268151858165139)
          ·
            refine ⟨5043024772902227787247709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3362016515268151858165139 5043024772902227787247709)
            ·
              refine ⟨1891134289838335420217891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5043024772902227787247709 1891134289838335420217891)
              ·
                refine ⟨2836701434757503130326837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1891134289838335420217891 2836701434757503130326837)
                ·
                  refine ⟨265940759508515918468141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2836701434757503130326837 265940759508515918468141)
                  ·
                    rfl

theorem cell22_2330630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_2330630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2330630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2330630 prefixEnd_2330630 := by exact prefixLift 2330630
  have htrace : WordTrace (prefixWord ++ tailWord_2330630) baseStart_2330630 baseEnd_2330630 := by
    simpa [prefixWord, tailWord_2330630, baseEnd_2330630] using wordTrace_append hprefix tailTrace_2330630
  have hstable : (prefixWord ++ tailWord_2330630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2330630).length < 2 ^ (prefixWord ++ tailWord_2330630).sum := by decide
  have hdescent : baseEnd_2330630 < baseStart_2330630 := by decide
  rcases family_descends (prefixWord ++ tailWord_2330630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2330652 : List Nat := [2, 2, 3, 1, 3, 1, 4, 6]
def baseStart_2330652 : Nat := 118140960795 + 2330652 * 2 ^ 59
def prefixEnd_2330652 : Nat := 4983230072969 + 3 ^ 40 * 2330652 * 2
def baseEnd_2330652 : Nat := 88647756619460781261595

theorem tailTrace_2330652 : CollatzResearch.WordTrace tailWord_2330652 prefixEnd_2330652 88647756619460781261595 := by
  unfold tailWord_2330652
  simp only [CollatzResearch.WordTrace]
  refine ⟨42502930976226661258417105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56670574634968881677889473 42502930976226661258417105)
  ·
    refine ⟨31877198232169995943812829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42502930976226661258417105 31877198232169995943812829)
    ·
      refine ⟨11953949337063748478929811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31877198232169995943812829 11953949337063748478929811)
      ·
        refine ⟨17930924005595622718394717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11953949337063748478929811 17930924005595622718394717)
        ·
          refine ⟨6724096502098358519398019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17930924005595622718394717 6724096502098358519398019)
          ·
            refine ⟨10086144753147537779097029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6724096502098358519398019 10086144753147537779097029)
            ·
              refine ⟨1891152141215163333580693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10086144753147537779097029 1891152141215163333580693)
              ·
                refine ⟨88647756619460781261595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1891152141215163333580693 88647756619460781261595)
                ·
                  rfl

theorem cell22_2330652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 4, 6].length) (baseStart_2330652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2330652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2330652 prefixEnd_2330652 := by exact prefixLift 2330652
  have htrace : WordTrace (prefixWord ++ tailWord_2330652) baseStart_2330652 baseEnd_2330652 := by
    simpa [prefixWord, tailWord_2330652, baseEnd_2330652] using wordTrace_append hprefix tailTrace_2330652
  have hstable : (prefixWord ++ tailWord_2330652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2330652).length < 2 ^ (prefixWord ++ tailWord_2330652).sum := by decide
  have hdescent : baseEnd_2330652 < baseStart_2330652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2330652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2330695 : List Nat := [1, 1, 4, 1, 3, 1, 2, 1, 1, 7]
def baseStart_2330695 : Nat := 118140960795 + 2330695 * 2 ^ 59
def prefixEnd_2330695 : Nat := 4983230072969 + 3 ^ 40 * 2330695 * 2
def baseEnd_2330695 : Nat := 797844529353909252529223

theorem tailTrace_2330695 : CollatzResearch.WordTrace tailWord_2330695 prefixEnd_2330695 797844529353909252529223 := by
  unfold tailWord_2330695
  simp only [CollatzResearch.WordTrace]
  refine ⟨85007430291297540860649539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56671620194198360573766359 85007430291297540860649539)
  ·
    refine ⟨127511145436946311290974309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85007430291297540860649539 127511145436946311290974309)
    ·
      refine ⟨23908339769427433367057683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 127511145436946311290974309 23908339769427433367057683)
      ·
        refine ⟨35862509654141150050586525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23908339769427433367057683 35862509654141150050586525)
        ·
          refine ⟨13448441120302931268969947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35862509654141150050586525 13448441120302931268969947)
          ·
            refine ⟨20172661680454396903454921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13448441120302931268969947 20172661680454396903454921)
            ·
              refine ⟨15129496260340797677591191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20172661680454396903454921 15129496260340797677591191)
              ·
                refine ⟨22694244390511196516386787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15129496260340797677591191 22694244390511196516386787)
                ·
                  refine ⟨34041366585766794774580181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22694244390511196516386787 34041366585766794774580181)
                  ·
                    refine ⟨797844529353909252529223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34041366585766794774580181 797844529353909252529223)
                    ·
                      rfl

theorem cell22_2330695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 7].length) (baseStart_2330695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2330695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2330695 prefixEnd_2330695 := by exact prefixLift 2330695
  have htrace : WordTrace (prefixWord ++ tailWord_2330695) baseStart_2330695 baseEnd_2330695 := by
    simpa [prefixWord, tailWord_2330695, baseEnd_2330695] using wordTrace_append hprefix tailTrace_2330695
  have hstable : (prefixWord ++ tailWord_2330695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2330695).length < 2 ^ (prefixWord ++ tailWord_2330695).sum := by decide
  have hdescent : baseEnd_2330695 < baseStart_2330695 := by decide
  rcases family_descends (prefixWord ++ tailWord_2330695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2330757 : List Nat := [1, 3, 1, 1, 5, 1, 1, 3, 1, 5]
def baseStart_2330757 : Nat := 118140960795 + 2330757 * 2 ^ 59
def prefixEnd_2330757 : Nat := 4983230072969 + 3 ^ 40 * 2330757 * 2
def baseEnd_2330757 : Nat := 797865753220961757479033

theorem tailTrace_2330757 : CollatzResearch.WordTrace tailWord_2330757 prefixEnd_2330757 797865753220961757479033 := by
  unfold tailWord_2330757
  simp only [CollatzResearch.WordTrace]
  refine ⟨85009691617072925449406525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56673127744715283632937683 85009691617072925449406525)
  ·
    refine ⟨31878634356402347043527447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85009691617072925449406525 31878634356402347043527447)
    ·
      refine ⟨47817951534603520565291171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31878634356402347043527447 47817951534603520565291171)
      ·
        refine ⟨71726927301905280847936757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47817951534603520565291171 71726927301905280847936757)
        ·
          refine ⟨6724399434553620079494071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 71726927301905280847936757 6724399434553620079494071)
          ·
            refine ⟨10086599151830430119241107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6724399434553620079494071 10086599151830430119241107)
            ·
              refine ⟨15129898727745645178861661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10086599151830430119241107 15129898727745645178861661)
              ·
                refine ⟨5673712022904616942073123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15129898727745645178861661 5673712022904616942073123)
                ·
                  refine ⟨8510568034356925413109685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5673712022904616942073123 8510568034356925413109685)
                  ·
                    refine ⟨797865753220961757479033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8510568034356925413109685 797865753220961757479033)
                    ·
                      rfl

theorem cell22_2330757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 3, 1, 5].length) (baseStart_2330757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2330757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2330757 prefixEnd_2330757 := by exact prefixLift 2330757
  have htrace : WordTrace (prefixWord ++ tailWord_2330757) baseStart_2330757 baseEnd_2330757 := by
    simpa [prefixWord, tailWord_2330757, baseEnd_2330757] using wordTrace_append hprefix tailTrace_2330757
  have hstable : (prefixWord ++ tailWord_2330757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2330757).length < 2 ^ (prefixWord ++ tailWord_2330757).sum := by decide
  have hdescent : baseEnd_2330757 < baseStart_2330757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2330757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2330776 : List Nat := [2, 1, 2, 4, 3, 1, 2, 3, 4]
def baseStart_2330776 : Nat := 118140960795 + 2330776 * 2 ^ 59
def prefixEnd_2330776 : Nat := 4983230072969 + 3 ^ 40 * 2330776 * 2
def baseEnd_2330776 : Nat := 265957419103084013751325

theorem tailTrace_2330776 : CollatzResearch.WordTrace tailWord_2330776 prefixEnd_2330776 265957419103084013751325 := by
  unfold tailWord_2330776
  simp only [CollatzResearch.WordTrace]
  refine ⟨42505192302002045847174091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56673589736002727796232121 42505192302002045847174091)
  ·
    refine ⟨63757788453003068770761137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42505192302002045847174091 63757788453003068770761137)
    ·
      refine ⟨47818341339752301578070853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63757788453003068770761137 47818341339752301578070853)
      ·
        refine ⟨8965939001203556545888285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47818341339752301578070853 8965939001203556545888285)
        ·
          refine ⟨3362227125451333704708107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8965939001203556545888285 3362227125451333704708107)
          ·
            refine ⟨5043340688177000557062161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3362227125451333704708107 5043340688177000557062161)
            ·
              refine ⟨3782505516132750417796621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5043340688177000557062161 3782505516132750417796621)
              ·
                refine ⟨1418439568549781406673733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3782505516132750417796621 1418439568549781406673733)
                ·
                  refine ⟨265957419103084013751325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1418439568549781406673733 265957419103084013751325)
                  ·
                    rfl

theorem cell22_2330776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 3, 4].length) (baseStart_2330776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2330776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2330776 prefixEnd_2330776 := by exact prefixLift 2330776
  have htrace : WordTrace (prefixWord ++ tailWord_2330776) baseStart_2330776 baseEnd_2330776 := by
    simpa [prefixWord, tailWord_2330776, baseEnd_2330776] using wordTrace_append hprefix tailTrace_2330776
  have hstable : (prefixWord ++ tailWord_2330776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2330776).length < 2 ^ (prefixWord ++ tailWord_2330776).sum := by decide
  have hdescent : baseEnd_2330776 < baseStart_2330776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2330776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2330778 : List Nat := [3, 1, 1, 5, 2, 2, 2, 1, 1, 4]
def baseStart_2330778 : Nat := 118140960795 + 2330778 * 2 ^ 59
def prefixEnd_2330778 : Nat := 4983230072969 + 3 ^ 40 * 2330778 * 2
def baseEnd_2330778 : Nat := 797872941950124702703969

theorem tailTrace_2330778 : CollatzResearch.WordTrace tailWord_2330778 prefixEnd_2330778 797872941950124702703969 := by
  unfold tailWord_2330778
  simp only [CollatzResearch.WordTrace]
  refine ⟨21252614387499211508980247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56673638366664564023947325 21252614387499211508980247)
  ·
    refine ⟨31878921581248817263470371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21252614387499211508980247 31878921581248817263470371)
    ·
      refine ⟨47818382371873225895205557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31878921581248817263470371 47818382371873225895205557)
      ·
        refine ⟨4482973347363114927675521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47818382371873225895205557 4482973347363114927675521)
        ·
          refine ⟨3362230010522336195756641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4482973347363114927675521 3362230010522336195756641)
          ·
            refine ⟨2521672507891752146817481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3362230010522336195756641 2521672507891752146817481)
            ·
              refine ⟨1891254380918814110113111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2521672507891752146817481 1891254380918814110113111)
              ·
                refine ⟨2836881571378221165169667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1891254380918814110113111 2836881571378221165169667)
                ·
                  refine ⟨4255322357067331747754501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2836881571378221165169667 4255322357067331747754501)
                  ·
                    refine ⟨797872941950124702703969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4255322357067331747754501 797872941950124702703969)
                    ·
                      rfl

theorem cell22_2330778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 2, 1, 1, 4].length) (baseStart_2330778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2330778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2330778 prefixEnd_2330778 := by exact prefixLift 2330778
  have htrace : WordTrace (prefixWord ++ tailWord_2330778) baseStart_2330778 baseEnd_2330778 := by
    simpa [prefixWord, tailWord_2330778, baseEnd_2330778] using wordTrace_append hprefix tailTrace_2330778
  have hstable : (prefixWord ++ tailWord_2330778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2330778).length < 2 ^ (prefixWord ++ tailWord_2330778).sum := by decide
  have hdescent : baseEnd_2330778 < baseStart_2330778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2330778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2330791 : List Nat := [1, 1, 6, 2, 2, 1, 1, 1, 4, 3]
def baseStart_2330791 : Nat := 118140960795 + 2330791 * 2 ^ 59
def prefixEnd_2330791 : Nat := 4983230072969 + 3 ^ 40 * 2330791 * 2
def baseEnd_2330791 : Nat := 797877392115797002128929

theorem tailTrace_2330791 : CollatzResearch.WordTrace tailWord_2330791 prefixEnd_2330791 797877392115797002128929 := by
  unfold tailWord_2330791
  simp only [CollatzResearch.WordTrace]
  refine ⟨85010931698949749256144227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56673954465966499504096151 85010931698949749256144227)
  ·
    refine ⟨127516397548424623884216341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85010931698949749256144227 127516397548424623884216341)
    ·
      refine ⟨5977331135082404244572641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 127516397548424623884216341 5977331135082404244572641)
      ·
        refine ⟨4482998351311803183429481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5977331135082404244572641 4482998351311803183429481)
        ·
          refine ⟨3362248763483852387572111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4482998351311803183429481 3362248763483852387572111)
          ·
            refine ⟨5043373145225778581358167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3362248763483852387572111 5043373145225778581358167)
            ·
              refine ⟨7565059717838667872037251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5043373145225778581358167 7565059717838667872037251)
              ·
                refine ⟨11347589576758001808055877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7565059717838667872037251 11347589576758001808055877)
                ·
                  refine ⟨2127673045642125339010477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11347589576758001808055877 2127673045642125339010477)
                  ·
                    refine ⟨797877392115797002128929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2127673045642125339010477 797877392115797002128929)
                    ·
                      rfl

theorem cell22_2330791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_2330791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2330791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2330791 prefixEnd_2330791 := by exact prefixLift 2330791
  have htrace : WordTrace (prefixWord ++ tailWord_2330791) baseStart_2330791 baseEnd_2330791 := by
    simpa [prefixWord, tailWord_2330791, baseEnd_2330791] using wordTrace_append hprefix tailTrace_2330791
  have hstable : (prefixWord ++ tailWord_2330791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2330791).length < 2 ^ (prefixWord ++ tailWord_2330791).sum := by decide
  have hdescent : baseEnd_2330791 < baseStart_2330791 := by decide
  rcases family_descends (prefixWord ++ tailWord_2330791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2330862 : List Nat := [4, 1, 2, 1, 1, 1, 1, 1, 2, 8]
def baseStart_2330862 : Nat := 118140960795 + 2330862 * 2 ^ 59
def prefixEnd_2330862 : Nat := 4983230072969 + 3 ^ 40 * 2330862 * 2
def baseEnd_2330862 : Nat := 797901696866776483603711

theorem tailTrace_2330862 : CollatzResearch.WordTrace tailWord_2330862 prefixEnd_2330862 797901696866776483603711 := by
  unfold tailWord_2330862
  simp only [CollatzResearch.WordTrace]
  refine ⟨10626690160211566047747355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56675680854461685587985893 10626690160211566047747355)
  ·
    refine ⟨15940035240317349071621033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10626690160211566047747355 15940035240317349071621033)
    ·
      refine ⟨11955026430238011803715775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15940035240317349071621033 11955026430238011803715775)
      ·
        refine ⟨17932539645357017705573663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11955026430238011803715775 17932539645357017705573663)
        ·
          refine ⟨26898809468035526558360495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17932539645357017705573663 26898809468035526558360495)
          ·
            refine ⟨40348214202053289837540743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26898809468035526558360495 40348214202053289837540743)
            ·
              refine ⟨60522321303079934756311115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40348214202053289837540743 60522321303079934756311115)
              ·
                refine ⟨90783481954619902134466673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60522321303079934756311115 90783481954619902134466673)
                ·
                  refine ⟨68087611465964926600850005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 90783481954619902134466673 68087611465964926600850005)
                  ·
                    refine ⟨797901696866776483603711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 68087611465964926600850005 797901696866776483603711)
                    ·
                      rfl

theorem cell22_2330862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_2330862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2330862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2330862 prefixEnd_2330862 := by exact prefixLift 2330862
  have htrace : WordTrace (prefixWord ++ tailWord_2330862) baseStart_2330862 baseEnd_2330862 := by
    simpa [prefixWord, tailWord_2330862, baseEnd_2330862] using wordTrace_append hprefix tailTrace_2330862
  have hstable : (prefixWord ++ tailWord_2330862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2330862).length < 2 ^ (prefixWord ++ tailWord_2330862).sum := by decide
  have hdescent : baseEnd_2330862 < baseStart_2330862 := by decide
  rcases family_descends (prefixWord ++ tailWord_2330862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2330866 : List Nat := [3, 2, 1, 3, 2, 1, 4, 1, 5]
def baseStart_2330866 : Nat := 118140960795 + 2330866 * 2 ^ 59
def prefixEnd_2330866 : Nat := 4983230072969 + 3 ^ 40 * 2330866 * 2
def baseEnd_2330866 : Nat := 265967688716173935501233

theorem tailTrace_2330866 : CollatzResearch.WordTrace tailWord_2330866 prefixEnd_2330866 265967688716173935501233 := by
  unfold tailWord_2330866
  simp only [CollatzResearch.WordTrace]
  refine ⟨21253416793419509266281113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56675778115785358043416301 21253416793419509266281113)
  ·
    refine ⟨15940062595064631949710835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21253416793419509266281113 15940062595064631949710835)
    ·
      refine ⟨23910093892596947924566253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15940062595064631949710835 23910093892596947924566253)
      ·
        refine ⟨8966285209723855471712345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23910093892596947924566253 8966285209723855471712345)
        ·
          refine ⟨6724713907292891603784259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8966285209723855471712345 6724713907292891603784259)
          ·
            refine ⟨10087070860939337405676389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6724713907292891603784259 10087070860939337405676389)
            ·
              refine ⟨1891325786426125763564323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10087070860939337405676389 1891325786426125763564323)
              ·
                refine ⟨2836988679639188645346485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1891325786426125763564323 2836988679639188645346485)
                ·
                  refine ⟨265967688716173935501233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2836988679639188645346485 265967688716173935501233)
                  ·
                    rfl

theorem cell22_2330866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 4, 1, 5].length) (baseStart_2330866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2330866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2330866 prefixEnd_2330866 := by exact prefixLift 2330866
  have htrace : WordTrace (prefixWord ++ tailWord_2330866) baseStart_2330866 baseEnd_2330866 := by
    simpa [prefixWord, tailWord_2330866, baseEnd_2330866] using wordTrace_append hprefix tailTrace_2330866
  have hstable : (prefixWord ++ tailWord_2330866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2330866).length < 2 ^ (prefixWord ++ tailWord_2330866).sum := by decide
  have hdescent : baseEnd_2330866 < baseStart_2330866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2330866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2330877 : List Nat := [1, 4, 1, 1, 1, 1, 1, 6, 6]
def baseStart_2330877 : Nat := 118140960795 + 2330877 * 2 ^ 59
def prefixEnd_2330877 : Nat := 4983230072969 + 3 ^ 40 * 2330877 * 2
def baseEnd_2330877 : Nat := 265968943891107148159555

theorem tailTrace_2330877 : CollatzResearch.WordTrace tailWord_2330877 prefixEnd_2330877 265968943891107148159555 := by
  unfold tailWord_2330877
  simp only [CollatzResearch.WordTrace]
  refine ⟨85014068376638185943774885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56676045584425457295849923 85014068376638185943774885)
  ·
    refine ⟨15940137820619659864457791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85014068376638185943774885 15940137820619659864457791)
    ·
      refine ⟨23910206730929489796686687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15940137820619659864457791 23910206730929489796686687)
      ·
        refine ⟨35865310096394234695030031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23910206730929489796686687 35865310096394234695030031)
        ·
          refine ⟨53797965144591352042545047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35865310096394234695030031 53797965144591352042545047)
          ·
            refine ⟨80696947716887028063817571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53797965144591352042545047 80696947716887028063817571)
            ·
              refine ⟨121045421575330542095726357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80696947716887028063817571 121045421575330542095726357)
              ·
                refine ⟨5674004136343619160737173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 121045421575330542095726357 5674004136343619160737173)
                ·
                  refine ⟨265968943891107148159555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5674004136343619160737173 265968943891107148159555)
                  ·
                    rfl

theorem cell22_2330877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 6, 6].length) (baseStart_2330877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2330877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2330877 prefixEnd_2330877 := by exact prefixLift 2330877
  have htrace : WordTrace (prefixWord ++ tailWord_2330877) baseStart_2330877 baseEnd_2330877 := by
    simpa [prefixWord, tailWord_2330877, baseEnd_2330877] using wordTrace_append hprefix tailTrace_2330877
  have hstable : (prefixWord ++ tailWord_2330877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2330877).length < 2 ^ (prefixWord ++ tailWord_2330877).sum := by decide
  have hdescent : baseEnd_2330877 < baseStart_2330877 := by decide
  rcases family_descends (prefixWord ++ tailWord_2330877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2330911 : List Nat := [1, 1, 2, 4, 3, 2, 1, 4, 4]
def baseStart_2330911 : Nat := 118140960795 + 2330911 * 2 ^ 59
def prefixEnd_2330911 : Nat := 4983230072969 + 3 ^ 40 * 2330911 * 2
def baseEnd_2330911 : Nat := 265972823522718896376187

theorem tailTrace_2330911 : CollatzResearch.WordTrace tailWord_2330911 prefixEnd_2330911 265972823522718896376187 := by
  unfold tailWord_2330911
  simp only [CollatzResearch.WordTrace]
  refine ⟨85015308458515009750512587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56676872305676673167008391 85015308458515009750512587)
  ·
    refine ⟨127522962687772514625768881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85015308458515009750512587 127522962687772514625768881)
    ·
      refine ⟨95642222015829385969326661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127522962687772514625768881 95642222015829385969326661)
      ·
        refine ⟨17932916627968009869248749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 95642222015829385969326661 17932916627968009869248749)
        ·
          refine ⟨6724843735488003700968281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17932916627968009869248749 6724843735488003700968281)
          ·
            refine ⟨5043632801616002775726211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6724843735488003700968281 5043632801616002775726211)
            ·
              refine ⟨7565449202424004163589317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5043632801616002775726211 7565449202424004163589317)
              ·
                refine ⟨1418521725454500780672997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7565449202424004163589317 1418521725454500780672997)
                ·
                  refine ⟨265972823522718896376187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1418521725454500780672997 265972823522718896376187)
                  ·
                    rfl

theorem cell22_2330911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 4, 4].length) (baseStart_2330911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2330911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2330911 prefixEnd_2330911 := by exact prefixLift 2330911
  have htrace : WordTrace (prefixWord ++ tailWord_2330911) baseStart_2330911 baseEnd_2330911 := by
    simpa [prefixWord, tailWord_2330911, baseEnd_2330911] using wordTrace_append hprefix tailTrace_2330911
  have hstable : (prefixWord ++ tailWord_2330911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2330911).length < 2 ^ (prefixWord ++ tailWord_2330911).sum := by decide
  have hdescent : baseEnd_2330911 < baseStart_2330911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2330911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2331005 : List Nat := [1, 4, 1, 1, 2, 5, 1, 3, 1, 3]
def baseStart_2331005 : Nat := 118140960795 + 2331005 * 2 ^ 59
def prefixEnd_2331005 : Nat := 4983230072969 + 3 ^ 40 * 2331005 * 2
def baseEnd_2331005 : Nat := 797950648689171777278273

theorem tailTrace_2331005 : CollatzResearch.WordTrace tailWord_2331005 prefixEnd_2331005 797950648689171777278273 := by
  unfold tailWord_2331005
  simp only [CollatzResearch.WordTrace]
  refine ⟨85018736920174463804434469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56679157946782975869622979 85018736920174463804434469)
  ·
    refine ⟨15941013172532711963331463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85018736920174463804434469 15941013172532711963331463)
    ·
      refine ⟨23911519758799067944997195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15941013172532711963331463 23911519758799067944997195)
      ·
        refine ⟨35867279638198601917495793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23911519758799067944997195 35867279638198601917495793)
        ·
          refine ⟨26900459728648951438121845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35867279638198601917495793 26900459728648951438121845)
          ·
            refine ⟨2521918099560839197323923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26900459728648951438121845 2521918099560839197323923)
            ·
              refine ⟨3782877149341258795985885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2521918099560839197323923 3782877149341258795985885)
              ·
                refine ⟨1418578931002972048494707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3782877149341258795985885 1418578931002972048494707)
                ·
                  refine ⟨2127868396504458072742061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1418578931002972048494707 2127868396504458072742061)
                  ·
                    refine ⟨797950648689171777278273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2127868396504458072742061 797950648689171777278273)
                    ·
                      rfl

theorem cell22_2331005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 3, 1, 3].length) (baseStart_2331005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2331005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2331005 prefixEnd_2331005 := by exact prefixLift 2331005
  have htrace : WordTrace (prefixWord ++ tailWord_2331005) baseStart_2331005 baseEnd_2331005 := by
    simpa [prefixWord, tailWord_2331005, baseEnd_2331005] using wordTrace_append hprefix tailTrace_2331005
  have hstable : (prefixWord ++ tailWord_2331005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2331005).length < 2 ^ (prefixWord ++ tailWord_2331005).sum := by decide
  have hdescent : baseEnd_2331005 < baseStart_2331005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2331005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2331022 : List Nat := [4, 1, 1, 4, 1, 2, 3, 2, 1, 3]
def baseStart_2331022 : Nat := 118140960795 + 2331022 * 2 ^ 59
def prefixEnd_2331022 : Nat := 4983230072969 + 3 ^ 40 * 2331022 * 2
def baseEnd_2331022 : Nat := 797956468136589399603221

theorem tailTrace_2331022 : CollatzResearch.WordTrace tailWord_2331022 prefixEnd_2331022 797956468136589399603221 := by
  unfold tailWord_2331022
  simp only [CollatzResearch.WordTrace]
  refine ⟨10627419620139109463475415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56679571307408583805202213 10627419620139109463475415)
  ·
    refine ⟨15941129430208664195213123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10627419620139109463475415 15941129430208664195213123)
    ·
      refine ⟨23911694145312996292819685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15941129430208664195213123 23911694145312996292819685)
      ·
        refine ⟨4483442652246186804903691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23911694145312996292819685 4483442652246186804903691)
        ·
          refine ⟨6725163978369280207355537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4483442652246186804903691 6725163978369280207355537)
          ·
            refine ⟨5043872983776960155516653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6725163978369280207355537 5043872983776960155516653)
            ·
              refine ⟨1891452368916360058318745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5043872983776960155516653 1891452368916360058318745)
              ·
                refine ⟨1418589276687270043739059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1891452368916360058318745 1418589276687270043739059)
                ·
                  refine ⟨2127883915030905065608589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1418589276687270043739059 2127883915030905065608589)
                  ·
                    refine ⟨797956468136589399603221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2127883915030905065608589 797956468136589399603221)
                    ·
                      rfl

theorem cell22_2331022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 3, 2, 1, 3].length) (baseStart_2331022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2331022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2331022 prefixEnd_2331022 := by exact prefixLift 2331022
  have htrace : WordTrace (prefixWord ++ tailWord_2331022) baseStart_2331022 baseEnd_2331022 := by
    simpa [prefixWord, tailWord_2331022, baseEnd_2331022] using wordTrace_append hprefix tailTrace_2331022
  have hstable : (prefixWord ++ tailWord_2331022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2331022).length < 2 ^ (prefixWord ++ tailWord_2331022).sum := by decide
  have hdescent : baseEnd_2331022 < baseStart_2331022 := by decide
  rcases family_descends (prefixWord ++ tailWord_2331022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2331048 : List Nat := [2, 1, 6, 1, 1, 2, 1, 1, 3, 4]
def baseStart_2331048 : Nat := 118140960795 + 2331048 * 2 ^ 59
def prefixEnd_2331048 : Nat := 4983230072969 + 3 ^ 40 * 2331048 * 2
def baseEnd_2331048 : Nat := 797965368467933998453141

theorem tailTrace_2331048 : CollatzResearch.WordTrace tailWord_2331048 prefixEnd_2331048 797965368467933998453141 := by
  unfold tailWord_2331048
  simp only [CollatzResearch.WordTrace]
  refine ⟨42510152629509341074124899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56680203506012454765499865 42510152629509341074124899)
  ·
    refine ⟨63765228944264011611187349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42510152629509341074124899 63765228944264011611187349)
    ·
      refine ⟨2988995106762375544274407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 63765228944264011611187349 2988995106762375544274407)
      ·
        refine ⟨4483492660143563316411611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2988995106762375544274407 4483492660143563316411611)
        ·
          refine ⟨6725238990215344974617417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4483492660143563316411611 6725238990215344974617417)
          ·
            refine ⟨5043929242661508730963063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6725238990215344974617417 5043929242661508730963063)
            ·
              refine ⟨7565893863992263096444595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5043929242661508730963063 7565893863992263096444595)
              ·
                refine ⟨11348840795988394644666893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7565893863992263096444595 11348840795988394644666893)
                ·
                  refine ⟨4255815298495647991750085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11348840795988394644666893 4255815298495647991750085)
                  ·
                    refine ⟨797965368467933998453141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4255815298495647991750085 797965368467933998453141)
                    ·
                      rfl

theorem cell22_2331048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_2331048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2331048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2331048 prefixEnd_2331048 := by exact prefixLift 2331048
  have htrace : WordTrace (prefixWord ++ tailWord_2331048) baseStart_2331048 baseEnd_2331048 := by
    simpa [prefixWord, tailWord_2331048, baseEnd_2331048] using wordTrace_append hprefix tailTrace_2331048
  have hstable : (prefixWord ++ tailWord_2331048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2331048).length < 2 ^ (prefixWord ++ tailWord_2331048).sum := by decide
  have hdescent : baseEnd_2331048 < baseStart_2331048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2331048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2331073 : List Nat := [1, 2, 7, 1, 2, 1, 2, 2, 1, 3]
def baseStart_2331073 : Nat := 118140960795 + 2331073 * 2 ^ 59
def prefixEnd_2331073 : Nat := 4983230072969 + 3 ^ 40 * 2331073 * 2
def baseEnd_2331073 : Nat := 797973926478842266578065

theorem tailTrace_2331073 : CollatzResearch.WordTrace tailWord_2331073 prefixEnd_2331073 797973926478842266578065 := by
  unfold tailWord_2331073
  simp only [CollatzResearch.WordTrace]
  refine ⟨85021217083928111417909873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56680811389285407611939915 85021217083928111417909873)
  ·
    refine ⟨63765912812946083563432405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85021217083928111417909873 63765912812946083563432405)
    ·
      refine ⟨1494513581553423833517947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 63765912812946083563432405 1494513581553423833517947)
      ·
        refine ⟨2241770372330135750276921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1494513581553423833517947 2241770372330135750276921)
        ·
          refine ⟨1681327779247601812707691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2241770372330135750276921 1681327779247601812707691)
          ·
            refine ⟨2521991668871402719061537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1681327779247601812707691 2521991668871402719061537)
            ·
              refine ⟨1891493751653552039296153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2521991668871402719061537 1891493751653552039296153)
              ·
                refine ⟨1418620313740164029472115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1891493751653552039296153 1418620313740164029472115)
                ·
                  refine ⟨2127930470610246044208173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1418620313740164029472115 2127930470610246044208173)
                  ·
                    refine ⟨797973926478842266578065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2127930470610246044208173 797973926478842266578065)
                    ·
                      rfl

theorem cell22_2331073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_2331073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2331073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2331073 prefixEnd_2331073 := by exact prefixLift 2331073
  have htrace : WordTrace (prefixWord ++ tailWord_2331073) baseStart_2331073 baseEnd_2331073 := by
    simpa [prefixWord, tailWord_2331073, baseEnd_2331073] using wordTrace_append hprefix tailTrace_2331073
  have hstable : (prefixWord ++ tailWord_2331073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2331073).length < 2 ^ (prefixWord ++ tailWord_2331073).sum := by decide
  have hdescent : baseEnd_2331073 < baseStart_2331073 := by decide
  rcases family_descends (prefixWord ++ tailWord_2331073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2331080 : List Nat := [2, 1, 3, 1, 3, 4, 2, 2, 4]
def baseStart_2331080 : Nat := 118140960795 + 2331080 * 2 ^ 59
def prefixEnd_2331080 : Nat := 4983230072969 + 3 ^ 40 * 2331080 * 2
def baseEnd_2331080 : Nat := 265992107573965527217681

theorem tailTrace_2331080 : CollatzResearch.WordTrace tailWord_2331080 prefixEnd_2331080 265992107573965527217681 := by
  unfold tailWord_2331080
  simp only [CollatzResearch.WordTrace]
  refine ⟨42510736197451375806707347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56680981596601834408943129 42510736197451375806707347)
  ·
    refine ⟨63766104296177063710061021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42510736197451375806707347 63766104296177063710061021)
    ·
      refine ⟨23912289111066398891272883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63766104296177063710061021 23912289111066398891272883)
      ·
        refine ⟨35868433666599598336909325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23912289111066398891272883 35868433666599598336909325)
        ·
          refine ⟨13450662624974849376340997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35868433666599598336909325 13450662624974849376340997)
          ·
            refine ⟨2521999242182784258063937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13450662624974849376340997 2521999242182784258063937)
            ·
              refine ⟨1891499431637088193547953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2521999242182784258063937 1891499431637088193547953)
              ·
                refine ⟨1418624573727816145160965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1891499431637088193547953 1418624573727816145160965)
                ·
                  refine ⟨265992107573965527217681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1418624573727816145160965 265992107573965527217681)
                  ·
                    rfl

theorem cell22_2331080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 2, 2, 4].length) (baseStart_2331080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2331080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2331080 prefixEnd_2331080 := by exact prefixLift 2331080
  have htrace : WordTrace (prefixWord ++ tailWord_2331080) baseStart_2331080 baseEnd_2331080 := by
    simpa [prefixWord, tailWord_2331080, baseEnd_2331080] using wordTrace_append hprefix tailTrace_2331080
  have hstable : (prefixWord ++ tailWord_2331080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2331080).length < 2 ^ (prefixWord ++ tailWord_2331080).sum := by decide
  have hdescent : baseEnd_2331080 < baseStart_2331080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2331080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2331104 : List Nat := [2, 1, 1, 3, 1, 1, 3, 2, 2, 6]
def baseStart_2331104 : Nat := 118140960795 + 2331104 * 2 ^ 59
def prefixEnd_2331104 : Nat := 4983230072969 + 3 ^ 40 * 2331104 * 2
def baseEnd_2331104 : Nat := 797984538412368519052969

theorem tailTrace_2331104 : CollatzResearch.WordTrace tailWord_2331104 prefixEnd_2331104 797984538412368519052969 := by
  unfold tailWord_2331104
  simp only [CollatzResearch.WordTrace]
  refine ⟨42511173873407901856144183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56681565164543869141525577 42511173873407901856144183)
  ·
    refine ⟨63766760810111852784216275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42511173873407901856144183 63766760810111852784216275)
    ·
      refine ⟨95650141215167779176324413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63766760810111852784216275 95650141215167779176324413)
      ·
        refine ⟨35868802955687917191121655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95650141215167779176324413 35868802955687917191121655)
        ·
          refine ⟨53803204433531875786682483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35868802955687917191121655 53803204433531875786682483)
          ·
            refine ⟨80704806650297813680023725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53803204433531875786682483 80704806650297813680023725)
            ·
              refine ⟨30264302493861680130008897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80704806650297813680023725 30264302493861680130008897)
              ·
                refine ⟨22698226870396260097506673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30264302493861680130008897 22698226870396260097506673)
                ·
                  refine ⟨17023670152797195073130005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22698226870396260097506673 17023670152797195073130005)
                  ·
                    refine ⟨797984538412368519052969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17023670152797195073130005 797984538412368519052969)
                    ·
                      rfl

theorem cell22_2331104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 2, 6].length) (baseStart_2331104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2331104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2331104 prefixEnd_2331104 := by exact prefixLift 2331104
  have htrace : WordTrace (prefixWord ++ tailWord_2331104) baseStart_2331104 baseEnd_2331104 := by
    simpa [prefixWord, tailWord_2331104, baseEnd_2331104] using wordTrace_append hprefix tailTrace_2331104
  have hstable : (prefixWord ++ tailWord_2331104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2331104).length < 2 ^ (prefixWord ++ tailWord_2331104).sum := by decide
  have hdescent : baseEnd_2331104 < baseStart_2331104 := by decide
  rcases family_descends (prefixWord ++ tailWord_2331104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2331119 : List Nat := [1, 1, 2, 1, 4, 1, 1, 4, 7]
def baseStart_2331119 : Nat := 118140960795 + 2331119 * 2 ^ 59
def prefixEnd_2331119 : Nat := 4983230072969 + 3 ^ 40 * 2331119 * 2
def baseEnd_2331119 : Nat := 265996557739637826642641

theorem tailTrace_2331119 : CollatzResearch.WordTrace tailWord_2331119 prefixEnd_2331119 265996557739637826642641 := by
  unfold tailWord_2331119
  simp only [CollatzResearch.WordTrace]
  refine ⟨85022894841761461274084411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56681929894507640849389607 85022894841761461274084411)
  ·
    refine ⟨127534342262642191911126617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85022894841761461274084411 127534342262642191911126617)
    ·
      refine ⟨95650756696981643933344963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127534342262642191911126617 95650756696981643933344963)
      ·
        refine ⟨143476135045472465900017445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95650756696981643933344963 143476135045472465900017445)
        ·
          refine ⟨26901775321026087356253271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 143476135045472465900017445 26901775321026087356253271)
          ·
            refine ⟨40352662981539131034379907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26901775321026087356253271 40352662981539131034379907)
            ·
              refine ⟨60528994472308696551569861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40352662981539131034379907 60528994472308696551569861)
              ·
                refine ⟨11349186463557880603419349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60528994472308696551569861 11349186463557880603419349)
                ·
                  refine ⟨265996557739637826642641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11349186463557880603419349 265996557739637826642641)
                  ·
                    rfl

theorem cell22_2331119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 4, 7].length) (baseStart_2331119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2331119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2331119 prefixEnd_2331119 := by exact prefixLift 2331119
  have htrace : WordTrace (prefixWord ++ tailWord_2331119) baseStart_2331119 baseEnd_2331119 := by
    simpa [prefixWord, tailWord_2331119, baseEnd_2331119] using wordTrace_append hprefix tailTrace_2331119
  have hstable : (prefixWord ++ tailWord_2331119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2331119).length < 2 ^ (prefixWord ++ tailWord_2331119).sum := by decide
  have hdescent : baseEnd_2331119 < baseStart_2331119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2331119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2331140 : List Nat := [2, 3, 2, 3, 1, 2, 2, 1, 3, 3]
def baseStart_2331140 : Nat := 118140960795 + 2331140 * 2 ^ 59
def prefixEnd_2331140 : Nat := 4983230072969 + 3 ^ 40 * 2331140 * 2
def baseEnd_2331140 : Nat := 797996861948076425152859

theorem tailTrace_2331140 : CollatzResearch.WordTrace tailWord_2331140 prefixEnd_2331140 797996861948076425152859 := by
  unfold tailWord_2331140
  simp only [CollatzResearch.WordTrace]
  refine ⟨42511830387342690930299437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56682440516456921240399249 42511830387342690930299437)
  ·
    refine ⟨15941936395253509098862289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42511830387342690930299437 15941936395253509098862289)
    ·
      refine ⟨11956452296440131824146717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15941936395253509098862289 11956452296440131824146717)
      ·
        refine ⟨4483669611165049434055019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11956452296440131824146717 4483669611165049434055019)
        ·
          refine ⟨6725504416747574151082529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4483669611165049434055019 6725504416747574151082529)
          ·
            refine ⟨5044128312560680613311897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6725504416747574151082529 5044128312560680613311897)
            ·
              refine ⟨3783096234420510459983923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5044128312560680613311897 3783096234420510459983923)
              ·
                refine ⟨5674644351630765689975885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3783096234420510459983923 5674644351630765689975885)
                ·
                  refine ⟨2127991631861537133740957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5674644351630765689975885 2127991631861537133740957)
                  ·
                    refine ⟨797996861948076425152859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2127991631861537133740957 797996861948076425152859)
                    ·
                      rfl

theorem cell22_2331140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 1, 3, 3].length) (baseStart_2331140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2331140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2331140 prefixEnd_2331140 := by exact prefixLift 2331140
  have htrace : WordTrace (prefixWord ++ tailWord_2331140) baseStart_2331140 baseEnd_2331140 := by
    simpa [prefixWord, tailWord_2331140, baseEnd_2331140] using wordTrace_append hprefix tailTrace_2331140
  have hstable : (prefixWord ++ tailWord_2331140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2331140).length < 2 ^ (prefixWord ++ tailWord_2331140).sum := by decide
  have hdescent : baseEnd_2331140 < baseStart_2331140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2331140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2331234 : List Nat := [3, 3, 2, 3, 1, 1, 3, 1, 1, 4]
def baseStart_2331234 : Nat := 118140960795 + 2331234 * 2 ^ 59
def prefixEnd_2331234 : Nat := 4983230072969 + 3 ^ 40 * 2331234 * 2
def baseEnd_2331234 : Nat := 798029040069091513302571

theorem tailTrace_2331234 : CollatzResearch.WordTrace tailWord_2331234 prefixEnd_2331234 798029040069091513302571 := by
  unfold tailWord_2331234
  simp only [CollatzResearch.WordTrace]
  refine ⟨21256772309086208978630189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56684726157563223943013837 21256772309086208978630189)
  ·
    refine ⟨7971289615907328366986321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21256772309086208978630189 7971289615907328366986321)
    ·
      refine ⟨5978467211930496275239741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7971289615907328366986321 5978467211930496275239741)
      ·
        refine ⟨2241925204473936103214903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5978467211930496275239741 2241925204473936103214903)
        ·
          refine ⟨3362887806710904154822355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2241925204473936103214903 3362887806710904154822355)
          ·
            refine ⟨5044331710066356232233533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3362887806710904154822355 5044331710066356232233533)
            ·
              refine ⟨1891624391274883587087575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5044331710066356232233533 1891624391274883587087575)
              ·
                refine ⟨2837436586912325380631363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1891624391274883587087575 2837436586912325380631363)
                ·
                  refine ⟨4256154880368488070947045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2837436586912325380631363 4256154880368488070947045)
                  ·
                    refine ⟨798029040069091513302571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4256154880368488070947045 798029040069091513302571)
                    ·
                      rfl

theorem cell22_2331234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_2331234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2331234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2331234 prefixEnd_2331234 := by exact prefixLift 2331234
  have htrace : WordTrace (prefixWord ++ tailWord_2331234) baseStart_2331234 baseEnd_2331234 := by
    simpa [prefixWord, tailWord_2331234, baseEnd_2331234] using wordTrace_append hprefix tailTrace_2331234
  have hstable : (prefixWord ++ tailWord_2331234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2331234).length < 2 ^ (prefixWord ++ tailWord_2331234).sum := by decide
  have hdescent : baseEnd_2331234 < baseStart_2331234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2331234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2331292 : List Nat := [2, 2, 3, 2, 2, 1, 1, 5, 1, 3]
def baseStart_2331292 : Nat := 118140960795 + 2331292 * 2 ^ 59
def prefixEnd_2331292 : Nat := 4983230072969 + 3 ^ 40 * 2331292 * 2
def baseEnd_2331292 : Nat := 798048894654398695352393

theorem tailTrace_2331292 : CollatzResearch.WordTrace tailWord_2331292 prefixEnd_2331292 798048894654398695352393 := by
  unfold tailWord_2331292
  simp only [CollatzResearch.WordTrace]
  refine ⟨42514602335067355910066065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56686136446756474546754753 42514602335067355910066065)
  ·
    refine ⟨31885951751300516932549549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42514602335067355910066065 31885951751300516932549549)
    ·
      refine ⟨11957231906737693849706081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31885951751300516932549549 11957231906737693849706081)
      ·
        refine ⟨8967923930053270387279561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11957231906737693849706081 8967923930053270387279561)
        ·
          refine ⟨6725942947539952790459671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8967923930053270387279561 6725942947539952790459671)
          ·
            refine ⟨10088914421309929185689507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6725942947539952790459671 10088914421309929185689507)
            ·
              refine ⟨15133371631964893778534261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10088914421309929185689507 15133371631964893778534261)
              ·
                refine ⟨1418753590496708791737587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15133371631964893778534261 1418753590496708791737587)
                ·
                  refine ⟨2128130385745063187606381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1418753590496708791737587 2128130385745063187606381)
                  ·
                    refine ⟨798048894654398695352393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2128130385745063187606381 798048894654398695352393)
                    ·
                      rfl

theorem cell22_2331292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 5, 1, 3].length) (baseStart_2331292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2331292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2331292 prefixEnd_2331292 := by exact prefixLift 2331292
  have htrace : WordTrace (prefixWord ++ tailWord_2331292) baseStart_2331292 baseEnd_2331292 := by
    simpa [prefixWord, tailWord_2331292, baseEnd_2331292] using wordTrace_append hprefix tailTrace_2331292
  have hstable : (prefixWord ++ tailWord_2331292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2331292).length < 2 ^ (prefixWord ++ tailWord_2331292).sum := by decide
  have hdescent : baseEnd_2331292 < baseStart_2331292 := by decide
  rcases family_descends (prefixWord ++ tailWord_2331292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2331365 : List Nat := [1, 3, 1, 4, 1, 2, 2, 1, 4, 3]
def baseStart_2331365 : Nat := 118140960795 + 2331365 * 2 ^ 59
def prefixEnd_2331365 : Nat := 4983230072969 + 3 ^ 40 * 2331365 * 2
def baseEnd_2331365 : Nat := 798073884046250838277169

theorem tailTrace_2331365 : CollatzResearch.WordTrace tailWord_2331365 prefixEnd_2331365 798073884046250838277169 := by
  unfold tailWord_2331365
  simp only [CollatzResearch.WordTrace]
  refine ⟨85031867198870245287539549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56687911465913496858359699 85031867198870245287539549)
  ·
    refine ⟨31886950199576341982827331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85031867198870245287539549 31886950199576341982827331)
    ·
      refine ⟨47830425299364512974240997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31886950199576341982827331 47830425299364512974240997)
      ·
        refine ⟨8968204743630846182670187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47830425299364512974240997 8968204743630846182670187)
        ·
          refine ⟨13452307115446269274005281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8968204743630846182670187 13452307115446269274005281)
          ·
            refine ⟨10089230336584701955503961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13452307115446269274005281 10089230336584701955503961)
            ·
              refine ⟨7566922752438526466627971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10089230336584701955503961 7566922752438526466627971)
              ·
                refine ⟨11350384128657789699941957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7566922752438526466627971 11350384128657789699941957)
                ·
                  refine ⟨2128197024123335568739117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11350384128657789699941957 2128197024123335568739117)
                  ·
                    refine ⟨798073884046250838277169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2128197024123335568739117 798073884046250838277169)
                    ·
                      rfl

theorem cell22_2331365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 1, 4, 3].length) (baseStart_2331365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2331365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2331365 prefixEnd_2331365 := by exact prefixLift 2331365
  have htrace : WordTrace (prefixWord ++ tailWord_2331365) baseStart_2331365 baseEnd_2331365 := by
    simpa [prefixWord, tailWord_2331365, baseEnd_2331365] using wordTrace_append hprefix tailTrace_2331365
  have hstable : (prefixWord ++ tailWord_2331365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2331365).length < 2 ^ (prefixWord ++ tailWord_2331365).sum := by decide
  have hdescent : baseEnd_2331365 < baseStart_2331365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2331365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2331378 : List Nat := [3, 2, 1, 3, 1, 2, 1, 9]
def baseStart_2331378 : Nat := 118140960795 + 2331378 * 2 ^ 59
def prefixEnd_2331378 : Nat := 4983230072969 + 3 ^ 40 * 2331378 * 2
def baseEnd_2331378 : Nat := 88675370467991459744681

theorem tailTrace_2331378 : CollatzResearch.WordTrace tailWord_2331378 prefixEnd_2331378 88675370467991459744681 := by
  unfold tailWord_2331378
  simp only [CollatzResearch.WordTrace]
  refine ⟨21258085336955787126940697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56688227565215432338508525 21258085336955787126940697)
  ·
    refine ⟨15943564002716840345205523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21258085336955787126940697 15943564002716840345205523)
    ·
      refine ⟨23915346004075260517808285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15943564002716840345205523 23915346004075260517808285)
      ·
        refine ⟨8968254751528222694178107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23915346004075260517808285 8968254751528222694178107)
        ·
          refine ⟨13452382127292334041267161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8968254751528222694178107 13452382127292334041267161)
          ·
            refine ⟨10089286595469250530950371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13452382127292334041267161 10089286595469250530950371)
            ·
              refine ⟨15133929893203875796425557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10089286595469250530950371 15133929893203875796425557)
              ·
                refine ⟨88675370467991459744681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15133929893203875796425557 88675370467991459744681)
                ·
                  rfl

theorem cell22_2331378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 9].length) (baseStart_2331378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2331378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2331378 prefixEnd_2331378 := by exact prefixLift 2331378
  have htrace : WordTrace (prefixWord ++ tailWord_2331378) baseStart_2331378 baseEnd_2331378 := by
    simpa [prefixWord, tailWord_2331378, baseEnd_2331378] using wordTrace_append hprefix tailTrace_2331378
  have hstable : (prefixWord ++ tailWord_2331378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2331378).length < 2 ^ (prefixWord ++ tailWord_2331378).sum := by decide
  have hdescent : baseEnd_2331378 < baseStart_2331378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2331378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2331382 : List Nat := [5, 1, 1, 1, 1, 2, 3, 3, 2, 3]
def baseStart_2331382 : Nat := 118140960795 + 2331382 * 2 ^ 59
def prefixEnd_2331382 : Nat := 4983230072969 + 3 ^ 40 * 2331382 * 2
def baseEnd_2331382 : Nat := 798079703493668460602117

theorem tailTrace_2331382 : CollatzResearch.WordTrace tailWord_2331382 prefixEnd_2331382 798079703493668460602117 := by
  unfold tailWord_2331382
  simp only [CollatzResearch.WordTrace]
  refine ⟨5314530452488041074431775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 56688324826539104793938933 5314530452488041074431775)
  ·
    refine ⟨7971795678732061611647663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5314530452488041074431775 7971795678732061611647663)
    ·
      refine ⟨11957693518098092417471495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7971795678732061611647663 11957693518098092417471495)
      ·
        refine ⟨17936540277147138626207243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11957693518098092417471495 17936540277147138626207243)
        ·
          refine ⟨26904810415720707939310865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17936540277147138626207243 26904810415720707939310865)
          ·
            refine ⟨20178607811790530954483149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26904810415720707939310865 20178607811790530954483149)
            ·
              refine ⟨7566977929421449107931181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20178607811790530954483149 7566977929421449107931181)
              ·
                refine ⟨2837616723533043415474193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7566977929421449107931181 2837616723533043415474193)
                ·
                  refine ⟨2128212542649782561605645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2837616723533043415474193 2128212542649782561605645)
                  ·
                    refine ⟨798079703493668460602117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2128212542649782561605645 798079703493668460602117)
                    ·
                      rfl

theorem cell22_2331382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 3, 2, 3].length) (baseStart_2331382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2331382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2331382 prefixEnd_2331382 := by exact prefixLift 2331382
  have htrace : WordTrace (prefixWord ++ tailWord_2331382) baseStart_2331382 baseEnd_2331382 := by
    simpa [prefixWord, tailWord_2331382, baseEnd_2331382] using wordTrace_append hprefix tailTrace_2331382
  have hstable : (prefixWord ++ tailWord_2331382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2331382).length < 2 ^ (prefixWord ++ tailWord_2331382).sum := by decide
  have hdescent : baseEnd_2331382 < baseStart_2331382 := by decide
  rcases family_descends (prefixWord ++ tailWord_2331382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2331444 : List Nat := [2, 5, 1, 1, 3, 1, 1, 2, 3, 3]
def baseStart_2331444 : Nat := 118140960795 + 2331444 * 2 ^ 59
def prefixEnd_2331444 : Nat := 4983230072969 + 3 ^ 40 * 2331444 * 2
def baseEnd_2331444 : Nat := 798100927360720965551927

theorem tailTrace_2331444 : CollatzResearch.WordTrace tailWord_2331444 prefixEnd_2331444 798100927360720965551927 := by
  unfold tailWord_2331444
  simp only [CollatzResearch.WordTrace]
  refine ⟨42517374282792020889832693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56689832377056027853110257 42517374282792020889832693)
  ·
    refine ⟨3986003839011751958421815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 42517374282792020889832693 3986003839011751958421815)
    ·
      refine ⟨5979005758517627937632723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3986003839011751958421815 5979005758517627937632723)
      ·
        refine ⟨8968508637776441906449085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5979005758517627937632723 8968508637776441906449085)
        ·
          refine ⟨3363190739166165714918407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8968508637776441906449085 3363190739166165714918407)
          ·
            refine ⟨5044786108749248572377611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3363190739166165714918407 5044786108749248572377611)
            ·
              refine ⟨7567179163123872858566417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5044786108749248572377611 7567179163123872858566417)
              ·
                refine ⟨5675384372342904643924813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7567179163123872858566417 5675384372342904643924813)
                ·
                  refine ⟨2128269139628589241471805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5675384372342904643924813 2128269139628589241471805)
                  ·
                    refine ⟨798100927360720965551927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2128269139628589241471805 798100927360720965551927)
                    ·
                      rfl

theorem cell22_2331444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_2331444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2331444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2331444 prefixEnd_2331444 := by exact prefixLift 2331444
  have htrace : WordTrace (prefixWord ++ tailWord_2331444) baseStart_2331444 baseEnd_2331444 := by
    simpa [prefixWord, tailWord_2331444, baseEnd_2331444] using wordTrace_append hprefix tailTrace_2331444
  have hstable : (prefixWord ++ tailWord_2331444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2331444).length < 2 ^ (prefixWord ++ tailWord_2331444).sum := by decide
  have hdescent : baseEnd_2331444 < baseStart_2331444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2331444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2331530 : List Nat := [3, 1, 2, 4, 1, 1, 10]
def baseStart_2331530 : Nat := 118140960795 + 2331530 * 2 ^ 59
def prefixEnd_2331530 : Nat := 4983230072969 + 3 ^ 40 * 2331530 * 2
def baseEnd_2331530 : Nat := 29560383959935015107469

theorem tailTrace_2331530 : CollatzResearch.WordTrace tailWord_2331530 prefixEnd_2331530 29560383959935015107469 := by
  unfold tailWord_2331530
  simp only [CollatzResearch.WordTrace]
  refine ⟨21259471310818119616824011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56691923495514985644864029 21259471310818119616824011)
  ·
    refine ⟨31889206966227179425236017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21259471310818119616824011 31889206966227179425236017)
    ·
      refine ⟨23916905224670384568927013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31889206966227179425236017 23916905224670384568927013)
      ·
        refine ⟨4484419729625697106673815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23916905224670384568927013 4484419729625697106673815)
        ·
          refine ⟨6726629594438545660010723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4484419729625697106673815 6726629594438545660010723)
          ·
            refine ⟨10089944391657818490016085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6726629594438545660010723 10089944391657818490016085)
            ·
              refine ⟨29560383959935015107469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10089944391657818490016085 29560383959935015107469)
              ·
                rfl

theorem cell22_2331530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 10].length) (baseStart_2331530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2331530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2331530 prefixEnd_2331530 := by exact prefixLift 2331530
  have htrace : WordTrace (prefixWord ++ tailWord_2331530) baseStart_2331530 baseEnd_2331530 := by
    simpa [prefixWord, tailWord_2331530, baseEnd_2331530] using wordTrace_append hprefix tailTrace_2331530
  have hstable : (prefixWord ++ tailWord_2331530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2331530).length < 2 ^ (prefixWord ++ tailWord_2331530).sum := by decide
  have hdescent : baseEnd_2331530 < baseStart_2331530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2331530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2331551 : List Nat := [1, 1, 2, 5, 2, 3, 2, 1, 2, 3]
def baseStart_2331551 : Nat := 118140960795 + 2331551 * 2 ^ 59
def prefixEnd_2331551 : Nat := 4983230072969 + 3 ^ 40 * 2331551 * 2
def baseEnd_2331551 : Nat := 798137555647408353126599

theorem tailTrace_2331551 : CollatzResearch.WordTrace tailWord_2331551 prefixEnd_2331551 798137555647408353126599 := by
  unfold tailWord_2331551
  simp only [CollatzResearch.WordTrace]
  refine ⟨85038651176196399053810507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56692434117464266035873671 85038651176196399053810507)
  ·
    refine ⟨127557976764294598580715761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85038651176196399053810507 127557976764294598580715761)
    ·
      refine ⟨95668482573220948935536821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127557976764294598580715761 95668482573220948935536821)
      ·
        refine ⟨8968920241239463962706577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 95668482573220948935536821 8968920241239463962706577)
        ·
          refine ⟨6726690180929597972029933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8968920241239463962706577 6726690180929597972029933)
          ·
            refine ⟨2522508817848599239511225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6726690180929597972029933 2522508817848599239511225)
            ·
              refine ⟨1891881613386449429633419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2522508817848599239511225 1891881613386449429633419)
              ·
                refine ⟨2837822420079674144450129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1891881613386449429633419 2837822420079674144450129)
                ·
                  refine ⟨2128366815059755608337597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2837822420079674144450129 2128366815059755608337597)
                  ·
                    refine ⟨798137555647408353126599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2128366815059755608337597 798137555647408353126599)
                    ·
                      rfl

theorem cell22_2331551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 2, 1, 2, 3].length) (baseStart_2331551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2331551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2331551 prefixEnd_2331551 := by exact prefixLift 2331551
  have htrace : WordTrace (prefixWord ++ tailWord_2331551) baseStart_2331551 baseEnd_2331551 := by
    simpa [prefixWord, tailWord_2331551, baseEnd_2331551] using wordTrace_append hprefix tailTrace_2331551
  have hstable : (prefixWord ++ tailWord_2331551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2331551).length < 2 ^ (prefixWord ++ tailWord_2331551).sum := by decide
  have hdescent : baseEnd_2331551 < baseStart_2331551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2331551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2331669 : List Nat := [1, 3, 2, 1, 4, 3, 1, 1, 1, 5]
def baseStart_2331669 : Nat := 118140960795 + 2331669 * 2 ^ 59
def prefixEnd_2331669 : Nat := 4983230072969 + 3 ^ 40 * 2331669 * 2
def baseEnd_2331669 : Nat := 798177949458895378676237

theorem tailTrace_2331669 : CollatzResearch.WordTrace tailWord_2331669 prefixEnd_2331669 798177949458895378676237 := by
  unfold tailWord_2331669
  simp only [CollatzResearch.WordTrace]
  refine ⟨85042954989768905206606061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56695303326512603471070707 85042954989768905206606061)
  ·
    refine ⟨31891108121163339452477273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85042954989768905206606061 31891108121163339452477273)
    ·
      refine ⟨23918331090872504589357955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31891108121163339452477273 23918331090872504589357955)
      ·
        refine ⟨35877496636308756884036933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23918331090872504589357955 35877496636308756884036933)
        ·
          refine ⟨6727030619307891915756925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35877496636308756884036933 6727030619307891915756925)
          ·
            refine ⟨2522636482240459468408847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6727030619307891915756925 2522636482240459468408847)
            ·
              refine ⟨3783954723360689202613271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2522636482240459468408847 3783954723360689202613271)
              ·
                refine ⟨5675932085041033803919907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3783954723360689202613271 5675932085041033803919907)
                ·
                  refine ⟨8513898127561550705879861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5675932085041033803919907 8513898127561550705879861)
                  ·
                    refine ⟨798177949458895378676237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8513898127561550705879861 798177949458895378676237)
                    ·
                      rfl

theorem cell22_2331669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 1, 1, 5].length) (baseStart_2331669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2331669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2331669 prefixEnd_2331669 := by exact prefixLift 2331669
  have htrace : WordTrace (prefixWord ++ tailWord_2331669) baseStart_2331669 baseEnd_2331669 := by
    simpa [prefixWord, tailWord_2331669, baseEnd_2331669] using wordTrace_append hprefix tailTrace_2331669
  have hstable : (prefixWord ++ tailWord_2331669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2331669).length < 2 ^ (prefixWord ++ tailWord_2331669).sum := by decide
  have hdescent : baseEnd_2331669 < baseStart_2331669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2331669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2331682 : List Nat := [3, 3, 1, 1, 1, 4, 1, 8]
def baseStart_2331682 : Nat := 118140960795 + 2331682 * 2 ^ 59
def prefixEnd_2331682 : Nat := 4983230072969 + 3 ^ 40 * 2331682 * 2
def baseEnd_2331682 : Nat := 88686933291618630900133

theorem tailTrace_2331682 : CollatzResearch.WordTrace tailWord_2331682 prefixEnd_2331682 88686933291618630900133 := by
  unfold tailWord_2331682
  simp only [CollatzResearch.WordTrace]
  refine ⟨21260857284680452106707325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56695619425814538951219533 21260857284680452106707325)
  ·
    refine ⟨7972821481755169540015247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21260857284680452106707325 7972821481755169540015247)
    ·
      refine ⟨11959232222632754310022871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7972821481755169540015247 11959232222632754310022871)
      ·
        refine ⟨17938848333949131465034307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11959232222632754310022871 17938848333949131465034307)
        ·
          refine ⟨26908272500923697197551461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17938848333949131465034307 26908272500923697197551461)
          ·
            refine ⟨5045301093923193224540899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26908272500923697197551461 5045301093923193224540899)
            ·
              refine ⟨7567951640884789836811349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5045301093923193224540899 7567951640884789836811349)
              ·
                refine ⟨88686933291618630900133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7567951640884789836811349 88686933291618630900133)
                ·
                  rfl

theorem cell22_2331682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 8].length) (baseStart_2331682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2331682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2331682 prefixEnd_2331682 := by exact prefixLift 2331682
  have htrace : WordTrace (prefixWord ++ tailWord_2331682) baseStart_2331682 baseEnd_2331682 := by
    simpa [prefixWord, tailWord_2331682, baseEnd_2331682] using wordTrace_append hprefix tailTrace_2331682
  have hstable : (prefixWord ++ tailWord_2331682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2331682).length < 2 ^ (prefixWord ++ tailWord_2331682).sum := by decide
  have hdescent : baseEnd_2331682 < baseStart_2331682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2331682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2331765 : List Nat := [1, 3, 4, 3, 1, 1, 1, 4, 1, 3]
def baseStart_2331765 : Nat := 118140960795 + 2331765 * 2 ^ 59
def prefixEnd_2331765 : Nat := 4983230072969 + 3 ^ 40 * 2331765 * 2
def baseEnd_2331765 : Nat := 798210812220783128275943

theorem tailTrace_2331765 : CollatzResearch.WordTrace tailWord_2331765 prefixEnd_2331765 798210812220783128275943 := by
  unfold tailWord_2331765
  simp only [CollatzResearch.WordTrace]
  refine ⟨85046456397421113602100749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56697637598280742401400499 85046456397421113602100749)
  ·
    refine ⟨31892421149032917600787781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85046456397421113602100749 31892421149032917600787781)
    ·
      refine ⟨5979828965443672050147709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31892421149032917600787781 5979828965443672050147709)
      ·
        refine ⟨2242435862041377018805391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5979828965443672050147709 2242435862041377018805391)
        ·
          refine ⟨3363653793062065528208087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2242435862041377018805391 3363653793062065528208087)
          ·
            refine ⟨5045480689593098292312131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3363653793062065528208087 5045480689593098292312131)
            ·
              refine ⟨7568221034389647438468197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5045480689593098292312131 7568221034389647438468197)
              ·
                refine ⟨1419041443948058894712787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7568221034389647438468197 1419041443948058894712787)
                ·
                  refine ⟨2128562165922088342069181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1419041443948058894712787 2128562165922088342069181)
                  ·
                    refine ⟨798210812220783128275943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2128562165922088342069181 798210812220783128275943)
                    ·
                      rfl

theorem cell22_2331765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_2331765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2331765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2331765 prefixEnd_2331765 := by exact prefixLift 2331765
  have htrace : WordTrace (prefixWord ++ tailWord_2331765) baseStart_2331765 baseEnd_2331765 := by
    simpa [prefixWord, tailWord_2331765, baseEnd_2331765] using wordTrace_append hprefix tailTrace_2331765
  have hstable : (prefixWord ++ tailWord_2331765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2331765).length < 2 ^ (prefixWord ++ tailWord_2331765).sum := by decide
  have hdescent : baseEnd_2331765 < baseStart_2331765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2331765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2331772 : List Nat := [2, 2, 2, 1, 1, 3, 2, 3, 6]
def baseStart_2331772 : Nat := 118140960795 + 2331772 * 2 ^ 59
def prefixEnd_2331772 : Nat := 4983230072969 + 3 ^ 40 * 2331772 * 2
def baseEnd_2331772 : Nat := 266071069487945814450307

theorem tailTrace_2331772 : CollatzResearch.WordTrace tailWord_2331772 prefixEnd_2331772 266071069487945814450307 := by
  unfold tailWord_2331772
  simp only [CollatzResearch.WordTrace]
  refine ⟨42523355854197876898802785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56697807805597169198403713 42523355854197876898802785)
  ·
    refine ⟨31892516890648407674102089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42523355854197876898802785 31892516890648407674102089)
    ·
      refine ⟨23919387667986305755576567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31892516890648407674102089 23919387667986305755576567)
      ·
        refine ⟨35879081501979458633364851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23919387667986305755576567 35879081501979458633364851)
        ·
          refine ⟨53818622252969187950047277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35879081501979458633364851 53818622252969187950047277)
          ·
            refine ⟨20181983344863445481267729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53818622252969187950047277 20181983344863445481267729)
            ·
              refine ⟨15136487508647584110950797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20181983344863445481267729 15136487508647584110950797)
              ·
                refine ⟨5676182815742844041606549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15136487508647584110950797 5676182815742844041606549)
                ·
                  refine ⟨266071069487945814450307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5676182815742844041606549 266071069487945814450307)
                  ·
                    rfl

theorem cell22_2331772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 3, 6].length) (baseStart_2331772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2331772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2331772 prefixEnd_2331772 := by exact prefixLift 2331772
  have htrace : WordTrace (prefixWord ++ tailWord_2331772) baseStart_2331772 baseEnd_2331772 := by
    simpa [prefixWord, tailWord_2331772, baseEnd_2331772] using wordTrace_append hprefix tailTrace_2331772
  have hstable : (prefixWord ++ tailWord_2331772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2331772).length < 2 ^ (prefixWord ++ tailWord_2331772).sum := by decide
  have hdescent : baseEnd_2331772 < baseStart_2331772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2331772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2331804 : List Nat := [2, 2, 3, 2, 1, 2, 2, 2, 1, 5]
def baseStart_2331804 : Nat := 118140960795 + 2331804 * 2 ^ 59
def prefixEnd_2331804 : Nat := 4983230072969 + 3 ^ 40 * 2331804 * 2
def baseEnd_2331804 : Nat := 798224162717800026550823

theorem tailTrace_2331804 : CollatzResearch.WordTrace tailWord_2331804 prefixEnd_2331804 798224162717800026550823 := by
  unfold tailWord_2331804
  simp only [CollatzResearch.WordTrace]
  refine ⟨42523939422139911631385233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56698585896186548841846977 42523939422139911631385233)
  ·
    refine ⟨31892954566604933723538925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42523939422139911631385233 31892954566604933723538925)
    ·
      refine ⟨11959857962476850146327097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31892954566604933723538925 11959857962476850146327097)
      ·
        refine ⟨8969893471857637609745323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11959857962476850146327097 8969893471857637609745323)
        ·
          refine ⟨13454840207786456414617985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8969893471857637609745323 13454840207786456414617985)
          ·
            refine ⟨10091130155839842310963489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13454840207786456414617985 10091130155839842310963489)
            ·
              refine ⟨7568347616879881733222617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10091130155839842310963489 7568347616879881733222617)
              ·
                refine ⟨5676260712659911299916963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7568347616879881733222617 5676260712659911299916963)
                ·
                  refine ⟨8514391068989866949875445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5676260712659911299916963 8514391068989866949875445)
                  ·
                    refine ⟨798224162717800026550823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8514391068989866949875445 798224162717800026550823)
                    ·
                      rfl

theorem cell22_2331804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_2331804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2331804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2331804 prefixEnd_2331804 := by exact prefixLift 2331804
  have htrace : WordTrace (prefixWord ++ tailWord_2331804) baseStart_2331804 baseEnd_2331804 := by
    simpa [prefixWord, tailWord_2331804, baseEnd_2331804] using wordTrace_append hprefix tailTrace_2331804
  have hstable : (prefixWord ++ tailWord_2331804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2331804).length < 2 ^ (prefixWord ++ tailWord_2331804).sum := by decide
  have hdescent : baseEnd_2331804 < baseStart_2331804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2331804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2331847 : List Nat := [1, 1, 4, 1, 1, 1, 1, 4, 2, 6]
def baseStart_2331847 : Nat := 118140960795 + 2331847 * 2 ^ 59
def prefixEnd_2331847 : Nat := 4983230072969 + 3 ^ 40 * 2331847 * 2
def baseEnd_2331847 : Nat := 798238882496562247725691

theorem tailTrace_2331847 : CollatzResearch.WordTrace tailWord_2331847 prefixEnd_2331847 798238882496562247725691 := by
  unfold tailWord_2331847
  simp only [CollatzResearch.WordTrace]
  refine ⟨85049447183124041606585795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56699631455416027737723863 85049447183124041606585795)
  ·
    refine ⟨127574170774686062409878693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85049447183124041606585795 127574170774686062409878693)
    ·
      refine ⟨23920157020253636701852255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 127574170774686062409878693 23920157020253636701852255)
      ·
        refine ⟨35880235530380455052778383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23920157020253636701852255 35880235530380455052778383)
        ·
          refine ⟨53820353295570682579167575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35880235530380455052778383 53820353295570682579167575)
          ·
            refine ⟨80730529943356023868751363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53820353295570682579167575 80730529943356023868751363)
            ·
              refine ⟨121095794915034035803127045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80730529943356023868751363 121095794915034035803127045)
              ·
                refine ⟨22705461546568881713086321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 121095794915034035803127045 22705461546568881713086321)
                ·
                  refine ⟨17029096159926661284814741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22705461546568881713086321 17029096159926661284814741)
                  ·
                    refine ⟨798238882496562247725691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17029096159926661284814741 798238882496562247725691)
                    ·
                      rfl

theorem cell22_2331847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 2, 6].length) (baseStart_2331847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2331847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2331847 prefixEnd_2331847 := by exact prefixLift 2331847
  have htrace : WordTrace (prefixWord ++ tailWord_2331847) baseStart_2331847 baseEnd_2331847 := by
    simpa [prefixWord, tailWord_2331847, baseEnd_2331847] using wordTrace_append hprefix tailTrace_2331847
  have hstable : (prefixWord ++ tailWord_2331847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2331847).length < 2 ^ (prefixWord ++ tailWord_2331847).sum := by decide
  have hdescent : baseEnd_2331847 < baseStart_2331847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2331847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2331894 : List Nat := [5, 1, 1, 1, 1, 1, 1, 3, 1, 7]
def baseStart_2331894 : Nat := 118140960795 + 2331894 * 2 ^ 59
def prefixEnd_2331894 : Nat := 4983230072969 + 3 ^ 40 * 2331894 * 2
def baseEnd_2331894 : Nat := 798254971557069791800547

theorem tailTrace_2331894 : CollatzResearch.WordTrace tailWord_2331894 prefixEnd_2331894 798254971557069791800547 := by
  unfold tailWord_2331894
  simp only [CollatzResearch.WordTrace]
  refine ⟨5315697588372110539596671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 56700774275969179089031157 5315697588372110539596671)
  ·
    refine ⟨7973546382558165809395007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5315697588372110539596671 7973546382558165809395007)
    ·
      refine ⟨11960319573837248714092511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7973546382558165809395007 11960319573837248714092511)
      ·
        refine ⟨17940479360755873071138767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11960319573837248714092511 17940479360755873071138767)
        ·
          refine ⟨26910719041133809606708151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17940479360755873071138767 26910719041133809606708151)
          ·
            refine ⟨40366078561700714410062227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26910719041133809606708151 40366078561700714410062227)
            ·
              refine ⟨60549117842551071615093341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40366078561700714410062227 60549117842551071615093341)
              ·
                refine ⟨22705919190956651855660003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60549117842551071615093341 22705919190956651855660003)
                ·
                  refine ⟨34058878786434977783490005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22705919190956651855660003 34058878786434977783490005)
                  ·
                    refine ⟨798254971557069791800547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34058878786434977783490005 798254971557069791800547)
                    ·
                      rfl

theorem cell22_2331894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_2331894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2331894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2331894 prefixEnd_2331894 := by exact prefixLift 2331894
  have htrace : WordTrace (prefixWord ++ tailWord_2331894) baseStart_2331894 baseEnd_2331894 := by
    simpa [prefixWord, tailWord_2331894, baseEnd_2331894] using wordTrace_append hprefix tailTrace_2331894
  have hstable : (prefixWord ++ tailWord_2331894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2331894).length < 2 ^ (prefixWord ++ tailWord_2331894).sum := by decide
  have hdescent : baseEnd_2331894 < baseStart_2331894 := by decide
  rcases family_descends (prefixWord ++ tailWord_2331894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2331909 : List Nat := [1, 3, 1, 1, 2, 1, 5, 1, 3, 4]
def baseStart_2331909 : Nat := 118140960795 + 2331909 * 2 ^ 59
def prefixEnd_2331909 : Nat := 4983230072969 + 3 ^ 40 * 2331909 * 2
def baseEnd_2331909 : Nat := 798260106363614752675501

theorem tailTrace_2331909 : CollatzResearch.WordTrace tailWord_2331909 prefixEnd_2331909 798260106363614752675501 := by
  unfold tailWord_2331909
  simp only [CollatzResearch.WordTrace]
  refine ⟨85051708508899426195342781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56701139005932950796895187 85051708508899426195342781)
  ·
    refine ⟨31894390690837284823253543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85051708508899426195342781 31894390690837284823253543)
    ·
      refine ⟨47841586036255927234880315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31894390690837284823253543 47841586036255927234880315)
      ·
        refine ⟨71762379054383890852320473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47841586036255927234880315 71762379054383890852320473)
        ·
          refine ⟨53821784290787918139240355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71762379054383890852320473 53821784290787918139240355)
          ·
            refine ⟨80732676436181877208860533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53821784290787918139240355 80732676436181877208860533)
            ·
              refine ⟨7568688415892050988330675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 80732676436181877208860533 7568688415892050988330675)
              ·
                refine ⟨11353032623838076482496013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7568688415892050988330675 11353032623838076482496013)
                ·
                  refine ⟨4257387233939278680936005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11353032623838076482496013 4257387233939278680936005)
                  ·
                    refine ⟨798260106363614752675501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4257387233939278680936005 798260106363614752675501)
                    ·
                      rfl

theorem cell22_2331909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 1, 3, 4].length) (baseStart_2331909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2331909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2331909 prefixEnd_2331909 := by exact prefixLift 2331909
  have htrace : WordTrace (prefixWord ++ tailWord_2331909) baseStart_2331909 baseEnd_2331909 := by
    simpa [prefixWord, tailWord_2331909, baseEnd_2331909] using wordTrace_append hprefix tailTrace_2331909
  have hstable : (prefixWord ++ tailWord_2331909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2331909).length < 2 ^ (prefixWord ++ tailWord_2331909).sum := by decide
  have hdescent : baseEnd_2331909 < baseStart_2331909 := by decide
  rcases family_descends (prefixWord ++ tailWord_2331909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2332035 : List Nat := [1, 1, 1, 3, 5, 1, 3, 3, 1, 3]
def baseStart_2332035 : Nat := 118140960795 + 2332035 * 2 ^ 59
def prefixEnd_2332035 : Nat := 4983230072969 + 3 ^ 40 * 2332035 * 2
def baseEnd_2332035 : Nat := 798303238738592424025115

theorem tailTrace_2332035 : CollatzResearch.WordTrace tailWord_2332035 prefixEnd_2332035 798303238738592424025115 := by
  unfold tailWord_2332035
  simp only [CollatzResearch.WordTrace]
  refine ⟨85056304106442949714429559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56704202737628633142953039 85056304106442949714429559)
  ·
    refine ⟨127584456159664424571644339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85056304106442949714429559 127584456159664424571644339)
    ·
      refine ⟨191376684239496636857466509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127584456159664424571644339 191376684239496636857466509)
      ·
        refine ⟨71766256589811238821549941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 191376684239496636857466509 71766256589811238821549941)
        ·
          refine ⟨6728086555294803639520307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 71766256589811238821549941 6728086555294803639520307)
          ·
            refine ⟨10092129832942205459280461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6728086555294803639520307 10092129832942205459280461)
            ·
              refine ⟨3784548687353327047230173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10092129832942205459280461 3784548687353327047230173)
              ·
                refine ⟨1419205757757497642711315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3784548687353327047230173 1419205757757497642711315)
                ·
                  refine ⟨2128808636636246464066973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1419205757757497642711315 2128808636636246464066973)
                  ·
                    refine ⟨798303238738592424025115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2128808636636246464066973 798303238738592424025115)
                    ·
                      rfl

theorem cell22_2332035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 3, 1, 3].length) (baseStart_2332035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2332035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2332035 prefixEnd_2332035 := by exact prefixLift 2332035
  have htrace : WordTrace (prefixWord ++ tailWord_2332035) baseStart_2332035 baseEnd_2332035 := by
    simpa [prefixWord, tailWord_2332035, baseEnd_2332035] using wordTrace_append hprefix tailTrace_2332035
  have hstable : (prefixWord ++ tailWord_2332035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2332035).length < 2 ^ (prefixWord ++ tailWord_2332035).sum := by decide
  have hdescent : baseEnd_2332035 < baseStart_2332035 := by decide
  rcases family_descends (prefixWord ++ tailWord_2332035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2332093 : List Nat := [1, 4, 1, 2, 2, 1, 2, 5, 4]
def baseStart_2332093 : Nat := 118140960795 + 2332093 * 2 ^ 59
def prefixEnd_2332093 : Nat := 4983230072969 + 3 ^ 40 * 2332093 * 2
def baseEnd_2332093 : Nat := 266107697774633202024979

theorem tailTrace_2332093 : CollatzResearch.WordTrace tailWord_2332093 prefixEnd_2332093 266107697774633202024979 := by
  unfold tailWord_2332093
  simp only [CollatzResearch.WordTrace]
  refine ⟨85058419540232825620040933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56705613026821883746693955 85058419540232825620040933)
  ·
    refine ⟨15948453663793654803757675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85058419540232825620040933 15948453663793654803757675)
    ·
      refine ⟨23922680495690482205636513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15948453663793654803757675 23922680495690482205636513)
      ·
        refine ⟨17942010371767861654227385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23922680495690482205636513 17942010371767861654227385)
        ·
          refine ⟨13456507778825896240670539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17942010371767861654227385 13456507778825896240670539)
          ·
            refine ⟨20184761668238844361005809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13456507778825896240670539 20184761668238844361005809)
            ·
              refine ⟨15138571251179133270754357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20184761668238844361005809 15138571251179133270754357)
              ·
                refine ⟨1419241054798043744133221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15138571251179133270754357 1419241054798043744133221)
                ·
                  refine ⟨266107697774633202024979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1419241054798043744133221 266107697774633202024979)
                  ·
                    rfl

theorem cell22_2332093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 5, 4].length) (baseStart_2332093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2332093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2332093 prefixEnd_2332093 := by exact prefixLift 2332093
  have htrace : WordTrace (prefixWord ++ tailWord_2332093) baseStart_2332093 baseEnd_2332093 := by
    simpa [prefixWord, tailWord_2332093, baseEnd_2332093] using wordTrace_append hprefix tailTrace_2332093
  have hstable : (prefixWord ++ tailWord_2332093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2332093).length < 2 ^ (prefixWord ++ tailWord_2332093).sum := by decide
  have hdescent : baseEnd_2332093 < baseStart_2332093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2332093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2332110 : List Nat := [4, 1, 1, 1, 2, 1, 6, 2, 4]
def baseStart_2332110 : Nat := 118140960795 + 2332110 * 2 ^ 59
def prefixEnd_2332110 : Nat := 4983230072969 + 3 ^ 40 * 2332110 * 2
def baseEnd_2332110 : Nat := 266109637590439076133295

theorem tailTrace_2332110 : CollatzResearch.WordTrace tailWord_2332110 prefixEnd_2332110 266109637590439076133295 := by
  unfold tailWord_2332110
  simp only [CollatzResearch.WordTrace]
  refine ⟨10632379947646404690426223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56706026387447491682273189 10632379947646404690426223)
  ·
    refine ⟨15948569921469607035639335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10632379947646404690426223 15948569921469607035639335)
    ·
      refine ⟨23922854882204410553459003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15948569921469607035639335 23922854882204410553459003)
      ·
        refine ⟨35884282323306615830188505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23922854882204410553459003 35884282323306615830188505)
        ·
          refine ⟨26913211742479961872641379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35884282323306615830188505 26913211742479961872641379)
          ·
            refine ⟨40369817613719942808962069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26913211742479961872641379 40369817613719942808962069)
            ·
              refine ⟨1892335200643122319170097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 40369817613719942808962069 1892335200643122319170097)
              ·
                refine ⟨1419251400482341739377573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1892335200643122319170097 1419251400482341739377573)
                ·
                  refine ⟨266109637590439076133295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1419251400482341739377573 266109637590439076133295)
                  ·
                    rfl

theorem cell22_2332110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 6, 2, 4].length) (baseStart_2332110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2332110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2332110 prefixEnd_2332110 := by exact prefixLift 2332110
  have htrace : WordTrace (prefixWord ++ tailWord_2332110) baseStart_2332110 baseEnd_2332110 := by
    simpa [prefixWord, tailWord_2332110, baseEnd_2332110] using wordTrace_append hprefix tailTrace_2332110
  have hstable : (prefixWord ++ tailWord_2332110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2332110).length < 2 ^ (prefixWord ++ tailWord_2332110).sum := by decide
  have hdescent : baseEnd_2332110 < baseStart_2332110 := by decide
  rcases family_descends (prefixWord ++ tailWord_2332110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2332121 : List Nat := [1, 2, 1, 2, 4, 2, 3, 7]
def baseStart_2332121 : Nat := 118140960795 + 2332121 * 2 ^ 59
def prefixEnd_2332121 : Nat := 4983230072969 + 3 ^ 40 * 2332121 * 2
def baseEnd_2332121 : Nat := 88703630921790762930539

theorem tailTrace_2332121 : CollatzResearch.WordTrace tailWord_2332121 prefixEnd_2332121 88703630921790762930539 := by
  unfold tailWord_2332121
  simp only [CollatzResearch.WordTrace]
  refine ⟨85059440784131386402060217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56706293856087590934706811 85059440784131386402060217)
  ·
    refine ⟨63794580588098539801545163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85059440784131386402060217 63794580588098539801545163)
    ·
      refine ⟨95691870882147809702317745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63794580588098539801545163 95691870882147809702317745)
      ·
        refine ⟨71768903161610857276738309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95691870882147809702317745 71768903161610857276738309)
        ·
          refine ⟨13456669342802035739388433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71768903161610857276738309 13456669342802035739388433)
          ·
            refine ⟨10092502007101526804541325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13456669342802035739388433 10092502007101526804541325)
            ·
              refine ⟨3784688252663072551702997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10092502007101526804541325 3784688252663072551702997)
              ·
                refine ⟨88703630921790762930539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3784688252663072551702997 88703630921790762930539)
                ·
                  rfl

theorem cell22_2332121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 7].length) (baseStart_2332121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2332121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2332121 prefixEnd_2332121 := by exact prefixLift 2332121
  have htrace : WordTrace (prefixWord ++ tailWord_2332121) baseStart_2332121 baseEnd_2332121 := by
    simpa [prefixWord, tailWord_2332121, baseEnd_2332121] using wordTrace_append hprefix tailTrace_2332121
  have hstable : (prefixWord ++ tailWord_2332121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2332121).length < 2 ^ (prefixWord ++ tailWord_2332121).sum := by decide
  have hdescent : baseEnd_2332121 < baseStart_2332121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2332121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2332125 : List Nat := [1, 4, 3, 1, 1, 2, 2, 3, 2, 3]
def baseStart_2332125 : Nat := 118140960795 + 2332125 * 2 ^ 59
def prefixEnd_2332125 : Nat := 4983230072969 + 3 ^ 40 * 2332125 * 2
def baseEnd_2332125 : Nat := 798334047577862189274839

theorem tailTrace_2332125 : CollatzResearch.WordTrace tailWord_2332125 prefixEnd_2332125 798334047577862189274839 := by
  unfold tailWord_2332125
  simp only [CollatzResearch.WordTrace]
  refine ⟨85059586676116895085205829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56706391117411263390137219 85059586676116895085205829)
  ·
    refine ⟨15948672501771917828476093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85059586676116895085205829 15948672501771917828476093)
    ·
      refine ⟨5980752188164469185678535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15948672501771917828476093 5980752188164469185678535)
      ·
        refine ⟨8971128282246703778517803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5980752188164469185678535 8971128282246703778517803)
        ·
          refine ⟨13456692423370055667776705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8971128282246703778517803 13456692423370055667776705)
          ·
            refine ⟨10092519317527541750832529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13456692423370055667776705 10092519317527541750832529)
            ·
              refine ⟨7569389488145656313124397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10092519317527541750832529 7569389488145656313124397)
              ·
                refine ⟨2838521058054621117421649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7569389488145656313124397 2838521058054621117421649)
                ·
                  refine ⟨2128890793540965838066237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2838521058054621117421649 2128890793540965838066237)
                  ·
                    refine ⟨798334047577862189274839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2128890793540965838066237 798334047577862189274839)
                    ·
                      rfl

theorem cell22_2332125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_2332125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2332125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2332125 prefixEnd_2332125 := by exact prefixLift 2332125
  have htrace : WordTrace (prefixWord ++ tailWord_2332125) baseStart_2332125 baseEnd_2332125 := by
    simpa [prefixWord, tailWord_2332125, baseEnd_2332125] using wordTrace_append hprefix tailTrace_2332125
  have hstable : (prefixWord ++ tailWord_2332125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2332125).length < 2 ^ (prefixWord ++ tailWord_2332125).sum := by decide
  have hdescent : baseEnd_2332125 < baseStart_2332125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2332125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2332170 : List Nat := [3, 1, 2, 2, 2, 3, 2, 1, 3, 3]
def baseStart_2332170 : Nat := 118140960795 + 2332170 * 2 ^ 59
def prefixEnd_2332170 : Nat := 4983230072969 + 3 ^ 40 * 2332170 * 2
def baseEnd_2332170 : Nat := 798349451997497071899701

theorem tailTrace_2332170 : CollatzResearch.WordTrace tailWord_2332170 prefixEnd_2332170 798349451997497071899701 := by
  unfold tailWord_2332170
  simp only [CollatzResearch.WordTrace]
  refine ⟨21265306990238466942648491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56707485307302578513729309 21265306990238466942648491)
  ·
    refine ⟨31897960485357700413972737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21265306990238466942648491 31897960485357700413972737)
    ·
      refine ⟨23923470364018275310479553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31897960485357700413972737 23923470364018275310479553)
      ·
        refine ⟨17942602773013706482859665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23923470364018275310479553 17942602773013706482859665)
        ·
          refine ⟨13456952079760279862144749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17942602773013706482859665 13456952079760279862144749)
          ·
            refine ⟨5046357029910104948304281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13456952079760279862144749 5046357029910104948304281)
            ·
              refine ⟨3784767772432578711228211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5046357029910104948304281 3784767772432578711228211)
              ·
                refine ⟨5677151658648868066842317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3784767772432578711228211 5677151658648868066842317)
                ·
                  refine ⟨2128931871993325525065869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5677151658648868066842317 2128931871993325525065869)
                  ·
                    refine ⟨798349451997497071899701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2128931871993325525065869 798349451997497071899701)
                    ·
                      rfl

theorem cell22_2332170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 1, 3, 3].length) (baseStart_2332170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2332170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2332170 prefixEnd_2332170 := by exact prefixLift 2332170
  have htrace : WordTrace (prefixWord ++ tailWord_2332170) baseStart_2332170 baseEnd_2332170 := by
    simpa [prefixWord, tailWord_2332170, baseEnd_2332170] using wordTrace_append hprefix tailTrace_2332170
  have hstable : (prefixWord ++ tailWord_2332170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2332170).length < 2 ^ (prefixWord ++ tailWord_2332170).sum := by decide
  have hdescent : baseEnd_2332170 < baseStart_2332170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2332170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2332277 : List Nat := [1, 3, 4, 2, 1, 1, 1, 4, 2, 3]
def baseStart_2332277 : Nat := 118140960795 + 2332277 * 2 ^ 59
def prefixEnd_2332277 : Nat := 4983230072969 + 3 ^ 40 * 2332277 * 2
def baseEnd_2332277 : Nat := 798386080284184459474373

theorem tailTrace_2332277 : CollatzResearch.WordTrace tailWord_2332277 prefixEnd_2332277 798386080284184459474373 := by
  unfold tailWord_2332277
  simp only [CollatzResearch.WordTrace]
  refine ⟨85065130571566225044739085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56710087047710816696492723 85065130571566225044739085)
  ·
    refine ⟨31899423964337334391777157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85065130571566225044739085 31899423964337334391777157)
    ·
      refine ⟨5981141993313250198458217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31899423964337334391777157 5981141993313250198458217)
      ·
        refine ⟨4485856494984937648843663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5981141993313250198458217 4485856494984937648843663)
        ·
          refine ⟨6728784742477406473265495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4485856494984937648843663 6728784742477406473265495)
          ·
            refine ⟨10093177113716109709898243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6728784742477406473265495 10093177113716109709898243)
            ·
              refine ⟨15139765670574164564847365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10093177113716109709898243 15139765670574164564847365)
              ·
                refine ⟨2838706063232655855908881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15139765670574164564847365 2838706063232655855908881)
                ·
                  refine ⟨2129029547424491891931661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2838706063232655855908881 2129029547424491891931661)
                  ·
                    refine ⟨798386080284184459474373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2129029547424491891931661 798386080284184459474373)
                    ·
                      rfl

theorem cell22_2332277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_2332277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2332277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2332277 prefixEnd_2332277 := by exact prefixLift 2332277
  have htrace : WordTrace (prefixWord ++ tailWord_2332277) baseStart_2332277 baseEnd_2332277 := by
    simpa [prefixWord, tailWord_2332277, baseEnd_2332277] using wordTrace_append hprefix tailTrace_2332277
  have hstable : (prefixWord ++ tailWord_2332277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2332277).length < 2 ^ (prefixWord ++ tailWord_2332277).sum := by decide
  have hdescent : baseEnd_2332277 < baseStart_2332277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2332277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2332328 : List Nat := [2, 1, 7, 1, 1, 2, 1, 2, 2, 3]
def baseStart_2332328 : Nat := 118140960795 + 2332328 * 2 ^ 59
def prefixEnd_2332328 : Nat := 4983230072969 + 3 ^ 40 * 2332328 * 2
def baseEnd_2332328 : Nat := 798403538626437326449217

theorem tailTrace_2332328 : CollatzResearch.WordTrace tailWord_2332328 prefixEnd_2332328 798403538626437326449217 := by
  unfold tailWord_2332328
  simp only [CollatzResearch.WordTrace]
  refine ⟨42533495347190730377422819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56711327129587640503230425 42533495347190730377422819)
  ·
    refine ⟨63800243020786095566134229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42533495347190730377422819 63800243020786095566134229)
    ·
      refine ⟨1495318195799674114831271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 63800243020786095566134229 1495318195799674114831271)
      ·
        refine ⟨2242977293699511172246907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1495318195799674114831271 2242977293699511172246907)
        ·
          refine ⟨3364465940549266758370361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2242977293699511172246907 3364465940549266758370361)
          ·
            refine ⟨2523349455411950068777771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3364465940549266758370361 2523349455411950068777771)
            ·
              refine ⟨3785024183117925103166657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2523349455411950068777771 3785024183117925103166657)
              ·
                refine ⟨2838768137338443827374993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3785024183117925103166657 2838768137338443827374993)
                ·
                  refine ⟨2129076103003832870531245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2838768137338443827374993 2129076103003832870531245)
                  ·
                    refine ⟨798403538626437326449217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2129076103003832870531245 798403538626437326449217)
                    ·
                      rfl

theorem cell22_2332328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_2332328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2332328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2332328 prefixEnd_2332328 := by exact prefixLift 2332328
  have htrace : WordTrace (prefixWord ++ tailWord_2332328) baseStart_2332328 baseEnd_2332328 := by
    simpa [prefixWord, tailWord_2332328, baseEnd_2332328] using wordTrace_append hprefix tailTrace_2332328
  have hstable : (prefixWord ++ tailWord_2332328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2332328).length < 2 ^ (prefixWord ++ tailWord_2332328).sum := by decide
  have hdescent : baseEnd_2332328 < baseStart_2332328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2332328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2332350 : List Nat := [4, 2, 1, 1, 2, 2, 2, 1, 2, 5]
def baseStart_2332350 : Nat := 118140960795 + 2332350 * 2 ^ 59
def prefixEnd_2332350 : Nat := 4983230072969 + 3 ^ 40 * 2332350 * 2
def baseEnd_2332350 : Nat := 798411069676036602399149

theorem tailTrace_2332350 : CollatzResearch.WordTrace tailWord_2332350 prefixEnd_2332350 798411069676036602399149 := by
  unfold tailWord_2332350
  simp only [CollatzResearch.WordTrace]
  refine ⟨10633474137537719814018313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56711862066867839008097669 10633474137537719814018313)
  ·
    refine ⟨7975105603153289860513735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10633474137537719814018313 7975105603153289860513735)
    ·
      refine ⟨11962658404729934790770603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7975105603153289860513735 11962658404729934790770603)
      ·
        refine ⟨17943987607094902186155905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11962658404729934790770603 17943987607094902186155905)
        ·
          refine ⟨13457990705321176639616929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17943987607094902186155905 13457990705321176639616929)
          ·
            refine ⟨10093493028990882479712697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13457990705321176639616929 10093493028990882479712697)
            ·
              refine ⟨7570119771743161859784523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10093493028990882479712697 7570119771743161859784523)
              ·
                refine ⟨11355179657614742789676785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7570119771743161859784523 11355179657614742789676785)
                ·
                  refine ⟨8516384743211057092257589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11355179657614742789676785 8516384743211057092257589)
                  ·
                    refine ⟨798411069676036602399149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8516384743211057092257589 798411069676036602399149)
                    ·
                      rfl

theorem cell22_2332350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_2332350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2332350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2332350 prefixEnd_2332350 := by exact prefixLift 2332350
  have htrace : WordTrace (prefixWord ++ tailWord_2332350) baseStart_2332350 baseEnd_2332350 := by
    simpa [prefixWord, tailWord_2332350, baseEnd_2332350] using wordTrace_append hprefix tailTrace_2332350
  have hstable : (prefixWord ++ tailWord_2332350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2332350).length < 2 ^ (prefixWord ++ tailWord_2332350).sum := by decide
  have hdescent : baseEnd_2332350 < baseStart_2332350 := by decide
  rcases family_descends (prefixWord ++ tailWord_2332350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2332395 : List Nat := [1, 1, 1, 1, 2, 4, 4, 1, 4, 3]
def baseStart_2332395 : Nat := 118140960795 + 2332395 * 2 ^ 59
def prefixEnd_2332395 : Nat := 4983230072969 + 3 ^ 40 * 2332395 * 2
def baseEnd_2332395 : Nat := 798426474095671485024011

theorem tailTrace_2332395 : CollatzResearch.WordTrace tailWord_2332395 prefixEnd_2332395 798426474095671485024011 := by
  unfold tailWord_2332395
  simp only [CollatzResearch.WordTrace]
  refine ⟨85069434385138731197534639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56712956256759154131689759 85069434385138731197534639)
  ·
    refine ⟨127604151577708096796301959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85069434385138731197534639 127604151577708096796301959)
    ·
      refine ⟨191406227366562145194452939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127604151577708096796301959 191406227366562145194452939)
      ·
        refine ⟨287109341049843217791679409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191406227366562145194452939 287109341049843217791679409)
        ·
          refine ⟨215332005787382413343759557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 287109341049843217791679409 215332005787382413343759557)
          ·
            refine ⟨40374751085134202501954917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 215332005787382413343759557 40374751085134202501954917)
            ·
              refine ⟨7570265828462662969116547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40374751085134202501954917 7570265828462662969116547)
              ·
                refine ⟨11355398742693994453674821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7570265828462662969116547 11355398742693994453674821)
                ·
                  refine ⟨2129137264255123960064029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11355398742693994453674821 2129137264255123960064029)
                  ·
                    refine ⟨798426474095671485024011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2129137264255123960064029 798426474095671485024011)
                    ·
                      rfl

theorem cell22_2332395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 1, 4, 3].length) (baseStart_2332395 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2332395 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2332395 prefixEnd_2332395 := by exact prefixLift 2332395
  have htrace : WordTrace (prefixWord ++ tailWord_2332395) baseStart_2332395 baseEnd_2332395 := by
    simpa [prefixWord, tailWord_2332395, baseEnd_2332395] using wordTrace_append hprefix tailTrace_2332395
  have hstable : (prefixWord ++ tailWord_2332395).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2332395).length < 2 ^ (prefixWord ++ tailWord_2332395).sum := by decide
  have hdescent : baseEnd_2332395 < baseStart_2332395 := by decide
  rcases family_descends (prefixWord ++ tailWord_2332395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2332397 : List Nat := [1, 5, 1, 2, 1, 4, 1, 1, 6]
def baseStart_2332397 : Nat := 118140960795 + 2332397 * 2 ^ 59
def prefixEnd_2332397 : Nat := 4983230072969 + 3 ^ 40 * 2332397 * 2
def baseEnd_2332397 : Nat := 266142386245514715491335

theorem tailTrace_2332397 : CollatzResearch.WordTrace tailWord_2332397 prefixEnd_2332397 266142386245514715491335 := by
  unfold tailWord_2332397
  simp only [CollatzResearch.WordTrace]
  refine ⟨85069507331131485539107445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56713004887420990359404963 85069507331131485539107445)
  ·
    refine ⟨7975266312293576769291323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 85069507331131485539107445 7975266312293576769291323)
    ·
      refine ⟨11962899468440365153936985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7975266312293576769291323 11962899468440365153936985)
      ·
        refine ⟨8972174601330273865452739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11962899468440365153936985 8972174601330273865452739)
        ·
          refine ⟨13458261901995410798179109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8972174601330273865452739 13458261901995410798179109)
          ·
            refine ⟨2523424106624139524658583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13458261901995410798179109 2523424106624139524658583)
            ·
              refine ⟨3785136159936209286987875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2523424106624139524658583 3785136159936209286987875)
              ·
                refine ⟨5677704239904313930481813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3785136159936209286987875 5677704239904313930481813)
                ·
                  refine ⟨266142386245514715491335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5677704239904313930481813 266142386245514715491335)
                  ·
                    rfl

theorem cell22_2332397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 1, 6].length) (baseStart_2332397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2332397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2332397 prefixEnd_2332397 := by exact prefixLift 2332397
  have htrace : WordTrace (prefixWord ++ tailWord_2332397) baseStart_2332397 baseEnd_2332397 := by
    simpa [prefixWord, tailWord_2332397, baseEnd_2332397] using wordTrace_append hprefix tailTrace_2332397
  have hstable : (prefixWord ++ tailWord_2332397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2332397).length < 2 ^ (prefixWord ++ tailWord_2332397).sum := by decide
  have hdescent : baseEnd_2332397 < baseStart_2332397 := by decide
  rcases family_descends (prefixWord ++ tailWord_2332397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2332412 : List Nat := [2, 2, 2, 1, 3, 1, 3, 3, 2, 3]
def baseStart_2332412 : Nat := 118140960795 + 2332412 * 2 ^ 59
def prefixEnd_2332412 : Nat := 4983230072969 + 3 ^ 40 * 2332412 * 2
def baseEnd_2332412 : Nat := 798432293543089107348959

theorem tailTrace_2332412 : CollatzResearch.WordTrace tailWord_2332412 prefixEnd_2332412 798432293543089107348959 := by
  unfold tailWord_2332412
  simp only [CollatzResearch.WordTrace]
  refine ⟨42535027213038571550451745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56713369617384762067268993 42535027213038571550451745)
  ·
    refine ⟨31901270409778928662838809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42535027213038571550451745 31901270409778928662838809)
    ·
      refine ⟨23925952807334196497129107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31901270409778928662838809 23925952807334196497129107)
      ·
        refine ⟨35888929211001294745693661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23925952807334196497129107 35888929211001294745693661)
        ·
          refine ⟨13458348454125485529635123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35888929211001294745693661 13458348454125485529635123)
          ·
            refine ⟨20187522681188228294452685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13458348454125485529635123 20187522681188228294452685)
            ·
              refine ⟨7570321005445585610419757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20187522681188228294452685 7570321005445585610419757)
              ·
                refine ⟨2838870377042094603907409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7570321005445585610419757 2838870377042094603907409)
                ·
                  refine ⟨2129152782781570952930557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2838870377042094603907409 2129152782781570952930557)
                  ·
                    refine ⟨798432293543089107348959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2129152782781570952930557 798432293543089107348959)
                    ·
                      rfl

theorem cell22_2332412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 3, 2, 3].length) (baseStart_2332412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2332412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2332412 prefixEnd_2332412 := by exact prefixLift 2332412
  have htrace : WordTrace (prefixWord ++ tailWord_2332412) baseStart_2332412 baseEnd_2332412 := by
    simpa [prefixWord, tailWord_2332412, baseEnd_2332412] using wordTrace_append hprefix tailTrace_2332412
  have hstable : (prefixWord ++ tailWord_2332412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2332412).length < 2 ^ (prefixWord ++ tailWord_2332412).sum := by decide
  have hdescent : baseEnd_2332412 < baseStart_2332412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2332412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2332547 : List Nat := [1, 1, 1, 3, 4, 2, 1, 2, 4, 3]
def baseStart_2332547 : Nat := 118140960795 + 2332547 * 2 ^ 59
def prefixEnd_2332547 : Nat := 4983230072969 + 3 ^ 40 * 2332547 * 2
def baseEnd_2332547 : Nat := 798478506801993755223545

theorem tailTrace_2332547 : CollatzResearch.WordTrace tailWord_2332547 prefixEnd_2332547 798478506801993755223545 := by
  unfold tailWord_2332547
  simp only [CollatzResearch.WordTrace]
  refine ⟨85074978280588061157067895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56716652187058707438045263 85074978280588061157067895)
  ·
    refine ⟨127612467420882091735601843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85074978280588061157067895 127612467420882091735601843)
    ·
      refine ⟨191418701131323137603402765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127612467420882091735601843 191418701131323137603402765)
      ·
        refine ⟨71782012924246176601276037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 191418701131323137603402765 71782012924246176601276037)
        ·
          refine ⟨13459127423296158112739257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71782012924246176601276037 13459127423296158112739257)
          ·
            refine ⟨10094345567472118584554443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13459127423296158112739257 10094345567472118584554443)
            ·
              refine ⟨15141518351208177876831665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10094345567472118584554443 15141518351208177876831665)
              ·
                refine ⟨11356138763406133407623749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15141518351208177876831665 11356138763406133407623749)
                ·
                  refine ⟨2129276018138650013929453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11356138763406133407623749 2129276018138650013929453)
                  ·
                    refine ⟨798478506801993755223545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2129276018138650013929453 798478506801993755223545)
                    ·
                      rfl

theorem cell22_2332547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 2, 4, 3].length) (baseStart_2332547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2332547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2332547 prefixEnd_2332547 := by exact prefixLift 2332547
  have htrace : WordTrace (prefixWord ++ tailWord_2332547) baseStart_2332547 baseEnd_2332547 := by
    simpa [prefixWord, tailWord_2332547, baseEnd_2332547] using wordTrace_append hprefix tailTrace_2332547
  have hstable : (prefixWord ++ tailWord_2332547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2332547).length < 2 ^ (prefixWord ++ tailWord_2332547).sum := by decide
  have hdescent : baseEnd_2332547 < baseStart_2332547 := by decide
  rcases family_descends (prefixWord ++ tailWord_2332547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2332564 : List Nat := [2, 4, 2, 1, 1, 2, 2, 1, 4, 3]
def baseStart_2332564 : Nat := 118140960795 + 2332564 * 2 ^ 59
def prefixEnd_2332564 : Nat := 4983230072969 + 3 ^ 40 * 2332564 * 2
def baseEnd_2332564 : Nat := 798484326249411377548493

theorem tailTrace_2332564 : CollatzResearch.WordTrace tailWord_2332564 prefixEnd_2332564 798484326249411377548493 := by
  unfold tailWord_2332564
  simp only [CollatzResearch.WordTrace]
  refine ⟨42537799160763236530218373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56717065547684315373624497 42537799160763236530218373)
  ·
    refine ⟨7975837342643106849415945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42537799160763236530218373 7975837342643106849415945)
    ·
      refine ⟨5981878006982330137061959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7975837342643106849415945 5981878006982330137061959)
      ·
        refine ⟨8972817010473495205592939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5981878006982330137061959 8972817010473495205592939)
        ·
          refine ⟨13459225515710242808389409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8972817010473495205592939 13459225515710242808389409)
          ·
            refine ⟨10094419136782682106292057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13459225515710242808389409 10094419136782682106292057)
            ·
              refine ⟨7570814352587011579719043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10094419136782682106292057 7570814352587011579719043)
              ·
                refine ⟨11356221528880517369578565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7570814352587011579719043 11356221528880517369578565)
                ·
                  refine ⟨2129291536665097006795981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11356221528880517369578565 2129291536665097006795981)
                  ·
                    refine ⟨798484326249411377548493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2129291536665097006795981 798484326249411377548493)
                    ·
                      rfl

theorem cell22_2332564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_2332564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2332564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2332564 prefixEnd_2332564 := by exact prefixLift 2332564
  have htrace : WordTrace (prefixWord ++ tailWord_2332564) baseStart_2332564 baseEnd_2332564 := by
    simpa [prefixWord, tailWord_2332564, baseEnd_2332564] using wordTrace_append hprefix tailTrace_2332564
  have hstable : (prefixWord ++ tailWord_2332564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2332564).length < 2 ^ (prefixWord ++ tailWord_2332564).sum := by decide
  have hdescent : baseEnd_2332564 < baseStart_2332564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2332564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2332684 : List Nat := [2, 2, 1, 2, 3, 1, 1, 6, 4]
def baseStart_2332684 : Nat := 118140960795 + 2332684 * 2 ^ 59
def prefixEnd_2332684 : Nat := 4983230072969 + 3 ^ 40 * 2332684 * 2
def baseEnd_2332684 : Nat := 266175134900590354849375

theorem tailTrace_2332684 : CollatzResearch.WordTrace tailWord_2332684 prefixEnd_2332684 266175134900590354849375 := by
  unfold tailWord_2332684
  simp only [CollatzResearch.WordTrace]
  refine ⟨42539987540545866777402553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56719983387394489036536737 42539987540545866777402553)
  ·
    refine ⟨31904990655409400083051915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42539987540545866777402553 31904990655409400083051915)
    ·
      refine ⟨47857485983114100124577873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31904990655409400083051915 47857485983114100124577873)
      ·
        refine ⟨35893114487335575093433405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47857485983114100124577873 35893114487335575093433405)
        ·
          refine ⟨13459917932750840660037527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35893114487335575093433405 13459917932750840660037527)
          ·
            refine ⟨20189876899126260990056291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13459917932750840660037527 20189876899126260990056291)
            ·
              refine ⟨30284815348689391485084437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20189876899126260990056291 30284815348689391485084437)
              ·
                refine ⟨1419600719469815225863333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 30284815348689391485084437 1419600719469815225863333)
                ·
                  refine ⟨266175134900590354849375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1419600719469815225863333 266175134900590354849375)
                  ·
                    rfl

theorem cell22_2332684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 6, 4].length) (baseStart_2332684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2332684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2332684 prefixEnd_2332684 := by exact prefixLift 2332684
  have htrace : WordTrace (prefixWord ++ tailWord_2332684) baseStart_2332684 baseEnd_2332684 := by
    simpa [prefixWord, tailWord_2332684, baseEnd_2332684] using wordTrace_append hprefix tailTrace_2332684
  have hstable : (prefixWord ++ tailWord_2332684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2332684).length < 2 ^ (prefixWord ++ tailWord_2332684).sum := by decide
  have hdescent : baseEnd_2332684 < baseStart_2332684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2332684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2332714 : List Nat := [3, 1, 4, 1, 2, 1, 2, 1, 1, 6]
def baseStart_2332714 : Nat := 118140960795 + 2332714 * 2 ^ 59
def prefixEnd_2332714 : Nat := 4983230072969 + 3 ^ 40 * 2332714 * 2
def baseEnd_2332714 : Nat := 798535674314860986298033

theorem tailTrace_2332714 : CollatzResearch.WordTrace tailWord_2332714 prefixEnd_2332714 798535674314860986298033 := by
  unfold tailWord_2332714
  simp only [CollatzResearch.WordTrace]
  refine ⟨21270267317745762169599299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56720712847322032452264797 21270267317745762169599299)
  ·
    refine ⟨31905400976618643254398949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21270267317745762169599299 31905400976618643254398949)
    ·
      refine ⟨5982262683115995610199803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31905400976618643254398949 5982262683115995610199803)
      ·
        refine ⟨8973394024673993415299705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5982262683115995610199803 8973394024673993415299705)
        ·
          refine ⟨6730045518505495061474779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8973394024673993415299705 6730045518505495061474779)
          ·
            refine ⟨10095068277758242592212169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6730045518505495061474779 10095068277758242592212169)
            ·
              refine ⟨7571301208318681944159127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10095068277758242592212169 7571301208318681944159127)
              ·
                refine ⟨11356951812478022916238691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7571301208318681944159127 11356951812478022916238691)
                ·
                  refine ⟨17035427718717034374358037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11356951812478022916238691 17035427718717034374358037)
                  ·
                    refine ⟨798535674314860986298033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17035427718717034374358037 798535674314860986298033)
                    ·
                      rfl

theorem cell22_2332714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_2332714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2332714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2332714 prefixEnd_2332714 := by exact prefixLift 2332714
  have htrace : WordTrace (prefixWord ++ tailWord_2332714) baseStart_2332714 baseEnd_2332714 := by
    simpa [prefixWord, tailWord_2332714, baseEnd_2332714] using wordTrace_append hprefix tailTrace_2332714
  have hstable : (prefixWord ++ tailWord_2332714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2332714).length < 2 ^ (prefixWord ++ tailWord_2332714).sum := by decide
  have hdescent : baseEnd_2332714 < baseStart_2332714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2332714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2332718 : List Nat := [4, 1, 3, 1, 1, 4, 1, 3, 4]
def baseStart_2332718 : Nat := 118140960795 + 2332718 * 2 ^ 59
def prefixEnd_2332718 : Nat := 4983230072969 + 3 ^ 40 * 2332718 * 2
def baseEnd_2332718 : Nat := 266179014532202103066007

theorem tailTrace_2332718 : CollatzResearch.WordTrace tailWord_2332718 prefixEnd_2332718 266179014532202103066007 := by
  unfold tailWord_2332718
  simp only [CollatzResearch.WordTrace]
  refine ⟨10635151895371069670192851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56720810108645704907695205 10635151895371069670192851)
  ·
    refine ⟨15952727843056604505289277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10635151895371069670192851 15952727843056604505289277)
    ·
      refine ⟨5982272941146226689483479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15952727843056604505289277 5982272941146226689483479)
      ·
        refine ⟨8973409411719340034225219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5982272941146226689483479 8973409411719340034225219)
        ·
          refine ⟨13460114117579010051337829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8973409411719340034225219 13460114117579010051337829)
          ·
            refine ⟨2523771397046064384625843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13460114117579010051337829 2523771397046064384625843)
            ·
              refine ⟨3785657095569096576938765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2523771397046064384625843 3785657095569096576938765)
              ·
                refine ⟨1419621410838411216352037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3785657095569096576938765 1419621410838411216352037)
                ·
                  refine ⟨266179014532202103066007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1419621410838411216352037 266179014532202103066007)
                  ·
                    rfl

theorem cell22_2332718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 3, 4].length) (baseStart_2332718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2332718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2332718 prefixEnd_2332718 := by exact prefixLift 2332718
  have htrace : WordTrace (prefixWord ++ tailWord_2332718) baseStart_2332718 baseEnd_2332718 := by
    simpa [prefixWord, tailWord_2332718, baseEnd_2332718] using wordTrace_append hprefix tailTrace_2332718
  have hstable : (prefixWord ++ tailWord_2332718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2332718).length < 2 ^ (prefixWord ++ tailWord_2332718).sum := by decide
  have hdescent : baseEnd_2332718 < baseStart_2332718 := by decide
  rcases family_descends (prefixWord ++ tailWord_2332718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2332729 : List Nat := [1, 2, 1, 5, 3, 2, 8]
def baseStart_2332729 : Nat := 118140960795 + 2332729 * 2 ^ 59
def prefixEnd_2332729 : Nat := 4983230072969 + 3 ^ 40 * 2332729 * 2
def baseEnd_2332729 : Nat := 29575585523015035080481

theorem tailTrace_2332729 : CollatzResearch.WordTrace tailWord_2332729 prefixEnd_2332729 29575585523015035080481 := by
  unfold tailWord_2332729
  simp only [CollatzResearch.WordTrace]
  refine ⟨85081616365928706240193241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56721077577285804160128827 85081616365928706240193241)
  ·
    refine ⟨63811212274446529680144931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85081616365928706240193241 63811212274446529680144931)
    ·
      refine ⟨95716818411669794520217397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63811212274446529680144931 95716818411669794520217397)
      ·
        refine ⟨8973451726094043236270381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 95716818411669794520217397 8973451726094043236270381)
        ·
          refine ⟨3365044397285266213601393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8973451726094043236270381 3365044397285266213601393)
          ·
            refine ⟨2523783297963949660201045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3365044397285266213601393 2523783297963949660201045)
            ·
              refine ⟨29575585523015035080481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2523783297963949660201045 29575585523015035080481)
              ·
                rfl

theorem cell22_2332729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 8].length) (baseStart_2332729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2332729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2332729 prefixEnd_2332729 := by exact prefixLift 2332729
  have htrace : WordTrace (prefixWord ++ tailWord_2332729) baseStart_2332729 baseEnd_2332729 := by
    simpa [prefixWord, tailWord_2332729, baseEnd_2332729] using wordTrace_append hprefix tailTrace_2332729
  have hstable : (prefixWord ++ tailWord_2332729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2332729).length < 2 ^ (prefixWord ++ tailWord_2332729).sum := by decide
  have hdescent : baseEnd_2332729 < baseStart_2332729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2332729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2332744 : List Nat := [2, 1, 3, 1, 1, 1, 2, 5, 3, 3]
def baseStart_2332744 : Nat := 118140960795 + 2332744 * 2 ^ 59
def prefixEnd_2332744 : Nat := 4983230072969 + 3 ^ 40 * 2332744 * 2
def baseEnd_2332744 : Nat := 798545943927950908047941

theorem tailTrace_2332744 : CollatzResearch.WordTrace tailWord_2332744 prefixEnd_2332744 798545943927950908047941 := by
  unfold tailWord_2332744
  simp only [CollatzResearch.WordTrace]
  refine ⟨42541081730437181900994643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56721442307249575867992857 42541081730437181900994643)
  ·
    refine ⟨63811622595655772851491965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42541081730437181900994643 63811622595655772851491965)
    ·
      refine ⟨23929358473370914819309487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63811622595655772851491965 23929358473370914819309487)
      ·
        refine ⟨35894037710056372228964231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23929358473370914819309487 35894037710056372228964231)
        ·
          refine ⟨53841056565084558343446347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35894037710056372228964231 53841056565084558343446347)
          ·
            refine ⟨80761584847626837515169521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53841056565084558343446347 80761584847626837515169521)
            ·
              refine ⟨60571188635720128136377141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80761584847626837515169521 60571188635720128136377141)
              ·
                refine ⟨5678548934598762012785357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 60571188635720128136377141 5678548934598762012785357)
                ·
                  refine ⟨2129455850474535754794509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5678548934598762012785357 2129455850474535754794509)
                  ·
                    refine ⟨798545943927950908047941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2129455850474535754794509 798545943927950908047941)
                    ·
                      rfl

theorem cell22_2332744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 5, 3, 3].length) (baseStart_2332744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2332744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2332744 prefixEnd_2332744 := by exact prefixLift 2332744
  have htrace : WordTrace (prefixWord ++ tailWord_2332744) baseStart_2332744 baseEnd_2332744 := by
    simpa [prefixWord, tailWord_2332744, baseEnd_2332744] using wordTrace_append hprefix tailTrace_2332744
  have hstable : (prefixWord ++ tailWord_2332744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2332744).length < 2 ^ (prefixWord ++ tailWord_2332744).sum := by decide
  have hdescent : baseEnd_2332744 < baseStart_2332744 := by decide
  rcases family_descends (prefixWord ++ tailWord_2332744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2332804 : List Nat := [2, 3, 2, 1, 2, 1, 1, 1, 5, 4]
def baseStart_2332804 : Nat := 118140960795 + 2332804 * 2 ^ 59
def prefixEnd_2332804 : Nat := 4983230072969 + 3 ^ 40 * 2332804 * 2
def baseEnd_2332804 : Nat := 798566483154130751547757

theorem tailTrace_2332804 : CollatzResearch.WordTrace tailWord_2332804 prefixEnd_2332804 798566483154130751547757 := by
  unfold tailWord_2332804
  simp only [CollatzResearch.WordTrace]
  refine ⟨42542175920328497024586733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56722901227104662699448977 42542175920328497024586733)
  ·
    refine ⟨15953315970123186384220025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42542175920328497024586733 15953315970123186384220025)
    ·
      refine ⟨11964986977592389788165019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15953315970123186384220025 11964986977592389788165019)
      ·
        refine ⟨17947480466388584682247529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11964986977592389788165019 17947480466388584682247529)
        ·
          refine ⟨13460610349791438511685647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17947480466388584682247529 13460610349791438511685647)
          ·
            refine ⟨20190915524687157767528471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13460610349791438511685647 20190915524687157767528471)
            ·
              refine ⟨30286373287030736651292707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20190915524687157767528471 30286373287030736651292707)
              ·
                refine ⟨45429559930546104976939061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30286373287030736651292707 45429559930546104976939061)
                ·
                  refine ⟨4259021243488697341588037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45429559930546104976939061 4259021243488697341588037)
                  ·
                    refine ⟨798566483154130751547757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4259021243488697341588037 798566483154130751547757)
                    ·
                      rfl

theorem cell22_2332804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_2332804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2332804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2332804 prefixEnd_2332804 := by exact prefixLift 2332804
  have htrace : WordTrace (prefixWord ++ tailWord_2332804) baseStart_2332804 baseEnd_2332804 := by
    simpa [prefixWord, tailWord_2332804, baseEnd_2332804] using wordTrace_append hprefix tailTrace_2332804
  have hstable : (prefixWord ++ tailWord_2332804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2332804).length < 2 ^ (prefixWord ++ tailWord_2332804).sum := by decide
  have hdescent : baseEnd_2332804 < baseStart_2332804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2332804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2332853 : List Nat := [1, 3, 3, 4, 1, 1, 2, 1, 6]
def baseStart_2332853 : Nat := 118140960795 + 2332853 * 2 ^ 59
def prefixEnd_2332853 : Nat := 4983230072969 + 3 ^ 40 * 2332853 * 2
def baseEnd_2332853 : Nat := 266194418951836985690869

theorem tailTrace_2332853 : CollatzResearch.WordTrace tailWord_2332853 prefixEnd_2332853 266194418951836985690869 := by
  unfold tailWord_2332853
  simp only [CollatzResearch.WordTrace]
  refine ⟨85086139017479475417707213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56724092678319650278471475 85086139017479475417707213)
  ·
    refine ⟨31907302131554803281640205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85086139017479475417707213 31907302131554803281640205)
    ·
      refine ⟨11965238299333051230615077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31907302131554803281640205 11965238299333051230615077)
      ·
        refine ⟨2243482181124947105740327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11965238299333051230615077 2243482181124947105740327)
        ·
          refine ⟨3365223271687420658610491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2243482181124947105740327 3365223271687420658610491)
          ·
            refine ⟨5047834907531130987915737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3365223271687420658610491 5047834907531130987915737)
            ·
              refine ⟨3785876180648348240936803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5047834907531130987915737 3785876180648348240936803)
              ·
                refine ⟨5678814270972522361405205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3785876180648348240936803 5678814270972522361405205)
                ·
                  refine ⟨266194418951836985690869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5678814270972522361405205 266194418951836985690869)
                  ·
                    rfl

theorem cell22_2332853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 1, 6].length) (baseStart_2332853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2332853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2332853 prefixEnd_2332853 := by exact prefixLift 2332853
  have htrace : WordTrace (prefixWord ++ tailWord_2332853) baseStart_2332853 baseEnd_2332853 := by
    simpa [prefixWord, tailWord_2332853, baseEnd_2332853] using wordTrace_append hprefix tailTrace_2332853
  have hstable : (prefixWord ++ tailWord_2332853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2332853).length < 2 ^ (prefixWord ++ tailWord_2332853).sum := by decide
  have hdescent : baseEnd_2332853 < baseStart_2332853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2332853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2332868 : List Nat := [2, 3, 3, 1, 2, 3, 1, 1, 1, 5]
def baseStart_2332868 : Nat := 118140960795 + 2332868 * 2 ^ 59
def prefixEnd_2332868 : Nat := 4983230072969 + 3 ^ 40 * 2332868 * 2
def baseEnd_2332868 : Nat := 798588391662055917947561

theorem tailTrace_2332868 : CollatzResearch.WordTrace tailWord_2332868 prefixEnd_2332868 798588391662055917947561 := by
  unfold tailWord_2332868
  simp only [CollatzResearch.WordTrace]
  refine ⟨42543343056212566489751629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56724457408283421986335505 42543343056212566489751629)
  ·
    refine ⟨15953753646079712433656861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42543343056212566489751629 15953753646079712433656861)
    ·
      refine ⟨5982657617279892162621323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15953753646079712433656861 5982657617279892162621323)
      ·
        refine ⟨8973986425919838243931985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5982657617279892162621323 8973986425919838243931985)
        ·
          refine ⟨6730489819439878682948989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8973986425919838243931985 6730489819439878682948989)
          ·
            refine ⟨2523933682289954506105871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6730489819439878682948989 2523933682289954506105871)
            ·
              refine ⟨3785900523434931759158807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2523933682289954506105871 3785900523434931759158807)
              ·
                refine ⟨5678850785152397638738211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3785900523434931759158807 5678850785152397638738211)
                ·
                  refine ⟨8518276177728596458107317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5678850785152397638738211 8518276177728596458107317)
                  ·
                    refine ⟨798588391662055917947561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8518276177728596458107317 798588391662055917947561)
                    ·
                      rfl

theorem cell22_2332868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_2332868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2332868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2332868 prefixEnd_2332868 := by exact prefixLift 2332868
  have htrace : WordTrace (prefixWord ++ tailWord_2332868) baseStart_2332868 baseEnd_2332868 := by
    simpa [prefixWord, tailWord_2332868, baseEnd_2332868] using wordTrace_append hprefix tailTrace_2332868
  have hstable : (prefixWord ++ tailWord_2332868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2332868).length < 2 ^ (prefixWord ++ tailWord_2332868).sum := by decide
  have hdescent : baseEnd_2332868 < baseStart_2332868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2332868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2332913 : List Nat := [1, 2, 2, 2, 2, 1, 2, 6, 1, 3]
def baseStart_2332913 : Nat := 118140960795 + 2332913 * 2 ^ 59
def prefixEnd_2332913 : Nat := 4983230072969 + 3 ^ 40 * 2332913 * 2
def baseEnd_2332913 : Nat := 798603796081690800572423

theorem tailTrace_2332913 : CollatzResearch.WordTrace tailWord_2332913 prefixEnd_2332913 798603796081690800572423 := by
  unfold tailWord_2332913
  simp only [CollatzResearch.WordTrace]
  refine ⟨85088327397262105664891393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56725551598174737109927595 85088327397262105664891393)
  ·
    refine ⟨63816245547946579248668545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85088327397262105664891393 63816245547946579248668545)
    ·
      refine ⟨47862184160959934436501409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63816245547946579248668545 47862184160959934436501409)
      ·
        refine ⟨35896638120719950827376057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47862184160959934436501409 35896638120719950827376057)
        ·
          refine ⟨26922478590539963120532043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35896638120719950827376057 26922478590539963120532043)
          ·
            refine ⟨40383717885809944680798065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26922478590539963120532043 40383717885809944680798065)
            ·
              refine ⟨30287788414357458510598549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40383717885809944680798065 30287788414357458510598549)
              ·
                refine ⟨1419740081923005867684307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 30287788414357458510598549 1419740081923005867684307)
                ·
                  refine ⟨2129610122884508801526461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1419740081923005867684307 2129610122884508801526461)
                  ·
                    refine ⟨798603796081690800572423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2129610122884508801526461 798603796081690800572423)
                    ·
                      rfl

theorem cell22_2332913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 6, 1, 3].length) (baseStart_2332913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2332913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2332913 prefixEnd_2332913 := by exact prefixLift 2332913
  have htrace : WordTrace (prefixWord ++ tailWord_2332913) baseStart_2332913 baseEnd_2332913 := by
    simpa [prefixWord, tailWord_2332913, baseEnd_2332913] using wordTrace_append hprefix tailTrace_2332913
  have hstable : (prefixWord ++ tailWord_2332913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2332913).length < 2 ^ (prefixWord ++ tailWord_2332913).sum := by decide
  have hdescent : baseEnd_2332913 < baseStart_2332913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2332913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2332986 : List Nat := [3, 1, 1, 1, 4, 2, 1, 3, 1, 5]
def baseStart_2332986 : Nat := 118140960795 + 2332986 * 2 ^ 59
def prefixEnd_2332986 : Nat := 4983230072969 + 3 ^ 40 * 2332986 * 2
def baseEnd_2332986 : Nat := 798628785473542943497199

theorem tailTrace_2332986 : CollatzResearch.WordTrace tailWord_2332986 prefixEnd_2332986 798628785473542943497199 := by
  unfold tailWord_2332986
  simp only [CollatzResearch.WordTrace]
  refine ⟨21272747481499409783074703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56727326617331759421532541 21272747481499409783074703)
  ·
    refine ⟨31909121222249114674612055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21272747481499409783074703 31909121222249114674612055)
    ·
      refine ⟨47863681833373672011918083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31909121222249114674612055 47863681833373672011918083)
      ·
        refine ⟨71795522750060508017877125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47863681833373672011918083 71795522750060508017877125)
        ·
          refine ⟨13461660515636345253351961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71795522750060508017877125 13461660515636345253351961)
          ·
            refine ⟨10096245386727258940013971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13461660515636345253351961 10096245386727258940013971)
            ·
              refine ⟨15144368080090888410020957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10096245386727258940013971 15144368080090888410020957)
              ·
                refine ⟨5679138030034083153757859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15144368080090888410020957 5679138030034083153757859)
                ·
                  refine ⟨8518707045051124730636789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5679138030034083153757859 8518707045051124730636789)
                  ·
                    refine ⟨798628785473542943497199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8518707045051124730636789 798628785473542943497199)
                    ·
                      rfl

theorem cell22_2332986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 3, 1, 5].length) (baseStart_2332986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2332986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2332986 prefixEnd_2332986 := by exact prefixLift 2332986
  have htrace : WordTrace (prefixWord ++ tailWord_2332986) baseStart_2332986 baseEnd_2332986 := by
    simpa [prefixWord, tailWord_2332986, baseEnd_2332986] using wordTrace_append hprefix tailTrace_2332986
  have hstable : (prefixWord ++ tailWord_2332986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2332986).length < 2 ^ (prefixWord ++ tailWord_2332986).sum := by decide
  have hdescent : baseEnd_2332986 < baseStart_2332986 := by decide
  rcases family_descends (prefixWord ++ tailWord_2332986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2333095 : List Nat := [1, 1, 6, 1, 1, 2, 4, 1, 5]
def baseStart_2333095 : Nat := 118140960795 + 2333095 * 2 ^ 59
def prefixEnd_2333095 : Nat := 4983230072969 + 3 ^ 40 * 2333095 * 2
def baseEnd_2333095 : Nat := 266222032800367664173955

theorem tailTrace_2333095 : CollatzResearch.WordTrace tailWord_2333095 prefixEnd_2333095 266222032800367664173955 := by
  unfold tailWord_2333095
  simp only [CollatzResearch.WordTrace]
  refine ⟨85094965482602750748016739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56729976988401833832011159 85094965482602750748016739)
  ·
    refine ⟨127642448223904126122025109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85094965482602750748016739 127642448223904126122025109)
    ·
      refine ⟨5983239760495505911969927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 127642448223904126122025109 5983239760495505911969927)
      ·
        refine ⟨8974859640743258867954891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5983239760495505911969927 8974859640743258867954891)
        ·
          refine ⟨13462289461114888301932337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8974859640743258867954891 13462289461114888301932337)
          ·
            refine ⟨10096717095836166226449253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13462289461114888301932337 10096717095836166226449253)
            ·
              refine ⟨1893134455469281167459235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10096717095836166226449253 1893134455469281167459235)
              ·
                refine ⟨2839701683203921751188853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1893134455469281167459235 2839701683203921751188853)
                ·
                  refine ⟨266222032800367664173955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2839701683203921751188853 266222032800367664173955)
                  ·
                    rfl

theorem cell22_2333095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 4, 1, 5].length) (baseStart_2333095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2333095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2333095 prefixEnd_2333095 := by exact prefixLift 2333095
  have htrace : WordTrace (prefixWord ++ tailWord_2333095) baseStart_2333095 baseEnd_2333095 := by
    simpa [prefixWord, tailWord_2333095, baseEnd_2333095] using wordTrace_append hprefix tailTrace_2333095
  have hstable : (prefixWord ++ tailWord_2333095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2333095).length < 2 ^ (prefixWord ++ tailWord_2333095).sum := by decide
  have hdescent : baseEnd_2333095 < baseStart_2333095 := by decide
  rcases family_descends (prefixWord ++ tailWord_2333095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2333106 : List Nat := [3, 2, 1, 1, 1, 1, 4, 1, 8]
def baseStart_2333106 : Nat := 118140960795 + 2333106 * 2 ^ 59
def prefixEnd_2333106 : Nat := 4983230072969 + 3 ^ 40 * 2333106 * 2
def baseEnd_2333106 : Nat := 266223287975300876832277

theorem tailTrace_2333106 : CollatzResearch.WordTrace tailWord_2333106 prefixEnd_2333106 266223287975300876832277 := by
  unfold tailWord_2333106
  simp only [CollatzResearch.WordTrace]
  refine ⟨21273841671390724906666793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56730244457041933084444781 21273841671390724906666793)
  ·
    refine ⟨15955381253543043680000095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21273841671390724906666793 15955381253543043680000095)
    ·
      refine ⟨23933071880314565520000143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15955381253543043680000095 23933071880314565520000143)
      ·
        refine ⟨35899607820471848280000215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23933071880314565520000143 35899607820471848280000215)
        ·
          refine ⟨53849411730707772420000323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35899607820471848280000215 53849411730707772420000323)
          ·
            refine ⟨80774117596061658630000485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53849411730707772420000323 80774117596061658630000485)
            ·
              refine ⟨15145147049261560993125091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 80774117596061658630000485 15145147049261560993125091)
              ·
                refine ⟨22717720573892341489687637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15145147049261560993125091 22717720573892341489687637)
                ·
                  refine ⟨266223287975300876832277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22717720573892341489687637 266223287975300876832277)
                  ·
                    rfl

theorem cell22_2333106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 8].length) (baseStart_2333106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2333106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2333106 prefixEnd_2333106 := by exact prefixLift 2333106
  have htrace : WordTrace (prefixWord ++ tailWord_2333106) baseStart_2333106 baseEnd_2333106 := by
    simpa [prefixWord, tailWord_2333106, baseEnd_2333106] using wordTrace_append hprefix tailTrace_2333106
  have hstable : (prefixWord ++ tailWord_2333106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2333106).length < 2 ^ (prefixWord ++ tailWord_2333106).sum := by decide
  have hdescent : baseEnd_2333106 < baseStart_2333106 := by decide
  rcases family_descends (prefixWord ++ tailWord_2333106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2333123 : List Nat := [1, 1, 1, 3, 1, 1, 3, 7, 4]
def baseStart_2333123 : Nat := 118140960795 + 2333123 * 2 ^ 59
def prefixEnd_2333123 : Nat := 4983230072969 + 3 ^ 40 * 2333123 * 2
def baseEnd_2333123 : Nat := 266225227791106750940593

theorem tailTrace_2333123 : CollatzResearch.WordTrace tailWord_2333123 prefixEnd_2333123 266225227791106750940593 := by
  unfold tailWord_2333123
  simp only [CollatzResearch.WordTrace]
  refine ⟨85095986726501311530036023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56730657817667541020024015 85095986726501311530036023)
  ·
    refine ⟨127643980089751967295054035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85095986726501311530036023 127643980089751967295054035)
    ·
      refine ⟨191465970134627950942581053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127643980089751967295054035 191465970134627950942581053)
      ·
        refine ⟨71799738800485481603467895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 191465970134627950942581053 71799738800485481603467895)
        ·
          refine ⟨107699608200728222405201843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71799738800485481603467895 107699608200728222405201843)
          ·
            refine ⟨161549412301092333607802765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107699608200728222405201843 161549412301092333607802765)
            ·
              refine ⟨60581029612909625102926037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 161549412301092333607802765 60581029612909625102926037)
              ·
                refine ⟨1419867881552569338349829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 60581029612909625102926037 1419867881552569338349829)
                ·
                  refine ⟨266225227791106750940593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1419867881552569338349829 266225227791106750940593)
                  ·
                    rfl

theorem cell22_2333123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 7, 4].length) (baseStart_2333123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2333123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2333123 prefixEnd_2333123 := by exact prefixLift 2333123
  have htrace : WordTrace (prefixWord ++ tailWord_2333123) baseStart_2333123 baseEnd_2333123 := by
    simpa [prefixWord, tailWord_2333123, baseEnd_2333123] using wordTrace_append hprefix tailTrace_2333123
  have hstable : (prefixWord ++ tailWord_2333123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2333123).length < 2 ^ (prefixWord ++ tailWord_2333123).sum := by decide
  have hdescent : baseEnd_2333123 < baseStart_2333123 := by decide
  rcases family_descends (prefixWord ++ tailWord_2333123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2333155 : List Nat := [1, 1, 1, 6, 3, 1, 2, 1, 1, 5]
def baseStart_2333155 : Nat := 118140960795 + 2333155 * 2 ^ 59
def prefixEnd_2333155 : Nat := 4983230072969 + 3 ^ 40 * 2333155 * 2
def baseEnd_2333155 : Nat := 798686637627282836021681

theorem tailTrace_2333155 : CollatzResearch.WordTrace tailWord_2333155 prefixEnd_2333155 798686637627282836021681 := by
  unfold tailWord_2333155
  simp only [CollatzResearch.WordTrace]
  refine ⟨85097153862385380995200919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56731435908256920663467279 85097153862385380995200919)
  ·
    refine ⟨127645730793578071492801379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85097153862385380995200919 127645730793578071492801379)
    ·
      refine ⟨191468596190367107239202069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127645730793578071492801379 191468596190367107239202069)
      ·
        refine ⟨8975090446423458151837597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 191468596190367107239202069 8975090446423458151837597)
        ·
          refine ⟨3365658917408796806939099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8975090446423458151837597 3365658917408796806939099)
          ·
            refine ⟨5048488376113195210408649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3365658917408796806939099 5048488376113195210408649)
            ·
              refine ⟨3786366282084896407806487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5048488376113195210408649 3786366282084896407806487)
              ·
                refine ⟨5679549423127344611709731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3786366282084896407806487 5679549423127344611709731)
                ·
                  refine ⟨8519324134691016917564597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5679549423127344611709731 8519324134691016917564597)
                  ·
                    refine ⟨798686637627282836021681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8519324134691016917564597 798686637627282836021681)
                    ·
                      rfl

theorem cell22_2333155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 1, 1, 5].length) (baseStart_2333155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2333155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2333155 prefixEnd_2333155 := by exact prefixLift 2333155
  have htrace : WordTrace (prefixWord ++ tailWord_2333155) baseStart_2333155 baseEnd_2333155 := by
    simpa [prefixWord, tailWord_2333155, baseEnd_2333155] using wordTrace_append hprefix tailTrace_2333155
  have hstable : (prefixWord ++ tailWord_2333155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2333155).length < 2 ^ (prefixWord ++ tailWord_2333155).sum := by decide
  have hdescent : baseEnd_2333155 < baseStart_2333155 := by decide
  rcases family_descends (prefixWord ++ tailWord_2333155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2333168 : List Nat := [2, 1, 1, 1, 3, 3, 5, 6]
def baseStart_2333168 : Nat := 118140960795 + 2333168 * 2 ^ 59
def prefixEnd_2333168 : Nat := 4983230072969 + 3 ^ 40 * 2333168 * 2
def baseEnd_2333168 : Nat := 88743454199217237271849

theorem tailTrace_2333168 : CollatzResearch.WordTrace tailWord_2333168 prefixEnd_2333168 88743454199217237271849 := by
  unfold tailWord_2333168
  simp only [CollatzResearch.WordTrace]
  refine ⟨42548814005669142107712079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56731752007558856143616105 42548814005669142107712079)
  ·
    refine ⟨63823221008503713161568119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42548814005669142107712079 63823221008503713161568119)
    ·
      refine ⟨95734831512755569742352179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63823221008503713161568119 95734831512755569742352179)
      ·
        refine ⟨143602247269133354613528269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95734831512755569742352179 143602247269133354613528269)
        ·
          refine ⟨53850842725925007980073101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 143602247269133354613528269 53850842725925007980073101)
          ·
            refine ⟨20194066022221877992527413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53850842725925007980073101 20194066022221877992527413)
            ·
              refine ⟨1893193689583301061799445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20194066022221877992527413 1893193689583301061799445)
              ·
                refine ⟨88743454199217237271849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1893193689583301061799445 88743454199217237271849)
                ·
                  rfl

theorem cell22_2333168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 5, 6].length) (baseStart_2333168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2333168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2333168 prefixEnd_2333168 := by exact prefixLift 2333168
  have htrace : WordTrace (prefixWord ++ tailWord_2333168) baseStart_2333168 baseEnd_2333168 := by
    simpa [prefixWord, tailWord_2333168, baseEnd_2333168] using wordTrace_append hprefix tailTrace_2333168
  have hstable : (prefixWord ++ tailWord_2333168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2333168).length < 2 ^ (prefixWord ++ tailWord_2333168).sum := by decide
  have hdescent : baseEnd_2333168 < baseStart_2333168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2333168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2333170 : List Nat := [3, 2, 1, 4, 2, 1, 1, 1, 1, 6]
def baseStart_2333170 : Nat := 118140960795 + 2333170 * 2 ^ 59
def prefixEnd_2333170 : Nat := 4983230072969 + 3 ^ 40 * 2333170 * 2
def baseEnd_2333170 : Nat := 798691772433827796896635

theorem tailTrace_2333170 : CollatzResearch.WordTrace tailWord_2333170 prefixEnd_2333170 798691772433827796896635 := by
  unfold tailWord_2333170
  simp only [CollatzResearch.WordTrace]
  refine ⟨21274425239332759639249241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56731800638220692371331309 21274425239332759639249241)
  ·
    refine ⟨15955818929499569729436931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21274425239332759639249241 15955818929499569729436931)
    ·
      refine ⟨23933728394249354594155397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15955818929499569729436931 23933728394249354594155397)
      ·
        refine ⟨4487574073921753986404137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23933728394249354594155397 4487574073921753986404137)
        ·
          refine ⟨3365680555441315489803103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4487574073921753986404137 3365680555441315489803103)
          ·
            refine ⟨5048520833161973234704655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3365680555441315489803103 5048520833161973234704655)
            ·
              refine ⟨7572781249742959852056983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5048520833161973234704655 7572781249742959852056983)
              ·
                refine ⟨11359171874614439778085475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7572781249742959852056983 11359171874614439778085475)
                ·
                  refine ⟨17038757811921659667128213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11359171874614439778085475 17038757811921659667128213)
                  ·
                    refine ⟨798691772433827796896635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17038757811921659667128213 798691772433827796896635)
                    ·
                      rfl

theorem cell22_2333170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 1, 1, 6].length) (baseStart_2333170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2333170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2333170 prefixEnd_2333170 := by exact prefixLift 2333170
  have htrace : WordTrace (prefixWord ++ tailWord_2333170) baseStart_2333170 baseEnd_2333170 := by
    simpa [prefixWord, tailWord_2333170, baseEnd_2333170] using wordTrace_append hprefix tailTrace_2333170
  have hstable : (prefixWord ++ tailWord_2333170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2333170).length < 2 ^ (prefixWord ++ tailWord_2333170).sum := by decide
  have hdescent : baseEnd_2333170 < baseStart_2333170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2333170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2333183 : List Nat := [1, 1, 2, 2, 1, 2, 3, 2, 5, 3]
def baseStart_2333183 : Nat := 118140960795 + 2333183 * 2 ^ 59
def prefixEnd_2333183 : Nat := 4983230072969 + 3 ^ 40 * 2333183 * 2
def baseEnd_2333183 : Nat := 798696222599500096321595

theorem tailTrace_2333183 : CollatzResearch.WordTrace tailWord_2333183 prefixEnd_2333183 798696222599500096321595 := by
  unfold tailWord_2333183
  simp only [CollatzResearch.WordTrace]
  refine ⟨85098175106283941777220203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56732116737522627851480135 85098175106283941777220203)
  ·
    refine ⟨127647262659425912665830305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85098175106283941777220203 127647262659425912665830305)
    ·
      refine ⟨95735446994569434499372729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127647262659425912665830305 95735446994569434499372729)
      ·
        refine ⟨71801585245927075874529547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95735446994569434499372729 71801585245927075874529547)
        ·
          refine ⟨107702377868890613811794321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71801585245927075874529547 107702377868890613811794321)
          ·
            refine ⟨80776783401667960358845741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107702377868890613811794321 80776783401667960358845741)
            ·
              refine ⟨30291293775625485134567153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80776783401667960358845741 30291293775625485134567153)
              ·
                refine ⟨22718470331719113850925365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30291293775625485134567153 22718470331719113850925365)
                ·
                  refine ⟨2129856593598666923524253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22718470331719113850925365 2129856593598666923524253)
                  ·
                    refine ⟨798696222599500096321595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2129856593598666923524253 798696222599500096321595)
                    ·
                      rfl

theorem cell22_2333183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 5, 3].length) (baseStart_2333183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2333183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2333183 prefixEnd_2333183 := by exact prefixLift 2333183
  have htrace : WordTrace (prefixWord ++ tailWord_2333183) baseStart_2333183 baseEnd_2333183 := by
    simpa [prefixWord, tailWord_2333183, baseEnd_2333183] using wordTrace_append hprefix tailTrace_2333183
  have hstable : (prefixWord ++ tailWord_2333183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2333183).length < 2 ^ (prefixWord ++ tailWord_2333183).sum := by decide
  have hdescent : baseEnd_2333183 < baseStart_2333183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2333183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2333290 : List Nat := [3, 1, 3, 2, 1, 1, 3, 2, 1, 5]
def baseStart_2333290 : Nat := 118140960795 + 2333290 * 2 ^ 59
def prefixEnd_2333290 : Nat := 4983230072969 + 3 ^ 40 * 2333290 * 2
def baseEnd_2333290 : Nat := 798732850886187483896267

theorem tailTrace_2333290 : CollatzResearch.WordTrace tailWord_2333290 prefixEnd_2333290 798732850886187483896267 := by
  unfold tailWord_2333290
  simp only [CollatzResearch.WordTrace]
  refine ⟨21275519429224074762841331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56734718477930866034243549 21275519429224074762841331)
  ·
    refine ⟨31913279143836112144261997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21275519429224074762841331 31913279143836112144261997)
    ·
      refine ⟨11967479678938542054098249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31913279143836112144261997 11967479678938542054098249)
      ·
        refine ⟨8975609759203906540573687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11967479678938542054098249 8975609759203906540573687)
        ·
          refine ⟨13463414638805859810860531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8975609759203906540573687 13463414638805859810860531)
          ·
            refine ⟨20195121958208789716290797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13463414638805859810860531 20195121958208789716290797)
            ·
              refine ⟨7573170734328296143609049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20195121958208789716290797 7573170734328296143609049)
              ·
                refine ⟨5679878050746222107706787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7573170734328296143609049 5679878050746222107706787)
                ·
                  refine ⟨8519817076119333161560181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5679878050746222107706787 8519817076119333161560181)
                  ·
                    refine ⟨798732850886187483896267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8519817076119333161560181 798732850886187483896267)
                    ·
                      rfl

theorem cell22_2333290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_2333290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2333290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2333290 prefixEnd_2333290 := by exact prefixLift 2333290
  have htrace : WordTrace (prefixWord ++ tailWord_2333290) baseStart_2333290 baseEnd_2333290 := by
    simpa [prefixWord, tailWord_2333290, baseEnd_2333290] using wordTrace_append hprefix tailTrace_2333290
  have hstable : (prefixWord ++ tailWord_2333290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2333290).length < 2 ^ (prefixWord ++ tailWord_2333290).sum := by decide
  have hdescent : baseEnd_2333290 < baseStart_2333290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2333290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2333294 : List Nat := [4, 1, 2, 2, 2, 2, 3, 1, 1, 4]
def baseStart_2333294 : Nat := 118140960795 + 2333294 * 2 ^ 59
def prefixEnd_2333294 : Nat := 4983230072969 + 3 ^ 40 * 2333294 * 2
def baseEnd_2333294 : Nat := 798734220167932806796255

theorem tailTrace_2333294 : CollatzResearch.WordTrace tailWord_2333294 prefixEnd_2333294 798734220167932806796255 := by
  unfold tailWord_2333294
  simp only [CollatzResearch.WordTrace]
  refine ⟨10637777951110225966813867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56734815739254538489673957 10637777951110225966813867)
  ·
    refine ⟨15956666926665338950220801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10637777951110225966813867 15956666926665338950220801)
    ·
      refine ⟨11967500194999004212665601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15956666926665338950220801 11967500194999004212665601)
      ·
        refine ⟨8975625146249253159499201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11967500194999004212665601 8975625146249253159499201)
        ·
          refine ⟨6731718859686939869624401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8975625146249253159499201 6731718859686939869624401)
          ·
            refine ⟨5048789144765204902218301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6731718859686939869624401 5048789144765204902218301)
            ·
              refine ⟨1893295929286951838331863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5048789144765204902218301 1893295929286951838331863)
              ·
                refine ⟨2839943893930427757497795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1893295929286951838331863 2839943893930427757497795)
                ·
                  refine ⟨4259915840895641636246693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2839943893930427757497795 4259915840895641636246693)
                  ·
                    refine ⟨798734220167932806796255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4259915840895641636246693 798734220167932806796255)
                    ·
                      rfl

theorem cell22_2333294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 3, 1, 1, 4].length) (baseStart_2333294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2333294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2333294 prefixEnd_2333294 := by exact prefixLift 2333294
  have htrace : WordTrace (prefixWord ++ tailWord_2333294) baseStart_2333294 baseEnd_2333294 := by
    simpa [prefixWord, tailWord_2333294, baseEnd_2333294] using wordTrace_append hprefix tailTrace_2333294
  have hstable : (prefixWord ++ tailWord_2333294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2333294).length < 2 ^ (prefixWord ++ tailWord_2333294).sum := by decide
  have hdescent : baseEnd_2333294 < baseStart_2333294 := by decide
  rcases family_descends (prefixWord ++ tailWord_2333294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2333305 : List Nat := [1, 2, 1, 3, 3, 2, 2, 2, 2, 4]
def baseStart_2333305 : Nat := 118140960795 + 2333305 * 2 ^ 59
def prefixEnd_2333305 : Nat := 4983230072969 + 3 ^ 40 * 2333305 * 2
def baseEnd_2333305 : Nat := 798737985692732444771221

theorem tailTrace_2333305 : CollatzResearch.WordTrace tailWord_2333305 prefixEnd_2333305 798737985692732444771221 := by
  unfold tailWord_2333305
  simp only [CollatzResearch.WordTrace]
  refine ⟨85102624811841956613161369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56735083207894637742107579 85102624811841956613161369)
  ·
    refine ⟨63826968608881467459871027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85102624811841956613161369 63826968608881467459871027)
    ·
      refine ⟨95740452913322201189806541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63826968608881467459871027 95740452913322201189806541)
      ·
        refine ⟨35902669842495825446177453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95740452913322201189806541 35902669842495825446177453)
        ·
          refine ⟨13463501190935934542316545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35902669842495825446177453 13463501190935934542316545)
          ·
            refine ⟨10097625893201950906737409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13463501190935934542316545 10097625893201950906737409)
            ·
              refine ⟨7573219419901463180053057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10097625893201950906737409 7573219419901463180053057)
              ·
                refine ⟨5679914564926097385039793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7573219419901463180053057 5679914564926097385039793)
                ·
                  refine ⟨4259935923694573038779845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5679914564926097385039793 4259935923694573038779845)
                  ·
                    refine ⟨798737985692732444771221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4259935923694573038779845 798737985692732444771221)
                    ·
                      rfl

theorem cell22_2333305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 2, 2, 4].length) (baseStart_2333305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2333305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2333305 prefixEnd_2333305 := by exact prefixLift 2333305
  have htrace : WordTrace (prefixWord ++ tailWord_2333305) baseStart_2333305 baseEnd_2333305 := by
    simpa [prefixWord, tailWord_2333305, baseEnd_2333305] using wordTrace_append hprefix tailTrace_2333305
  have hstable : (prefixWord ++ tailWord_2333305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2333305).length < 2 ^ (prefixWord ++ tailWord_2333305).sum := by decide
  have hdescent : baseEnd_2333305 < baseStart_2333305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2333305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2333412 : List Nat := [2, 3, 1, 1, 1, 4, 2, 3, 1, 4]
def baseStart_2333412 : Nat := 118140960795 + 2333412 * 2 ^ 59
def prefixEnd_2333412 : Nat := 4983230072969 + 3 ^ 40 * 2333412 * 2
def baseEnd_2333412 : Nat := 798774613979419832345893

theorem tailTrace_2333412 : CollatzResearch.WordTrace tailWord_2333412 prefixEnd_2333412 798774613979419832345893 := by
  unfold tailWord_2333412
  simp only [CollatzResearch.WordTrace]
  refine ⟨42553263711227156943653245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56737684948302875924870993 42553263711227156943653245)
  ·
    refine ⟨15957473891710183853869967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42553263711227156943653245 15957473891710183853869967)
    ·
      refine ⟨23936210837565275780804951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15957473891710183853869967 23936210837565275780804951)
      ·
        refine ⟨35904316256347913671207427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23936210837565275780804951 35904316256347913671207427)
        ·
          refine ⟨53856474384521870506811141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35904316256347913671207427 53856474384521870506811141)
          ·
            refine ⟨10098088947097850720027089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53856474384521870506811141 10098088947097850720027089)
            ·
              refine ⟨7573566710323388040020317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10098088947097850720027089 7573566710323388040020317)
              ·
                refine ⟨2840087516371270515007619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7573566710323388040020317 2840087516371270515007619)
                ·
                  refine ⟨4260131274556905772511429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2840087516371270515007619 4260131274556905772511429)
                  ·
                    refine ⟨798774613979419832345893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4260131274556905772511429 798774613979419832345893)
                    ·
                      rfl

theorem cell22_2333412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 3, 1, 4].length) (baseStart_2333412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2333412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2333412 prefixEnd_2333412 := by exact prefixLift 2333412
  have htrace : WordTrace (prefixWord ++ tailWord_2333412) baseStart_2333412 baseEnd_2333412 := by
    simpa [prefixWord, tailWord_2333412, baseEnd_2333412] using wordTrace_append hprefix tailTrace_2333412
  have hstable : (prefixWord ++ tailWord_2333412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2333412).length < 2 ^ (prefixWord ++ tailWord_2333412).sum := by decide
  have hdescent : baseEnd_2333412 < baseStart_2333412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2333412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2333476 : List Nat := [2, 3, 1, 3, 3, 1, 2, 2, 2, 3]
def baseStart_2333476 : Nat := 118140960795 + 2333476 * 2 ^ 59
def prefixEnd_2333476 : Nat := 4983230072969 + 3 ^ 40 * 2333476 * 2
def baseEnd_2333476 : Nat := 798796522487344998745697

theorem tailTrace_2333476 : CollatzResearch.WordTrace tailWord_2333476 prefixEnd_2333476 798796522487344998745697 := by
  unfold tailWord_2333476
  simp only [CollatzResearch.WordTrace]
  refine ⟨42554430847111226408818141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56739241129481635211757521 42554430847111226408818141)
  ·
    refine ⟨15957911567666709903306803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42554430847111226408818141 15957911567666709903306803)
    ·
      refine ⟨23936867351500064854960205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15957911567666709903306803 23936867351500064854960205)
      ·
        refine ⟨8976325256812524320610077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23936867351500064854960205 8976325256812524320610077)
        ·
          refine ⟨3366121971304696620228779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8976325256812524320610077 3366121971304696620228779)
          ·
            refine ⟨5049182956957044930343169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3366121971304696620228779 5049182956957044930343169)
            ·
              refine ⟨3786887217717783697757377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5049182956957044930343169 3786887217717783697757377)
              ·
                refine ⟨2840165413288337773318033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3786887217717783697757377 2840165413288337773318033)
                ·
                  refine ⟨2130124059966253329988525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2840165413288337773318033 2130124059966253329988525)
                  ·
                    refine ⟨798796522487344998745697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2130124059966253329988525 798796522487344998745697)
                    ·
                      rfl

theorem cell22_2333476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 2, 2, 3].length) (baseStart_2333476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2333476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2333476 prefixEnd_2333476 := by exact prefixLift 2333476
  have htrace : WordTrace (prefixWord ++ tailWord_2333476) baseStart_2333476 baseEnd_2333476 := by
    simpa [prefixWord, tailWord_2333476, baseEnd_2333476] using wordTrace_append hprefix tailTrace_2333476
  have hstable : (prefixWord ++ tailWord_2333476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2333476).length < 2 ^ (prefixWord ++ tailWord_2333476).sum := by decide
  have hdescent : baseEnd_2333476 < baseStart_2333476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2333476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2333500 : List Nat := [2, 2, 2, 2, 1, 1, 1, 2, 9]
def baseStart_2333500 : Nat := 118140960795 + 2333500 * 2 ^ 59
def prefixEnd_2333500 : Nat := 4983230072969 + 3 ^ 40 * 2333500 * 2
def baseEnd_2333500 : Nat := 266268246059272312048541

theorem tailTrace_2333500 : CollatzResearch.WordTrace tailWord_2333500 prefixEnd_2333500 266268246059272312048541 := by
  unfold tailWord_2333500
  simp only [CollatzResearch.WordTrace]
  refine ⟨42554868523067752458254977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56739824697423669944339969 42554868523067752458254977)
  ·
    refine ⟨31916151392300814343691233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42554868523067752458254977 31916151392300814343691233)
    ·
      refine ⟨23937113544225610757768425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31916151392300814343691233 23937113544225610757768425)
      ·
        refine ⟨17952835158169208068326319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23937113544225610757768425 17952835158169208068326319)
        ·
          refine ⟨26929252737253812102489479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17952835158169208068326319 26929252737253812102489479)
          ·
            refine ⟨40393879105880718153734219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26929252737253812102489479 40393879105880718153734219)
            ·
              refine ⟨60590818658821077230601329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40393879105880718153734219 60590818658821077230601329)
              ·
                refine ⟨45443113994115807922950997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60590818658821077230601329 45443113994115807922950997)
                ·
                  refine ⟨266268246059272312048541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 45443113994115807922950997 266268246059272312048541)
                  ·
                    rfl

theorem cell22_2333500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 9].length) (baseStart_2333500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2333500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2333500 prefixEnd_2333500 := by exact prefixLift 2333500
  have htrace : WordTrace (prefixWord ++ tailWord_2333500) baseStart_2333500 baseEnd_2333500 := by
    simpa [prefixWord, tailWord_2333500, baseEnd_2333500] using wordTrace_append hprefix tailTrace_2333500
  have hstable : (prefixWord ++ tailWord_2333500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2333500).length < 2 ^ (prefixWord ++ tailWord_2333500).sum := by decide
  have hdescent : baseEnd_2333500 < baseStart_2333500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2333500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2333508 : List Nat := [2, 3, 4, 2, 1, 2, 1, 1, 2, 4]
def baseStart_2333508 : Nat := 118140960795 + 2333508 * 2 ^ 59
def prefixEnd_2333508 : Nat := 4983230072969 + 3 ^ 40 * 2333508 * 2
def baseEnd_2333508 : Nat := 798807476741307581945599

theorem tailTrace_2333508 : CollatzResearch.WordTrace tailWord_2333508 prefixEnd_2333508 798807476741307581945599 := by
  unfold tailWord_2333508
  simp only [CollatzResearch.WordTrace]
  refine ⟨42555014415053261141400589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56740019220071014855200785 42555014415053261141400589)
  ·
    refine ⟨15958130405644972928025221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42555014415053261141400589 15958130405644972928025221)
    ·
      refine ⟨2992149451058432424004729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15958130405644972928025221 2992149451058432424004729)
      ·
        refine ⟨2244112088293824318003547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2992149451058432424004729 2244112088293824318003547)
        ·
          refine ⟨3366168132440736477005321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2244112088293824318003547 3366168132440736477005321)
          ·
            refine ⟨2524626099330552357753991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3366168132440736477005321 2524626099330552357753991)
            ·
              refine ⟨3786939148995828536630987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2524626099330552357753991 3786939148995828536630987)
              ·
                refine ⟨5680408723493742804946481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3786939148995828536630987 5680408723493742804946481)
                ·
                  refine ⟨4260306542620307103709861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5680408723493742804946481 4260306542620307103709861)
                  ·
                    refine ⟨798807476741307581945599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4260306542620307103709861 798807476741307581945599)
                    ·
                      rfl

theorem cell22_2333508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_2333508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2333508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2333508 prefixEnd_2333508 := by exact prefixLift 2333508
  have htrace : WordTrace (prefixWord ++ tailWord_2333508) baseStart_2333508 baseEnd_2333508 := by
    simpa [prefixWord, tailWord_2333508, baseEnd_2333508] using wordTrace_append hprefix tailTrace_2333508
  have hstable : (prefixWord ++ tailWord_2333508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2333508).length < 2 ^ (prefixWord ++ tailWord_2333508).sum := by decide
  have hdescent : baseEnd_2333508 < baseStart_2333508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2333508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2333579 : List Nat := [1, 1, 1, 1, 4, 2, 5, 3, 4]
def baseStart_2333579 : Nat := 118140960795 + 2333579 * 2 ^ 59
def prefixEnd_2333579 : Nat := 4983230072969 + 3 ^ 40 * 2333579 * 2
def baseEnd_2333579 : Nat := 266277260497429021140127

theorem tailTrace_2333579 : CollatzResearch.WordTrace tailWord_2333579 prefixEnd_2333579 266277260497429021140127 := by
  unfold tailWord_2333579
  simp only [CollatzResearch.WordTrace]
  refine ⟨85112618412849301408635791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56741745608566200939090527 85112618412849301408635791)
  ·
    refine ⟨127668927619273952112953687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85112618412849301408635791 127668927619273952112953687)
    ·
      refine ⟨191503391428910928169430531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127668927619273952112953687 191503391428910928169430531)
      ·
        refine ⟨287255087143366392254145797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191503391428910928169430531 287255087143366392254145797)
        ·
          refine ⟨53860328839381198547652337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 287255087143366392254145797 53860328839381198547652337)
          ·
            refine ⟨40395246629535898910739253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53860328839381198547652337 40395246629535898910739253)
            ·
              refine ⟨3787054371518990522881805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40395246629535898910739253 3787054371518990522881805)
              ·
                refine ⟨1420145389319621446080677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3787054371518990522881805 1420145389319621446080677)
                ·
                  refine ⟨266277260497429021140127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1420145389319621446080677 266277260497429021140127)
                  ·
                    rfl

theorem cell22_2333579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 3, 4].length) (baseStart_2333579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2333579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2333579 prefixEnd_2333579 := by exact prefixLift 2333579
  have htrace : WordTrace (prefixWord ++ tailWord_2333579) baseStart_2333579 baseEnd_2333579 := by
    simpa [prefixWord, tailWord_2333579, baseEnd_2333579] using wordTrace_append hprefix tailTrace_2333579
  have hstable : (prefixWord ++ tailWord_2333579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2333579).length < 2 ^ (prefixWord ++ tailWord_2333579).sum := by decide
  have hdescent : baseEnd_2333579 < baseStart_2333579 := by decide
  rcases family_descends (prefixWord ++ tailWord_2333579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2333596 : List Nat := [2, 2, 3, 3, 2, 2, 1, 1, 6]
def baseStart_2333596 : Nat := 118140960795 + 2333596 * 2 ^ 59
def prefixEnd_2333596 : Nat := 4983230072969 + 3 ^ 40 * 2333596 * 2
def baseEnd_2333596 : Nat := 266279200313234895248443

theorem tailTrace_2333596 : CollatzResearch.WordTrace tailWord_2333596 prefixEnd_2333596 266279200313234895248443 := by
  unfold tailWord_2333596
  simp only [CollatzResearch.WordTrace]
  refine ⟨42556619226893856656002321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56742158969191808874669761 42556619226893856656002321)
  ·
    refine ⟨31917464420170392492001741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42556619226893856656002321 31917464420170392492001741)
    ·
      refine ⟨11969049157563897184500653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31917464420170392492001741 11969049157563897184500653)
      ·
        refine ⟨4488393434086461444187745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11969049157563897184500653 4488393434086461444187745)
        ·
          refine ⟨3366295075564846083140809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4488393434086461444187745 3366295075564846083140809)
          ·
            refine ⟨2524721306673634562355607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3366295075564846083140809 2524721306673634562355607)
            ·
              refine ⟨3787081960010451843533411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2524721306673634562355607 3787081960010451843533411)
              ·
                refine ⟨5680622940015677765300117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3787081960010451843533411 5680622940015677765300117)
                ·
                  refine ⟨266279200313234895248443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5680622940015677765300117 266279200313234895248443)
                  ·
                    rfl

theorem cell22_2333596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 1, 6].length) (baseStart_2333596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2333596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2333596 prefixEnd_2333596 := by exact prefixLift 2333596
  have htrace : WordTrace (prefixWord ++ tailWord_2333596) baseStart_2333596 baseEnd_2333596 := by
    simpa [prefixWord, tailWord_2333596, baseEnd_2333596] using wordTrace_append hprefix tailTrace_2333596
  have hstable : (prefixWord ++ tailWord_2333596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2333596).length < 2 ^ (prefixWord ++ tailWord_2333596).sum := by decide
  have hdescent : baseEnd_2333596 < baseStart_2333596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2333596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2333744 : List Nat := [2, 1, 1, 1, 2, 4, 2, 3, 2, 4]
def baseStart_2333744 : Nat := 118140960795 + 2333744 * 2 ^ 59
def prefixEnd_2333744 : Nat := 4983230072969 + 3 ^ 40 * 2333744 * 2
def baseEnd_2333744 : Nat := 798888264364281633044875

theorem tailTrace_2333744 : CollatzResearch.WordTrace tailWord_2333744 prefixEnd_2333744 798888264364281633044875 := by
  unfold tailWord_2333744
  simp only [CollatzResearch.WordTrace]
  refine ⟨42559318228625767294196143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56745757638167689725594857 42559318228625767294196143)
  ·
    refine ⟨63838977342938650941294215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42559318228625767294196143 63838977342938650941294215)
    ·
      refine ⟨95758466014407976411941323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63838977342938650941294215 95758466014407976411941323)
      ·
        refine ⟨143637699021611964617911985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95758466014407976411941323 143637699021611964617911985)
        ·
          refine ⟨107728274266208973463433989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143637699021611964617911985 107728274266208973463433989)
          ·
            refine ⟨20199051424914182524393873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 107728274266208973463433989 20199051424914182524393873)
            ·
              refine ⟨15149288568685636893295405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20199051424914182524393873 15149288568685636893295405)
              ·
                refine ⟨5680983213257113834985777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15149288568685636893295405 5680983213257113834985777)
                ·
                  refine ⟨4260737409942835376239333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5680983213257113834985777 4260737409942835376239333)
                  ·
                    refine ⟨798888264364281633044875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4260737409942835376239333 798888264364281633044875)
                    ·
                      rfl

theorem cell22_2333744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 3, 2, 4].length) (baseStart_2333744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2333744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2333744 prefixEnd_2333744 := by exact prefixLift 2333744
  have htrace : WordTrace (prefixWord ++ tailWord_2333744) baseStart_2333744 baseEnd_2333744 := by
    simpa [prefixWord, tailWord_2333744, baseEnd_2333744] using wordTrace_append hprefix tailTrace_2333744
  have hstable : (prefixWord ++ tailWord_2333744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2333744).length < 2 ^ (prefixWord ++ tailWord_2333744).sum := by decide
  have hdescent : baseEnd_2333744 < baseStart_2333744 := by decide
  rcases family_descends (prefixWord ++ tailWord_2333744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2333808 : List Nat := [2, 1, 1, 1, 5, 1, 2, 5, 1, 3]
def baseStart_2333808 : Nat := 118140960795 + 2333808 * 2 ^ 59
def prefixEnd_2333808 : Nat := 4983230072969 + 3 ^ 40 * 2333808 * 2
def baseEnd_2333808 : Nat := 798910172872206799444679

theorem tailTrace_2333808 : CollatzResearch.WordTrace tailWord_2333808 prefixEnd_2333808 798910172872206799444679 := by
  unfold tailWord_2333808
  simp only [CollatzResearch.WordTrace]
  refine ⟨42560485364509836759361039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56747313819346449012481385 42560485364509836759361039)
  ·
    refine ⟨63840728046764755139041559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42560485364509836759361039 63840728046764755139041559)
    ·
      refine ⟨95761092070147132708562339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63840728046764755139041559 95761092070147132708562339)
      ·
        refine ⟨143641638105220699062843509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95761092070147132708562339 143641638105220699062843509)
        ·
          refine ⟨13466403572364440537141579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 143641638105220699062843509 13466403572364440537141579)
          ·
            refine ⟨20199605358546660805712369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13466403572364440537141579 20199605358546660805712369)
            ·
              refine ⟨15149704018909995604284277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20199605358546660805712369 15149704018909995604284277)
              ·
                refine ⟨1420284751772812087901651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15149704018909995604284277 1420284751772812087901651)
                ·
                  refine ⟨2130427127659218131852477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1420284751772812087901651 2130427127659218131852477)
                  ·
                    refine ⟨798910172872206799444679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2130427127659218131852477 798910172872206799444679)
                    ·
                      rfl

theorem cell22_2333808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 5, 1, 3].length) (baseStart_2333808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2333808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2333808 prefixEnd_2333808 := by exact prefixLift 2333808
  have htrace : WordTrace (prefixWord ++ tailWord_2333808) baseStart_2333808 baseEnd_2333808 := by
    simpa [prefixWord, tailWord_2333808, baseEnd_2333808] using wordTrace_append hprefix tailTrace_2333808
  have hstable : (prefixWord ++ tailWord_2333808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2333808).length < 2 ^ (prefixWord ++ tailWord_2333808).sum := by decide
  have hdescent : baseEnd_2333808 < baseStart_2333808 := by decide
  rcases family_descends (prefixWord ++ tailWord_2333808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2333821 : List Nat := [1, 4, 1, 1, 3, 1, 4, 2, 5]
def baseStart_2333821 : Nat := 118140960795 + 2333821 * 2 ^ 59
def prefixEnd_2333821 : Nat := 4983230072969 + 3 ^ 40 * 2333821 * 2
def baseEnd_2333821 : Nat := 266304874345959699623213

theorem tailTrace_2333821 : CollatzResearch.WordTrace tailWord_2333821 prefixEnd_2333821 266304874345959699623213 := by
  unfold tailWord_2333821
  simp only [CollatzResearch.WordTrace]
  refine ⟨85121444877972576738945317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56747629918648384492630211 85121444877972576738945317)
  ·
    refine ⟨15960270914619858138552247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85121444877972576738945317 15960270914619858138552247)
    ·
      refine ⟨23940406371929787207828371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15960270914619858138552247 23940406371929787207828371)
      ·
        refine ⟨35910609557894680811742557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23940406371929787207828371 35910609557894680811742557)
        ·
          refine ⟨13466478584210505304403459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35910609557894680811742557 13466478584210505304403459)
          ·
            refine ⟨20199717876315757956605189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13466478584210505304403459 20199717876315757956605189)
            ·
              refine ⟨3787447101809204616863473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20199717876315757956605189 3787447101809204616863473)
              ·
                refine ⟨2840585326356903462647605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3787447101809204616863473 2840585326356903462647605)
                ·
                  refine ⟨266304874345959699623213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2840585326356903462647605 266304874345959699623213)
                  ·
                    rfl

theorem cell22_2333821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 2, 5].length) (baseStart_2333821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2333821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2333821 prefixEnd_2333821 := by exact prefixLift 2333821
  have htrace : WordTrace (prefixWord ++ tailWord_2333821) baseStart_2333821 baseEnd_2333821 := by
    simpa [prefixWord, tailWord_2333821, baseEnd_2333821] using wordTrace_append hprefix tailTrace_2333821
  have hstable : (prefixWord ++ tailWord_2333821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2333821).length < 2 ^ (prefixWord ++ tailWord_2333821).sum := by decide
  have hdescent : baseEnd_2333821 < baseStart_2333821 := by decide
  rcases family_descends (prefixWord ++ tailWord_2333821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2333825 : List Nat := [1, 2, 4, 2, 2, 2, 1, 4, 1, 3]
def baseStart_2333825 : Nat := 118140960795 + 2333825 * 2 ^ 59
def prefixEnd_2333825 : Nat := 4983230072969 + 3 ^ 40 * 2333825 * 2
def baseEnd_2333825 : Nat := 798915992319624421769627

theorem tailTrace_2333825 : CollatzResearch.WordTrace tailWord_2333825 prefixEnd_2333825 798915992319624421769627 := by
  unfold tailWord_2333825
  simp only [CollatzResearch.WordTrace]
  refine ⟨85121590769958085422090929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56747727179972056948060619 85121590769958085422090929)
  ·
    refine ⟨63841193077468564066568197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85121590769958085422090929 63841193077468564066568197)
    ·
      refine ⟨11970223702025355762481537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63841193077468564066568197 11970223702025355762481537)
      ·
        refine ⟨8977667776519016821861153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11970223702025355762481537 8977667776519016821861153)
        ·
          refine ⟨6733250832389262616395865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8977667776519016821861153 6733250832389262616395865)
          ·
            refine ⟨5049938124291946962296899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6733250832389262616395865 5049938124291946962296899)
            ·
              refine ⟨7574907186437920443445349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5049938124291946962296899 7574907186437920443445349)
              ·
                refine ⟨1420295097457110083146003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7574907186437920443445349 1420295097457110083146003)
                ·
                  refine ⟨2130442646185665124719005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1420295097457110083146003 2130442646185665124719005)
                  ·
                    refine ⟨798915992319624421769627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2130442646185665124719005 798915992319624421769627)
                    ·
                      rfl

theorem cell22_2333825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 4, 1, 3].length) (baseStart_2333825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2333825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2333825 prefixEnd_2333825 := by exact prefixLift 2333825
  have htrace : WordTrace (prefixWord ++ tailWord_2333825) baseStart_2333825 baseEnd_2333825 := by
    simpa [prefixWord, tailWord_2333825, baseEnd_2333825] using wordTrace_append hprefix tailTrace_2333825
  have hstable : (prefixWord ++ tailWord_2333825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2333825).length < 2 ^ (prefixWord ++ tailWord_2333825).sum := by decide
  have hdescent : baseEnd_2333825 < baseStart_2333825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2333825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2333898 : List Nat := [3, 1, 2, 1, 3, 4, 1, 1, 1, 5]
def baseStart_2333898 : Nat := 118140960795 + 2333898 * 2 ^ 59
def prefixEnd_2333898 : Nat := 4983230072969 + 3 ^ 40 * 2333898 * 2
def baseEnd_2333898 : Nat := 798940981711476564694403

theorem tailTrace_2333898 : CollatzResearch.WordTrace tailWord_2333898 prefixEnd_2333898 798940981711476564694403 := by
  unfold tailWord_2333898
  simp only [CollatzResearch.WordTrace]
  refine ⟨21281063324673404722374587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56749502199129079259665565 21281063324673404722374587)
  ·
    refine ⟨31921594987010107083561881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21281063324673404722374587 31921594987010107083561881)
    ·
      refine ⟨23941196240257580312671411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31921594987010107083561881 23941196240257580312671411)
      ·
        refine ⟨35911794360386370469007117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23941196240257580312671411 35911794360386370469007117)
        ·
          refine ⟨13466922885144888925877669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35911794360386370469007117 13466922885144888925877669)
          ·
            refine ⟨2525048040964666673602063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13466922885144888925877669 2525048040964666673602063)
            ·
              refine ⟨3787572061447000010403095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2525048040964666673602063 3787572061447000010403095)
              ·
                refine ⟨5681358092170500015604643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3787572061447000010403095 5681358092170500015604643)
                ·
                  refine ⟨8522037138255750023406965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5681358092170500015604643 8522037138255750023406965)
                  ·
                    refine ⟨798940981711476564694403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8522037138255750023406965 798940981711476564694403)
                    ·
                      rfl

theorem cell22_2333898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 1, 1, 5].length) (baseStart_2333898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2333898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2333898 prefixEnd_2333898 := by exact prefixLift 2333898
  have htrace : WordTrace (prefixWord ++ tailWord_2333898) baseStart_2333898 baseEnd_2333898 := by
    simpa [prefixWord, tailWord_2333898, baseEnd_2333898] using wordTrace_append hprefix tailTrace_2333898
  have hstable : (prefixWord ++ tailWord_2333898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2333898).length < 2 ^ (prefixWord ++ tailWord_2333898).sum := by decide
  have hdescent : baseEnd_2333898 < baseStart_2333898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2333898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2333911 : List Nat := [1, 1, 3, 2, 1, 2, 6, 6]
def baseStart_2333911 : Nat := 118140960795 + 2333911 * 2 ^ 59
def prefixEnd_2333911 : Nat := 4983230072969 + 3 ^ 40 * 2333911 * 2
def baseEnd_2333911 : Nat := 88771714653016540457707

theorem tailTrace_2333911 : CollatzResearch.WordTrace tailWord_2333911 prefixEnd_2333911 88771714653016540457707 := by
  unfold tailWord_2333911
  simp only [CollatzResearch.WordTrace]
  refine ⟨85124727447646522109721587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56749818298431014739814391 85124727447646522109721587)
  ·
    refine ⟨127687091171469783164582381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85124727447646522109721587 127687091171469783164582381)
    ·
      refine ⟨47882659189301168686718393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127687091171469783164582381 47882659189301168686718393)
      ·
        refine ⟨35911994391975876515038795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47882659189301168686718393 35911994391975876515038795)
        ·
          refine ⟨53867991587963814772558193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35911994391975876515038795 53867991587963814772558193)
          ·
            refine ⟨40400993690972861079418645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53867991587963814772558193 40400993690972861079418645)
            ·
              refine ⟨1893796579264352863097749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 40400993690972861079418645 1893796579264352863097749)
              ·
                refine ⟨88771714653016540457707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1893796579264352863097749 88771714653016540457707)
                ·
                  rfl

theorem cell22_2333911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 6, 6].length) (baseStart_2333911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2333911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2333911 prefixEnd_2333911 := by exact prefixLift 2333911
  have htrace : WordTrace (prefixWord ++ tailWord_2333911) baseStart_2333911 baseEnd_2333911 := by
    simpa [prefixWord, tailWord_2333911, baseEnd_2333911] using wordTrace_append hprefix tailTrace_2333911
  have hstable : (prefixWord ++ tailWord_2333911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2333911).length < 2 ^ (prefixWord ++ tailWord_2333911).sum := by decide
  have hdescent : baseEnd_2333911 < baseStart_2333911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2333911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2333917 : List Nat := [1, 4, 3, 2, 2, 2, 1, 3, 4]
def baseStart_2333917 : Nat := 118140960795 + 2333917 * 2 ^ 59
def prefixEnd_2333917 : Nat := 4983230072969 + 3 ^ 40 * 2333917 * 2
def baseEnd_2333917 : Nat := 266315828599922282823115

theorem tailTrace_2333917 : CollatzResearch.WordTrace tailWord_2333917 prefixEnd_2333917 266315828599922282823115 := by
  unfold tailWord_2333917
  simp only [CollatzResearch.WordTrace]
  refine ⟨85124946285624785134440005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56749964190416523422960003 85124946285624785134440005)
  ·
    refine ⟨15960927428554647212707501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85124946285624785134440005 15960927428554647212707501)
    ·
      refine ⟨5985347785707992704765313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15960927428554647212707501 5985347785707992704765313)
      ·
        refine ⟨4489010839280994528573985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5985347785707992704765313 4489010839280994528573985)
        ·
          refine ⟨3366758129460745896430489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4489010839280994528573985 3366758129460745896430489)
          ·
            refine ⟨2525068597095559422322867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3366758129460745896430489 2525068597095559422322867)
            ·
              refine ⟨3787602895643339133484301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2525068597095559422322867 3787602895643339133484301)
              ·
                refine ⟨1420351085866252175056613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3787602895643339133484301 1420351085866252175056613)
                ·
                  refine ⟨266315828599922282823115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1420351085866252175056613 266315828599922282823115)
                  ·
                    rfl

theorem cell22_2333917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 3, 4].length) (baseStart_2333917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2333917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2333917 prefixEnd_2333917 := by exact prefixLift 2333917
  have htrace : WordTrace (prefixWord ++ tailWord_2333917) baseStart_2333917 baseEnd_2333917 := by
    simpa [prefixWord, tailWord_2333917, baseEnd_2333917] using wordTrace_append hprefix tailTrace_2333917
  have hstable : (prefixWord ++ tailWord_2333917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2333917).length < 2 ^ (prefixWord ++ tailWord_2333917).sum := by decide
  have hdescent : baseEnd_2333917 < baseStart_2333917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2333917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2333994 : List Nat := [3, 1, 4, 2, 1, 1, 4, 2, 1, 3]
def baseStart_2333994 : Nat := 118140960795 + 2333994 * 2 ^ 59
def prefixEnd_2333994 : Nat := 4983230072969 + 3 ^ 40 * 2333994 * 2
def baseEnd_2333994 : Nat := 798973844473364314294109

theorem tailTrace_2333994 : CollatzResearch.WordTrace tailWord_2333994 prefixEnd_2333994 798973844473364314294109 := by
  unfold tailWord_2333994
  simp only [CollatzResearch.WordTrace]
  refine ⟨21281938676586456821248259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56751836470897218189995357 21281938676586456821248259)
  ·
    refine ⟨31922908014879685231872389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21281938676586456821248259 31922908014879685231872389)
    ·
      refine ⟨5985545252789940980976073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31922908014879685231872389 5985545252789940980976073)
      ·
        refine ⟨4489158939592455735732055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5985545252789940980976073 4489158939592455735732055)
        ·
          refine ⟨6733738409388683603598083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4489158939592455735732055 6733738409388683603598083)
          ·
            refine ⟨10100607614083025405397125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6733738409388683603598083 10100607614083025405397125)
            ·
              refine ⟨1893863927640567263511961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10100607614083025405397125 1893863927640567263511961)
              ·
                refine ⟨1420397945730425447633971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1893863927640567263511961 1420397945730425447633971)
                ·
                  refine ⟨2130596918595638171450957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1420397945730425447633971 2130596918595638171450957)
                  ·
                    refine ⟨798973844473364314294109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2130596918595638171450957 798973844473364314294109)
                    ·
                      rfl

theorem cell22_2333994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_2333994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2333994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2333994 prefixEnd_2333994 := by exact prefixLift 2333994
  have htrace : WordTrace (prefixWord ++ tailWord_2333994) baseStart_2333994 baseEnd_2333994 := by
    simpa [prefixWord, tailWord_2333994, baseEnd_2333994] using wordTrace_append hprefix tailTrace_2333994
  have hstable : (prefixWord ++ tailWord_2333994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2333994).length < 2 ^ (prefixWord ++ tailWord_2333994).sum := by decide
  have hdescent : baseEnd_2333994 < baseStart_2333994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2333994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2334020 : List Nat := [2, 3, 4, 1, 1, 1, 2, 1, 3, 4]
def baseStart_2334020 : Nat := 118140960795 + 2334020 * 2 ^ 59
def prefixEnd_2334020 : Nat := 4983230072969 + 3 ^ 40 * 2334020 * 2
def baseEnd_2334020 : Nat := 798982744804708913144029

theorem tailTrace_2334020 : CollatzResearch.WordTrace tailWord_2334020 prefixEnd_2334020 798982744804708913144029 := by
  unfold tailWord_2334020
  simp only [CollatzResearch.WordTrace]
  refine ⟨42564351502125816862719757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56752468669501089150293009 42564351502125816862719757)
  ·
    refine ⟨15961631813297181323519909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42564351502125816862719757 15961631813297181323519909)
    ·
      refine ⟨2992805964993221498159983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15961631813297181323519909 2992805964993221498159983)
      ·
        refine ⟨4489208947489832247239975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2992805964993221498159983 4489208947489832247239975)
        ·
          refine ⟨6733813421234748370859963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4489208947489832247239975 6733813421234748370859963)
          ·
            refine ⟨10100720131852122556289945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6733813421234748370859963 10100720131852122556289945)
            ·
              refine ⟨7575540098889091917217459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10100720131852122556289945 7575540098889091917217459)
              ·
                refine ⟨11363310148333637875826189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7575540098889091917217459 11363310148333637875826189)
                ·
                  refine ⟨4261241305625114203434821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11363310148333637875826189 4261241305625114203434821)
                  ·
                    refine ⟨798982744804708913144029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4261241305625114203434821 798982744804708913144029)
                    ·
                      rfl

theorem cell22_2334020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_2334020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2334020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2334020 prefixEnd_2334020 := by exact prefixLift 2334020
  have htrace : WordTrace (prefixWord ++ tailWord_2334020) baseStart_2334020 baseEnd_2334020 := by
    simpa [prefixWord, tailWord_2334020, baseEnd_2334020] using wordTrace_append hprefix tailTrace_2334020
  have hstable : (prefixWord ++ tailWord_2334020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2334020).length < 2 ^ (prefixWord ++ tailWord_2334020).sum := by decide
  have hdescent : baseEnd_2334020 < baseStart_2334020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2334020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2334033 : List Nat := [1, 2, 2, 1, 4, 1, 2, 2, 4, 3]
def baseStart_2334033 : Nat := 118140960795 + 2334033 * 2 ^ 59
def prefixEnd_2334033 : Nat := 4983230072969 + 3 ^ 40 * 2334033 * 2
def baseEnd_2334033 : Nat := 798987194970381212568989

theorem tailTrace_2334033 : CollatzResearch.WordTrace tailWord_2334033 prefixEnd_2334033 798987194970381212568989 := by
  unfold tailWord_2334033
  simp only [CollatzResearch.WordTrace]
  refine ⟨85129177153204536945662753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56752784768803024630441835 85129177153204536945662753)
  ·
    refine ⟨63846882864903402709247065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85129177153204536945662753 63846882864903402709247065)
    ·
      refine ⟨47885162148677552031935299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63846882864903402709247065 47885162148677552031935299)
      ·
        refine ⟨71827743223016328047902949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47885162148677552031935299 71827743223016328047902949)
        ·
          refine ⟨13467701854315561508981803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71827743223016328047902949 13467701854315561508981803)
          ·
            refine ⟨20201552781473342263472705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13467701854315561508981803 20201552781473342263472705)
            ·
              refine ⟨15151164586105006697604529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20201552781473342263472705 15151164586105006697604529)
              ·
                refine ⟨11363373439578755023203397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15151164586105006697604529 11363373439578755023203397)
                ·
                  refine ⟨2130632519921016566850637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11363373439578755023203397 2130632519921016566850637)
                  ·
                    refine ⟨798987194970381212568989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2130632519921016566850637 798987194970381212568989)
                    ·
                      rfl

theorem cell22_2334033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 2, 4, 3].length) (baseStart_2334033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2334033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2334033 prefixEnd_2334033 := by exact prefixLift 2334033
  have htrace : WordTrace (prefixWord ++ tailWord_2334033) baseStart_2334033 baseEnd_2334033 := by
    simpa [prefixWord, tailWord_2334033, baseEnd_2334033] using wordTrace_append hprefix tailTrace_2334033
  have hstable : (prefixWord ++ tailWord_2334033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2334033).length < 2 ^ (prefixWord ++ tailWord_2334033).sum := by decide
  have hdescent : baseEnd_2334033 < baseStart_2334033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2334033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2334037 : List Nat := [1, 3, 2, 2, 3, 3, 2, 1, 1, 4]
def baseStart_2334037 : Nat := 118140960795 + 2334037 * 2 ^ 59
def prefixEnd_2334037 : Nat := 4983230072969 + 3 ^ 40 * 2334037 * 2
def baseEnd_2334037 : Nat := 798988564252126535468977

theorem tailTrace_2334037 : CollatzResearch.WordTrace tailWord_2334037 prefixEnd_2334037 798988564252126535468977 := by
  unfold tailWord_2334037
  simp only [CollatzResearch.WordTrace]
  refine ⟨85129323045190045628808365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56752882030126697085872243 85129323045190045628808365)
  ·
    refine ⟨31923496141946267110803137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85129323045190045628808365 31923496141946267110803137)
    ·
      refine ⟨23942622106459700333102353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31923496141946267110803137 23942622106459700333102353)
      ·
        refine ⟨17956966579844775249826765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23942622106459700333102353 17956966579844775249826765)
        ·
          refine ⟨6733862467441790718685037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17956966579844775249826765 6733862467441790718685037)
          ·
            refine ⟨2525198425290671519506889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6733862467441790718685037 2525198425290671519506889)
            ·
              refine ⟨1893898818968003639630167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2525198425290671519506889 1893898818968003639630167)
              ·
                refine ⟨2840848228452005459445251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1893898818968003639630167 2840848228452005459445251)
                ·
                  refine ⟨4261272342678008189167877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2840848228452005459445251 4261272342678008189167877)
                  ·
                    refine ⟨798988564252126535468977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4261272342678008189167877 798988564252126535468977)
                    ·
                      rfl

theorem cell22_2334037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 2, 1, 1, 4].length) (baseStart_2334037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2334037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2334037 prefixEnd_2334037 := by exact prefixLift 2334037
  have htrace : WordTrace (prefixWord ++ tailWord_2334037) baseStart_2334037 baseEnd_2334037 := by
    simpa [prefixWord, tailWord_2334037, baseEnd_2334037] using wordTrace_append hprefix tailTrace_2334037
  have hstable : (prefixWord ++ tailWord_2334037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2334037).length < 2 ^ (prefixWord ++ tailWord_2334037).sum := by decide
  have hdescent : baseEnd_2334037 < baseStart_2334037 := by decide
  rcases family_descends (prefixWord ++ tailWord_2334037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2334050 : List Nat := [3, 3, 2, 1, 1, 1, 3, 1, 4, 3]
def baseStart_2334050 : Nat := 118140960795 + 2334050 * 2 ^ 59
def prefixEnd_2334050 : Nat := 4983230072969 + 3 ^ 40 * 2334050 * 2
def baseEnd_2334050 : Nat := 798993014417798834893937

theorem tailTrace_2334050 : CollatzResearch.WordTrace tailWord_2334050 prefixEnd_2334050 798993014417798834893937 := by
  unfold tailWord_2334050
  simp only [CollatzResearch.WordTrace]
  refine ⟨21282449298535737212257901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56753198129428632566021069 21282449298535737212257901)
  ·
    refine ⟨7980918486950901454596713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21282449298535737212257901 7980918486950901454596713)
    ·
      refine ⟨5985688865213176090947535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7980918486950901454596713 5985688865213176090947535)
      ·
        refine ⟨8978533297819764136421303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5985688865213176090947535 8978533297819764136421303)
        ·
          refine ⟨13467799946729646204631955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8978533297819764136421303 13467799946729646204631955)
          ·
            refine ⟨20201699920094469306947933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13467799946729646204631955 20201699920094469306947933)
            ·
              refine ⟨7575637470035425990105475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20201699920094469306947933 7575637470035425990105475)
              ·
                refine ⟨11363456205053138985158213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7575637470035425990105475 11363456205053138985158213)
                ·
                  refine ⟨2130648038447463559717165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11363456205053138985158213 2130648038447463559717165)
                  ·
                    refine ⟨798993014417798834893937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2130648038447463559717165 798993014417798834893937)
                    ·
                      rfl

theorem cell22_2334050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_2334050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2334050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2334050 prefixEnd_2334050 := by exact prefixLift 2334050
  have htrace : WordTrace (prefixWord ++ tailWord_2334050) baseStart_2334050 baseEnd_2334050 := by
    simpa [prefixWord, tailWord_2334050, baseEnd_2334050] using wordTrace_append hprefix tailTrace_2334050
  have hstable : (prefixWord ++ tailWord_2334050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2334050).length < 2 ^ (prefixWord ++ tailWord_2334050).sum := by decide
  have hdescent : baseEnd_2334050 < baseStart_2334050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2334050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2334091 : List Nat := [1, 1, 1, 1, 4, 3, 1, 1, 9]
def baseStart_2334091 : Nat := 118140960795 + 2334091 * 2 ^ 59
def prefixEnd_2334091 : Nat := 4983230072969 + 3 ^ 40 * 2334091 * 2
def baseEnd_2334091 : Nat := 266335683185229464872937

theorem tailTrace_2334091 : CollatzResearch.WordTrace tailWord_2334091 prefixEnd_2334091 266335683185229464872937 := by
  unfold tailWord_2334091
  simp only [CollatzResearch.WordTrace]
  refine ⟨85131292586994412851274127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56754195057996275234182751 85131292586994412851274127)
  ·
    refine ⟨127696938880491619276911191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85131292586994412851274127 127696938880491619276911191)
    ·
      refine ⟨191545408320737428915366787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127696938880491619276911191 191545408320737428915366787)
      ·
        refine ⟨287318112481106143373050181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191545408320737428915366787 287318112481106143373050181)
        ·
          refine ⟨53872146090207401882446909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 287318112481106143373050181 53872146090207401882446909)
          ·
            refine ⟨20202054783827775705917591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53872146090207401882446909 20202054783827775705917591)
            ·
              refine ⟨30303082175741663558876387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20202054783827775705917591 30303082175741663558876387)
              ·
                refine ⟨45454623263612495338314581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30303082175741663558876387 45454623263612495338314581)
                ·
                  refine ⟨266335683185229464872937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 45454623263612495338314581 266335683185229464872937)
                  ·
                    rfl

theorem cell22_2334091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 9].length) (baseStart_2334091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2334091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2334091 prefixEnd_2334091 := by exact prefixLift 2334091
  have htrace : WordTrace (prefixWord ++ tailWord_2334091) baseStart_2334091 baseEnd_2334091 := by
    simpa [prefixWord, tailWord_2334091, baseEnd_2334091] using wordTrace_append hprefix tailTrace_2334091
  have hstable : (prefixWord ++ tailWord_2334091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2334091).length < 2 ^ (prefixWord ++ tailWord_2334091).sum := by decide
  have hdescent : baseEnd_2334091 < baseStart_2334091 := by decide
  rcases family_descends (prefixWord ++ tailWord_2334091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2334121 : List Nat := [1, 2, 1, 1, 1, 1, 3, 1, 1, 10]
def baseStart_2334121 : Nat := 118140960795 + 2334121 * 2 ^ 59
def prefixEnd_2334121 : Nat := 4983230072969 + 3 ^ 40 * 2334121 * 2
def baseEnd_2334121 : Nat := 799017319168778316368719

theorem tailTrace_2334121 : CollatzResearch.WordTrace tailWord_2334121 prefixEnd_2334121 799017319168778316368719 := by
  unfold tailWord_2334121
  simp only [CollatzResearch.WordTrace]
  refine ⟨85132386776885727974866217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56754924517923818649910811 85132386776885727974866217)
  ·
    refine ⟨63849290082664295981149663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85132386776885727974866217 63849290082664295981149663)
    ·
      refine ⟨95773935123996443971724495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63849290082664295981149663 95773935123996443971724495)
      ·
        refine ⟨143660902685994665957586743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95773935123996443971724495 143660902685994665957586743)
        ·
          refine ⟨215491354028991998936380115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143660902685994665957586743 215491354028991998936380115)
          ·
            refine ⟨323237031043487998404570173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215491354028991998936380115 323237031043487998404570173)
            ·
              refine ⟨121213886641307999401713815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 323237031043487998404570173 121213886641307999401713815)
              ·
                refine ⟨181820829961961999102570723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 121213886641307999401713815 181820829961961999102570723)
                ·
                  refine ⟨272731244942942998653856085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 181820829961961999102570723 272731244942942998653856085)
                  ·
                    refine ⟨799017319168778316368719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 272731244942942998653856085 799017319168778316368719)
                    ·
                      rfl

theorem cell22_2334121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 10].length) (baseStart_2334121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2334121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2334121 prefixEnd_2334121 := by exact prefixLift 2334121
  have htrace : WordTrace (prefixWord ++ tailWord_2334121) baseStart_2334121 baseEnd_2334121 := by
    simpa [prefixWord, tailWord_2334121, baseEnd_2334121] using wordTrace_append hprefix tailTrace_2334121
  have hstable : (prefixWord ++ tailWord_2334121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2334121).length < 2 ^ (prefixWord ++ tailWord_2334121).sum := by decide
  have hdescent : baseEnd_2334121 < baseStart_2334121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2334121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2334200 : List Nat := [2, 1, 2, 1, 1, 5, 3, 1, 2, 4]
def baseStart_2334200 : Nat := 118140960795 + 2334200 * 2 ^ 59
def prefixEnd_2334200 : Nat := 4983230072969 + 3 ^ 40 * 2334200 * 2
def baseEnd_2334200 : Nat := 799044362483248443643477

theorem tailTrace_2334200 : CollatzResearch.WordTrace tailWord_2334200 prefixEnd_2334200 799044362483248443643477 := by
  unfold tailWord_2334200
  simp only [CollatzResearch.WordTrace]
  refine ⟨42567634071799762233496027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56756845429066349644661369 42567634071799762233496027)
  ·
    refine ⟨63851451107699643350244041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42567634071799762233496027 63851451107699643350244041)
    ·
      refine ⟨47888588330774732512683031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63851451107699643350244041 47888588330774732512683031)
      ·
        refine ⟨71832882496162098769024547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47888588330774732512683031 71832882496162098769024547)
        ·
          refine ⟨107749323744243148153536821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71832882496162098769024547 107749323744243148153536821)
          ·
            refine ⟨10101499101022795139394077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 107749323744243148153536821 10101499101022795139394077)
            ·
              refine ⟨3788062162883548177272779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10101499101022795139394077 3788062162883548177272779)
              ·
                refine ⟨5682093244325322265909169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3788062162883548177272779 5682093244325322265909169)
                ·
                  refine ⟨4261569933243991699431877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5682093244325322265909169 4261569933243991699431877)
                  ·
                    refine ⟨799044362483248443643477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4261569933243991699431877 799044362483248443643477)
                    ·
                      rfl

theorem cell22_2334200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 1, 2, 4].length) (baseStart_2334200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2334200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2334200 prefixEnd_2334200 := by exact prefixLift 2334200
  have htrace : WordTrace (prefixWord ++ tailWord_2334200) baseStart_2334200 baseEnd_2334200 := by
    simpa [prefixWord, tailWord_2334200, baseEnd_2334200] using wordTrace_append hprefix tailTrace_2334200
  have hstable : (prefixWord ++ tailWord_2334200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2334200).length < 2 ^ (prefixWord ++ tailWord_2334200).sum := by decide
  have hdescent : baseEnd_2334200 < baseStart_2334200 := by decide
  rcases family_descends (prefixWord ++ tailWord_2334200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2334219 : List Nat := [1, 1, 1, 1, 8, 2, 1, 2, 2, 3]
def baseStart_2334219 : Nat := 118140960795 + 2334219 * 2 ^ 59
def prefixEnd_2334219 : Nat := 4983230072969 + 3 ^ 40 * 2334219 * 2
def baseEnd_2334219 : Nat := 799050866571538727418419

theorem tailTrace_2334219 : CollatzResearch.WordTrace tailWord_2334219 prefixEnd_2334219 799050866571538727418419 := by
  unfold tailWord_2334219
  simp only [CollatzResearch.WordTrace]
  refine ⟨85135961130530690711933711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56757307420353793807955807 85135961130530690711933711)
  ·
    refine ⟨127703941695796036067900567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85135961130530690711933711 127703941695796036067900567)
    ·
      refine ⟨191555912543694054101850851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127703941695796036067900567 191555912543694054101850851)
      ·
        refine ⟨287333868815541081152776277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191555912543694054101850851 287333868815541081152776277)
        ·
          refine ⟨3367193775182122044759097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 287333868815541081152776277 3367193775182122044759097)
          ·
            refine ⟨2525395331386591533569323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3367193775182122044759097 2525395331386591533569323)
            ·
              refine ⟨3788092997079887300353985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2525395331386591533569323 3788092997079887300353985)
              ·
                refine ⟨2841069747809915475265489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3788092997079887300353985 2841069747809915475265489)
                ·
                  refine ⟨2130802310857436606449117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2841069747809915475265489 2130802310857436606449117)
                  ·
                    refine ⟨799050866571538727418419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2130802310857436606449117 799050866571538727418419)
                    ·
                      rfl

theorem cell22_2334219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 2, 2, 3].length) (baseStart_2334219 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2334219 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2334219 prefixEnd_2334219 := by exact prefixLift 2334219
  have htrace : WordTrace (prefixWord ++ tailWord_2334219) baseStart_2334219 baseEnd_2334219 := by
    simpa [prefixWord, tailWord_2334219, baseEnd_2334219] using wordTrace_append hprefix tailTrace_2334219
  have hstable : (prefixWord ++ tailWord_2334219).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2334219).length < 2 ^ (prefixWord ++ tailWord_2334219).sum := by decide
  have hdescent : baseEnd_2334219 < baseStart_2334219 := by decide
  rcases family_descends (prefixWord ++ tailWord_2334219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2334264 : List Nat := [2, 1, 2, 1, 4, 2, 3, 3, 1, 3]
def baseStart_2334264 : Nat := 118140960795 + 2334264 * 2 ^ 59
def prefixEnd_2334264 : Nat := 4983230072969 + 3 ^ 40 * 2334264 * 2
def baseEnd_2334264 : Nat := 799066270991173610043281

theorem tailTrace_2334264 : CollatzResearch.WordTrace tailWord_2334264 prefixEnd_2334264 799066270991173610043281 := by
  unfold tailWord_2334264
  simp only [CollatzResearch.WordTrace]
  refine ⟨42568801207683831698660923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56758401610245108931547897 42568801207683831698660923)
  ·
    refine ⟨63853201811525747547991385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42568801207683831698660923 63853201811525747547991385)
    ·
      refine ⟨47889901358644310660993539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63853201811525747547991385 47889901358644310660993539)
      ·
        refine ⟨71834852037966465991490309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47889901358644310660993539 71834852037966465991490309)
        ·
          refine ⟨13469034757118712373404433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71834852037966465991490309 13469034757118712373404433)
          ·
            refine ⟨10101776067839034280053325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13469034757118712373404433 10101776067839034280053325)
            ·
              refine ⟨3788166025439637855019997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10101776067839034280053325 3788166025439637855019997)
              ·
                refine ⟨1420562259539864195632499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3788166025439637855019997 1420562259539864195632499)
                ·
                  refine ⟨2130843389309796293448749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1420562259539864195632499 2130843389309796293448749)
                  ·
                    refine ⟨799066270991173610043281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2130843389309796293448749 799066270991173610043281)
                    ·
                      rfl

theorem cell22_2334264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 3, 1, 3].length) (baseStart_2334264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2334264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2334264 prefixEnd_2334264 := by exact prefixLift 2334264
  have htrace : WordTrace (prefixWord ++ tailWord_2334264) baseStart_2334264 baseEnd_2334264 := by
    simpa [prefixWord, tailWord_2334264, baseEnd_2334264] using wordTrace_append hprefix tailTrace_2334264
  have hstable : (prefixWord ++ tailWord_2334264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2334264).length < 2 ^ (prefixWord ++ tailWord_2334264).sum := by decide
  have hdescent : baseEnd_2334264 < baseStart_2334264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2334264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2334307 : List Nat := [1, 1, 1, 5, 1, 3, 3, 2, 1, 4]
def baseStart_2334307 : Nat := 118140960795 + 2334307 * 2 ^ 59
def prefixEnd_2334307 : Nat := 4983230072969 + 3 ^ 40 * 2334307 * 2
def baseEnd_2334307 : Nat := 799080990769935831218149

theorem tailTrace_2334307 : CollatzResearch.WordTrace tailWord_2334307 prefixEnd_2334307 799080990769935831218149 := by
  unfold tailWord_2334307
  simp only [CollatzResearch.WordTrace]
  refine ⟨85139170754211881741137175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56759447169474587827424783 85139170754211881741137175)
  ·
    refine ⟨127708756131317822611705763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85139170754211881741137175 127708756131317822611705763)
    ·
      refine ⟨191563134196976733917558645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127708756131317822611705763 191563134196976733917558645)
      ·
        refine ⟨17959043830966568804771123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 191563134196976733917558645 17959043830966568804771123)
        ·
          refine ⟨26938565746449853207156685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17959043830966568804771123 26938565746449853207156685)
          ·
            refine ⟨10101962154918694952683757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26938565746449853207156685 10101962154918694952683757)
            ·
              refine ⟨3788235808094510607256409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10101962154918694952683757 3788235808094510607256409)
              ·
                refine ⟨2841176856070882955442307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3788235808094510607256409 2841176856070882955442307)
                ·
                  refine ⟨4261765284106324433163461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2841176856070882955442307 4261765284106324433163461)
                  ·
                    refine ⟨799080990769935831218149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4261765284106324433163461 799080990769935831218149)
                    ·
                      rfl

theorem cell22_2334307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 2, 1, 4].length) (baseStart_2334307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2334307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2334307 prefixEnd_2334307 := by exact prefixLift 2334307
  have htrace : WordTrace (prefixWord ++ tailWord_2334307) baseStart_2334307 baseEnd_2334307 := by
    simpa [prefixWord, tailWord_2334307, baseEnd_2334307] using wordTrace_append hprefix tailTrace_2334307
  have hstable : (prefixWord ++ tailWord_2334307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2334307).length < 2 ^ (prefixWord ++ tailWord_2334307).sum := by decide
  have hdescent : baseEnd_2334307 < baseStart_2334307 := by decide
  rcases family_descends (prefixWord ++ tailWord_2334307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2334320 : List Nat := [2, 1, 1, 1, 6, 1, 1, 1, 3, 5]
def baseStart_2334320 : Nat := 118140960795 + 2334320 * 2 ^ 59
def prefixEnd_2334320 : Nat := 4983230072969 + 3 ^ 40 * 2334320 * 2
def baseEnd_2334320 : Nat := 799085440935608130643109

theorem tailTrace_2334320 : CollatzResearch.WordTrace tailWord_2334320 prefixEnd_2334320 799085440935608130643109 := by
  unfold tailWord_2334320
  simp only [CollatzResearch.WordTrace]
  refine ⟨42569822451582392480680207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56759763268776523307573609 42569822451582392480680207)
  ·
    refine ⟨63854733677373588721020311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42569822451582392480680207 63854733677373588721020311)
    ·
      refine ⟨95782100516060383081530467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63854733677373588721020311 95782100516060383081530467)
      ·
        refine ⟨143673150774090574622295701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95782100516060383081530467 143673150774090574622295701)
        ·
          refine ⟨6734678942535495685420111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 143673150774090574622295701 6734678942535495685420111)
          ·
            refine ⟨10102018413803243528130167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6734678942535495685420111 10102018413803243528130167)
            ·
              refine ⟨15153027620704865292195251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10102018413803243528130167 15153027620704865292195251)
              ·
                refine ⟨22729541431057297938292877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15153027620704865292195251 22729541431057297938292877)
                ·
                  refine ⟨8523578036646486726859829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22729541431057297938292877 8523578036646486726859829)
                  ·
                    refine ⟨799085440935608130643109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8523578036646486726859829 799085440935608130643109)
                    ·
                      rfl

theorem cell22_2334320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 3, 5].length) (baseStart_2334320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2334320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2334320 prefixEnd_2334320 := by exact prefixLift 2334320
  have htrace : WordTrace (prefixWord ++ tailWord_2334320) baseStart_2334320 baseEnd_2334320 := by
    simpa [prefixWord, tailWord_2334320, baseEnd_2334320] using wordTrace_append hprefix tailTrace_2334320
  have hstable : (prefixWord ++ tailWord_2334320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2334320).length < 2 ^ (prefixWord ++ tailWord_2334320).sum := by decide
  have hdescent : baseEnd_2334320 < baseStart_2334320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2334320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2334354 : List Nat := [3, 2, 3, 1, 3, 1, 2, 1, 1, 5]
def baseStart_2334354 : Nat := 118140960795 + 2334354 * 2 ^ 59
def prefixEnd_2334354 : Nat := 4983230072969 + 3 ^ 40 * 2334354 * 2
def baseEnd_2334354 : Nat := 799097079830443375293005

theorem tailTrace_2334354 : CollatzResearch.WordTrace tailWord_2334354 prefixEnd_2334354 799097079830443375293005 := by
  unfold tailWord_2334354
  simp only [CollatzResearch.WordTrace]
  refine ⟨21285221246260402192024529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56760589990027739178732077 21285221246260402192024529)
  ·
    refine ⟨15963915934695301644018397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21285221246260402192024529 15963915934695301644018397)
    ·
      refine ⟨5986468475510738116506899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15963915934695301644018397 5986468475510738116506899)
      ·
        refine ⟨8979702713266107174760349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5986468475510738116506899 8979702713266107174760349)
        ·
          refine ⟨3367388517474790190535131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8979702713266107174760349 3367388517474790190535131)
          ·
            refine ⟨5051082776212185285802697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3367388517474790190535131 5051082776212185285802697)
            ·
              refine ⟨3788312082159138964352023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5051082776212185285802697 3788312082159138964352023)
              ·
                refine ⟨5682468123238708446528035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3788312082159138964352023 5682468123238708446528035)
                ·
                  refine ⟨8523702184858062669792053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5682468123238708446528035 8523702184858062669792053)
                  ·
                    refine ⟨799097079830443375293005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8523702184858062669792053 799097079830443375293005)
                    ·
                      rfl

theorem cell22_2334354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_2334354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2334354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2334354 prefixEnd_2334354 := by exact prefixLift 2334354
  have htrace : WordTrace (prefixWord ++ tailWord_2334354) baseStart_2334354 baseEnd_2334354 := by
    simpa [prefixWord, tailWord_2334354, baseEnd_2334354] using wordTrace_append hprefix tailTrace_2334354
  have hstable : (prefixWord ++ tailWord_2334354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2334354).length < 2 ^ (prefixWord ++ tailWord_2334354).sum := by decide
  have hdescent : baseEnd_2334354 < baseStart_2334354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2334354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2334369 : List Nat := [1, 2, 3, 3, 2, 3, 1, 1, 2, 4]
def baseStart_2334369 : Nat := 118140960795 + 2334369 * 2 ^ 59
def prefixEnd_2334369 : Nat := 4983230072969 + 3 ^ 40 * 2334369 * 2
def baseEnd_2334369 : Nat := 799102214636988336167959

theorem tailTrace_2334369 : CollatzResearch.WordTrace tailWord_2334369 prefixEnd_2334369 799102214636988336167959 := by
  unfold tailWord_2334369
  simp only [CollatzResearch.WordTrace]
  refine ⟨85141432079987266329894161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56760954719991510886596107 85141432079987266329894161)
  ·
    refine ⟨63856074059990449747420621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85141432079987266329894161 63856074059990449747420621)
    ·
      refine ⟨23946027772496418655282733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63856074059990449747420621 23946027772496418655282733)
      ·
        refine ⟨8979760414686156995731025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23946027772496418655282733 8979760414686156995731025)
        ·
          refine ⟨6734820311014617746798269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8979760414686156995731025 6734820311014617746798269)
          ·
            refine ⟨2525557616630481655049351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6734820311014617746798269 2525557616630481655049351)
            ·
              refine ⟨3788336424945722482574027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2525557616630481655049351 3788336424945722482574027)
              ·
                refine ⟨5682504637418583723861041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3788336424945722482574027 5682504637418583723861041)
                ·
                  refine ⟨4261878478063937792895781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5682504637418583723861041 4261878478063937792895781)
                  ·
                    refine ⟨799102214636988336167959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4261878478063937792895781 799102214636988336167959)
                    ·
                      rfl

theorem cell22_2334369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 1, 2, 4].length) (baseStart_2334369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2334369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2334369 prefixEnd_2334369 := by exact prefixLift 2334369
  have htrace : WordTrace (prefixWord ++ tailWord_2334369) baseStart_2334369 baseEnd_2334369 := by
    simpa [prefixWord, tailWord_2334369, baseEnd_2334369] using wordTrace_append hprefix tailTrace_2334369
  have hstable : (prefixWord ++ tailWord_2334369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2334369).length < 2 ^ (prefixWord ++ tailWord_2334369).sum := by decide
  have hdescent : baseEnd_2334369 < baseStart_2334369 := by decide
  rcases family_descends (prefixWord ++ tailWord_2334369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2334399 : List Nat := [1, 1, 2, 2, 2, 3, 1, 6, 1, 3]
def baseStart_2334399 : Nat := 118140960795 + 2334399 * 2 ^ 59
def prefixEnd_2334399 : Nat := 4983230072969 + 3 ^ 40 * 2334399 * 2
def baseEnd_2334399 : Nat := 799112484250078257917867

theorem tailTrace_2334399 : CollatzResearch.WordTrace tailWord_2334399 prefixEnd_2334399 799112484250078257917867 := by
  unfold tailWord_2334399
  simp only [CollatzResearch.WordTrace]
  refine ⟨85142526269878581453486251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56761684179919054302324167 85142526269878581453486251)
  ·
    refine ⟨127713789404817872180229377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85142526269878581453486251 127713789404817872180229377)
    ·
      refine ⟨95785342053613404135172033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127713789404817872180229377 95785342053613404135172033)
      ·
        refine ⟨71839006540210053101379025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95785342053613404135172033 71839006540210053101379025)
        ·
          refine ⟨53879254905157539826034269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71839006540210053101379025 53879254905157539826034269)
          ·
            refine ⟨20204720589434077434762851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53879254905157539826034269 20204720589434077434762851)
            ·
              refine ⟨30307080884151116152144277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20204720589434077434762851 30307080884151116152144277)
              ·
                refine ⟨1420644416444583569631763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 30307080884151116152144277 1420644416444583569631763)
                ·
                  refine ⟨2130966624666875354447645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1420644416444583569631763 2130966624666875354447645)
                  ·
                    refine ⟨799112484250078257917867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2130966624666875354447645 799112484250078257917867)
                    ·
                      rfl

theorem cell22_2334399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 6, 1, 3].length) (baseStart_2334399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2334399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2334399 prefixEnd_2334399 := by exact prefixLift 2334399
  have htrace : WordTrace (prefixWord ++ tailWord_2334399) baseStart_2334399 baseEnd_2334399 := by
    simpa [prefixWord, tailWord_2334399, baseEnd_2334399] using wordTrace_append hprefix tailTrace_2334399
  have hstable : (prefixWord ++ tailWord_2334399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2334399).length < 2 ^ (prefixWord ++ tailWord_2334399).sum := by decide
  have hdescent : baseEnd_2334399 < baseStart_2334399 := by decide
  rcases family_descends (prefixWord ++ tailWord_2334399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2334433 : List Nat := [1, 2, 3, 1, 5, 2, 1, 3, 1, 3]
def baseStart_2334433 : Nat := 118140960795 + 2334433 * 2 ^ 59
def prefixEnd_2334433 : Nat := 4983230072969 + 3 ^ 40 * 2334433 * 2
def baseEnd_2334433 : Nat := 799124123144913502567763

theorem tailTrace_2334433 : CollatzResearch.WordTrace tailWord_2334433 prefixEnd_2334433 799124123144913502567763 := by
  unfold tailWord_2334433
  simp only [CollatzResearch.WordTrace]
  refine ⟨85143766351755405260223953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56762510901170270173482635 85143766351755405260223953)
  ·
    refine ⟨63857824763816553945167965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85143766351755405260223953 63857824763816553945167965)
    ·
      refine ⟨23946684286431207729437987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63857824763816553945167965 23946684286431207729437987)
      ·
        refine ⟨35920026429646811594156981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23946684286431207729437987 35920026429646811594156981)
        ·
          refine ⟨3367502477779388586952217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35920026429646811594156981 3367502477779388586952217)
          ·
            refine ⟨2525626858334541440214163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3367502477779388586952217 2525626858334541440214163)
            ·
              refine ⟨3788440287501812160321245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2525626858334541440214163 3788440287501812160321245)
              ·
                refine ⟨1420665107813179560120467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3788440287501812160321245 1420665107813179560120467)
                ·
                  refine ⟨2130997661719769340180701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1420665107813179560120467 2130997661719769340180701)
                  ·
                    refine ⟨799124123144913502567763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2130997661719769340180701 799124123144913502567763)
                    ·
                      rfl

theorem cell22_2334433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 3, 1, 3].length) (baseStart_2334433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2334433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2334433 prefixEnd_2334433 := by exact prefixLift 2334433
  have htrace : WordTrace (prefixWord ++ tailWord_2334433) baseStart_2334433 baseEnd_2334433 := by
    simpa [prefixWord, tailWord_2334433, baseEnd_2334433] using wordTrace_append hprefix tailTrace_2334433
  have hstable : (prefixWord ++ tailWord_2334433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2334433).length < 2 ^ (prefixWord ++ tailWord_2334433).sum := by decide
  have hdescent : baseEnd_2334433 < baseStart_2334433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2334433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2334472 : List Nat := [2, 1, 3, 2, 2, 1, 2, 3, 1, 5]
def baseStart_2334472 : Nat := 118140960795 + 2334472 * 2 ^ 59
def prefixEnd_2334472 : Nat := 4983230072969 + 3 ^ 40 * 2334472 * 2
def baseEnd_2334472 : Nat := 799137473641930400842643

theorem tailTrace_2334472 : CollatzResearch.WordTrace tailWord_2334472 prefixEnd_2334472 799137473641930400842643 := by
  unfold tailWord_2334472
  simp only [CollatzResearch.WordTrace]
  refine ⟨42572594399307057460446835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56763459199076076613929113 42572594399307057460446835)
  ·
    refine ⟨63858891598960586190670253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42572594399307057460446835 63858891598960586190670253)
    ·
      refine ⟨23947084349610219821501345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63858891598960586190670253 23947084349610219821501345)
      ·
        refine ⟨17960313262207664866126009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23947084349610219821501345 17960313262207664866126009)
        ·
          refine ⟨13470234946655748649594507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17960313262207664866126009 13470234946655748649594507)
          ·
            refine ⟨20205352419983622974391761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13470234946655748649594507 20205352419983622974391761)
            ·
              refine ⟨15154014314987717230793821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20205352419983622974391761 15154014314987717230793821)
              ·
                refine ⟨5682755368120393961547683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15154014314987717230793821 5682755368120393961547683)
                ·
                  refine ⟨8524133052180590942321525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5682755368120393961547683 8524133052180590942321525)
                  ·
                    refine ⟨799137473641930400842643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8524133052180590942321525 799137473641930400842643)
                    ·
                      rfl

theorem cell22_2334472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 3, 1, 5].length) (baseStart_2334472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2334472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2334472 prefixEnd_2334472 := by exact prefixLift 2334472
  have htrace : WordTrace (prefixWord ++ tailWord_2334472) baseStart_2334472 baseEnd_2334472 := by
    simpa [prefixWord, tailWord_2334472, baseEnd_2334472] using wordTrace_append hprefix tailTrace_2334472
  have hstable : (prefixWord ++ tailWord_2334472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2334472).length < 2 ^ (prefixWord ++ tailWord_2334472).sum := by decide
  have hdescent : baseEnd_2334472 < baseStart_2334472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2334472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2334504 : List Nat := [2, 1, 5, 1, 1, 2, 2, 2, 2, 4]
def baseStart_2334504 : Nat := 118140960795 + 2334504 * 2 ^ 59
def prefixEnd_2334504 : Nat := 4983230072969 + 3 ^ 40 * 2334504 * 2
def baseEnd_2334504 : Nat := 799148427895892984042545

theorem tailTrace_2334504 : CollatzResearch.WordTrace tailWord_2334504 prefixEnd_2334504 799148427895892984042545 := by
  unfold tailWord_2334504
  simp only [CollatzResearch.WordTrace]
  refine ⟨42573177967249092193029283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56764237289665456257372377 42573177967249092193029283)
  ·
    refine ⟨63859766950873638289543925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42573177967249092193029283 63859766950873638289543925)
    ·
      refine ⟨5986853151644403589644743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 63859766950873638289543925 5986853151644403589644743)
      ·
        refine ⟨8980279727466605384467115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5986853151644403589644743 8980279727466605384467115)
        ·
          refine ⟨13470419591199908076700673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8980279727466605384467115 13470419591199908076700673)
          ·
            refine ⟨10102814693399931057525505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13470419591199908076700673 10102814693399931057525505)
            ·
              refine ⟨7577111020049948293144129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10102814693399931057525505 7577111020049948293144129)
              ·
                refine ⟨5682833265037461219858097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7577111020049948293144129 5682833265037461219858097)
                ·
                  refine ⟨4262124948778095914893573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5682833265037461219858097 4262124948778095914893573)
                  ·
                    refine ⟨799148427895892984042545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4262124948778095914893573 799148427895892984042545)
                    ·
                      rfl

theorem cell22_2334504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_2334504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2334504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2334504 prefixEnd_2334504 := by exact prefixLift 2334504
  have htrace : WordTrace (prefixWord ++ tailWord_2334504) baseStart_2334504 baseEnd_2334504 := by
    simpa [prefixWord, tailWord_2334504, baseEnd_2334504] using wordTrace_append hprefix tailTrace_2334504
  have hstable : (prefixWord ++ tailWord_2334504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2334504).length < 2 ^ (prefixWord ++ tailWord_2334504).sum := by decide
  have hdescent : baseEnd_2334504 < baseStart_2334504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2334504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2334564 : List Nat := [2, 3, 1, 1, 5, 1, 1, 1, 7]
def baseStart_2334564 : Nat := 118140960795 + 2334564 * 2 ^ 59
def prefixEnd_2334564 : Nat := 4983230072969 + 3 ^ 40 * 2334564 * 2
def baseEnd_2334564 : Nat := 266389655707357609180787

theorem tailTrace_2334564 : CollatzResearch.WordTrace tailWord_2334564 prefixEnd_2334564 266389655707357609180787 := by
  unfold tailWord_2334564
  simp only [CollatzResearch.WordTrace]
  refine ⟨42574272157140407316621373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56765696209520543088828497 42574272157140407316621373)
  ·
    refine ⟨15965352058927652743733015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42574272157140407316621373 15965352058927652743733015)
    ·
      refine ⟨23948028088391479115599523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15965352058927652743733015 23948028088391479115599523)
      ·
        refine ⟨35922042132587218673399285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23948028088391479115599523 35922042132587218673399285)
        ·
          refine ⟨3367691449930051750631183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35922042132587218673399285 3367691449930051750631183)
          ·
            refine ⟨5051537174895077625946775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3367691449930051750631183 5051537174895077625946775)
            ·
              refine ⟨7577305762342616438920163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5051537174895077625946775 7577305762342616438920163)
              ·
                refine ⟨11365958643513924658380245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7577305762342616438920163 11365958643513924658380245)
                ·
                  refine ⟨266389655707357609180787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11365958643513924658380245 266389655707357609180787)
                  ·
                    rfl

theorem cell22_2334564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 1, 7].length) (baseStart_2334564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2334564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2334564 prefixEnd_2334564 := by exact prefixLift 2334564
  have htrace : WordTrace (prefixWord ++ tailWord_2334564) baseStart_2334564 baseEnd_2334564 := by
    simpa [prefixWord, tailWord_2334564, baseEnd_2334564] using wordTrace_append hprefix tailTrace_2334564
  have hstable : (prefixWord ++ tailWord_2334564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2334564).length < 2 ^ (prefixWord ++ tailWord_2334564).sum := by decide
  have hdescent : baseEnd_2334564 < baseStart_2334564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2334564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2334581 : List Nat := [1, 3, 4, 1, 1, 1, 5, 1, 5]
def baseStart_2334581 : Nat := 118140960795 + 2334581 * 2 ^ 59
def prefixEnd_2334581 : Nat := 4983230072969 + 3 ^ 40 * 2334581 * 2
def baseEnd_2334581 : Nat := 266391595523163483289103

theorem tailTrace_2334581 : CollatzResearch.WordTrace tailWord_2334581 prefixEnd_2334581 266391595523163483289103 := by
  unfold tailWord_2334581
  simp only [CollatzResearch.WordTrace]
  refine ⟨85149164355219226536611597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56766109570146151024407731 85149164355219226536611597)
  ·
    refine ⟨31930936633207209951229349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85149164355219226536611597 31930936633207209951229349)
    ·
      refine ⟨5987050618726351865855503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31930936633207209951229349 5987050618726351865855503)
      ·
        refine ⟨8980575928089527798783255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5987050618726351865855503 8980575928089527798783255)
        ·
          refine ⟨13470863892134291698174883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8980575928089527798783255 13470863892134291698174883)
          ·
            refine ⟨20206295838201437547262325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13470863892134291698174883 20206295838201437547262325)
            ·
              refine ⟨1894340234831384770055843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20206295838201437547262325 1894340234831384770055843)
              ·
                refine ⟨2841510352247077155083765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1894340234831384770055843 2841510352247077155083765)
                ·
                  refine ⟨266391595523163483289103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2841510352247077155083765 266391595523163483289103)
                  ·
                    rfl

theorem cell22_2334581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 5, 1, 5].length) (baseStart_2334581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2334581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2334581 prefixEnd_2334581 := by exact prefixLift 2334581
  have htrace : WordTrace (prefixWord ++ tailWord_2334581) baseStart_2334581 baseEnd_2334581 := by
    simpa [prefixWord, tailWord_2334581, baseEnd_2334581] using wordTrace_append hprefix tailTrace_2334581
  have hstable : (prefixWord ++ tailWord_2334581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2334581).length < 2 ^ (prefixWord ++ tailWord_2334581).sum := by decide
  have hdescent : baseEnd_2334581 < baseStart_2334581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2334581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2334592 : List Nat := [2, 1, 1, 2, 1, 2, 3, 4, 6]
def baseStart_2334592 : Nat := 118140960795 + 2334592 * 2 ^ 59
def prefixEnd_2334592 : Nat := 4983230072969 + 3 ^ 40 * 2334592 * 2
def baseEnd_2334592 : Nat := 266392850698096695947425

theorem tailTrace_2334592 : CollatzResearch.WordTrace tailWord_2334592 prefixEnd_2334592 266392850698096695947425 := by
  unfold tailWord_2334592
  simp only [CollatzResearch.WordTrace]
  refine ⟨42574782779089687707631015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56766377038786250276841353 42574782779089687707631015)
  ·
    refine ⟨63862174168634531561446523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42574782779089687707631015 63862174168634531561446523)
    ·
      refine ⟨95793261252951797342169785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63862174168634531561446523 95793261252951797342169785)
      ·
        refine ⟨71844945939713848006627339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95793261252951797342169785 71844945939713848006627339)
        ·
          refine ⟨107767418909570772009941009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71844945939713848006627339 107767418909570772009941009)
          ·
            refine ⟨80825564182178079007455757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107767418909570772009941009 80825564182178079007455757)
            ·
              refine ⟨30309586568316779627795909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80825564182178079007455757 30309586568316779627795909)
              ·
                refine ⟨5683047481559396180211733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30309586568316779627795909 5683047481559396180211733)
                ·
                  refine ⟨266392850698096695947425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5683047481559396180211733 266392850698096695947425)
                  ·
                    rfl

theorem cell22_2334592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 4, 6].length) (baseStart_2334592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2334592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2334592 prefixEnd_2334592 := by exact prefixLift 2334592
  have htrace : WordTrace (prefixWord ++ tailWord_2334592) baseStart_2334592 baseEnd_2334592 := by
    simpa [prefixWord, tailWord_2334592, baseEnd_2334592] using wordTrace_append hprefix tailTrace_2334592
  have hstable : (prefixWord ++ tailWord_2334592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2334592).length < 2 ^ (prefixWord ++ tailWord_2334592).sum := by decide
  have hdescent : baseEnd_2334592 < baseStart_2334592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2334592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2334602 : List Nat := [3, 1, 2, 4, 3, 1, 1, 3, 1, 3]
def baseStart_2334602 : Nat := 118140960795 + 2334602 * 2 ^ 59
def prefixEnd_2334602 : Nat := 4983230072969 + 3 ^ 40 * 2334602 * 2
def baseEnd_2334602 : Nat := 799181975298653395092245

theorem tailTrace_2334602 : CollatzResearch.WordTrace tailWord_2334602 prefixEnd_2334602 799181975298653395092245 := by
  unfold tailWord_2334602
  simp only [CollatzResearch.WordTrace]
  refine ⟨21287482572035786780781515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56766620192095431415417373 21287482572035786780781515)
  ·
    refine ⟨31931223858053680171172273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21287482572035786780781515 31931223858053680171172273)
    ·
      refine ⟨23948417893540260128379205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31931223858053680171172273 23948417893540260128379205)
      ·
        refine ⟨4490328355038798774071101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23948417893540260128379205 4490328355038798774071101)
        ·
          refine ⟨1683873133139549540276663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4490328355038798774071101 1683873133139549540276663)
          ·
            refine ⟨2525809699709324310414995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1683873133139549540276663 2525809699709324310414995)
            ·
              refine ⟨3788714549563986465622493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2525809699709324310414995 3788714549563986465622493)
              ·
                refine ⟨1420767956086494924608435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3788714549563986465622493 1420767956086494924608435)
                ·
                  refine ⟨2131151934129742386912653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1420767956086494924608435 2131151934129742386912653)
                  ·
                    refine ⟨799181975298653395092245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2131151934129742386912653 799181975298653395092245)
                    ·
                      rfl

theorem cell22_2334602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 3, 1, 3].length) (baseStart_2334602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2334602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2334602 prefixEnd_2334602 := by exact prefixLift 2334602
  have htrace : WordTrace (prefixWord ++ tailWord_2334602) baseStart_2334602 baseEnd_2334602 := by
    simpa [prefixWord, tailWord_2334602, baseEnd_2334602] using wordTrace_append hprefix tailTrace_2334602
  have hstable : (prefixWord ++ tailWord_2334602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2334602).length < 2 ^ (prefixWord ++ tailWord_2334602).sum := by decide
  have hdescent : baseEnd_2334602 < baseStart_2334602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2334602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2334632 : List Nat := [2, 1, 6, 2, 2, 1, 2, 1, 5]
def baseStart_2334632 : Nat := 118140960795 + 2334632 * 2 ^ 59
def prefixEnd_2334632 : Nat := 4983230072969 + 3 ^ 40 * 2334632 * 2
def baseEnd_2334632 : Nat := 266397414970581105614051

theorem tailTrace_2334632 : CollatzResearch.WordTrace tailWord_2334632 prefixEnd_2334632 266397414970581105614051 := by
  unfold tailWord_2334632
  simp only [CollatzResearch.WordTrace]
  refine ⟨42575512239017231123359075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56767349652022974831145433 42575512239017231123359075)
  ·
    refine ⟨63863268358525846685038613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42575512239017231123359075 63863268358525846685038613)
    ·
      refine ⟨2993590704305899063361185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 63863268358525846685038613 2993590704305899063361185)
      ·
        refine ⟨2245193028229424297520889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2993590704305899063361185 2245193028229424297520889)
        ·
          refine ⟨1683894771172068223140667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2245193028229424297520889 1683894771172068223140667)
          ·
            refine ⟨2525842156758102334711001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1683894771172068223140667 2525842156758102334711001)
            ·
              refine ⟨1894381617568576751033251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2525842156758102334711001 1894381617568576751033251)
              ·
                refine ⟨2841572426352865126549877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1894381617568576751033251 2841572426352865126549877)
                ·
                  refine ⟨266397414970581105614051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2841572426352865126549877 266397414970581105614051)
                  ·
                    rfl

theorem cell22_2334632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 2, 1, 5].length) (baseStart_2334632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2334632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2334632 prefixEnd_2334632 := by exact prefixLift 2334632
  have htrace : WordTrace (prefixWord ++ tailWord_2334632) baseStart_2334632 baseEnd_2334632 := by
    simpa [prefixWord, tailWord_2334632, baseEnd_2334632] using wordTrace_append hprefix tailTrace_2334632
  have hstable : (prefixWord ++ tailWord_2334632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2334632).length < 2 ^ (prefixWord ++ tailWord_2334632).sum := by decide
  have hdescent : baseEnd_2334632 < baseStart_2334632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2334632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2334654 : List Nat := [4, 2, 1, 1, 1, 3, 2, 8]
def baseStart_2334654 : Nat := 118140960795 + 2334654 * 2 ^ 59
def prefixEnd_2334654 : Nat := 4983230072969 + 3 ^ 40 * 2334654 * 2
def baseEnd_2334654 : Nat := 88799975106815843643565

theorem tailTrace_2334654 : CollatzResearch.WordTrace tailWord_2334654 prefixEnd_2334654 88799975106815843643565 := by
  unfold tailWord_2334654
  simp only [CollatzResearch.WordTrace]
  refine ⟨10643978360494345000502377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56767884589303173336012677 10643978360494345000502377)
  ·
    refine ⟨7982983770370758750376783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10643978360494345000502377 7982983770370758750376783)
    ·
      refine ⟨11974475655556138125565175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7982983770370758750376783 11974475655556138125565175)
      ·
        refine ⟨17961713483334207188347763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11974475655556138125565175 17961713483334207188347763)
        ·
          refine ⟨26942570225001310782521645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17961713483334207188347763 26942570225001310782521645)
          ·
            refine ⟨10103463834375491543445617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26942570225001310782521645 10103463834375491543445617)
            ·
              refine ⟨7577597875781618657584213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10103463834375491543445617 7577597875781618657584213)
              ·
                refine ⟨88799975106815843643565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7577597875781618657584213 88799975106815843643565)
                ·
                  rfl

theorem cell22_2334654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 8].length) (baseStart_2334654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2334654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2334654 prefixEnd_2334654 := by exact prefixLift 2334654
  have htrace : WordTrace (prefixWord ++ tailWord_2334654) baseStart_2334654 baseEnd_2334654 := by
    simpa [prefixWord, tailWord_2334654, baseEnd_2334654] using wordTrace_append hprefix tailTrace_2334654
  have hstable : (prefixWord ++ tailWord_2334654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2334654).length < 2 ^ (prefixWord ++ tailWord_2334654).sum := by decide
  have hdescent : baseEnd_2334654 < baseStart_2334654 := by decide
  rcases family_descends (prefixWord ++ tailWord_2334654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2334726 : List Nat := [6, 2, 1, 2, 1, 2, 1, 2, 2, 3]
def baseStart_2334726 : Nat := 118140960795 + 2334726 * 2 ^ 59
def prefixEnd_2334726 : Nat := 4983230072969 + 3 ^ 40 * 2334726 * 2
def baseEnd_2334726 : Nat := 799224423032758404991865

theorem tailTrace_2334726 : CollatzResearch.WordTrace tailWord_2334726 prefixEnd_2334726 799224423032758404991865 := by
  unfold tailWord_2334726
  simp only [CollatzResearch.WordTrace]
  refine ⟨2661076654365434884395001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 56769635293129277533760021 2661076654365434884395001)
  ·
    refine ⟨1995807490774076163296251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2661076654365434884395001 1995807490774076163296251)
    ·
      refine ⟨2993711236161114244944377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1995807490774076163296251 2993711236161114244944377)
      ·
        refine ⟨2245283427120835683708283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2993711236161114244944377 2245283427120835683708283)
        ·
          refine ⟨3367925140681253525562425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2245283427120835683708283 3367925140681253525562425)
          ·
            refine ⟨2525943855510940144171819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3367925140681253525562425 2525943855510940144171819)
            ·
              refine ⟨3788915783266410216257729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2525943855510940144171819 3788915783266410216257729)
              ·
                refine ⟨2841686837449807662193297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3788915783266410216257729 2841686837449807662193297)
                ·
                  refine ⟨2131265128087355746644973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2841686837449807662193297 2131265128087355746644973)
                  ·
                    refine ⟨799224423032758404991865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2131265128087355746644973 799224423032758404991865)
                    ·
                      rfl

theorem cell22_2334726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_2334726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2334726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2334726 prefixEnd_2334726 := by exact prefixLift 2334726
  have htrace : WordTrace (prefixWord ++ tailWord_2334726) baseStart_2334726 baseEnd_2334726 := by
    simpa [prefixWord, tailWord_2334726, baseEnd_2334726] using wordTrace_append hprefix tailTrace_2334726
  have hstable : (prefixWord ++ tailWord_2334726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2334726).length < 2 ^ (prefixWord ++ tailWord_2334726).sum := by decide
  have hdescent : baseEnd_2334726 < baseStart_2334726 := by decide
  rcases family_descends (prefixWord ++ tailWord_2334726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2334791 : List Nat := [1, 1, 4, 1, 3, 1, 3, 2, 2, 4]
def baseStart_2334791 : Nat := 118140960795 + 2334791 * 2 ^ 59
def prefixEnd_2334791 : Nat := 4983230072969 + 3 ^ 40 * 2334791 * 2
def baseEnd_2334791 : Nat := 799246673861119902116665

theorem tailTrace_2334791 : CollatzResearch.WordTrace tailWord_2334791 prefixEnd_2334791 799246673861119902116665 := by
  unfold tailWord_2334791
  simp only [CollatzResearch.WordTrace]
  refine ⟨85156823684458432401756227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56771215789638954934504151 85156823684458432401756227)
  ·
    refine ⟨127735235526687648602634341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85156823684458432401756227 127735235526687648602634341)
    ·
      refine ⟨23950356661253934112993939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 127735235526687648602634341 23950356661253934112993939)
      ·
        refine ⟨35925534991880901169490909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23950356661253934112993939 35925534991880901169490909)
        ·
          refine ⟨13472075621955337938559091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35925534991880901169490909 13472075621955337938559091)
          ·
            refine ⟨20208113432933006907838637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13472075621955337938559091 20208113432933006907838637)
            ·
              refine ⟨7578042537349877590439489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20208113432933006907838637 7578042537349877590439489)
              ·
                refine ⟨5683531903012408192829617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7578042537349877590439489 5683531903012408192829617)
                ·
                  refine ⟨4262648927259306144622213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5683531903012408192829617 4262648927259306144622213)
                  ·
                    refine ⟨799246673861119902116665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4262648927259306144622213 799246673861119902116665)
                    ·
                      rfl

theorem cell22_2334791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 2, 2, 4].length) (baseStart_2334791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2334791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2334791 prefixEnd_2334791 := by exact prefixLift 2334791
  have htrace : WordTrace (prefixWord ++ tailWord_2334791) baseStart_2334791 baseEnd_2334791 := by
    simpa [prefixWord, tailWord_2334791, baseEnd_2334791] using wordTrace_append hprefix tailTrace_2334791
  have hstable : (prefixWord ++ tailWord_2334791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2334791).length < 2 ^ (prefixWord ++ tailWord_2334791).sum := by decide
  have hdescent : baseEnd_2334791 < baseStart_2334791 := by decide
  rcases family_descends (prefixWord ++ tailWord_2334791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2334814 : List Nat := [4, 4, 1, 1, 2, 2, 1, 2, 1, 4]
def baseStart_2334814 : Nat := 118140960795 + 2334814 * 2 ^ 59
def prefixEnd_2334814 : Nat := 4983230072969 + 3 ^ 40 * 2334814 * 2
def baseEnd_2334814 : Nat := 799254547231155508791595

theorem tailTrace_2334814 : CollatzResearch.WordTrace tailWord_2334814 prefixEnd_2334814 799254547231155508791595 := by
  unfold tailWord_2334814
  simp only [CollatzResearch.WordTrace]
  refine ⟨10644707820421888416230437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56771775042250071553228997 10644707820421888416230437)
  ·
    refine ⟨1995882716329104078043207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10644707820421888416230437 1995882716329104078043207)
    ·
      refine ⟨2993824074493656117064811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1995882716329104078043207 2993824074493656117064811)
      ·
        refine ⟨4490736111740484175597217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2993824074493656117064811 4490736111740484175597217)
        ·
          refine ⟨3368052083805363131697913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4490736111740484175597217 3368052083805363131697913)
          ·
            refine ⟨2526039062854022348773435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3368052083805363131697913 2526039062854022348773435)
            ·
              refine ⟨3789058594281033523160153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2526039062854022348773435 3789058594281033523160153)
              ·
                refine ⟨2841793945710775142370115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3789058594281033523160153 2841793945710775142370115)
                ·
                  refine ⟨4262690918566162713555173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2841793945710775142370115 4262690918566162713555173)
                  ·
                    refine ⟨799254547231155508791595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4262690918566162713555173 799254547231155508791595)
                    ·
                      rfl

theorem cell22_2334814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_2334814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2334814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2334814 prefixEnd_2334814 := by exact prefixLift 2334814
  have htrace : WordTrace (prefixWord ++ tailWord_2334814) baseStart_2334814 baseEnd_2334814 := by
    simpa [prefixWord, tailWord_2334814, baseEnd_2334814] using wordTrace_append hprefix tailTrace_2334814
  have hstable : (prefixWord ++ tailWord_2334814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2334814).length < 2 ^ (prefixWord ++ tailWord_2334814).sum := by decide
  have hdescent : baseEnd_2334814 < baseStart_2334814 := by decide
  rcases family_descends (prefixWord ++ tailWord_2334814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2334851 : List Nat := [1, 1, 1, 3, 3, 3, 1, 4, 5]
def baseStart_2334851 : Nat := 118140960795 + 2334851 * 2 ^ 59
def prefixEnd_2334851 : Nat := 4983230072969 + 3 ^ 40 * 2334851 * 2
def baseEnd_2334851 : Nat := 266422404362433248538827

theorem tailTrace_2334851 : CollatzResearch.WordTrace tailWord_2334851 prefixEnd_2334851 266422404362433248538827 := by
  unfold tailWord_2334851
  simp only [CollatzResearch.WordTrace]
  refine ⟨85159012064241062648940407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56772674709494041765960271 85159012064241062648940407)
  ·
    refine ⟨127738518096361593973410611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85159012064241062648940407 127738518096361593973410611)
    ·
      refine ⟨191607777144542390960115917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127738518096361593973410611 191607777144542390960115917)
      ·
        refine ⟨71852916429203396610043469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 191607777144542390960115917 71852916429203396610043469)
        ·
          refine ⟨26944843660951273728766301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71852916429203396610043469 26944843660951273728766301)
          ·
            refine ⟨10104316372856727648287363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26944843660951273728766301 10104316372856727648287363)
            ·
              refine ⟨15156474559285091472431045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10104316372856727648287363 15156474559285091472431045)
              ·
                refine ⟨2841838979865954651080821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15156474559285091472431045 2841838979865954651080821)
                ·
                  refine ⟨266422404362433248538827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2841838979865954651080821 266422404362433248538827)
                  ·
                    rfl

theorem cell22_2334851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 4, 5].length) (baseStart_2334851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2334851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2334851 prefixEnd_2334851 := by exact prefixLift 2334851
  have htrace : WordTrace (prefixWord ++ tailWord_2334851) baseStart_2334851 baseEnd_2334851 := by
    simpa [prefixWord, tailWord_2334851, baseEnd_2334851] using wordTrace_append hprefix tailTrace_2334851
  have hstable : (prefixWord ++ tailWord_2334851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2334851).length < 2 ^ (prefixWord ++ tailWord_2334851).sum := by decide
  have hdescent : baseEnd_2334851 < baseStart_2334851 := by decide
  rcases family_descends (prefixWord ++ tailWord_2334851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2334898 : List Nat := [3, 2, 1, 1, 1, 3, 3, 3, 1, 4]
def baseStart_2334898 : Nat := 118140960795 + 2334898 * 2 ^ 59
def prefixEnd_2334898 : Nat := 4983230072969 + 3 ^ 40 * 2334898 * 2
def baseEnd_2334898 : Nat := 799283302147807289691337

theorem tailTrace_2334898 : CollatzResearch.WordTrace tailWord_2334898 prefixEnd_2334898 799283302147807289691337 := by
  unfold tailWord_2334898
  simp only [CollatzResearch.WordTrace]
  refine ⟨21290181573767697418975337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56773817530047193117267565 21290181573767697418975337)
  ·
    refine ⟨15967636180325773064231503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21290181573767697418975337 15967636180325773064231503)
    ·
      refine ⟨23951454270488659596347255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15967636180325773064231503 23951454270488659596347255)
      ·
        refine ⟨35927181405732989394520883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23951454270488659596347255 35927181405732989394520883)
        ·
          refine ⟨53890772108599484091781325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35927181405732989394520883 53890772108599484091781325)
          ·
            refine ⟨20209039540724806534417997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53890772108599484091781325 20209039540724806534417997)
            ·
              refine ⟨7578389827771802450406749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20209039540724806534417997 7578389827771802450406749)
              ·
                refine ⟨2841896185414425918902531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7578389827771802450406749 2841896185414425918902531)
                ·
                  refine ⟨4262844278121638878353797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2841896185414425918902531 4262844278121638878353797)
                  ·
                    refine ⟨799283302147807289691337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4262844278121638878353797 799283302147807289691337)
                    ·
                      rfl

theorem cell22_2334898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 3, 1, 4].length) (baseStart_2334898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2334898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2334898 prefixEnd_2334898 := by exact prefixLift 2334898
  have htrace : WordTrace (prefixWord ++ tailWord_2334898) baseStart_2334898 baseEnd_2334898 := by
    simpa [prefixWord, tailWord_2334898, baseEnd_2334898] using wordTrace_append hprefix tailTrace_2334898
  have hstable : (prefixWord ++ tailWord_2334898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2334898).length < 2 ^ (prefixWord ++ tailWord_2334898).sum := by decide
  have hdescent : baseEnd_2334898 < baseStart_2334898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2334898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2335031 : List Nat := [1, 1, 3, 1, 2, 1, 1, 2, 10]
def baseStart_2335031 : Nat := 118140960795 + 2335031 * 2 ^ 59
def prefixEnd_2335031 : Nat := 4983230072969 + 3 ^ 40 * 2335031 * 2
def baseEnd_2335031 : Nat := 266442943588613092038643

theorem tailTrace_2335031 : CollatzResearch.WordTrace tailWord_2335031 prefixEnd_2335031 266442943588613092038643 := by
  unfold tailWord_2335031
  simp only [CollatzResearch.WordTrace]
  refine ⟨85165577203588953390492947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56777051469059302260328631 85165577203588953390492947)
  ·
    refine ⟨127748365805383430085739421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85165577203588953390492947 127748365805383430085739421)
    ·
      refine ⟨47905637177018786282152283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127748365805383430085739421 47905637177018786282152283)
      ·
        refine ⟨71858455765528179423228425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47905637177018786282152283 71858455765528179423228425)
        ·
          refine ⟨53893841824146134567421319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71858455765528179423228425 53893841824146134567421319)
          ·
            refine ⟨80840762736219201851131979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53893841824146134567421319 80840762736219201851131979)
            ·
              refine ⟨121261144104328802776697969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80840762736219201851131979 121261144104328802776697969)
              ·
                refine ⟨90945858078246602082523477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121261144104328802776697969 90945858078246602082523477)
                ·
                  refine ⟨266442943588613092038643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 90945858078246602082523477 266442943588613092038643)
                  ·
                    rfl

theorem cell22_2335031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 10].length) (baseStart_2335031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2335031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2335031 prefixEnd_2335031 := by exact prefixLift 2335031
  have htrace : WordTrace (prefixWord ++ tailWord_2335031) baseStart_2335031 baseEnd_2335031 := by
    simpa [prefixWord, tailWord_2335031, baseEnd_2335031] using wordTrace_append hprefix tailTrace_2335031
  have hstable : (prefixWord ++ tailWord_2335031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2335031).length < 2 ^ (prefixWord ++ tailWord_2335031).sum := by decide
  have hdescent : baseEnd_2335031 < baseStart_2335031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2335031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2335063 : List Nat := [1, 1, 3, 2, 3, 1, 1, 4, 1, 5]
def baseStart_2335063 : Nat := 118140960795 + 2335063 * 2 ^ 59
def prefixEnd_2335063 : Nat := 4983230072969 + 3 ^ 40 * 2335063 * 2
def baseEnd_2335063 : Nat := 799339785019801859315831

theorem tailTrace_2335063 : CollatzResearch.WordTrace tailWord_2335063 prefixEnd_2335063 799339785019801859315831 := by
  unfold tailWord_2335063
  simp only [CollatzResearch.WordTrace]
  refine ⟨85166744339473022855657843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56777829559648681903771895 85166744339473022855657843)
  ·
    refine ⟨127750116509209534283486765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85166744339473022855657843 127750116509209534283486765)
    ·
      refine ⟨47906293690953575356307537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127750116509209534283486765 47906293690953575356307537)
      ·
        refine ⟨35929720268215181517230653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47906293690953575356307537 35929720268215181517230653)
        ·
          refine ⟨13473645100580693068961495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35929720268215181517230653 13473645100580693068961495)
          ·
            refine ⟨20210467650871039603442243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13473645100580693068961495 20210467650871039603442243)
            ·
              refine ⟨30315701476306559405163365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20210467650871039603442243 30315701476306559405163365)
              ·
                refine ⟨5684194026807479888468131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30315701476306559405163365 5684194026807479888468131)
                ·
                  refine ⟨8526291040211219832702197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5684194026807479888468131 8526291040211219832702197)
                  ·
                    refine ⟨799339785019801859315831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8526291040211219832702197 799339785019801859315831)
                    ·
                      rfl

theorem cell22_2335063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 4, 1, 5].length) (baseStart_2335063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2335063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2335063 prefixEnd_2335063 := by exact prefixLift 2335063
  have htrace : WordTrace (prefixWord ++ tailWord_2335063) baseStart_2335063 baseEnd_2335063 := by
    simpa [prefixWord, tailWord_2335063, baseEnd_2335063] using wordTrace_append hprefix tailTrace_2335063
  have hstable : (prefixWord ++ tailWord_2335063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2335063).length < 2 ^ (prefixWord ++ tailWord_2335063).sum := by decide
  have hdescent : baseEnd_2335063 < baseStart_2335063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2335063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2335082 : List Nat := [3, 1, 3, 3, 1, 1, 2, 4, 4]
def baseStart_2335082 : Nat := 118140960795 + 2335082 * 2 ^ 59
def prefixEnd_2335082 : Nat := 4983230072969 + 3 ^ 40 * 2335082 * 2
def baseEnd_2335082 : Nat := 266448763036030714363591

theorem tailTrace_2335082 : CollatzResearch.WordTrace tailWord_2335082 prefixEnd_2335082 266448763036030714363591 := by
  unfold tailWord_2335082
  simp only [CollatzResearch.WordTrace]
  refine ⟨21291859331601047275149875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56778291550936126067066333 21291859331601047275149875)
  ·
    refine ⟨31937788997401570912724813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21291859331601047275149875 31937788997401570912724813)
    ·
      refine ⟨11976670874025589092271805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31937788997401570912724813 11976670874025589092271805)
      ·
        refine ⟨4491251577759595909601927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11976670874025589092271805 4491251577759595909601927)
        ·
          refine ⟨6736877366639393864402891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4491251577759595909601927 6736877366639393864402891)
          ·
            refine ⟨10105316049959090796604337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6736877366639393864402891 10105316049959090796604337)
            ·
              refine ⟨7578987037469318097453253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10105316049959090796604337 7578987037469318097453253)
              ·
                refine ⟨1421060069525497143272485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7578987037469318097453253 1421060069525497143272485)
                ·
                  refine ⟨266448763036030714363591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1421060069525497143272485 266448763036030714363591)
                  ·
                    rfl

theorem cell22_2335082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 4, 4].length) (baseStart_2335082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2335082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2335082 prefixEnd_2335082 := by exact prefixLift 2335082
  have htrace : WordTrace (prefixWord ++ tailWord_2335082) baseStart_2335082 baseEnd_2335082 := by
    simpa [prefixWord, tailWord_2335082, baseEnd_2335082] using wordTrace_append hprefix tailTrace_2335082
  have hstable : (prefixWord ++ tailWord_2335082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2335082).length < 2 ^ (prefixWord ++ tailWord_2335082).sum := by decide
  have hdescent : baseEnd_2335082 < baseStart_2335082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2335082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2335108 : List Nat := [2, 3, 2, 1, 1, 2, 1, 1, 2, 7]
def baseStart_2335108 : Nat := 118140960795 + 2335108 * 2 ^ 59
def prefixEnd_2335108 : Nat := 4983230072969 + 3 ^ 40 * 2335108 * 2
def baseEnd_2335108 : Nat := 799355189439436741940693

theorem tailTrace_2335108 : CollatzResearch.WordTrace tailWord_2335108 prefixEnd_2335108 799355189439436741940693 := by
  unfold tailWord_2335108
  simp only [CollatzResearch.WordTrace]
  refine ⟨42584192812154997770522989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56778923749539997027363985 42584192812154997770522989)
  ·
    refine ⟨15969072304558124163946121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42584192812154997770522989 15969072304558124163946121)
    ·
      refine ⟨11976804228418593122959591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15969072304558124163946121 11976804228418593122959591)
      ·
        refine ⟨17965206342627889684439387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11976804228418593122959591 17965206342627889684439387)
        ·
          refine ⟨26947809513941834526659081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17965206342627889684439387 26947809513941834526659081)
          ·
            refine ⟨20210857135456375894994311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26947809513941834526659081 20210857135456375894994311)
            ·
              refine ⟨30316285703184563842491467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20210857135456375894994311 30316285703184563842491467)
              ·
                refine ⟨45474428554776845763737201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30316285703184563842491467 45474428554776845763737201)
                ·
                  refine ⟨34105821416082634322802901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45474428554776845763737201 34105821416082634322802901)
                  ·
                    refine ⟨799355189439436741940693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34105821416082634322802901 799355189439436741940693)
                    ·
                      rfl

theorem cell22_2335108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_2335108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2335108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2335108 prefixEnd_2335108 := by exact prefixLift 2335108
  have htrace : WordTrace (prefixWord ++ tailWord_2335108) baseStart_2335108 baseEnd_2335108 := by
    simpa [prefixWord, tailWord_2335108, baseEnd_2335108] using wordTrace_append hprefix tailTrace_2335108
  have hstable : (prefixWord ++ tailWord_2335108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2335108).length < 2 ^ (prefixWord ++ tailWord_2335108).sum := by decide
  have hdescent : baseEnd_2335108 < baseStart_2335108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2335108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2335185 : List Nat := [1, 2, 2, 1, 2, 1, 1, 7, 1, 4]
def baseStart_2335185 : Nat := 118140960795 + 2335185 * 2 ^ 59
def prefixEnd_2335185 : Nat := 4983230072969 + 3 ^ 40 * 2335185 * 2
def baseEnd_2335185 : Nat := 799381548113034207765457

theorem tailTrace_2335185 : CollatzResearch.WordTrace tailWord_2335185 prefixEnd_2335185 799381548113034207765457 := by
  unfold tailWord_2335185
  simp only [CollatzResearch.WordTrace]
  refine ⟨85171194045031037691599009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56780796030020691794399339 85171194045031037691599009)
  ·
    refine ⟨63878395533773278268699257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85171194045031037691599009 63878395533773278268699257)
    ·
      refine ⟨47908796650329958701524443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63878395533773278268699257 47908796650329958701524443)
      ·
        refine ⟨71863194975494938052286665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47908796650329958701524443 71863194975494938052286665)
        ·
          refine ⟨53897396231621203539214999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71863194975494938052286665 53897396231621203539214999)
          ·
            refine ⟨80846094347431805308822499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53897396231621203539214999 80846094347431805308822499)
            ·
              refine ⟨121269141521147707963233749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80846094347431805308822499 121269141521147707963233749)
              ·
                refine ⟨2842245504401899405388291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 121269141521147707963233749 2842245504401899405388291)
                ·
                  refine ⟨4263368256602849108082437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2842245504401899405388291 4263368256602849108082437)
                  ·
                    refine ⟨799381548113034207765457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4263368256602849108082437 799381548113034207765457)
                    ·
                      rfl

theorem cell22_2335185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 7, 1, 4].length) (baseStart_2335185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2335185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2335185 prefixEnd_2335185 := by exact prefixLift 2335185
  have htrace : WordTrace (prefixWord ++ tailWord_2335185) baseStart_2335185 baseEnd_2335185 := by
    simpa [prefixWord, tailWord_2335185, baseEnd_2335185] using wordTrace_append hprefix tailTrace_2335185
  have hstable : (prefixWord ++ tailWord_2335185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2335185).length < 2 ^ (prefixWord ++ tailWord_2335185).sum := by decide
  have hdescent : baseEnd_2335185 < baseStart_2335185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2335185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2335215 : List Nat := [1, 1, 2, 1, 4, 1, 1, 2, 6, 3]
def baseStart_2335215 : Nat := 118140960795 + 2335215 * 2 ^ 59
def prefixEnd_2335215 : Nat := 4983230072969 + 3 ^ 40 * 2335215 * 2
def baseEnd_2335215 : Nat := 799391817726124129515365

theorem tailTrace_2335215 : CollatzResearch.WordTrace tailWord_2335215 prefixEnd_2335215 799391817726124129515365 := by
  unfold tailWord_2335215
  simp only [CollatzResearch.WordTrace]
  refine ⟨85172288234922352815191099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56781525489948235210127399 85172288234922352815191099)
  ·
    refine ⟨127758432352383529222786649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85172288234922352815191099 127758432352383529222786649)
    ·
      refine ⟨95818824264287646917089987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127758432352383529222786649 95818824264287646917089987)
      ·
        refine ⟨143728236396431470375634981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95818824264287646917089987 143728236396431470375634981)
        ·
          refine ⟨26949044324330900695431559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 143728236396431470375634981 26949044324330900695431559)
          ·
            refine ⟨40423566486496351043147339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26949044324330900695431559 40423566486496351043147339)
            ·
              refine ⟨60635349729744526564721009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40423566486496351043147339 60635349729744526564721009)
              ·
                refine ⟨45476512297308394923540757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60635349729744526564721009 45476512297308394923540757)
                ·
                  refine ⟨2131711513936331012040973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 45476512297308394923540757 2131711513936331012040973)
                  ·
                    refine ⟨799391817726124129515365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2131711513936331012040973 799391817726124129515365)
                    ·
                      rfl

theorem cell22_2335215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 6, 3].length) (baseStart_2335215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2335215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2335215 prefixEnd_2335215 := by exact prefixLift 2335215
  have htrace : WordTrace (prefixWord ++ tailWord_2335215) baseStart_2335215 baseEnd_2335215 := by
    simpa [prefixWord, tailWord_2335215, baseEnd_2335215] using wordTrace_append hprefix tailTrace_2335215
  have hstable : (prefixWord ++ tailWord_2335215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2335215).length < 2 ^ (prefixWord ++ tailWord_2335215).sum := by decide
  have hdescent : baseEnd_2335215 < baseStart_2335215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2335215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2335236 : List Nat := [2, 3, 2, 3, 1, 3, 2, 1, 1, 4]
def baseStart_2335236 : Nat := 118140960795 + 2335236 * 2 ^ 59
def prefixEnd_2335236 : Nat := 4983230072969 + 3 ^ 40 * 2335236 * 2
def baseEnd_2335236 : Nat := 799399006455287074740301

theorem tailTrace_2335236 : CollatzResearch.WordTrace tailWord_2335236 prefixEnd_2335236 799399006455287074740301 := by
  unfold tailWord_2335236
  simp only [CollatzResearch.WordTrace]
  refine ⟨42586527083923136700852781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56782036111897515601137041 42586527083923136700852781)
  ·
    refine ⟨15969947656471176262819793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42586527083923136700852781 15969947656471176262819793)
    ·
      refine ⟨11977460742353382197114845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15969947656471176262819793 11977460742353382197114845)
      ·
        refine ⟨4491547778382518323918067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11977460742353382197114845 4491547778382518323918067)
        ·
          refine ⟨6737321667573777485877101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4491547778382518323918067 6737321667573777485877101)
          ·
            refine ⟨2526495625340166557203913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6737321667573777485877101 2526495625340166557203913)
            ·
              refine ⟨1894871719005124917902935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2526495625340166557203913 1894871719005124917902935)
              ·
                refine ⟨2842307578507687376854403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1894871719005124917902935 2842307578507687376854403)
                ·
                  refine ⟨4263461367761531065281605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2842307578507687376854403 4263461367761531065281605)
                  ·
                    refine ⟨799399006455287074740301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4263461367761531065281605 799399006455287074740301)
                    ·
                      rfl

theorem cell22_2335236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 2, 1, 1, 4].length) (baseStart_2335236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2335236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2335236 prefixEnd_2335236 := by exact prefixLift 2335236
  have htrace : WordTrace (prefixWord ++ tailWord_2335236) baseStart_2335236 baseEnd_2335236 := by
    simpa [prefixWord, tailWord_2335236, baseEnd_2335236] using wordTrace_append hprefix tailTrace_2335236
  have hstable : (prefixWord ++ tailWord_2335236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2335236).length < 2 ^ (prefixWord ++ tailWord_2335236).sum := by decide
  have hdescent : baseEnd_2335236 < baseStart_2335236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2335236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2335290 : List Nat := [3, 1, 1, 1, 3, 3, 1, 2, 7]
def baseStart_2335290 : Nat := 118140960795 + 2335290 * 2 ^ 59
def prefixEnd_2335290 : Nat := 4983230072969 + 3 ^ 40 * 2335290 * 2
def baseEnd_2335290 : Nat := 266472497252949644630045

theorem tailTrace_2335290 : CollatzResearch.WordTrace tailWord_2335290 prefixEnd_2335290 266472497252949644630045 := by
  unfold tailWord_2335290
  simp only [CollatzResearch.WordTrace]
  refine ⟨21293755927412660156042831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56783349139767093749447549 21293755927412660156042831)
  ·
    refine ⟨31940633891118990234064247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21293755927412660156042831 31940633891118990234064247)
    ·
      refine ⟨47910950836678485351096371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31940633891118990234064247 47910950836678485351096371)
      ·
        refine ⟨71866426255017728026644557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47910950836678485351096371 71866426255017728026644557)
        ·
          refine ⟨26949909845631648009991709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71866426255017728026644557 26949909845631648009991709)
          ·
            refine ⟨10106216192111868003746891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26949909845631648009991709 10106216192111868003746891)
            ·
              refine ⟨15159324288167802005620337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10106216192111868003746891 15159324288167802005620337)
              ·
                refine ⟨11369493216125851504215253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15159324288167802005620337 11369493216125851504215253)
                ·
                  refine ⟨266472497252949644630045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11369493216125851504215253 266472497252949644630045)
                  ·
                    rfl

theorem cell22_2335290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 2, 7].length) (baseStart_2335290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2335290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2335290 prefixEnd_2335290 := by exact prefixLift 2335290
  have htrace : WordTrace (prefixWord ++ tailWord_2335290) baseStart_2335290 baseEnd_2335290 := by
    simpa [prefixWord, tailWord_2335290, baseEnd_2335290] using wordTrace_append hprefix tailTrace_2335290
  have hstable : (prefixWord ++ tailWord_2335290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2335290).length < 2 ^ (prefixWord ++ tailWord_2335290).sum := by decide
  have hdescent : baseEnd_2335290 < baseStart_2335290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2335290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2335324 : List Nat := [2, 2, 4, 1, 3, 1, 1, 3, 5]
def baseStart_2335324 : Nat := 118140960795 + 2335324 * 2 ^ 59
def prefixEnd_2335324 : Nat := 4983230072969 + 3 ^ 40 * 2335324 * 2
def baseEnd_2335324 : Nat := 266476376884561392846677

theorem tailTrace_2335324 : CollatzResearch.WordTrace tailWord_2335324 prefixEnd_2335324 266476376884561392846677 := by
  unfold tailWord_2335324
  simp only [CollatzResearch.WordTrace]
  refine ⟨42588131895763732215454513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56784175861018309620606017 42588131895763732215454513)
  ·
    refine ⟨31941098921822799161590885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42588131895763732215454513 31941098921822799161590885)
    ·
      refine ⟨5988956047841774842798291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31941098921822799161590885 5988956047841774842798291)
      ·
        refine ⟨8983434071762662264197437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5988956047841774842798291 8983434071762662264197437)
        ·
          refine ⟨3368787776910998349074039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8983434071762662264197437 3368787776910998349074039)
          ·
            refine ⟨5053181665366497523611059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3368787776910998349074039 5053181665366497523611059)
            ·
              refine ⟨7579772498049746285416589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5053181665366497523611059 7579772498049746285416589)
              ·
                refine ⟨2842414686768654857031221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7579772498049746285416589 2842414686768654857031221)
                ·
                  refine ⟨266476376884561392846677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2842414686768654857031221 266476376884561392846677)
                  ·
                    rfl

theorem cell22_2335324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 3, 5].length) (baseStart_2335324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2335324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2335324 prefixEnd_2335324 := by exact prefixLift 2335324
  have htrace : WordTrace (prefixWord ++ tailWord_2335324) baseStart_2335324 baseEnd_2335324 := by
    simpa [prefixWord, tailWord_2335324, baseEnd_2335324] using wordTrace_append hprefix tailTrace_2335324
  have hstable : (prefixWord ++ tailWord_2335324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2335324).length < 2 ^ (prefixWord ++ tailWord_2335324).sum := by decide
  have hdescent : baseEnd_2335324 < baseStart_2335324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2335324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2335335 : List Nat := [1, 1, 5, 1, 1, 1, 1, 3, 8]
def baseStart_2335335 : Nat := 118140960795 + 2335335 * 2 ^ 59
def prefixEnd_2335335 : Nat := 4983230072969 + 3 ^ 40 * 2335335 * 2
def baseEnd_2335335 : Nat := 266477632059494605504999

theorem tailTrace_2335335 : CollatzResearch.WordTrace tailWord_2335335 prefixEnd_2335335 266477632059494605504999 := by
  unfold tailWord_2335335
  simp only [CollatzResearch.WordTrace]
  refine ⟨85176664994487613309559459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56784443329658408873039639 85176664994487613309559459)
  ·
    refine ⟨127764997491731419964339189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85176664994487613309559459 127764997491731419964339189)
    ·
      refine ⟨11977968514849820621656799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 127764997491731419964339189 11977968514849820621656799)
      ·
        refine ⟨17966952772274730932485199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11977968514849820621656799 17966952772274730932485199)
        ·
          refine ⟨26950429158412096398727799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17966952772274730932485199 26950429158412096398727799)
          ·
            refine ⟨40425643737618144598091699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26950429158412096398727799 40425643737618144598091699)
            ·
              refine ⟨60638465606427216897137549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40425643737618144598091699 60638465606427216897137549)
              ·
                refine ⟨22739424602410206336426581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60638465606427216897137549 22739424602410206336426581)
                ·
                  refine ⟨266477632059494605504999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22739424602410206336426581 266477632059494605504999)
                  ·
                    rfl

theorem cell22_2335335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 8].length) (baseStart_2335335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2335335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2335335 prefixEnd_2335335 := by exact prefixLift 2335335
  have htrace : WordTrace (prefixWord ++ tailWord_2335335) baseStart_2335335 baseEnd_2335335 := by
    simpa [prefixWord, tailWord_2335335, baseEnd_2335335] using wordTrace_append hprefix tailTrace_2335335
  have hstable : (prefixWord ++ tailWord_2335335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2335335).length < 2 ^ (prefixWord ++ tailWord_2335335).sum := by decide
  have hdescent : baseEnd_2335335 < baseStart_2335335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2335335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2335362 : List Nat := [3, 4, 3, 1, 1, 1, 1, 4, 1, 3]
def baseStart_2335362 : Nat := 118140960795 + 2335362 * 2 ^ 59
def prefixEnd_2335362 : Nat := 4983230072969 + 3 ^ 40 * 2335362 * 2
def baseEnd_2335362 : Nat := 799442138830264746089915

theorem tailTrace_2335362 : CollatzResearch.WordTrace tailWord_2335362 prefixEnd_2335362 799442138830264746089915 := by
  unfold tailWord_2335362
  simp only [CollatzResearch.WordTrace]
  refine ⟨21294412441347449230198085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56785099843593197947194893 21294412441347449230198085)
  ·
    refine ⟨3992702332752646730662141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21294412441347449230198085 3992702332752646730662141)
    ·
      refine ⟨1497263374782242523998303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3992702332752646730662141 1497263374782242523998303)
      ·
        refine ⟨2245895062173363785997455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1497263374782242523998303 2245895062173363785997455)
        ·
          refine ⟨3368842593260045678996183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2245895062173363785997455 3368842593260045678996183)
          ·
            refine ⟨5053263889890068518494275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3368842593260045678996183 5053263889890068518494275)
            ·
              refine ⟨7579895834835102777741413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5053263889890068518494275 7579895834835102777741413)
              ·
                refine ⟨1421230469031581770826515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7579895834835102777741413 1421230469031581770826515)
                ·
                  refine ⟨2131845703547372656239773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1421230469031581770826515 2131845703547372656239773)
                  ·
                    refine ⟨799442138830264746089915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2131845703547372656239773 799442138830264746089915)
                    ·
                      rfl

theorem cell22_2335362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_2335362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2335362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2335362 prefixEnd_2335362 := by exact prefixLift 2335362
  have htrace : WordTrace (prefixWord ++ tailWord_2335362) baseStart_2335362 baseEnd_2335362 := by
    simpa [prefixWord, tailWord_2335362, baseEnd_2335362] using wordTrace_append hprefix tailTrace_2335362
  have hstable : (prefixWord ++ tailWord_2335362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2335362).length < 2 ^ (prefixWord ++ tailWord_2335362).sum := by decide
  have hdescent : baseEnd_2335362 < baseStart_2335362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2335362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2335384 : List Nat := [2, 1, 2, 4, 1, 1, 1, 5, 2, 3]
def baseStart_2335384 : Nat := 118140960795 + 2335384 * 2 ^ 59
def prefixEnd_2335384 : Nat := 4983230072969 + 3 ^ 40 * 2335384 * 2
def baseEnd_2335384 : Nat := 799449669879864022039847

theorem tailTrace_2335384 : CollatzResearch.WordTrace tailWord_2335384 prefixEnd_2335384 799449669879864022039847 := by
  unfold tailWord_2335384
  simp only [CollatzResearch.WordTrace]
  refine ⟨42589226085655047339046603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56785634780873396452062137 42589226085655047339046603)
  ·
    refine ⟨63883839128482571008569905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42589226085655047339046603 63883839128482571008569905)
    ·
      refine ⟨47912879346361928256427429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63883839128482571008569905 47912879346361928256427429)
      ·
        refine ⟨8983664877442861548080143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47912879346361928256427429 8983664877442861548080143)
        ·
          refine ⟨13475497316164292322120215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8983664877442861548080143 13475497316164292322120215)
          ·
            refine ⟨20213245974246438483180323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13475497316164292322120215 20213245974246438483180323)
            ·
              refine ⟨30319868961369657724770485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20213245974246438483180323 30319868961369657724770485)
              ·
                refine ⟨2842487715128405411697233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30319868961369657724770485 2842487715128405411697233)
                ·
                  refine ⟨2131865786346304058772925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2842487715128405411697233 2131865786346304058772925)
                  ·
                    refine ⟨799449669879864022039847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2131865786346304058772925 799449669879864022039847)
                    ·
                      rfl

theorem cell22_2335384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 5, 2, 3].length) (baseStart_2335384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2335384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2335384 prefixEnd_2335384 := by exact prefixLift 2335384
  have htrace : WordTrace (prefixWord ++ tailWord_2335384) baseStart_2335384 baseEnd_2335384 := by
    simpa [prefixWord, tailWord_2335384, baseEnd_2335384] using wordTrace_append hprefix tailTrace_2335384
  have hstable : (prefixWord ++ tailWord_2335384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2335384).length < 2 ^ (prefixWord ++ tailWord_2335384).sum := by decide
  have hdescent : baseEnd_2335384 < baseStart_2335384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2335384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2335395 : List Nat := [1, 1, 1, 4, 1, 1, 2, 1, 1, 9]
def baseStart_2335395 : Nat := 118140960795 + 2335395 * 2 ^ 59
def prefixEnd_2335395 : Nat := 4983230072969 + 3 ^ 40 * 2335395 * 2
def baseEnd_2335395 : Nat := 799453435404663660014813

theorem tailTrace_2335395 : CollatzResearch.WordTrace tailWord_2335395 prefixEnd_2335395 799453435404663660014813 := by
  unfold tailWord_2335395
  simp only [CollatzResearch.WordTrace]
  refine ⟨85178853374270243556743639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56785902249513495704495759 85178853374270243556743639)
  ·
    refine ⟨127768280061405365335115459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85178853374270243556743639 127768280061405365335115459)
    ·
      refine ⟨191652420092108048002673189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127768280061405365335115459 191652420092108048002673189)
      ·
        refine ⟨35934828767270259000501223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 191652420092108048002673189 35934828767270259000501223)
        ·
          refine ⟨53902243150905388500751835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35934828767270259000501223 53902243150905388500751835)
          ·
            refine ⟨80853364726358082751127753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53902243150905388500751835 80853364726358082751127753)
            ·
              refine ⟨60640023544768562063345815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80853364726358082751127753 60640023544768562063345815)
              ·
                refine ⟨90960035317152843095018723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60640023544768562063345815 90960035317152843095018723)
                ·
                  refine ⟨136440052975729264642528085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90960035317152843095018723 136440052975729264642528085)
                  ·
                    refine ⟨799453435404663660014813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 136440052975729264642528085 799453435404663660014813)
                    ·
                      rfl

theorem cell22_2335395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 9].length) (baseStart_2335395 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2335395 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2335395 prefixEnd_2335395 := by exact prefixLift 2335395
  have htrace : WordTrace (prefixWord ++ tailWord_2335395) baseStart_2335395 baseEnd_2335395 := by
    simpa [prefixWord, tailWord_2335395, baseEnd_2335395] using wordTrace_append hprefix tailTrace_2335395
  have hstable : (prefixWord ++ tailWord_2335395).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2335395).length < 2 ^ (prefixWord ++ tailWord_2335395).sum := by decide
  have hdescent : baseEnd_2335395 < baseStart_2335395 := by decide
  rcases family_descends (prefixWord ++ tailWord_2335395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2335519 : List Nat := [1, 1, 2, 4, 2, 3, 1, 2, 1, 5]
def baseStart_2335519 : Nat := 118140960795 + 2335519 * 2 ^ 59
def prefixEnd_2335519 : Nat := 4983230072969 + 3 ^ 40 * 2335519 * 2
def baseEnd_2335519 : Nat := 799495883138768669914433

theorem tailTrace_2335519 : CollatzResearch.WordTrace tailWord_2335519 prefixEnd_2335519 799495883138768669914433 := by
  unfold tailWord_2335519
  simp only [CollatzResearch.WordTrace]
  refine ⟨85183376025821012734257611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56788917350547341822838407 85183376025821012734257611)
  ·
    refine ⟨127775064038731519101386417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85183376025821012734257611 127775064038731519101386417)
    ·
      refine ⟨95831298029048639326039813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127775064038731519101386417 95831298029048639326039813)
      ·
        refine ⟨17968368380446619873632465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 95831298029048639326039813 17968368380446619873632465)
        ·
          refine ⟨13476276285334964905224349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17968368380446619873632465 13476276285334964905224349)
          ·
            refine ⟨5053603607000611839459131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13476276285334964905224349 5053603607000611839459131)
            ·
              refine ⟨7580405410500917759188697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5053603607000611839459131 7580405410500917759188697)
              ·
                refine ⟨5685304057875688319391523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7580405410500917759188697 5685304057875688319391523)
                ·
                  refine ⟨8527956086813532479087285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5685304057875688319391523 8527956086813532479087285)
                  ·
                    refine ⟨799495883138768669914433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8527956086813532479087285 799495883138768669914433)
                    ·
                      rfl

theorem cell22_2335519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 2, 1, 5].length) (baseStart_2335519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2335519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2335519 prefixEnd_2335519 := by exact prefixLift 2335519
  have htrace : WordTrace (prefixWord ++ tailWord_2335519) baseStart_2335519 baseEnd_2335519 := by
    simpa [prefixWord, tailWord_2335519, baseEnd_2335519] using wordTrace_append hprefix tailTrace_2335519
  have hstable : (prefixWord ++ tailWord_2335519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2335519).length < 2 ^ (prefixWord ++ tailWord_2335519).sum := by decide
  have hdescent : baseEnd_2335519 < baseStart_2335519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2335519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2335553 : List Nat := [1, 2, 5, 3, 1, 1, 2, 1, 1, 5]
def baseStart_2335553 : Nat := 118140960795 + 2335553 * 2 ^ 59
def prefixEnd_2335553 : Nat := 4983230072969 + 3 ^ 40 * 2335553 * 2
def baseEnd_2335553 : Nat := 799507522033603914564329

theorem tailTrace_2335553 : CollatzResearch.WordTrace tailWord_2335553 prefixEnd_2335553 799507522033603914564329 := by
  unfold tailWord_2335553
  simp only [CollatzResearch.WordTrace]
  refine ⟨85184616107697836540995313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56789744071798557693996875 85184616107697836540995313)
  ·
    refine ⟨63888462080773377405746485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85184616107697836540995313 63888462080773377405746485)
    ·
      refine ⟨5989543320072504131788733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 63888462080773377405746485 5989543320072504131788733)
      ·
        refine ⟨2246078745027189049420775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5989543320072504131788733 2246078745027189049420775)
        ·
          refine ⟨3369118117540783574131163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2246078745027189049420775 3369118117540783574131163)
          ·
            refine ⟨5053677176311175361196745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3369118117540783574131163 5053677176311175361196745)
            ·
              refine ⟨3790257882233381520897559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5053677176311175361196745 3790257882233381520897559)
              ·
                refine ⟨5685386823350072281346339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3790257882233381520897559 5685386823350072281346339)
                ·
                  refine ⟨8528080235025108422019509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5685386823350072281346339 8528080235025108422019509)
                  ·
                    refine ⟨799507522033603914564329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8528080235025108422019509 799507522033603914564329)
                    ·
                      rfl

theorem cell22_2335553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_2335553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2335553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2335553 prefixEnd_2335553 := by exact prefixLift 2335553
  have htrace : WordTrace (prefixWord ++ tailWord_2335553) baseStart_2335553 baseEnd_2335553 := by
    simpa [prefixWord, tailWord_2335553, baseEnd_2335553] using wordTrace_append hprefix tailTrace_2335553
  have hstable : (prefixWord ++ tailWord_2335553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2335553).length < 2 ^ (prefixWord ++ tailWord_2335553).sum := by decide
  have hdescent : baseEnd_2335553 < baseStart_2335553 := by decide
  rcases family_descends (prefixWord ++ tailWord_2335553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2335609 : List Nat := [1, 2, 1, 3, 2, 3, 2, 1, 2, 5]
def baseStart_2335609 : Nat := 118140960795 + 2335609 * 2 ^ 59
def prefixEnd_2335609 : Nat := 4983230072969 + 3 ^ 40 * 2335609 * 2
def baseEnd_2335609 : Nat := 799526691978038435164157

theorem tailTrace_2335609 : CollatzResearch.WordTrace tailWord_2335609 prefixEnd_2335609 799526691978038435164157 := by
  unfold tailWord_2335609
  simp only [CollatzResearch.WordTrace]
  refine ⟨85186658595494958105033881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56791105730329972070022587 85186658595494958105033881)
  ·
    refine ⟨63889993946621218578775411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85186658595494958105033881 63889993946621218578775411)
    ·
      refine ⟨95834990919931827868163117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63889993946621218578775411 95834990919931827868163117)
      ·
        refine ⟨35938121594974435450561169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95834990919931827868163117 35938121594974435450561169)
        ·
          refine ⟨26953591196230826587920877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35938121594974435450561169 26953591196230826587920877)
          ·
            refine ⟨10107596698586559970470329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26953591196230826587920877 10107596698586559970470329)
            ·
              refine ⟨7580697523939919977852747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10107596698586559970470329 7580697523939919977852747)
              ·
                refine ⟨11371046285909879966779121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7580697523939919977852747 11371046285909879966779121)
                ·
                  refine ⟨8528284714432409975084341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11371046285909879966779121 8528284714432409975084341)
                  ·
                    refine ⟨799526691978038435164157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8528284714432409975084341 799526691978038435164157)
                    ·
                      rfl

theorem cell22_2335609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 1, 2, 5].length) (baseStart_2335609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2335609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2335609 prefixEnd_2335609 := by exact prefixLift 2335609
  have htrace : WordTrace (prefixWord ++ tailWord_2335609) baseStart_2335609 baseEnd_2335609 := by
    simpa [prefixWord, tailWord_2335609, baseEnd_2335609] using wordTrace_append hprefix tailTrace_2335609
  have hstable : (prefixWord ++ tailWord_2335609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2335609).length < 2 ^ (prefixWord ++ tailWord_2335609).sum := by decide
  have hdescent : baseEnd_2335609 < baseStart_2335609 := by decide
  rcases family_descends (prefixWord ++ tailWord_2335609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2335701 : List Nat := [1, 3, 2, 3, 4, 9]
def baseStart_2335701 : Nat := 118140960795 + 2335701 * 2 ^ 59
def prefixEnd_2335701 : Nat := 4983230072969 + 3 ^ 40 * 2335701 * 2
def baseEnd_2335701 : Nat := 9871088709360257553875

theorem tailTrace_2335701 : CollatzResearch.WordTrace tailWord_2335701 prefixEnd_2335701 9871088709360257553875 := by
  unfold tailWord_2335701
  simp only [CollatzResearch.WordTrace]
  refine ⟨85190014111161657817382957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56793342740774438544921971 85190014111161657817382957)
  ·
    refine ⟨31946255291685621681518609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85190014111161657817382957 31946255291685621681518609)
    ·
      refine ⟨23959691468764216261138957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31946255291685621681518609 23959691468764216261138957)
      ·
        refine ⟨8984884300786581097927109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23959691468764216261138957 8984884300786581097927109)
        ·
          refine ⟨1684665806397483955861333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8984884300786581097927109 1684665806397483955861333)
          ·
            refine ⟨9871088709360257553875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1684665806397483955861333 9871088709360257553875)
            ·
              rfl

theorem cell22_2335701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 9].length) (baseStart_2335701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2335701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2335701 prefixEnd_2335701 := by exact prefixLift 2335701
  have htrace : WordTrace (prefixWord ++ tailWord_2335701) baseStart_2335701 baseEnd_2335701 := by
    simpa [prefixWord, tailWord_2335701, baseEnd_2335701] using wordTrace_append hprefix tailTrace_2335701
  have hstable : (prefixWord ++ tailWord_2335701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2335701).length < 2 ^ (prefixWord ++ tailWord_2335701).sum := by decide
  have hdescent : baseEnd_2335701 < baseStart_2335701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2335701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2335780 : List Nat := [2, 3, 1, 4, 1, 2, 3, 1, 5]
def baseStart_2335780 : Nat := 118140960795 + 2335780 * 2 ^ 59
def prefixEnd_2335780 : Nat := 4983230072969 + 3 ^ 40 * 2335780 * 2
def baseEnd_2335780 : Nat := 266528409590883663046211

theorem tailTrace_2335780 : CollatzResearch.WordTrace tailWord_2335780 prefixEnd_2335780 266528409590883663046211 := by
  unfold tailWord_2335780
  simp only [CollatzResearch.WordTrace]
  refine ⟨42596447738937727154754397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56795263651916969539672529 42596447738937727154754397)
  ·
    refine ⟨15973667902101647683032899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42596447738937727154754397 15973667902101647683032899)
    ·
      refine ⟨23960501853152471524549349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15973667902101647683032899 23960501853152471524549349)
      ·
        refine ⟨4492594097466088410853003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23960501853152471524549349 4492594097466088410853003)
        ·
          refine ⟨6738891146199132616279505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4492594097466088410853003 6738891146199132616279505)
          ·
            refine ⟨5054168359649349462209629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6738891146199132616279505 5054168359649349462209629)
            ·
              refine ⟨1895313134868506048328611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5054168359649349462209629 1895313134868506048328611)
              ·
                refine ⟨2842969702302759072492917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1895313134868506048328611 2842969702302759072492917)
                ·
                  refine ⟨266528409590883663046211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2842969702302759072492917 266528409590883663046211)
                  ·
                    rfl

theorem cell22_2335780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 3, 1, 5].length) (baseStart_2335780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2335780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2335780 prefixEnd_2335780 := by exact prefixLift 2335780
  have htrace : WordTrace (prefixWord ++ tailWord_2335780) baseStart_2335780 baseEnd_2335780 := by
    simpa [prefixWord, tailWord_2335780, baseEnd_2335780] using wordTrace_append hprefix tailTrace_2335780
  have hstable : (prefixWord ++ tailWord_2335780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2335780).length < 2 ^ (prefixWord ++ tailWord_2335780).sum := by decide
  have hdescent : baseEnd_2335780 < baseStart_2335780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2335780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2335793 : List Nat := [1, 2, 2, 3, 1, 2, 4, 2, 1, 4]
def baseStart_2335793 : Nat := 118140960795 + 2335793 * 2 ^ 59
def prefixEnd_2335793 : Nat := 4983230072969 + 3 ^ 40 * 2335793 * 2
def baseEnd_2335793 : Nat := 799589678938323288563593

theorem tailTrace_2335793 : CollatzResearch.WordTrace tailWord_2335793 prefixEnd_2335793 799589678938323288563593 := by
  unfold tailWord_2335793
  simp only [CollatzResearch.WordTrace]
  refine ⟨85193369626828357529732033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56795579751218905019821355 85193369626828357529732033)
  ·
    refine ⟨63895027220121268147299025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85193369626828357529732033 63895027220121268147299025)
    ·
      refine ⟨47921270415090951110474269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63895027220121268147299025 47921270415090951110474269)
      ·
        refine ⟨17970476405659106666427851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47921270415090951110474269 17970476405659106666427851)
        ·
          refine ⟨26955714608488659999641777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17970476405659106666427851 26955714608488659999641777)
          ·
            refine ⟨20216785956366494999731333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26955714608488659999641777 20216785956366494999731333)
            ·
              refine ⟨3790647366818717812449625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20216785956366494999731333 3790647366818717812449625)
              ·
                refine ⟨2842985525114038359337219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3790647366818717812449625 2842985525114038359337219)
                ·
                  refine ⟨4264478287671057539005829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2842985525114038359337219 4264478287671057539005829)
                  ·
                    refine ⟨799589678938323288563593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4264478287671057539005829 799589678938323288563593)
                    ·
                      rfl

theorem cell22_2335793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 2, 1, 4].length) (baseStart_2335793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2335793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2335793 prefixEnd_2335793 := by exact prefixLift 2335793
  have htrace : WordTrace (prefixWord ++ tailWord_2335793) baseStart_2335793 baseEnd_2335793 := by
    simpa [prefixWord, tailWord_2335793, baseEnd_2335793] using wordTrace_append hprefix tailTrace_2335793
  have hstable : (prefixWord ++ tailWord_2335793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2335793).length < 2 ^ (prefixWord ++ tailWord_2335793).sum := by decide
  have hdescent : baseEnd_2335793 < baseStart_2335793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2335793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2335870 : List Nat := [4, 2, 4, 1, 11]
def baseStart_2335870 : Nat := 118140960795 + 2335870 * 2 ^ 59
def prefixEnd_2335870 : Nat := 4983230072969 + 3 ^ 40 * 2335870 * 2
def baseEnd_2335870 : Nat := 3290600977826834380199

theorem tailTrace_2335870 : CollatzResearch.WordTrace tailWord_2335870 prefixEnd_2335870 3290600977826834380199 := by
  unfold tailWord_2335870
  simp only [CollatzResearch.WordTrace]
  refine ⟨10649522255943674960035633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56797452031699599786856709 10649522255943674960035633)
  ·
    refine ⟨7987141691957756220026725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10649522255943674960035633 7987141691957756220026725)
    ·
      refine ⟨1497589067242079291255011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7987141691957756220026725 1497589067242079291255011)
      ·
        refine ⟨2246383600863118936882517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1497589067242079291255011 2246383600863118936882517)
        ·
          refine ⟨3290600977826834380199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 2246383600863118936882517 3290600977826834380199)
          ·
            rfl

theorem cell22_2335870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 11].length) (baseStart_2335870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2335870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2335870 prefixEnd_2335870 := by exact prefixLift 2335870
  have htrace : WordTrace (prefixWord ++ tailWord_2335870) baseStart_2335870 baseEnd_2335870 := by
    simpa [prefixWord, tailWord_2335870, baseEnd_2335870] using wordTrace_append hprefix tailTrace_2335870
  have hstable : (prefixWord ++ tailWord_2335870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2335870).length < 2 ^ (prefixWord ++ tailWord_2335870).sum := by decide
  have hdescent : baseEnd_2335870 < baseStart_2335870 := by decide
  rcases family_descends (prefixWord ++ tailWord_2335870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2335902 : List Nat := [4, 3, 1, 1, 2, 2, 1, 2, 3, 3]
def baseStart_2335902 : Nat := 118140960795 + 2335902 * 2 ^ 59
def prefixEnd_2335902 : Nat := 4983230072969 + 3 ^ 40 * 2335902 * 2
def baseEnd_2335902 : Nat := 799626991865883337588259

theorem tailTrace_2335902 : CollatzResearch.WordTrace tailWord_2335902 prefixEnd_2335902 799626991865883337588259 := by
  unfold tailWord_2335902
  simp only [CollatzResearch.WordTrace]
  refine ⟨10649668147929183643181245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56798230122288979430299973 10649668147929183643181245)
  ·
    refine ⟨3993625555473443866192967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10649668147929183643181245 3993625555473443866192967)
    ·
      refine ⟨5990438333210165799289451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3993625555473443866192967 5990438333210165799289451)
      ·
        refine ⟨8985657499815248698934177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5990438333210165799289451 8985657499815248698934177)
        ·
          refine ⟨6739243124861436524200633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8985657499815248698934177 6739243124861436524200633)
          ·
            refine ⟨5054432343646077393150475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6739243124861436524200633 5054432343646077393150475)
            ·
              refine ⟨7581648515469116089725713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5054432343646077393150475 7581648515469116089725713)
              ·
                refine ⟨5686236386601837067294285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7581648515469116089725713 5686236386601837067294285)
                ·
                  refine ⟨2132338644975688900235357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5686236386601837067294285 2132338644975688900235357)
                  ·
                    refine ⟨799626991865883337588259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2132338644975688900235357 799626991865883337588259)
                    ·
                      rfl

theorem cell22_2335902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_2335902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2335902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2335902 prefixEnd_2335902 := by exact prefixLift 2335902
  have htrace : WordTrace (prefixWord ++ tailWord_2335902) baseStart_2335902 baseEnd_2335902 := by
    simpa [prefixWord, tailWord_2335902, baseEnd_2335902] using wordTrace_append hprefix tailTrace_2335902
  have hstable : (prefixWord ++ tailWord_2335902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2335902).length < 2 ^ (prefixWord ++ tailWord_2335902).sum := by decide
  have hdescent : baseEnd_2335902 < baseStart_2335902 := by decide
  rcases family_descends (prefixWord ++ tailWord_2335902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2336048 : List Nat := [2, 1, 1, 1, 2, 2, 4, 2, 2, 5]
def baseStart_2336048 : Nat := 118140960795 + 2336048 * 2 ^ 59
def prefixEnd_2336048 : Nat := 4983230072969 + 3 ^ 40 * 2336048 * 2
def baseEnd_2336048 : Nat := 799676970649587623437811

theorem tailTrace_2336048 : CollatzResearch.WordTrace tailWord_2336048 prefixEnd_2336048 799676970649587623437811 := by
  unfold tailWord_2336048
  simp only [CollatzResearch.WordTrace]
  refine ⟨42601335120452268040132399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56801780160603024053509865 42601335120452268040132399)
  ·
    refine ⟨63902002680678402060198599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42601335120452268040132399 63902002680678402060198599)
    ·
      refine ⟨95853004021017603090297899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63902002680678402060198599 95853004021017603090297899)
      ·
        refine ⟨143779506031526404635446849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95853004021017603090297899 143779506031526404635446849)
        ·
          refine ⟨107834629523644803476585137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143779506031526404635446849 107834629523644803476585137)
          ·
            refine ⟨80875972142733602607438853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107834629523644803476585137 80875972142733602607438853)
            ·
              refine ⟨15164244776762550488894785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 80875972142733602607438853 15164244776762550488894785)
              ·
                refine ⟨11373183582571912866671089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15164244776762550488894785 11373183582571912866671089)
                ·
                  refine ⟨8529887686928934650003317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11373183582571912866671089 8529887686928934650003317)
                  ·
                    refine ⟨799676970649587623437811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8529887686928934650003317 799676970649587623437811)
                    ·
                      rfl

theorem cell22_2336048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 2, 2, 5].length) (baseStart_2336048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2336048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2336048 prefixEnd_2336048 := by exact prefixLift 2336048
  have htrace : WordTrace (prefixWord ++ tailWord_2336048) baseStart_2336048 baseEnd_2336048 := by
    simpa [prefixWord, tailWord_2336048, baseEnd_2336048] using wordTrace_append hprefix tailTrace_2336048
  have hstable : (prefixWord ++ tailWord_2336048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2336048).length < 2 ^ (prefixWord ++ tailWord_2336048).sum := by decide
  have hdescent : baseEnd_2336048 < baseStart_2336048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2336048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2336050 : List Nat := [3, 2, 1, 1, 4, 1, 1, 4, 5]
def baseStart_2336050 : Nat := 118140960795 + 2336050 * 2 ^ 59
def prefixEnd_2336050 : Nat := 4983230072969 + 3 ^ 40 * 2336050 * 2
def baseEnd_2336050 : Nat := 266559218430153428295935

theorem tailTrace_2336050 : CollatzResearch.WordTrace tailWord_2336050 prefixEnd_2336050 266559218430153428295935 := by
  unfold tailWord_2336050
  simp only [CollatzResearch.WordTrace]
  refine ⟨21300685796724322605459401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56801828791264860281225069 21300685796724322605459401)
  ·
    refine ⟨15975514347543241954094551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21300685796724322605459401 15975514347543241954094551)
    ·
      refine ⟨23963271521314862931141827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15975514347543241954094551 23963271521314862931141827)
      ·
        refine ⟨35944907281972294396712741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23963271521314862931141827 35944907281972294396712741)
        ·
          refine ⟨6739670115369805199383639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35944907281972294396712741 6739670115369805199383639)
          ·
            refine ⟨10109505173054707799075459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6739670115369805199383639 10109505173054707799075459)
            ·
              refine ⟨15164257759582061698613189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10109505173054707799075459 15164257759582061698613189)
              ·
                refine ⟨2843298329921636568489973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15164257759582061698613189 2843298329921636568489973)
                ·
                  refine ⟨266559218430153428295935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2843298329921636568489973 266559218430153428295935)
                  ·
                    rfl

theorem cell22_2336050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 4, 5].length) (baseStart_2336050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2336050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2336050 prefixEnd_2336050 := by exact prefixLift 2336050
  have htrace : WordTrace (prefixWord ++ tailWord_2336050) baseStart_2336050 baseEnd_2336050 := by
    simpa [prefixWord, tailWord_2336050, baseEnd_2336050] using wordTrace_append hprefix tailTrace_2336050
  have hstable : (prefixWord ++ tailWord_2336050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2336050).length < 2 ^ (prefixWord ++ tailWord_2336050).sum := by decide
  have hdescent : baseEnd_2336050 < baseStart_2336050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2336050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2336065 : List Nat := [1, 2, 5, 2, 1, 1, 1, 1, 1, 7]
def baseStart_2336065 : Nat := 118140960795 + 2336065 * 2 ^ 59
def prefixEnd_2336065 : Nat := 4983230072969 + 3 ^ 40 * 2336065 * 2
def baseEnd_2336065 : Nat := 799682790097005245762759

theorem tailTrace_2336065 : CollatzResearch.WordTrace tailWord_2336065 prefixEnd_2336065 799682790097005245762759 := by
  unfold tailWord_2336065
  simp only [CollatzResearch.WordTrace]
  refine ⟨85203290281842947983633649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56802193521228631989089099 85203290281842947983633649)
  ·
    refine ⟨63902467711382210987725237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85203290281842947983633649 63902467711382210987725237)
    ·
      refine ⟨5990856347942082280099241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 63902467711382210987725237 5990856347942082280099241)
      ·
        refine ⟨4493142260956561710074431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5990856347942082280099241 4493142260956561710074431)
        ·
          refine ⟨6739713391434842565111647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4493142260956561710074431 6739713391434842565111647)
          ·
            refine ⟨10109570087152263847667471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6739713391434842565111647 10109570087152263847667471)
            ·
              refine ⟨15164355130728395771501207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10109570087152263847667471 15164355130728395771501207)
              ·
                refine ⟨22746532696092593657251811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15164355130728395771501207 22746532696092593657251811)
                ·
                  refine ⟨34119799044138890485877717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22746532696092593657251811 34119799044138890485877717)
                  ·
                    refine ⟨799682790097005245762759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34119799044138890485877717 799682790097005245762759)
                    ·
                      rfl

theorem cell22_2336065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_2336065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2336065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2336065 prefixEnd_2336065 := by exact prefixLift 2336065
  have htrace : WordTrace (prefixWord ++ tailWord_2336065) baseStart_2336065 baseEnd_2336065 := by
    simpa [prefixWord, tailWord_2336065, baseEnd_2336065] using wordTrace_append hprefix tailTrace_2336065
  have hstable : (prefixWord ++ tailWord_2336065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2336065).length < 2 ^ (prefixWord ++ tailWord_2336065).sum := by decide
  have hdescent : baseEnd_2336065 < baseStart_2336065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2336065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2336080 : List Nat := [2, 1, 1, 1, 1, 5, 2, 4, 1, 4]
def baseStart_2336080 : Nat := 118140960795 + 2336080 * 2 ^ 59
def prefixEnd_2336080 : Nat := 4983230072969 + 3 ^ 40 * 2336080 * 2
def baseEnd_2336080 : Nat := 799687924903550206637713

theorem tailTrace_2336080 : CollatzResearch.WordTrace tailWord_2336080 prefixEnd_2336080 799687924903550206637713 := by
  unfold tailWord_2336080
  simp only [CollatzResearch.WordTrace]
  refine ⟨42601918688394302772714847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56802558251192403696953129 42601918688394302772714847)
  ·
    refine ⟨63902878032591454159072271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42601918688394302772714847 63902878032591454159072271)
    ·
      refine ⟨95854317048887181238608407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63902878032591454159072271 95854317048887181238608407)
      ·
        refine ⟨143781475573330771857912611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95854317048887181238608407 143781475573330771857912611)
        ·
          refine ⟨215672213359996157786868917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143781475573330771857912611 215672213359996157786868917)
          ·
            refine ⟨20219270002499639792518961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 215672213359996157786868917 20219270002499639792518961)
            ·
              refine ⟨15164452501874729844389221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20219270002499639792518961 15164452501874729844389221)
              ·
                refine ⟨2843334844101511845822979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15164452501874729844389221 2843334844101511845822979)
                ·
                  refine ⟨4265002266152267768734469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2843334844101511845822979 4265002266152267768734469)
                  ·
                    refine ⟨799687924903550206637713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4265002266152267768734469 799687924903550206637713)
                    ·
                      rfl

theorem cell22_2336080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 4, 1, 4].length) (baseStart_2336080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2336080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2336080 prefixEnd_2336080 := by exact prefixLift 2336080
  have htrace : WordTrace (prefixWord ++ tailWord_2336080) baseStart_2336080 baseEnd_2336080 := by
    simpa [prefixWord, tailWord_2336080, baseEnd_2336080] using wordTrace_append hprefix tailTrace_2336080
  have hstable : (prefixWord ++ tailWord_2336080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2336080).length < 2 ^ (prefixWord ++ tailWord_2336080).sum := by decide
  have hdescent : baseEnd_2336080 < baseStart_2336080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2336080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2336123 : List Nat := [1, 1, 1, 1, 1, 6, 2, 9]
def baseStart_2336123 : Nat := 118140960795 + 2336123 * 2 ^ 59
def prefixEnd_2336123 : Nat := 4983230072969 + 3 ^ 40 * 2336123 * 2
def baseEnd_2336123 : Nat := 88855849409145825312509

theorem tailTrace_2336123 : CollatzResearch.WordTrace tailWord_2336123 prefixEnd_2336123 88855849409145825312509 := by
  unfold tailWord_2336123
  simp only [CollatzResearch.WordTrace]
  refine ⟨85205405715632823889245023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56803603810421882592830015 85205405715632823889245023)
  ·
    refine ⟨127808108573449235833867535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85205405715632823889245023 127808108573449235833867535)
    ·
      refine ⟨191712162860173853750801303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127808108573449235833867535 191712162860173853750801303)
      ·
        refine ⟨287568244290260780626201955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191712162860173853750801303 287568244290260780626201955)
        ·
          refine ⟨431352366435391170939302933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 287568244290260780626201955 431352366435391170939302933)
          ·
            refine ⟨20219642176658961137779825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 431352366435391170939302933 20219642176658961137779825)
            ·
              refine ⟨15164731632494220853334869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20219642176658961137779825 15164731632494220853334869)
              ·
                refine ⟨88855849409145825312509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15164731632494220853334869 88855849409145825312509)
                ·
                  rfl

theorem cell22_2336123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 9].length) (baseStart_2336123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2336123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2336123 prefixEnd_2336123 := by exact prefixLift 2336123
  have htrace : WordTrace (prefixWord ++ tailWord_2336123) baseStart_2336123 baseEnd_2336123 := by
    simpa [prefixWord, tailWord_2336123, baseEnd_2336123] using wordTrace_append hprefix tailTrace_2336123
  have hstable : (prefixWord ++ tailWord_2336123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2336123).length < 2 ^ (prefixWord ++ tailWord_2336123).sum := by decide
  have hdescent : baseEnd_2336123 < baseStart_2336123 := by decide
  rcases family_descends (prefixWord ++ tailWord_2336123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2336172 : List Nat := [2, 2, 1, 1, 1, 1, 7, 1, 3, 3]
def baseStart_2336172 : Nat := 118140960795 + 2336172 * 2 ^ 59
def prefixEnd_2336172 : Nat := 4983230072969 + 3 ^ 40 * 2336172 * 2
def baseEnd_2336172 : Nat := 799719418383692633337431

theorem tailTrace_2336172 : CollatzResearch.WordTrace tailWord_2336172 prefixEnd_2336172 799719418383692633337431 := by
  unfold tailWord_2336172
  simp only [CollatzResearch.WordTrace]
  refine ⟨42603596446227652628889385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56804795261636870171852513 42603596446227652628889385)
  ·
    refine ⟨31952697334670739471667039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42603596446227652628889385 31952697334670739471667039)
    ·
      refine ⟨47929046002006109207500559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31952697334670739471667039 47929046002006109207500559)
      ·
        refine ⟨71893569003009163811250839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47929046002006109207500559 71893569003009163811250839)
        ·
          refine ⟨107840353504513745716876259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71893569003009163811250839 107840353504513745716876259)
          ·
            refine ⟨161760530256770618575314389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107840353504513745716876259 161760530256770618575314389)
            ·
              refine ⟨3791262427893061372858931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 161760530256770618575314389 3791262427893061372858931)
              ·
                refine ⟨5686893641839592059288397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3791262427893061372858931 5686893641839592059288397)
                ·
                  refine ⟨2132585115689847022233149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5686893641839592059288397 2132585115689847022233149)
                  ·
                    refine ⟨799719418383692633337431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2132585115689847022233149 799719418383692633337431)
                    ·
                      rfl

theorem cell22_2336172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 3].length) (baseStart_2336172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2336172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2336172 prefixEnd_2336172 := by exact prefixLift 2336172
  have htrace : WordTrace (prefixWord ++ tailWord_2336172) baseStart_2336172 baseEnd_2336172 := by
    simpa [prefixWord, tailWord_2336172, baseEnd_2336172] using wordTrace_append hprefix tailTrace_2336172
  have hstable : (prefixWord ++ tailWord_2336172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2336172).length < 2 ^ (prefixWord ++ tailWord_2336172).sum := by decide
  have hdescent : baseEnd_2336172 < baseStart_2336172 := by decide
  rcases family_descends (prefixWord ++ tailWord_2336172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2336266 : List Nat := [3, 1, 2, 2, 2, 4, 2, 1, 1, 4]
def baseStart_2336266 : Nat := 118140960795 + 2336266 * 2 ^ 59
def prefixEnd_2336266 : Nat := 4983230072969 + 3 ^ 40 * 2336266 * 2
def baseEnd_2336266 : Nat := 799751596504707721487143

theorem tailTrace_2336266 : CollatzResearch.WordTrace tailWord_2336266 prefixEnd_2336266 799751596504707721487143 := by
  unfold tailWord_2336266
  simp only [CollatzResearch.WordTrace]
  refine ⟨21302655338528689827925163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56807080902743172874467101 21302655338528689827925163)
  ·
    refine ⟨31953983007793034741887745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21302655338528689827925163 31953983007793034741887745)
    ·
      refine ⟨23965487255844776056415809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31953983007793034741887745 23965487255844776056415809)
      ·
        refine ⟨17974115441883582042311857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23965487255844776056415809 17974115441883582042311857)
        ·
          refine ⟨13480586581412686531733893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17974115441883582042311857 13480586581412686531733893)
          ·
            refine ⟨2527609984014878724700105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13480586581412686531733893 2527609984014878724700105)
            ·
              refine ⟨1895707488011159043525079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2527609984014878724700105 1895707488011159043525079)
              ·
                refine ⟨2843561232016738565287619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1895707488011159043525079 2843561232016738565287619)
                ·
                  refine ⟨4265341848025107847931429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2843561232016738565287619 4265341848025107847931429)
                  ·
                    refine ⟨799751596504707721487143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4265341848025107847931429 799751596504707721487143)
                    ·
                      rfl

theorem cell22_2336266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 2, 1, 1, 4].length) (baseStart_2336266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2336266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2336266 prefixEnd_2336266 := by exact prefixLift 2336266
  have htrace : WordTrace (prefixWord ++ tailWord_2336266) baseStart_2336266 baseEnd_2336266 := by
    simpa [prefixWord, tailWord_2336266, baseEnd_2336266] using wordTrace_append hprefix tailTrace_2336266
  have hstable : (prefixWord ++ tailWord_2336266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2336266).length < 2 ^ (prefixWord ++ tailWord_2336266).sum := by decide
  have hdescent : baseEnd_2336266 < baseStart_2336266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2336266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2336275 : List Nat := [1, 1, 1, 2, 1, 7, 9]
def baseStart_2336275 : Nat := 118140960795 + 2336275 * 2 ^ 59
def prefixEnd_2336275 : Nat := 4983230072969 + 3 ^ 40 * 2336275 * 2
def baseEnd_2336275 : Nat := 29620543606986470296745

theorem tailTrace_2336275 : CollatzResearch.WordTrace tailWord_2336275 prefixEnd_2336275 29620543606986470296745 := by
  unfold tailWord_2336275
  simp only [CollatzResearch.WordTrace]
  refine ⟨85210949611082153848778279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56807299740721435899185519 85210949611082153848778279)
  ·
    refine ⟨127816424416623230773167419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85210949611082153848778279 127816424416623230773167419)
    ·
      refine ⟨191724636624934846159751129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127816424416623230773167419 191724636624934846159751129)
      ·
        refine ⟨143793477468701134619813347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191724636624934846159751129 143793477468701134619813347)
        ·
          refine ⟨215690216203051701929720021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143793477468701134619813347 215690216203051701929720021)
          ·
            refine ⟨5055239442259024263977813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 215690216203051701929720021 5055239442259024263977813)
            ·
              refine ⟨29620543606986470296745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5055239442259024263977813 29620543606986470296745)
              ·
                rfl

theorem cell22_2336275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 9].length) (baseStart_2336275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2336275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2336275 prefixEnd_2336275 := by exact prefixLift 2336275
  have htrace : WordTrace (prefixWord ++ tailWord_2336275) baseStart_2336275 baseEnd_2336275 := by
    simpa [prefixWord, tailWord_2336275, baseEnd_2336275] using wordTrace_append hprefix tailTrace_2336275
  have hstable : (prefixWord ++ tailWord_2336275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2336275).length < 2 ^ (prefixWord ++ tailWord_2336275).sum := by decide
  have hdescent : baseEnd_2336275 < baseStart_2336275 := by decide
  rcases family_descends (prefixWord ++ tailWord_2336275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2336296 : List Nat := [2, 1, 5, 2, 2, 2, 1, 1, 1, 5]
def baseStart_2336296 : Nat := 118140960795 + 2336296 * 2 ^ 59
def prefixEnd_2336296 : Nat := 4983230072969 + 3 ^ 40 * 2336296 * 2
def baseEnd_2336296 : Nat := 799761866117797643237051

theorem tailTrace_2336296 : CollatzResearch.WordTrace tailWord_2336296 prefixEnd_2336296 799761866117797643237051 := by
  unfold tailWord_2336296
  simp only [CollatzResearch.WordTrace]
  refine ⟨42605857772003037217646371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56807810362670716290195161 42605857772003037217646371)
  ·
    refine ⟨63908786658004555826469557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42605857772003037217646371 63908786658004555826469557)
    ·
      refine ⟨5991448749187927108731521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 63908786658004555826469557 5991448749187927108731521)
      ·
        refine ⟨4493586561890945331548641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5991448749187927108731521 4493586561890945331548641)
        ·
          refine ⟨3370189921418208998661481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4493586561890945331548641 3370189921418208998661481)
          ·
            refine ⟨2527642441063656748996111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3370189921418208998661481 2527642441063656748996111)
            ·
              refine ⟨3791463661595485123494167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2527642441063656748996111 3791463661595485123494167)
              ·
                refine ⟨5687195492393227685241251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3791463661595485123494167 5687195492393227685241251)
                ·
                  refine ⟨8530793238589841527861877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5687195492393227685241251 8530793238589841527861877)
                  ·
                    refine ⟨799761866117797643237051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8530793238589841527861877 799761866117797643237051)
                    ·
                      rfl

theorem cell22_2336296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_2336296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2336296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2336296 prefixEnd_2336296 := by exact prefixLift 2336296
  have htrace : WordTrace (prefixWord ++ tailWord_2336296) baseStart_2336296 baseEnd_2336296 := by
    simpa [prefixWord, tailWord_2336296, baseEnd_2336296] using wordTrace_append hprefix tailTrace_2336296
  have hstable : (prefixWord ++ tailWord_2336296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2336296).length < 2 ^ (prefixWord ++ tailWord_2336296).sum := by decide
  have hdescent : baseEnd_2336296 < baseStart_2336296 := by decide
  rcases family_descends (prefixWord ++ tailWord_2336296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2336309 : List Nat := [1, 3, 3, 1, 1, 5, 2, 6]
def baseStart_2336309 : Nat := 118140960795 + 2336309 * 2 ^ 59
def prefixEnd_2336309 : Nat := 4983230072969 + 3 ^ 40 * 2336309 * 2
def baseEnd_2336309 : Nat := 88862924031496660295779

theorem tailTrace_2336309 : CollatzResearch.WordTrace tailWord_2336309 prefixEnd_2336309 88862924031496660295779 := by
  unfold tailWord_2336309
  simp only [CollatzResearch.WordTrace]
  refine ⟨85212189692958977655515981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56808126461972651770343987 85212189692958977655515981)
  ·
    refine ⟨31954571134859616620818493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85212189692958977655515981 31954571134859616620818493)
    ·
      refine ⟨11982964175572356232806935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31954571134859616620818493 11982964175572356232806935)
      ·
        refine ⟨17974446263358534349210403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11982964175572356232806935 17974446263358534349210403)
        ·
          refine ⟨26961669395037801523815605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17974446263358534349210403 26961669395037801523815605)
          ·
            refine ⟨2527656505784793892857713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26961669395037801523815605 2527656505784793892857713)
            ·
              refine ⟨1895742379338595419643285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2527656505784793892857713 1895742379338595419643285)
              ·
                refine ⟨88862924031496660295779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1895742379338595419643285 88862924031496660295779)
                ·
                  rfl

theorem cell22_2336309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 2, 6].length) (baseStart_2336309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2336309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2336309 prefixEnd_2336309 := by exact prefixLift 2336309
  have htrace : WordTrace (prefixWord ++ tailWord_2336309) baseStart_2336309 baseEnd_2336309 := by
    simpa [prefixWord, tailWord_2336309, baseEnd_2336309] using wordTrace_append hprefix tailTrace_2336309
  have hstable : (prefixWord ++ tailWord_2336309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2336309).length < 2 ^ (prefixWord ++ tailWord_2336309).sum := by decide
  have hdescent : baseEnd_2336309 < baseStart_2336309 := by decide
  rcases family_descends (prefixWord ++ tailWord_2336309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2336326 : List Nat := [6, 1, 1, 1, 3, 2, 8]
def baseStart_2336326 : Nat := 118140960795 + 2336326 * 2 ^ 59
def prefixEnd_2336326 : Nat := 4983230072969 + 3 ^ 40 * 2336326 * 2
def baseEnd_2336326 : Nat := 29621190212255094999517

theorem tailTrace_2336326 : CollatzResearch.WordTrace tailWord_2336326 prefixEnd_2336326 29621190212255094999517 := by
  unfold tailWord_2336326
  simp only [CollatzResearch.WordTrace]
  refine ⟨2662900304184293423715151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 56808539822598259705923221 2662900304184293423715151)
  ·
    refine ⟨3994350456276440135572727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2662900304184293423715151 3994350456276440135572727)
    ·
      refine ⟨5991525684414660203359091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3994350456276440135572727 5991525684414660203359091)
      ·
        refine ⟨8987288526621990305038637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5991525684414660203359091 8987288526621990305038637)
        ·
          refine ⟨3370233197483246364389489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8987288526621990305038637 3370233197483246364389489)
          ·
            refine ⟨2527674898112434773292117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3370233197483246364389489 2527674898112434773292117)
            ·
              refine ⟨29621190212255094999517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2527674898112434773292117 29621190212255094999517)
              ·
                rfl

theorem cell22_2336326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 8].length) (baseStart_2336326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2336326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2336326 prefixEnd_2336326 := by exact prefixLift 2336326
  have htrace : WordTrace (prefixWord ++ tailWord_2336326) baseStart_2336326 baseEnd_2336326 := by
    simpa [prefixWord, tailWord_2336326, baseEnd_2336326] using wordTrace_append hprefix tailTrace_2336326
  have hstable : (prefixWord ++ tailWord_2336326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2336326).length < 2 ^ (prefixWord ++ tailWord_2336326).sum := by decide
  have hdescent : baseEnd_2336326 < baseStart_2336326 := by decide
  rcases family_descends (prefixWord ++ tailWord_2336326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2336337 : List Nat := [1, 2, 2, 1, 3, 2, 2, 4, 5]
def baseStart_2336337 : Nat := 118140960795 + 2336337 * 2 ^ 59
def prefixEnd_2336337 : Nat := 4983230072969 + 3 ^ 40 * 2336337 * 2
def baseEnd_2336337 : Nat := 266591967085229067653975

theorem tailTrace_2336337 : CollatzResearch.WordTrace tailWord_2336337 prefixEnd_2336337 266591967085229067653975 := by
  unfold tailWord_2336337
  simp only [CollatzResearch.WordTrace]
  refine ⟨85213210936857538437535265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56808807291238358958356843 85213210936857538437535265)
  ·
    refine ⟨63909908202643153828151449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85213210936857538437535265 63909908202643153828151449)
    ·
      refine ⟨47932431151982365371113587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63909908202643153828151449 47932431151982365371113587)
      ·
        refine ⟨71898646727973548056670381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47932431151982365371113587 71898646727973548056670381)
        ·
          refine ⟨26961992522990080521251393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71898646727973548056670381 26961992522990080521251393)
          ·
            refine ⟨20221494392242560390938545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26961992522990080521251393 20221494392242560390938545)
            ·
              refine ⟨15166120794181920293203909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20221494392242560390938545 15166120794181920293203909)
              ·
                refine ⟨2843647648909110054975733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15166120794181920293203909 2843647648909110054975733)
                ·
                  refine ⟨266591967085229067653975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2843647648909110054975733 266591967085229067653975)
                  ·
                    rfl

theorem cell22_2336337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 4, 5].length) (baseStart_2336337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2336337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2336337 prefixEnd_2336337 := by exact prefixLift 2336337
  have htrace : WordTrace (prefixWord ++ tailWord_2336337) baseStart_2336337 baseEnd_2336337 := by
    simpa [prefixWord, tailWord_2336337, baseEnd_2336337] using wordTrace_append hprefix tailTrace_2336337
  have hstable : (prefixWord ++ tailWord_2336337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2336337).length < 2 ^ (prefixWord ++ tailWord_2336337).sum := by decide
  have hdescent : baseEnd_2336337 < baseStart_2336337 := by decide
  rcases family_descends (prefixWord ++ tailWord_2336337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2336392 : List Nat := [2, 1, 3, 5, 1, 2, 2, 2, 1, 3]
def baseStart_2336392 : Nat := 118140960795 + 2336392 * 2 ^ 59
def prefixEnd_2336392 : Nat := 4983230072969 + 3 ^ 40 * 2336392 * 2
def baseEnd_2336392 : Nat := 799794728879685392836757

theorem tailTrace_2336392 : CollatzResearch.WordTrace tailWord_2336392 prefixEnd_2336392 799794728879685392836757 := by
  unfold tailWord_2336392
  simp only [CollatzResearch.WordTrace]
  refine ⟨42607608475829141415393715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56810144634438855220524953 42607608475829141415393715)
  ·
    refine ⟨63911412713743712123090573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42607608475829141415393715 63911412713743712123090573)
    ·
      refine ⟨23966779767653892046158965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63911412713743712123090573 23966779767653892046158965)
      ·
        refine ⟨2246885603217552379327403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23966779767653892046158965 2246885603217552379327403)
        ·
          refine ⟨3370328404826328568991105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2246885603217552379327403 3370328404826328568991105)
          ·
            refine ⟨2527746303619746426743329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3370328404826328568991105 2527746303619746426743329)
            ·
              refine ⟨1895809727714809820057497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2527746303619746426743329 1895809727714809820057497)
              ·
                refine ⟨1421857295786107365043123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1895809727714809820057497 1421857295786107365043123)
                ·
                  refine ⟨2132785943679161047564685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1421857295786107365043123 2132785943679161047564685)
                  ·
                    refine ⟨799794728879685392836757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2132785943679161047564685 799794728879685392836757)
                    ·
                      rfl

theorem cell22_2336392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 2, 2, 1, 3].length) (baseStart_2336392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2336392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2336392 prefixEnd_2336392 := by exact prefixLift 2336392
  have htrace : WordTrace (prefixWord ++ tailWord_2336392) baseStart_2336392 baseEnd_2336392 := by
    simpa [prefixWord, tailWord_2336392, baseEnd_2336392] using wordTrace_append hprefix tailTrace_2336392
  have hstable : (prefixWord ++ tailWord_2336392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2336392).length < 2 ^ (prefixWord ++ tailWord_2336392).sum := by decide
  have hdescent : baseEnd_2336392 < baseStart_2336392 := by decide
  rcases family_descends (prefixWord ++ tailWord_2336392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2336429 : List Nat := [1, 5, 2, 1, 1, 1, 3, 1, 1, 6]
def baseStart_2336429 : Nat := 118140960795 + 2336429 * 2 ^ 59
def prefixEnd_2336429 : Nat := 4983230072969 + 3 ^ 40 * 2336429 * 2
def baseEnd_2336429 : Nat := 799807394735829629661643

theorem tailTrace_2336429 : CollatzResearch.WordTrace tailWord_2336429 prefixEnd_2336429 799807394735829629661643 := by
  unfold tailWord_2336429
  simp only [CollatzResearch.WordTrace]
  refine ⟨85216566452524238149884341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56811044301682825433256227 85216566452524238149884341)
  ·
    refine ⟨7989053104924147326551657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 85216566452524238149884341 7989053104924147326551657)
    ·
      refine ⟨5991789828693110494913743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7989053104924147326551657 5991789828693110494913743)
      ·
        refine ⟨8987684743039665742370615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5991789828693110494913743 8987684743039665742370615)
        ·
          refine ⟨13481527114559498613555923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8987684743039665742370615 13481527114559498613555923)
          ·
            refine ⟨20222290671839247920333885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13481527114559498613555923 20222290671839247920333885)
            ·
              refine ⟨7583359001939717970125207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20222290671839247920333885 7583359001939717970125207)
              ·
                refine ⟨11375038502909576955187811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7583359001939717970125207 11375038502909576955187811)
                ·
                  refine ⟨17062557754364365432781717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11375038502909576955187811 17062557754364365432781717)
                  ·
                    refine ⟨799807394735829629661643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17062557754364365432781717 799807394735829629661643)
                    ·
                      rfl

theorem cell22_2336429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_2336429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2336429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2336429 prefixEnd_2336429 := by exact prefixLift 2336429
  have htrace : WordTrace (prefixWord ++ tailWord_2336429) baseStart_2336429 baseEnd_2336429 := by
    simpa [prefixWord, tailWord_2336429, baseEnd_2336429] using wordTrace_append hprefix tailTrace_2336429
  have hstable : (prefixWord ++ tailWord_2336429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2336429).length < 2 ^ (prefixWord ++ tailWord_2336429).sum := by decide
  have hdescent : baseEnd_2336429 < baseStart_2336429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2336429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2336450 : List Nat := [3, 5, 1, 2, 1, 1, 2, 1, 6]
def baseStart_2336450 : Nat := 118140960795 + 2336450 * 2 ^ 59
def prefixEnd_2336450 : Nat := 4983230072969 + 3 ^ 40 * 2336450 * 2
def baseEnd_2336450 : Nat := 266604861154997524962193

theorem tailTrace_2336450 : CollatzResearch.WordTrace tailWord_2336450 prefixEnd_2336450 266604861154997524962193 := by
  unfold tailWord_2336450
  simp only [CollatzResearch.WordTrace]
  refine ⟨21304333096362039684099701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56811554923632105824265869 21304333096362039684099701)
  ·
    refine ⟨1997281227783941220384347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21304333096362039684099701 1997281227783941220384347)
    ·
      refine ⟨2995921841675911830576521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1997281227783941220384347 2995921841675911830576521)
      ·
        refine ⟨2246941381256933872932391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2995921841675911830576521 2246941381256933872932391)
        ·
          refine ⟨3370412071885400809398587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2246941381256933872932391 3370412071885400809398587)
          ·
            refine ⟨5055618107828101214097881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3370412071885400809398587 5055618107828101214097881)
            ·
              refine ⟨3791713580871075910573411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5055618107828101214097881 3791713580871075910573411)
              ·
                refine ⟨5687570371306613865860117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3791713580871075910573411 5687570371306613865860117)
                ·
                  refine ⟨266604861154997524962193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5687570371306613865860117 266604861154997524962193)
                  ·
                    rfl

theorem cell22_2336450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_2336450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2336450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2336450 prefixEnd_2336450 := by exact prefixLift 2336450
  have htrace : WordTrace (prefixWord ++ tailWord_2336450) baseStart_2336450 baseEnd_2336450 := by
    simpa [prefixWord, tailWord_2336450, baseEnd_2336450] using wordTrace_append hprefix tailTrace_2336450
  have hstable : (prefixWord ++ tailWord_2336450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2336450).length < 2 ^ (prefixWord ++ tailWord_2336450).sum := by decide
  have hdescent : baseEnd_2336450 < baseStart_2336450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2336450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2336510 : List Nat := [4, 2, 2, 1, 3, 2, 1, 1, 3, 3]
def baseStart_2336510 : Nat := 118140960795 + 2336510 * 2 ^ 59
def prefixEnd_2336510 : Nat := 4983230072969 + 3 ^ 40 * 2336510 * 2
def baseEnd_2336510 : Nat := 799835122691172418386395

theorem tailTrace_2336510 : CollatzResearch.WordTrace tailWord_2336510 prefixEnd_2336510 799835122691172418386395 := by
  unfold tailWord_2336510
  simp only [CollatzResearch.WordTrace]
  refine ⟨10652440095653848622947873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56813013843487192655721989 10652440095653848622947873)
  ·
    refine ⟨7989330071740386467210905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10652440095653848622947873 7989330071740386467210905)
    ·
      refine ⟨5991997553805289850408179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7989330071740386467210905 5991997553805289850408179)
      ·
        refine ⟨8987996330707934775612269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5991997553805289850408179 8987996330707934775612269)
        ·
          refine ⟨3370498624015475540854601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8987996330707934775612269 3370498624015475540854601)
          ·
            refine ⟨2527873968011606655640951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3370498624015475540854601 2527873968011606655640951)
            ·
              refine ⟨3791810952017409983461427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2527873968011606655640951 3791810952017409983461427)
              ·
                refine ⟨5687716428026114975192141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3791810952017409983461427 5687716428026114975192141)
                ·
                  refine ⟨2132893660509793115697053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5687716428026114975192141 2132893660509793115697053)
                  ·
                    refine ⟨799835122691172418386395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2132893660509793115697053 799835122691172418386395)
                    ·
                      rfl

theorem cell22_2336510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_2336510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2336510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2336510 prefixEnd_2336510 := by exact prefixLift 2336510
  have htrace : WordTrace (prefixWord ++ tailWord_2336510) baseStart_2336510 baseEnd_2336510 := by
    simpa [prefixWord, tailWord_2336510, baseEnd_2336510] using wordTrace_append hprefix tailTrace_2336510
  have hstable : (prefixWord ++ tailWord_2336510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2336510).length < 2 ^ (prefixWord ++ tailWord_2336510).sum := by decide
  have hdescent : baseEnd_2336510 < baseStart_2336510 := by decide
  rcases family_descends (prefixWord ++ tailWord_2336510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2336536 : List Nat := [2, 1, 2, 3, 1, 1, 5, 2, 1, 4]
def baseStart_2336536 : Nat := 118140960795 + 2336536 * 2 ^ 59
def prefixEnd_2336536 : Nat := 4983230072969 + 3 ^ 40 * 2336536 * 2
def baseEnd_2336536 : Nat := 799844023022517017236315

theorem tailTrace_2336536 : CollatzResearch.WordTrace tailWord_2336536 prefixEnd_2336536 799844023022517017236315 := by
  unfold tailWord_2336536
  simp only [CollatzResearch.WordTrace]
  refine ⟨42610234531568297712014731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56813646042091063616019641 42610234531568297712014731)
  ·
    refine ⟨63915351797352446568022097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42610234531568297712014731 63915351797352446568022097)
    ·
      refine ⟨47936513848014334926016573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63915351797352446568022097 47936513848014334926016573)
      ·
        refine ⟨17976192693005375597256215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47936513848014334926016573 17976192693005375597256215)
        ·
          refine ⟨26964289039508063395884323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17976192693005375597256215 26964289039508063395884323)
          ·
            refine ⟨40446433559262095093826485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26964289039508063395884323 40446433559262095093826485)
            ·
              refine ⟨3791853146180821415046233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40446433559262095093826485 3791853146180821415046233)
              ·
                refine ⟨2843889859635616061284675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3791853146180821415046233 2843889859635616061284675)
                ·
                  refine ⟨4265834789453424091927013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2843889859635616061284675 4265834789453424091927013)
                  ·
                    refine ⟨799844023022517017236315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4265834789453424091927013 799844023022517017236315)
                    ·
                      rfl

theorem cell22_2336536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 2, 1, 4].length) (baseStart_2336536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2336536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2336536 prefixEnd_2336536 := by exact prefixLift 2336536
  have htrace : WordTrace (prefixWord ++ tailWord_2336536) baseStart_2336536 baseEnd_2336536 := by
    simpa [prefixWord, tailWord_2336536, baseEnd_2336536] using wordTrace_append hprefix tailTrace_2336536
  have hstable : (prefixWord ++ tailWord_2336536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2336536).length < 2 ^ (prefixWord ++ tailWord_2336536).sum := by decide
  have hdescent : baseEnd_2336536 < baseStart_2336536 := by decide
  rcases family_descends (prefixWord ++ tailWord_2336536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2336549 : List Nat := [1, 3, 1, 2, 3, 2, 1, 1, 3, 5]
def baseStart_2336549 : Nat := 118140960795 + 2336549 * 2 ^ 59
def prefixEnd_2336549 : Nat := 4983230072969 + 3 ^ 40 * 2336549 * 2
def baseEnd_2336549 : Nat := 799848473188189316661275

theorem tailTrace_2336549 : CollatzResearch.WordTrace tailWord_2336549 prefixEnd_2336549 799848473188189316661275 := by
  unfold tailWord_2336549
  simp only [CollatzResearch.WordTrace]
  refine ⟨85220943212089498644252701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56813962141392999096168467 85220943212089498644252701)
  ·
    refine ⟨31957853704533561991594763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85220943212089498644252701 31957853704533561991594763)
    ·
      refine ⟨47936780556800342987392145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31957853704533561991594763 47936780556800342987392145)
      ·
        refine ⟨35952585417600257240544109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47936780556800342987392145 35952585417600257240544109)
        ·
          refine ⟨13482219531600096465204041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35952585417600257240544109 13482219531600096465204041)
          ·
            refine ⟨10111664648700072348903031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13482219531600096465204041 10111664648700072348903031)
            ·
              refine ⟨15167496973050108523354547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10111664648700072348903031 15167496973050108523354547)
              ·
                refine ⟨22751245459575162785031821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15167496973050108523354547 22751245459575162785031821)
                ·
                  refine ⟨8531717047340686044386933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22751245459575162785031821 8531717047340686044386933)
                  ·
                    refine ⟨799848473188189316661275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8531717047340686044386933 799848473188189316661275)
                    ·
                      rfl

theorem cell22_2336549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 3, 5].length) (baseStart_2336549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2336549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2336549 prefixEnd_2336549 := by exact prefixLift 2336549
  have htrace : WordTrace (prefixWord ++ tailWord_2336549) baseStart_2336549 baseEnd_2336549 := by
    simpa [prefixWord, tailWord_2336549, baseEnd_2336549] using wordTrace_append hprefix tailTrace_2336549
  have hstable : (prefixWord ++ tailWord_2336549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2336549).length < 2 ^ (prefixWord ++ tailWord_2336549).sum := by decide
  have hdescent : baseEnd_2336549 < baseStart_2336549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2336549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2336568 : List Nat := [2, 1, 2, 1, 3, 3, 4, 2, 4]
def baseStart_2336568 : Nat := 118140960795 + 2336568 * 2 ^ 59
def prefixEnd_2336568 : Nat := 4983230072969 + 3 ^ 40 * 2336568 * 2
def baseEnd_2336568 : Nat := 266618325758826533478739

theorem tailTrace_2336568 : CollatzResearch.WordTrace tailWord_2336568 prefixEnd_2336568 266618325758826533478739 := by
  unfold tailWord_2336568
  simp only [CollatzResearch.WordTrace]
  refine ⟨42610818099510332444597179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56814424132680443259462905 42610818099510332444597179)
  ·
    refine ⟨63916227149265498666895769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42610818099510332444597179 63916227149265498666895769)
    ·
      refine ⟨47937170361949124000171827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63916227149265498666895769 47937170361949124000171827)
      ·
        refine ⟨71905755542923686000257741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47937170361949124000171827 71905755542923686000257741)
        ·
          refine ⟨26964658328596382250096653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71905755542923686000257741 26964658328596382250096653)
          ·
            refine ⟨10111746873223643343786245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26964658328596382250096653 10111746873223643343786245)
            ·
              refine ⟨1895952538729433126959921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10111746873223643343786245 1895952538729433126959921)
              ·
                refine ⟨1421964404047074845219941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1895952538729433126959921 1421964404047074845219941)
                ·
                  refine ⟨266618325758826533478739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1421964404047074845219941 266618325758826533478739)
                  ·
                    rfl

theorem cell22_2336568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 4, 2, 4].length) (baseStart_2336568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2336568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2336568 prefixEnd_2336568 := by exact prefixLift 2336568
  have htrace : WordTrace (prefixWord ++ tailWord_2336568) baseStart_2336568 baseEnd_2336568 := by
    simpa [prefixWord, tailWord_2336568, baseEnd_2336568] using wordTrace_append hprefix tailTrace_2336568
  have hstable : (prefixWord ++ tailWord_2336568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2336568).length < 2 ^ (prefixWord ++ tailWord_2336568).sum := by decide
  have hdescent : baseEnd_2336568 < baseStart_2336568 := by decide
  rcases family_descends (prefixWord ++ tailWord_2336568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2336579 : List Nat := [1, 1, 1, 3, 1, 5, 3, 7]
def baseStart_2336579 : Nat := 118140960795 + 2336579 * 2 ^ 59
def prefixEnd_2336579 : Nat := 4983230072969 + 3 ^ 40 * 2336579 * 2
def baseEnd_2336579 : Nat := 88873193644586582045687

theorem tailTrace_2336579 : CollatzResearch.WordTrace tailWord_2336579 prefixEnd_2336579 88873193644586582045687 := by
  unfold tailWord_2336579
  simp only [CollatzResearch.WordTrace]
  refine ⟨85222037401980813767844791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56814691601320542511896527 85222037401980813767844791)
  ·
    refine ⟨127833056102971220651767187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85222037401980813767844791 127833056102971220651767187)
    ·
      refine ⟨191749584154456830977650781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127833056102971220651767187 191749584154456830977650781)
      ·
        refine ⟨71906094057921311616619043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 191749584154456830977650781 71906094057921311616619043)
        ·
          refine ⟨107859141086881967424928565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71906094057921311616619043 107859141086881967424928565)
          ·
            refine ⟨10111794476895184446087053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 107859141086881967424928565 10111794476895184446087053)
            ·
              refine ⟨3791922928835694167282645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10111794476895184446087053 3791922928835694167282645)
              ·
                refine ⟨88873193644586582045687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3791922928835694167282645 88873193644586582045687)
                ·
                  rfl

theorem cell22_2336579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 7].length) (baseStart_2336579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2336579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2336579 prefixEnd_2336579 := by exact prefixLift 2336579
  have htrace : WordTrace (prefixWord ++ tailWord_2336579) baseStart_2336579 baseEnd_2336579 := by
    simpa [prefixWord, tailWord_2336579, baseEnd_2336579] using wordTrace_append hprefix tailTrace_2336579
  have hstable : (prefixWord ++ tailWord_2336579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2336579).length < 2 ^ (prefixWord ++ tailWord_2336579).sum := by decide
  have hdescent : baseEnd_2336579 < baseStart_2336579 := by decide
  rcases family_descends (prefixWord ++ tailWord_2336579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2336684 : List Nat := [2, 2, 1, 1, 1, 1, 2, 1, 2, 9]
def baseStart_2336684 : Nat := 118140960795 + 2336684 * 2 ^ 59
def prefixEnd_2336684 : Nat := 4983230072969 + 3 ^ 40 * 2336684 * 2
def baseEnd_2336684 : Nat := 799894686447093964535861

theorem tailTrace_2336684 : CollatzResearch.WordTrace tailWord_2336684 prefixEnd_2336684 799894686447093964535861 := by
  unfold tailWord_2336684
  simp only [CollatzResearch.WordTrace]
  refine ⟨42612933533300208350208553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56817244711066944466944737 42612933533300208350208553)
  ·
    refine ⟨31959700149975156262656415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42612933533300208350208553 31959700149975156262656415)
    ·
      refine ⟨47939550224962734393984623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31959700149975156262656415 47939550224962734393984623)
      ·
        refine ⟨71909325337444101590976935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47939550224962734393984623 71909325337444101590976935)
        ·
          refine ⟨107863988006166152386465403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71909325337444101590976935 107863988006166152386465403)
          ·
            refine ⟨161795982009249228579698105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107863988006166152386465403 161795982009249228579698105)
            ·
              refine ⟨121346986506936921434773579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 161795982009249228579698105 121346986506936921434773579)
              ·
                refine ⟨182020479760405382152160369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 121346986506936921434773579 182020479760405382152160369)
                ·
                  refine ⟨136515359820304036614120277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 182020479760405382152160369 136515359820304036614120277)
                  ·
                    refine ⟨799894686447093964535861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 136515359820304036614120277 799894686447093964535861)
                    ·
                      rfl

theorem cell22_2336684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 9].length) (baseStart_2336684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2336684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2336684 prefixEnd_2336684 := by exact prefixLift 2336684
  have htrace : WordTrace (prefixWord ++ tailWord_2336684) baseStart_2336684 baseEnd_2336684 := by
    simpa [prefixWord, tailWord_2336684, baseEnd_2336684] using wordTrace_append hprefix tailTrace_2336684
  have hstable : (prefixWord ++ tailWord_2336684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2336684).length < 2 ^ (prefixWord ++ tailWord_2336684).sum := by decide
  have hdescent : baseEnd_2336684 < baseStart_2336684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2336684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2336722 : List Nat := [3, 2, 2, 3, 2, 1, 3, 1, 1, 4]
def baseStart_2336722 : Nat := 118140960795 + 2336722 * 2 ^ 59
def prefixEnd_2336722 : Nat := 4983230072969 + 3 ^ 40 * 2336722 * 2
def baseEnd_2336722 : Nat := 799907694623674532085745

theorem tailTrace_2336722 : CollatzResearch.WordTrace tailWord_2336722 prefixEnd_2336722 799907694623674532085745 := by
  unfold tailWord_2336722
  simp only [CollatzResearch.WordTrace]
  refine ⟨21306813260115687297575105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56818168693641832793533613 21306813260115687297575105)
  ·
    refine ⟨15980109945086765473181329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21306813260115687297575105 15980109945086765473181329)
    ·
      refine ⟨11985082458815074104885997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15980109945086765473181329 11985082458815074104885997)
      ·
        refine ⟨4494405922055652789332249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11985082458815074104885997 4494405922055652789332249)
        ·
          refine ⟨3370804441541739591999187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4494405922055652789332249 3370804441541739591999187)
          ·
            refine ⟨5056206662312609387998781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3370804441541739591999187 5056206662312609387998781)
            ·
              refine ⟨1896077498367228520499543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5056206662312609387998781 1896077498367228520499543)
              ·
                refine ⟨2844116247550842780749315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1896077498367228520499543 2844116247550842780749315)
                ·
                  refine ⟨4266174371326264171123973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2844116247550842780749315 4266174371326264171123973)
                  ·
                    refine ⟨799907694623674532085745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4266174371326264171123973 799907694623674532085745)
                    ·
                      rfl

theorem cell22_2336722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 3, 1, 1, 4].length) (baseStart_2336722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2336722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2336722 prefixEnd_2336722 := by exact prefixLift 2336722
  have htrace : WordTrace (prefixWord ++ tailWord_2336722) baseStart_2336722 baseEnd_2336722 := by
    simpa [prefixWord, tailWord_2336722, baseEnd_2336722] using wordTrace_append hprefix tailTrace_2336722
  have hstable : (prefixWord ++ tailWord_2336722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2336722).length < 2 ^ (prefixWord ++ tailWord_2336722).sum := by decide
  have hdescent : baseEnd_2336722 < baseStart_2336722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2336722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2336735 : List Nat := [1, 1, 2, 3, 4, 2, 2, 2, 2, 3]
def baseStart_2336735 : Nat := 118140960795 + 2336735 * 2 ^ 59
def prefixEnd_2336735 : Nat := 4983230072969 + 3 ^ 40 * 2336735 * 2
def baseEnd_2336735 : Nat := 799912144789346831510705

theorem tailTrace_2336735 : CollatzResearch.WordTrace tailWord_2336735 prefixEnd_2336735 799912144789346831510705 := by
  unfold tailWord_2336735
  simp only [CollatzResearch.WordTrace]
  refine ⟨85227727189415652410523659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56818484792943768273682439 85227727189415652410523659)
  ·
    refine ⟨127841590784123478615785489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85227727189415652410523659 127841590784123478615785489)
    ·
      refine ⟨95881193088092608961839117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127841590784123478615785489 95881193088092608961839117)
      ·
        refine ⟨35955447408034728360689669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95881193088092608961839117 35955447408034728360689669)
        ·
          refine ⟨6741646389006511567629313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35955447408034728360689669 6741646389006511567629313)
          ·
            refine ⟨5056234791754883675721985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6741646389006511567629313 5056234791754883675721985)
            ·
              refine ⟨3792176093816162756791489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5056234791754883675721985 3792176093816162756791489)
              ·
                refine ⟨2844132070362122067593617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3792176093816162756791489 2844132070362122067593617)
                ·
                  refine ⟨2133099052771591550695213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2844132070362122067593617 2133099052771591550695213)
                  ·
                    refine ⟨799912144789346831510705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2133099052771591550695213 799912144789346831510705)
                    ·
                      rfl

theorem cell22_2336735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 2, 2, 3].length) (baseStart_2336735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2336735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2336735 prefixEnd_2336735 := by exact prefixLift 2336735
  have htrace : WordTrace (prefixWord ++ tailWord_2336735) baseStart_2336735 baseEnd_2336735 := by
    simpa [prefixWord, tailWord_2336735, baseEnd_2336735] using wordTrace_append hprefix tailTrace_2336735
  have hstable : (prefixWord ++ tailWord_2336735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2336735).length < 2 ^ (prefixWord ++ tailWord_2336735).sum := by decide
  have hdescent : baseEnd_2336735 < baseStart_2336735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2336735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2336776 : List Nat := [2, 1, 3, 2, 1, 2, 2, 2, 7]
def baseStart_2336776 : Nat := 118140960795 + 2336776 * 2 ^ 59
def prefixEnd_2336776 : Nat := 4983230072969 + 3 ^ 40 * 2336776 * 2
def baseEnd_2336776 : Nat := 266642059975745463745193

theorem tailTrace_2336776 : CollatzResearch.WordTrace tailWord_2336776 prefixEnd_2336776 266642059975745463745193 := by
  unfold tailWord_2336776
  simp only [CollatzResearch.WordTrace]
  refine ⟨42614611291133558206383091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56819481721511410941844121 42614611291133558206383091)
  ·
    refine ⟨63921916936700337309574637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42614611291133558206383091 63921916936700337309574637)
    ·
      refine ⟨23970718851262626491090489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63921916936700337309574637 23970718851262626491090489)
      ·
        refine ⟨17978039138446969868317867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23970718851262626491090489 17978039138446969868317867)
        ·
          refine ⟨26967058707670454802476801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17978039138446969868317867 26967058707670454802476801)
          ·
            refine ⟨20225294030752841101857601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26967058707670454802476801 20225294030752841101857601)
            ·
              refine ⟨15168970523064630826393201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20225294030752841101857601 15168970523064630826393201)
              ·
                refine ⟨11376727892298473119794901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15168970523064630826393201 11376727892298473119794901)
                ·
                  refine ⟨266642059975745463745193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11376727892298473119794901 266642059975745463745193)
                  ·
                    rfl

theorem cell22_2336776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 2, 7].length) (baseStart_2336776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2336776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2336776 prefixEnd_2336776 := by exact prefixLift 2336776
  have htrace : WordTrace (prefixWord ++ tailWord_2336776) baseStart_2336776 baseEnd_2336776 := by
    simpa [prefixWord, tailWord_2336776, baseEnd_2336776] using wordTrace_append hprefix tailTrace_2336776
  have hstable : (prefixWord ++ tailWord_2336776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2336776).length < 2 ^ (prefixWord ++ tailWord_2336776).sum := by decide
  have hdescent : baseEnd_2336776 < baseStart_2336776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2336776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2336797 : List Nat := [1, 4, 2, 2, 2, 1, 2, 4, 1, 3]
def baseStart_2336797 : Nat := 118140960795 + 2336797 * 2 ^ 59
def prefixEnd_2336797 : Nat := 4983230072969 + 3 ^ 40 * 2336797 * 2
def baseEnd_2336797 : Nat := 799933368656399336460515

theorem tailTrace_2336797 : CollatzResearch.WordTrace tailWord_2336797 prefixEnd_2336797 799933368656399336460515 := by
  unfold tailWord_2336797
  simp only [CollatzResearch.WordTrace]
  refine ⟨85229988515191036999280645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56819992343460691332853763 85229988515191036999280645)
  ·
    refine ⟨15980622846598319437365121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85229988515191036999280645 15980622846598319437365121)
    ·
      refine ⟨11985467134948739578023841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15980622846598319437365121 11985467134948739578023841)
      ·
        refine ⟨8989100351211554683517881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11985467134948739578023841 8989100351211554683517881)
        ·
          refine ⟨6741825263408666012638411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8989100351211554683517881 6741825263408666012638411)
          ·
            refine ⟨10112737895112999018957617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6741825263408666012638411 10112737895112999018957617)
            ·
              refine ⟨7584553421334749264218213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10112737895112999018957617 7584553421334749264218213)
              ·
                refine ⟨1422103766500265487040915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7584553421334749264218213 1422103766500265487040915)
                ·
                  refine ⟨2133155649750398230561373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1422103766500265487040915 2133155649750398230561373)
                  ·
                    refine ⟨799933368656399336460515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2133155649750398230561373 799933368656399336460515)
                    ·
                      rfl

theorem cell22_2336797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 4, 1, 3].length) (baseStart_2336797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2336797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2336797 prefixEnd_2336797 := by exact prefixLift 2336797
  have htrace : WordTrace (prefixWord ++ tailWord_2336797) baseStart_2336797 baseEnd_2336797 := by
    simpa [prefixWord, tailWord_2336797, baseEnd_2336797] using wordTrace_append hprefix tailTrace_2336797
  have hstable : (prefixWord ++ tailWord_2336797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2336797).length < 2 ^ (prefixWord ++ tailWord_2336797).sum := by decide
  have hdescent : baseEnd_2336797 < baseStart_2336797 := by decide
  rcases family_descends (prefixWord ++ tailWord_2336797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2336823 : List Nat := [1, 1, 3, 1, 2, 2, 3, 4, 1, 4]
def baseStart_2336823 : Nat := 118140960795 + 2336823 * 2 ^ 59
def prefixEnd_2336823 : Nat := 4983230072969 + 3 ^ 40 * 2336823 * 2
def baseEnd_2336823 : Nat := 799942268987743935310435

theorem tailTrace_2336823 : CollatzResearch.WordTrace tailWord_2336823 prefixEnd_2336823 799942268987743935310435 := by
  unfold tailWord_2336823
  simp only [CollatzResearch.WordTrace]
  refine ⟨85230936813096843439727123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56820624542064562293151415 85230936813096843439727123)
  ·
    refine ⟨127846405219645265159590685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85230936813096843439727123 127846405219645265159590685)
    ·
      refine ⟨47942401957366974434846507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127846405219645265159590685 47942401957366974434846507)
      ·
        refine ⟨71913602936050461652269761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47942401957366974434846507 71913602936050461652269761)
        ·
          refine ⟨53935202202037846239202321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71913602936050461652269761 53935202202037846239202321)
          ·
            refine ⟨40451401651528384679401741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53935202202037846239202321 40451401651528384679401741)
            ·
              refine ⟨15169275619323144254775653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40451401651528384679401741 15169275619323144254775653)
              ·
                refine ⟨2844239178623089547770435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15169275619323144254775653 2844239178623089547770435)
                ·
                  refine ⟨4266358767934634321655653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2844239178623089547770435 4266358767934634321655653)
                  ·
                    refine ⟨799942268987743935310435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4266358767934634321655653 799942268987743935310435)
                    ·
                      rfl

theorem cell22_2336823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 4, 1, 4].length) (baseStart_2336823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2336823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2336823 prefixEnd_2336823 := by exact prefixLift 2336823
  have htrace : WordTrace (prefixWord ++ tailWord_2336823) baseStart_2336823 baseEnd_2336823 := by
    simpa [prefixWord, tailWord_2336823, baseEnd_2336823] using wordTrace_append hprefix tailTrace_2336823
  have hstable : (prefixWord ++ tailWord_2336823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2336823).length < 2 ^ (prefixWord ++ tailWord_2336823).sum := by decide
  have hdescent : baseEnd_2336823 < baseStart_2336823 := by decide
  rcases family_descends (prefixWord ++ tailWord_2336823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2336874 : List Nat := [3, 1, 3, 2, 4, 1, 1, 2, 1, 4]
def baseStart_2336874 : Nat := 118140960795 + 2336874 * 2 ^ 59
def prefixEnd_2336874 : Nat := 4983230072969 + 3 ^ 40 * 2336874 * 2
def baseEnd_2336874 : Nat := 799959727329996802285279

theorem tailTrace_2336874 : CollatzResearch.WordTrace tailWord_2336874 prefixEnd_2336874 799959727329996802285279 := by
  unfold tailWord_2336874
  simp only [CollatzResearch.WordTrace]
  refine ⟨21308199233978019787458419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56821864623941386099889117 21308199233978019787458419)
  ·
    refine ⟨31962298850967029681187629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21308199233978019787458419 31962298850967029681187629)
    ·
      refine ⟨11985862069112636130445361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31962298850967029681187629 11985862069112636130445361)
      ·
        refine ⟨8989396551834477097834021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11985862069112636130445361 8989396551834477097834021)
        ·
          refine ⟨1685511853468964455843879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8989396551834477097834021 1685511853468964455843879)
          ·
            refine ⟨2528267780203446683765819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1685511853468964455843879 2528267780203446683765819)
            ·
              refine ⟨3792401670305170025648729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2528267780203446683765819 3792401670305170025648729)
              ·
                refine ⟨2844301252728877519236547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3792401670305170025648729 2844301252728877519236547)
                ·
                  refine ⟨4266451879093316278854821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2844301252728877519236547 4266451879093316278854821)
                  ·
                    refine ⟨799959727329996802285279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4266451879093316278854821 799959727329996802285279)
                    ·
                      rfl

theorem cell22_2336874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 2, 1, 4].length) (baseStart_2336874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2336874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2336874 prefixEnd_2336874 := by exact prefixLift 2336874
  have htrace : WordTrace (prefixWord ++ tailWord_2336874) baseStart_2336874 baseEnd_2336874 := by
    simpa [prefixWord, tailWord_2336874, baseEnd_2336874] using wordTrace_append hprefix tailTrace_2336874
  have hstable : (prefixWord ++ tailWord_2336874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2336874).length < 2 ^ (prefixWord ++ tailWord_2336874).sum := by decide
  have hdescent : baseEnd_2336874 < baseStart_2336874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2336874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2336932 : List Nat := [2, 3, 1, 2, 4, 1, 1, 2, 3, 3]
def baseStart_2336932 : Nat := 118140960795 + 2336932 * 2 ^ 59
def prefixEnd_2336932 : Nat := 4983230072969 + 3 ^ 40 * 2336932 * 2
def baseEnd_2336932 : Nat := 799979581915303984335101

theorem tailTrace_2336932 : CollatzResearch.WordTrace tailWord_2336932 prefixEnd_2336932 799979581915303984335101 := by
  unfold tailWord_2336932
  simp only [CollatzResearch.WordTrace]
  refine ⟨42617456184850977527722525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56823274913134636703630033 42617456184850977527722525)
  ·
    refine ⟨15981546069319116572895947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42617456184850977527722525 15981546069319116572895947)
    ·
      refine ⟨23972319103978674859343921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15981546069319116572895947 23972319103978674859343921)
      ·
        refine ⟨17979239327984006144507941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23972319103978674859343921 17979239327984006144507941)
        ·
          refine ⟨3371107373997001152095239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17979239327984006144507941 3371107373997001152095239)
          ·
            refine ⟨5056661060995501728142859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3371107373997001152095239 5056661060995501728142859)
            ·
              refine ⟨7584991591493252592214289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5056661060995501728142859 7584991591493252592214289)
              ·
                refine ⟨5688743693619939444160717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7584991591493252592214289 5688743693619939444160717)
                ·
                  refine ⟨2133278885107477291560269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5688743693619939444160717 2133278885107477291560269)
                  ·
                    refine ⟨799979581915303984335101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2133278885107477291560269 799979581915303984335101)
                    ·
                      rfl

theorem cell22_2336932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 2, 3, 3].length) (baseStart_2336932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2336932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2336932 prefixEnd_2336932 := by exact prefixLift 2336932
  have htrace : WordTrace (prefixWord ++ tailWord_2336932) baseStart_2336932 baseEnd_2336932 := by
    simpa [prefixWord, tailWord_2336932, baseEnd_2336932] using wordTrace_append hprefix tailTrace_2336932
  have hstable : (prefixWord ++ tailWord_2336932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2336932).length < 2 ^ (prefixWord ++ tailWord_2336932).sum := by decide
  have hdescent : baseEnd_2336932 < baseStart_2336932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2336932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2337003 : List Nat := [1, 1, 1, 1, 2, 5, 1, 3, 1, 6]
def baseStart_2337003 : Nat := 118140960795 + 2337003 * 2 ^ 59
def prefixEnd_2337003 : Nat := 4983230072969 + 3 ^ 40 * 2337003 * 2
def baseEnd_2337003 : Nat := 800003886666283465809883

theorem tailTrace_2337003 : CollatzResearch.WordTrace tailWord_2337003 prefixEnd_2337003 800003886666283465809883 := by
  unfold tailWord_2337003
  simp only [CollatzResearch.WordTrace]
  refine ⟨85237501952444734181279663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56825001301629822787519775 85237501952444734181279663)
  ·
    refine ⟨127856252928667101271919495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85237501952444734181279663 127856252928667101271919495)
    ·
      refine ⟨191784379393000651907879243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127856252928667101271919495 191784379393000651907879243)
      ·
        refine ⟨287676569089500977861818865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191784379393000651907879243 287676569089500977861818865)
        ·
          refine ⟨215757426817125733396364149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 287676569089500977861818865 215757426817125733396364149)
          ·
            refine ⟨20227258764105537505909139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 215757426817125733396364149 20227258764105537505909139)
            ·
              refine ⟨30340888146158306258863709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20227258764105537505909139 30340888146158306258863709)
              ·
                refine ⟨11377833054809364847073891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30340888146158306258863709 11377833054809364847073891)
                ·
                  refine ⟨17066749582214047270610837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11377833054809364847073891 17066749582214047270610837)
                  ·
                    refine ⟨800003886666283465809883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17066749582214047270610837 800003886666283465809883)
                    ·
                      rfl

theorem cell22_2337003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 3, 1, 6].length) (baseStart_2337003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2337003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2337003 prefixEnd_2337003 := by exact prefixLift 2337003
  have htrace : WordTrace (prefixWord ++ tailWord_2337003) baseStart_2337003 baseEnd_2337003 := by
    simpa [prefixWord, tailWord_2337003, baseEnd_2337003] using wordTrace_append hprefix tailTrace_2337003
  have hstable : (prefixWord ++ tailWord_2337003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2337003).length < 2 ^ (prefixWord ++ tailWord_2337003).sum := by decide
  have hdescent : baseEnd_2337003 < baseStart_2337003 := by decide
  rcases family_descends (prefixWord ++ tailWord_2337003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2337007 : List Nat := [1, 1, 2, 1, 6, 1, 3, 3, 4]
def baseStart_2337007 : Nat := 118140960795 + 2337007 * 2 ^ 59
def prefixEnd_2337007 : Nat := 4983230072969 + 3 ^ 40 * 2337007 * 2
def baseEnd_2337007 : Nat := 266668418649342929569957

theorem tailTrace_2337007 : CollatzResearch.WordTrace tailWord_2337007 prefixEnd_2337007 266668418649342929569957 := by
  unfold tailWord_2337007
  simp only [CollatzResearch.WordTrace]
  refine ⟨85237647844430242864425275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56825098562953495242950183 85237647844430242864425275)
  ·
    refine ⟨127856471766645364296637913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85237647844430242864425275 127856471766645364296637913)
    ·
      refine ⟨95892353824984023222478435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127856471766645364296637913 95892353824984023222478435)
      ·
        refine ⟨143838530737476034833717653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95892353824984023222478435 143838530737476034833717653)
        ·
          refine ⟨6742431128319189132830515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 143838530737476034833717653 6742431128319189132830515)
          ·
            refine ⟨10113646692478783699245773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6742431128319189132830515 10113646692478783699245773)
            ·
              refine ⟨3792617509679543887217165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10113646692478783699245773 3792617509679543887217165)
              ·
                refine ⟨1422231566129828957706437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3792617509679543887217165 1422231566129828957706437)
                ·
                  refine ⟨266668418649342929569957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1422231566129828957706437 266668418649342929569957)
                  ·
                    rfl

theorem cell22_2337007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 3, 4].length) (baseStart_2337007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2337007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2337007 prefixEnd_2337007 := by exact prefixLift 2337007
  have htrace : WordTrace (prefixWord ++ tailWord_2337007) baseStart_2337007 baseEnd_2337007 := by
    simpa [prefixWord, tailWord_2337007, baseEnd_2337007] using wordTrace_append hprefix tailTrace_2337007
  have hstable : (prefixWord ++ tailWord_2337007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2337007).length < 2 ^ (prefixWord ++ tailWord_2337007).sum := by decide
  have hdescent : baseEnd_2337007 < baseStart_2337007 := by decide
  rcases family_descends (prefixWord ++ tailWord_2337007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2337018 : List Nat := [3, 1, 1, 1, 1, 5, 10]
def baseStart_2337018 : Nat := 118140960795 + 2337018 * 2 ^ 59
def prefixEnd_2337018 : Nat := 4983230072969 + 3 ^ 40 * 2337018 * 2
def baseEnd_2337018 : Nat := 29629963758252904692031

theorem tailTrace_2337018 : CollatzResearch.WordTrace tailWord_2337018 prefixEnd_2337018 29629963758252904692031 := by
  unfold tailWord_2337018
  simp only [CollatzResearch.WordTrace]
  refine ⟨21309512261847597935768927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56825366031593594495383805 21309512261847597935768927)
  ·
    refine ⟨31964268392771396903653391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21309512261847597935768927 31964268392771396903653391)
    ·
      refine ⟨47946402589157095355480087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31964268392771396903653391 47946402589157095355480087)
      ·
        refine ⟨71919603883735643033220131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47946402589157095355480087 71919603883735643033220131)
        ·
          refine ⟨107879405825603464549830197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71919603883735643033220131 107879405825603464549830197)
          ·
            refine ⟨10113694296150324801546581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 107879405825603464549830197 10113694296150324801546581)
            ·
              refine ⟨29629963758252904692031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10113694296150324801546581 29629963758252904692031)
              ·
                rfl

theorem cell22_2337018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 10].length) (baseStart_2337018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2337018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2337018 prefixEnd_2337018 := by exact prefixLift 2337018
  have htrace : WordTrace (prefixWord ++ tailWord_2337018) baseStart_2337018 baseEnd_2337018 := by
    simpa [prefixWord, tailWord_2337018, baseEnd_2337018] using wordTrace_append hprefix tailTrace_2337018
  have hstable : (prefixWord ++ tailWord_2337018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2337018).length < 2 ^ (prefixWord ++ tailWord_2337018).sum := by decide
  have hdescent : baseEnd_2337018 < baseStart_2337018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2337018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2337020 : List Nat := [2, 2, 2, 1, 4, 1, 1, 1, 4, 4]
def baseStart_2337020 : Nat := 118140960795 + 2337020 * 2 ^ 59
def prefixEnd_2337020 : Nat := 4983230072969 + 3 ^ 40 * 2337020 * 2
def baseEnd_2337020 : Nat := 800009706113701088134831

theorem tailTrace_2337020 : CollatzResearch.WordTrace tailWord_2337020 prefixEnd_2337020 800009706113701088134831 := by
  unfold tailWord_2337020
  simp only [CollatzResearch.WordTrace]
  refine ⟨42619060996691573042324257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56825414662255430723099009 42619060996691573042324257)
  ·
    refine ⟨31964295747518679781743193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42619060996691573042324257 31964295747518679781743193)
    ·
      refine ⟨23973221810639009836307395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31964295747518679781743193 23973221810639009836307395)
      ·
        refine ⟨35959832715958514754461093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23973221810639009836307395 35959832715958514754461093)
        ·
          refine ⟨6742468634242221516461455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35959832715958514754461093 6742468634242221516461455)
          ·
            refine ⟨10113702951363332274692183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6742468634242221516461455 10113702951363332274692183)
            ·
              refine ⟨15170554427044998412038275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10113702951363332274692183 15170554427044998412038275)
              ·
                refine ⟨22755831640567497618057413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15170554427044998412038275 22755831640567497618057413)
                ·
                  refine ⟨4266718432606405803385765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22755831640567497618057413 4266718432606405803385765)
                  ·
                    refine ⟨800009706113701088134831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4266718432606405803385765 800009706113701088134831)
                    ·
                      rfl

theorem cell22_2337020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 4, 4].length) (baseStart_2337020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2337020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2337020 prefixEnd_2337020 := by exact prefixLift 2337020
  have htrace : WordTrace (prefixWord ++ tailWord_2337020) baseStart_2337020 baseEnd_2337020 := by
    simpa [prefixWord, tailWord_2337020, baseEnd_2337020] using wordTrace_append hprefix tailTrace_2337020
  have hstable : (prefixWord ++ tailWord_2337020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2337020).length < 2 ^ (prefixWord ++ tailWord_2337020).sum := by decide
  have hdescent : baseEnd_2337020 < baseStart_2337020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2337020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2337022 : List Nat := [4, 2, 2, 1, 1, 1, 1, 3, 4, 3]
def baseStart_2337022 : Nat := 118140960795 + 2337022 * 2 ^ 59
def prefixEnd_2337022 : Nat := 4983230072969 + 3 ^ 40 * 2337022 * 2
def baseEnd_2337022 : Nat := 800010390754573749584825

theorem tailTrace_2337022 : CollatzResearch.WordTrace tailWord_2337022 prefixEnd_2337022 800010390754573749584825 := by
  unfold tailWord_2337022
  simp only [CollatzResearch.WordTrace]
  refine ⟨10654774367421987553277665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56825463292917266950814213 10654774367421987553277665)
  ·
    refine ⟨7991080775566490664958249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10654774367421987553277665 7991080775566490664958249)
    ·
      refine ⟨5993310581674867998718687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7991080775566490664958249 5993310581674867998718687)
      ·
        refine ⟨8989965872512301998078031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5993310581674867998718687 8989965872512301998078031)
        ·
          refine ⟨13484948808768452997117047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8989965872512301998078031 13484948808768452997117047)
          ·
            refine ⟨20227423213152679495675571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13484948808768452997117047 20227423213152679495675571)
            ·
              refine ⟨30341134819729019243513357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20227423213152679495675571 30341134819729019243513357)
              ·
                refine ⟨11377925557398382216317509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30341134819729019243513357 11377925557398382216317509)
                ·
                  refine ⟨2133361042012196665559533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11377925557398382216317509 2133361042012196665559533)
                  ·
                    refine ⟨800010390754573749584825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2133361042012196665559533 800010390754573749584825)
                    ·
                      rfl

theorem cell22_2337022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_2337022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2337022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2337022 prefixEnd_2337022 := by exact prefixLift 2337022
  have htrace : WordTrace (prefixWord ++ tailWord_2337022) baseStart_2337022 baseEnd_2337022 := by
    simpa [prefixWord, tailWord_2337022, baseEnd_2337022] using wordTrace_append hprefix tailTrace_2337022
  have hstable : (prefixWord ++ tailWord_2337022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2337022).length < 2 ^ (prefixWord ++ tailWord_2337022).sum := by decide
  have hdescent : baseEnd_2337022 < baseStart_2337022 := by decide
  rcases family_descends (prefixWord ++ tailWord_2337022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2337054 : List Nat := [4, 3, 2, 1, 1, 1, 1, 3, 2, 4]
def baseStart_2337054 : Nat := 118140960795 + 2337054 * 2 ^ 59
def prefixEnd_2337054 : Nat := 4983230072969 + 3 ^ 40 * 2337054 * 2
def baseEnd_2337054 : Nat := 800021345008536332784727

theorem tailTrace_2337054 : CollatzResearch.WordTrace tailWord_2337054 prefixEnd_2337054 800021345008536332784727 := by
  unfold tailWord_2337054
  simp only [CollatzResearch.WordTrace]
  refine ⟨10654920259407496236423277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56826241383506646594257477 10654920259407496236423277)
  ·
    refine ⟨3995595097277811088658729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10654920259407496236423277 3995595097277811088658729)
    ·
      refine ⟨2996696322958358316494047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3995595097277811088658729 2996696322958358316494047)
      ·
        refine ⟨4495044484437537474741071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2996696322958358316494047 4495044484437537474741071)
        ·
          refine ⟨6742566726656306212111607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4495044484437537474741071 6742566726656306212111607)
          ·
            refine ⟨10113850089984459318167411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6742566726656306212111607 10113850089984459318167411)
            ·
              refine ⟨15170775134976688977251117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10113850089984459318167411 15170775134976688977251117)
              ·
                refine ⟨5689040675616258366469169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15170775134976688977251117 5689040675616258366469169)
                ·
                  refine ⟨4266780506712193774851877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5689040675616258366469169 4266780506712193774851877)
                  ·
                    refine ⟨800021345008536332784727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4266780506712193774851877 800021345008536332784727)
                    ·
                      rfl

theorem cell22_2337054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_2337054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2337054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2337054 prefixEnd_2337054 := by exact prefixLift 2337054
  have htrace : WordTrace (prefixWord ++ tailWord_2337054) baseStart_2337054 baseEnd_2337054 := by
    simpa [prefixWord, tailWord_2337054, baseEnd_2337054] using wordTrace_append hprefix tailTrace_2337054
  have hstable : (prefixWord ++ tailWord_2337054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2337054).length < 2 ^ (prefixWord ++ tailWord_2337054).sum := by decide
  have hdescent : baseEnd_2337054 < baseStart_2337054 := by decide
  rcases family_descends (prefixWord ++ tailWord_2337054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2337080 : List Nat := [2, 1, 2, 1, 3, 1, 3, 4, 5]
def baseStart_2337080 : Nat := 118140960795 + 2337080 * 2 ^ 59
def prefixEnd_2337080 : Nat := 4983230072969 + 3 ^ 40 * 2337080 * 2
def baseEnd_2337080 : Nat := 266676748446626977211549

theorem tailTrace_2337080 : CollatzResearch.WordTrace tailWord_2337080 prefixEnd_2337080 266676748446626977211549 := by
  unfold tailWord_2337080
  simp only [CollatzResearch.WordTrace]
  refine ⟨42620155186582888165916347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56826873582110517554555129 42620155186582888165916347)
  ·
    refine ⟨63930232779874332248874521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42620155186582888165916347 63930232779874332248874521)
    ·
      refine ⟨47947674584905749186655891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63930232779874332248874521 47947674584905749186655891)
      ·
        refine ⟨71921511877358623779983837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47947674584905749186655891 71921511877358623779983837)
        ·
          refine ⟨26970566954009483917493939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71921511877358623779983837 26970566954009483917493939)
          ·
            refine ⟨40455850431014225876240909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26970566954009483917493939 40455850431014225876240909)
            ·
              refine ⟨15170943911630334703590341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40455850431014225876240909 15170943911630334703590341)
              ·
                refine ⟨2844551983430687756923189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15170943911630334703590341 2844551983430687756923189)
                ·
                  refine ⟨266676748446626977211549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2844551983430687756923189 266676748446626977211549)
                  ·
                    rfl

theorem cell22_2337080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 4, 5].length) (baseStart_2337080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2337080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2337080 prefixEnd_2337080 := by exact prefixLift 2337080
  have htrace : WordTrace (prefixWord ++ tailWord_2337080) baseStart_2337080 baseEnd_2337080 := by
    simpa [prefixWord, tailWord_2337080, baseEnd_2337080] using wordTrace_append hprefix tailTrace_2337080
  have hstable : (prefixWord ++ tailWord_2337080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2337080).length < 2 ^ (prefixWord ++ tailWord_2337080).sum := by decide
  have hdescent : baseEnd_2337080 < baseStart_2337080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2337080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2337084 : List Nat := [2, 2, 2, 2, 1, 2, 3, 4, 1, 3]
def baseStart_2337084 : Nat := 118140960795 + 2337084 * 2 ^ 59
def prefixEnd_2337084 : Nat := 4983230072969 + 3 ^ 40 * 2337084 * 2
def baseEnd_2337084 : Nat := 800031614621626254534635

theorem tailTrace_2337084 : CollatzResearch.WordTrace tailWord_2337084 prefixEnd_2337084 800031614621626254534635 := by
  unfold tailWord_2337084
  simp only [CollatzResearch.WordTrace]
  refine ⟨42620228132575642507489153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56826970843434190009985537 42620228132575642507489153)
  ·
    refine ⟨31965171099431731880616865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42620228132575642507489153 31965171099431731880616865)
    ·
      refine ⟨23973878324573798910462649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31965171099431731880616865 23973878324573798910462649)
      ·
        refine ⟨17980408743430349182846987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23973878324573798910462649 17980408743430349182846987)
        ·
          refine ⟨26970613115145523774270481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17980408743430349182846987 26970613115145523774270481)
          ·
            refine ⟨20227959836359142830702861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26970613115145523774270481 20227959836359142830702861)
            ·
              refine ⟨7585484938634678561513573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20227959836359142830702861 7585484938634678561513573)
              ·
                refine ⟨1422278425994002230283795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7585484938634678561513573 1422278425994002230283795)
                ·
                  refine ⟨2133417638991003345425693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1422278425994002230283795 2133417638991003345425693)
                  ·
                    refine ⟨800031614621626254534635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2133417638991003345425693 800031614621626254534635)
                    ·
                      rfl

theorem cell22_2337084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 4, 1, 3].length) (baseStart_2337084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2337084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2337084 prefixEnd_2337084 := by exact prefixLift 2337084
  have htrace : WordTrace (prefixWord ++ tailWord_2337084) baseStart_2337084 baseEnd_2337084 := by
    simpa [prefixWord, tailWord_2337084, baseEnd_2337084] using wordTrace_append hprefix tailTrace_2337084
  have hstable : (prefixWord ++ tailWord_2337084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2337084).length < 2 ^ (prefixWord ++ tailWord_2337084).sum := by decide
  have hdescent : baseEnd_2337084 < baseStart_2337084 := by decide
  rcases family_descends (prefixWord ++ tailWord_2337084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2337095 : List Nat := [1, 1, 4, 1, 2, 2, 3, 1, 2, 5]
def baseStart_2337095 : Nat := 118140960795 + 2337095 * 2 ^ 59
def prefixEnd_2337095 : Nat := 4983230072969 + 3 ^ 40 * 2337095 * 2
def baseEnd_2337095 : Nat := 800035380146425892509601

theorem tailTrace_2337095 : CollatzResearch.WordTrace tailWord_2337095 prefixEnd_2337095 800035380146425892509601 := by
  unfold tailWord_2337095
  simp only [CollatzResearch.WordTrace]
  refine ⟨85240857468111433893628739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56827238312074289262419159 85240857468111433893628739)
  ·
    refine ⟨127861286202167150840443109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85240857468111433893628739 127861286202167150840443109)
    ·
      refine ⟨23973991162906340782583083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 127861286202167150840443109 23973991162906340782583083)
      ·
        refine ⟨35960986744359511173874625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23973991162906340782583083 35960986744359511173874625)
        ·
          refine ⟨26970740058269633380405969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35960986744359511173874625 26970740058269633380405969)
          ·
            refine ⟨20228055043702225035304477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26970740058269633380405969 20228055043702225035304477)
            ·
              refine ⟨7585520641388334388239179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20228055043702225035304477 7585520641388334388239179)
              ·
                refine ⟨11378280962082501582358769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7585520641388334388239179 11378280962082501582358769)
                ·
                  refine ⟨8533710721561876186769077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11378280962082501582358769 8533710721561876186769077)
                  ·
                    refine ⟨800035380146425892509601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8533710721561876186769077 800035380146425892509601)
                    ·
                      rfl

theorem cell22_2337095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 1, 2, 5].length) (baseStart_2337095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2337095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2337095 prefixEnd_2337095 := by exact prefixLift 2337095
  have htrace : WordTrace (prefixWord ++ tailWord_2337095) baseStart_2337095 baseEnd_2337095 := by
    simpa [prefixWord, tailWord_2337095, baseEnd_2337095] using wordTrace_append hprefix tailTrace_2337095
  have hstable : (prefixWord ++ tailWord_2337095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2337095).length < 2 ^ (prefixWord ++ tailWord_2337095).sum := by decide
  have hdescent : baseEnd_2337095 < baseStart_2337095 := by decide
  rcases family_descends (prefixWord ++ tailWord_2337095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2337176 : List Nat := [2, 1, 2, 5, 1, 3, 1, 3, 4]
def baseStart_2337176 : Nat := 118140960795 + 2337176 * 2 ^ 59
def prefixEnd_2337176 : Nat := 4983230072969 + 3 ^ 40 * 2337176 * 2
def baseEnd_2337176 : Nat := 266687702700589560411451

theorem tailTrace_2337176 : CollatzResearch.WordTrace tailWord_2337176 prefixEnd_2337176 266687702700589560411451 := by
  unfold tailWord_2337176
  simp only [CollatzResearch.WordTrace]
  refine ⟨42621905890408992363663691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56829207853878656484884921 42621905890408992363663691)
  ·
    refine ⟨63932858835613488545495537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42621905890408992363663691 63932858835613488545495537)
    ·
      refine ⟨47949644126710116409121653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63932858835613488545495537 47949644126710116409121653)
      ·
        refine ⟨4495279136879073413355155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47949644126710116409121653 4495279136879073413355155)
        ·
          refine ⟨6742918705318610120032733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4495279136879073413355155 6742918705318610120032733)
          ·
            refine ⟨2528594514494478795012275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6742918705318610120032733 2528594514494478795012275)
            ·
              refine ⟨3792891771741718192518413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2528594514494478795012275 3792891771741718192518413)
              ·
                refine ⟨1422334414403144322194405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3792891771741718192518413 1422334414403144322194405)
                ·
                  refine ⟨266687702700589560411451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1422334414403144322194405 266687702700589560411451)
                  ·
                    rfl

theorem cell22_2337176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 3, 4].length) (baseStart_2337176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2337176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2337176 prefixEnd_2337176 := by exact prefixLift 2337176
  have htrace : WordTrace (prefixWord ++ tailWord_2337176) baseStart_2337176 baseEnd_2337176 := by
    simpa [prefixWord, tailWord_2337176, baseEnd_2337176] using wordTrace_append hprefix tailTrace_2337176
  have hstable : (prefixWord ++ tailWord_2337176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2337176).length < 2 ^ (prefixWord ++ tailWord_2337176).sum := by decide
  have hdescent : baseEnd_2337176 < baseStart_2337176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2337176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2337253 : List Nat := [1, 3, 1, 5, 2, 1, 1, 4, 1, 3]
def baseStart_2337253 : Nat := 118140960795 + 2337253 * 2 ^ 59
def prefixEnd_2337253 : Nat := 4983230072969 + 3 ^ 40 * 2337253 * 2
def baseEnd_2337253 : Nat := 800089466775366147059117

theorem tailTrace_2337253 : CollatzResearch.WordTrace tailWord_2337253 prefixEnd_2337253 800089466775366147059117 := by
  unfold tailWord_2337253
  simp only [CollatzResearch.WordTrace]
  refine ⟨85246620201539026877880413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56831080134359351251920275 85246620201539026877880413)
  ·
    refine ⟨31967482575577135079205155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85246620201539026877880413 31967482575577135079205155)
    ·
      refine ⟨47951223863365702618807733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31967482575577135079205155 47951223863365702618807733)
      ·
        refine ⟨4495427237190534620513225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47951223863365702618807733 4495427237190534620513225)
        ·
          refine ⟨3371570427892900965384919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4495427237190534620513225 3371570427892900965384919)
          ·
            refine ⟨5057355641839351448077379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3371570427892900965384919 5057355641839351448077379)
            ·
              refine ⟨7586033462759027172116069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5057355641839351448077379 7586033462759027172116069)
              ·
                refine ⟨1422381274267317594771763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7586033462759027172116069 1422381274267317594771763)
                ·
                  refine ⟨2133571911400976392157645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1422381274267317594771763 2133571911400976392157645)
                  ·
                    refine ⟨800089466775366147059117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2133571911400976392157645 800089466775366147059117)
                    ·
                      rfl

theorem cell22_2337253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 4, 1, 3].length) (baseStart_2337253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2337253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2337253 prefixEnd_2337253 := by exact prefixLift 2337253
  have htrace : WordTrace (prefixWord ++ tailWord_2337253) baseStart_2337253 baseEnd_2337253 := by
    simpa [prefixWord, tailWord_2337253, baseEnd_2337253] using wordTrace_append hprefix tailTrace_2337253
  have hstable : (prefixWord ++ tailWord_2337253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2337253).length < 2 ^ (prefixWord ++ tailWord_2337253).sum := by decide
  have hdescent : baseEnd_2337253 < baseStart_2337253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2337253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2337277 : List Nat := [1, 4, 1, 1, 1, 3, 3, 2, 6]
def baseStart_2337277 : Nat := 118140960795 + 2337277 * 2 ^ 59
def prefixEnd_2337277 : Nat := 4983230072969 + 3 ^ 40 * 2337277 * 2
def baseEnd_2337277 : Nat := 266699227488612694819681

theorem tailTrace_2337277 : CollatzResearch.WordTrace tailWord_2337277 prefixEnd_2337277 266699227488612694819681 := by
  unfold tailWord_2337277
  simp only [CollatzResearch.WordTrace]
  refine ⟨85247495553452078976754085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56831663702301385984502723 85247495553452078976754085)
  ·
    refine ⟨15983905416272264808141391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85247495553452078976754085 15983905416272264808141391)
    ·
      refine ⟨23975858124408397212212087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15983905416272264808141391 23975858124408397212212087)
      ·
        refine ⟨35963787186612595818318131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23975858124408397212212087 35963787186612595818318131)
        ·
          refine ⟨53945680779918893727477197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35963787186612595818318131 53945680779918893727477197)
          ·
            refine ⟨20229630292469585147803949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53945680779918893727477197 20229630292469585147803949)
            ·
              refine ⟨7586111359676094430426481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20229630292469585147803949 7586111359676094430426481)
              ·
                refine ⟨5689583519757070822819861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7586111359676094430426481 5689583519757070822819861)
                ·
                  refine ⟨266699227488612694819681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5689583519757070822819861 266699227488612694819681)
                  ·
                    rfl

theorem cell22_2337277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 2, 6].length) (baseStart_2337277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2337277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2337277 prefixEnd_2337277 := by exact prefixLift 2337277
  have htrace : WordTrace (prefixWord ++ tailWord_2337277) baseStart_2337277 baseEnd_2337277 := by
    simpa [prefixWord, tailWord_2337277, baseEnd_2337277] using wordTrace_append hprefix tailTrace_2337277
  have hstable : (prefixWord ++ tailWord_2337277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2337277).length < 2 ^ (prefixWord ++ tailWord_2337277).sum := by decide
  have hdescent : baseEnd_2337277 < baseStart_2337277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2337277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2337337 : List Nat := [1, 2, 1, 5, 1, 1, 1, 1, 2, 7]
def baseStart_2337337 : Nat := 118140960795 + 2337337 * 2 ^ 59
def prefixEnd_2337337 : Nat := 4983230072969 + 3 ^ 40 * 2337337 * 2
def baseEnd_2337337 : Nat := 800118221692017927958859

theorem tailTrace_2337337 : CollatzResearch.WordTrace tailWord_2337337 prefixEnd_2337337 800118221692017927958859 := by
  unfold tailWord_2337337
  simp only [CollatzResearch.WordTrace]
  refine ⟨85249683933234709223938265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56833122622156472815958843 85249683933234709223938265)
  ·
    refine ⟨63937262949926031917953699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85249683933234709223938265 63937262949926031917953699)
    ·
      refine ⟨95905894424889047876930549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63937262949926031917953699 95905894424889047876930549)
      ·
        refine ⟨8991177602333348238462239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 95905894424889047876930549 8991177602333348238462239)
        ·
          refine ⟨13486766403500022357693359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8991177602333348238462239 13486766403500022357693359)
          ·
            refine ⟨20230149605250033536540039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13486766403500022357693359 20230149605250033536540039)
            ·
              refine ⟨30345224407875050304810059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20230149605250033536540039 30345224407875050304810059)
              ·
                refine ⟨45517836611812575457215089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30345224407875050304810059 45517836611812575457215089)
                ·
                  refine ⟨34138377458859431592911317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45517836611812575457215089 34138377458859431592911317)
                  ·
                    refine ⟨800118221692017927958859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34138377458859431592911317 800118221692017927958859)
                    ·
                      rfl

theorem cell22_2337337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 7].length) (baseStart_2337337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2337337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2337337 prefixEnd_2337337 := by exact prefixLift 2337337
  have htrace : WordTrace (prefixWord ++ tailWord_2337337) baseStart_2337337 baseEnd_2337337 := by
    simpa [prefixWord, tailWord_2337337, baseEnd_2337337] using wordTrace_append hprefix tailTrace_2337337
  have hstable : (prefixWord ++ tailWord_2337337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2337337).length < 2 ^ (prefixWord ++ tailWord_2337337).sum := by decide
  have hdescent : baseEnd_2337337 < baseStart_2337337 := by decide
  rcases family_descends (prefixWord ++ tailWord_2337337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2337367 : List Nat := [1, 1, 3, 2, 2, 2, 1, 3, 7]
def baseStart_2337367 : Nat := 118140960795 + 2337367 * 2 ^ 59
def prefixEnd_2337367 : Nat := 4983230072969 + 3 ^ 40 * 2337367 * 2
def baseEnd_2337367 : Nat := 266709497101702616569589

theorem tailTrace_2337367 : CollatzResearch.WordTrace tailWord_2337367 prefixEnd_2337367 266709497101702616569589 := by
  unfold tailWord_2337367
  simp only [CollatzResearch.WordTrace]
  refine ⟨85250778123126024347530355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56833852082084016231686903 85250778123126024347530355)
  ·
    refine ⟨127876167184689036521295533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85250778123126024347530355 127876167184689036521295533)
    ·
      refine ⟨47953562694258388695485825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127876167184689036521295533 47953562694258388695485825)
      ·
        refine ⟨35965172020693791521614369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47953562694258388695485825 35965172020693791521614369)
        ·
          refine ⟨26973879015520343641210777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35965172020693791521614369 26973879015520343641210777)
          ·
            refine ⟨20230409261640257730908083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26973879015520343641210777 20230409261640257730908083)
            ·
              refine ⟨30345613892460386596362125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20230409261640257730908083 30345613892460386596362125)
              ·
                refine ⟨11379605209672644973635797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30345613892460386596362125 11379605209672644973635797)
                ·
                  refine ⟨266709497101702616569589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11379605209672644973635797 266709497101702616569589)
                  ·
                    rfl

theorem cell22_2337367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 3, 7].length) (baseStart_2337367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2337367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2337367 prefixEnd_2337367 := by exact prefixLift 2337367
  have htrace : WordTrace (prefixWord ++ tailWord_2337367) baseStart_2337367 baseEnd_2337367 := by
    simpa [prefixWord, tailWord_2337367, baseEnd_2337367] using wordTrace_append hprefix tailTrace_2337367
  have hstable : (prefixWord ++ tailWord_2337367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2337367).length < 2 ^ (prefixWord ++ tailWord_2337367).sum := by decide
  have hdescent : baseEnd_2337367 < baseStart_2337367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2337367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2337459 : List Nat := [1, 1, 1, 2, 3, 5, 1, 1, 1, 6]
def baseStart_2337459 : Nat := 118140960795 + 2337459 * 2 ^ 59
def prefixEnd_2337459 : Nat := 4983230072969 + 3 ^ 40 * 2337459 * 2
def baseEnd_2337459 : Nat := 800159984785250276408485

theorem tailTrace_2337459 : CollatzResearch.WordTrace tailWord_2337459 prefixEnd_2337459 800159984785250276408485 := by
  unfold tailWord_2337459
  simp only [CollatzResearch.WordTrace]
  refine ⟨85254133638792724059879431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56836089092528482706586287 85254133638792724059879431)
  ·
    refine ⟨127881200458189086089819147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85254133638792724059879431 127881200458189086089819147)
    ·
      refine ⟨191821800687283629134728721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127881200458189086089819147 191821800687283629134728721)
      ·
        refine ⟨143866350515462721851046541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191821800687283629134728721 143866350515462721851046541)
        ·
          refine ⟨53949881443298520694142453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 143866350515462721851046541 53949881443298520694142453)
          ·
            refine ⟨5057801385309236315075855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53949881443298520694142453 5057801385309236315075855)
            ·
              refine ⟨7586702077963854472613783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5057801385309236315075855 7586702077963854472613783)
              ·
                refine ⟨11380053116945781708920675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7586702077963854472613783 11380053116945781708920675)
                ·
                  refine ⟨17070079675418672563381013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11380053116945781708920675 17070079675418672563381013)
                  ·
                    refine ⟨800159984785250276408485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17070079675418672563381013 800159984785250276408485)
                    ·
                      rfl

theorem cell22_2337459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 1, 1, 6].length) (baseStart_2337459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2337459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2337459 prefixEnd_2337459 := by exact prefixLift 2337459
  have htrace : WordTrace (prefixWord ++ tailWord_2337459) baseStart_2337459 baseEnd_2337459 := by
    simpa [prefixWord, tailWord_2337459, baseEnd_2337459] using wordTrace_append hprefix tailTrace_2337459
  have hstable : (prefixWord ++ tailWord_2337459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2337459).length < 2 ^ (prefixWord ++ tailWord_2337459).sum := by decide
  have hdescent : baseEnd_2337459 < baseStart_2337459 := by decide
  rcases family_descends (prefixWord ++ tailWord_2337459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2337461 : List Nat := [1, 3, 3, 3, 1, 1, 2, 2, 1, 5]
def baseStart_2337461 : Nat := 118140960795 + 2337461 * 2 ^ 59
def prefixEnd_2337461 : Nat := 4983230072969 + 3 ^ 40 * 2337461 * 2
def baseEnd_2337461 : Nat := 800160669426122937858479

theorem tailTrace_2337461 : CollatzResearch.WordTrace tailWord_2337461 prefixEnd_2337461 800160669426122937858479 := by
  unfold tailWord_2337461
  simp only [CollatzResearch.WordTrace]
  refine ⟨85254206584785478401452237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56836137723190318934301491 85254206584785478401452237)
  ·
    refine ⟨31970327469294554400544589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85254206584785478401452237 31970327469294554400544589)
    ·
      refine ⟨11988872800985457900204221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31970327469294554400544589 11988872800985457900204221)
      ·
        refine ⟨4495827300369546712576583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11988872800985457900204221 4495827300369546712576583)
        ·
          refine ⟨6743740950554320068864875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4495827300369546712576583 6743740950554320068864875)
          ·
            refine ⟨10115611425831480103297313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6743740950554320068864875 10115611425831480103297313)
            ·
              refine ⟨7586708569373610077472985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10115611425831480103297313 7586708569373610077472985)
              ·
                refine ⟨5690031427030207558104739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7586708569373610077472985 5690031427030207558104739)
                ·
                  refine ⟨8535047140545311337157109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5690031427030207558104739 8535047140545311337157109)
                  ·
                    refine ⟨800160669426122937858479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8535047140545311337157109 800160669426122937858479)
                    ·
                      rfl

theorem cell22_2337461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_2337461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2337461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2337461 prefixEnd_2337461 := by exact prefixLift 2337461
  have htrace : WordTrace (prefixWord ++ tailWord_2337461) baseStart_2337461 baseEnd_2337461 := by
    simpa [prefixWord, tailWord_2337461, baseEnd_2337461] using wordTrace_append hprefix tailTrace_2337461
  have hstable : (prefixWord ++ tailWord_2337461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2337461).length < 2 ^ (prefixWord ++ tailWord_2337461).sum := by decide
  have hdescent : baseEnd_2337461 < baseStart_2337461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2337461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2337463 : List Nat := [1, 1, 3, 1, 6, 1, 2, 3, 4]
def baseStart_2337463 : Nat := 118140960795 + 2337463 * 2 ^ 59
def prefixEnd_2337463 : Nat := 4983230072969 + 3 ^ 40 * 2337463 * 2
def baseEnd_2337463 : Nat := 266720451355665199769491

theorem tailTrace_2337463 : CollatzResearch.WordTrace tailWord_2337463 prefixEnd_2337463 266720451355665199769491 := by
  unfold tailWord_2337463
  simp only [CollatzResearch.WordTrace]
  refine ⟨85254279530778232743025043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56836186353852155162016695 85254279530778232743025043)
  ·
    refine ⟨127881419296167349114537565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85254279530778232743025043 127881419296167349114537565)
    ·
      refine ⟨47955532236062755917951587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127881419296167349114537565 47955532236062755917951587)
      ·
        refine ⟨71933298354094133876927381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47955532236062755917951587 71933298354094133876927381)
        ·
          refine ⟨3371873360348162525480971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 71933298354094133876927381 3371873360348162525480971)
          ·
            refine ⟨5057810040522243788221457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3371873360348162525480971 5057810040522243788221457)
            ·
              refine ⟨3793357530391682841166093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5057810040522243788221457 3793357530391682841166093)
              ·
                refine ⟨1422509073896881065437285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3793357530391682841166093 1422509073896881065437285)
                ·
                  refine ⟨266720451355665199769491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1422509073896881065437285 266720451355665199769491)
                  ·
                    rfl

theorem cell22_2337463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 3, 4].length) (baseStart_2337463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2337463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2337463 prefixEnd_2337463 := by exact prefixLift 2337463
  have htrace : WordTrace (prefixWord ++ tailWord_2337463) baseStart_2337463 baseEnd_2337463 := by
    simpa [prefixWord, tailWord_2337463, baseEnd_2337463] using wordTrace_append hprefix tailTrace_2337463
  have hstable : (prefixWord ++ tailWord_2337463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2337463).length < 2 ^ (prefixWord ++ tailWord_2337463).sum := by decide
  have hdescent : baseEnd_2337463 < baseStart_2337463 := by decide
  rcases family_descends (prefixWord ++ tailWord_2337463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2337519 : List Nat := [1, 1, 2, 1, 5, 2, 1, 2, 7]
def baseStart_2337519 : Nat := 118140960795 + 2337519 * 2 ^ 59
def prefixEnd_2337519 : Nat := 4983230072969 + 3 ^ 40 * 2337519 * 2
def baseEnd_2337519 : Nat := 266726841337143373302767

theorem tailTrace_2337519 : CollatzResearch.WordTrace tailWord_2337519 prefixEnd_2337519 266726841337143373302767 := by
  unfold tailWord_2337519
  simp only [CollatzResearch.WordTrace]
  refine ⟨85256322018575354307063611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56837548012383569538042407 85256322018575354307063611)
  ·
    refine ⟨127884483027863031460595417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85256322018575354307063611 127884483027863031460595417)
    ·
      refine ⟨95913362270897273595446563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127884483027863031460595417 95913362270897273595446563)
      ·
        refine ⟨143870043406345910393169845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95913362270897273595446563 143870043406345910393169845)
        ·
          refine ⟨13487816569344929099359673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 143870043406345910393169845 13487816569344929099359673)
          ·
            refine ⟨10115862427008696824519755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13487816569344929099359673 10115862427008696824519755)
            ·
              refine ⟨15173793640513045236779633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10115862427008696824519755 15173793640513045236779633)
              ·
                refine ⟨11380345230384783927584725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15173793640513045236779633 11380345230384783927584725)
                ·
                  refine ⟨266726841337143373302767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11380345230384783927584725 266726841337143373302767)
                  ·
                    rfl

theorem cell22_2337519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 2, 7].length) (baseStart_2337519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2337519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2337519 prefixEnd_2337519 := by exact prefixLift 2337519
  have htrace : WordTrace (prefixWord ++ tailWord_2337519) baseStart_2337519 baseEnd_2337519 := by
    simpa [prefixWord, tailWord_2337519, baseEnd_2337519] using wordTrace_append hprefix tailTrace_2337519
  have hstable : (prefixWord ++ tailWord_2337519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2337519).length < 2 ^ (prefixWord ++ tailWord_2337519).sum := by decide
  have hdescent : baseEnd_2337519 < baseStart_2337519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2337519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2337525 : List Nat := [1, 3, 6, 1, 1, 2, 8]
def baseStart_2337525 : Nat := 118140960795 + 2337525 * 2 ^ 59
def prefixEnd_2337525 : Nat := 4983230072969 + 3 ^ 40 * 2337525 * 2
def baseEnd_2337525 : Nat := 29636391775335114972529

theorem tailTrace_2337525 : CollatzResearch.WordTrace tailWord_2337525 prefixEnd_2337525 29636391775335114972529 := by
  unfold tailWord_2337525
  simp only [CollatzResearch.WordTrace]
  refine ⟨85256540856553617331782029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56837693904369078221188019 85256540856553617331782029)
  ·
    refine ⟨31971202821207606499418261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85256540856553617331782029 31971202821207606499418261)
    ·
      refine ⟨1498650132244106554660231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 31971202821207606499418261 1498650132244106554660231)
      ·
        refine ⟨2247975198366159831990347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1498650132244106554660231 2247975198366159831990347)
        ·
          refine ⟨3371962797549239747985521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2247975198366159831990347 3371962797549239747985521)
          ·
            refine ⟨2528972098161929810989141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3371962797549239747985521 2528972098161929810989141)
            ·
              refine ⟨29636391775335114972529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2528972098161929810989141 29636391775335114972529)
              ·
                rfl

theorem cell22_2337525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 8].length) (baseStart_2337525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2337525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2337525 prefixEnd_2337525 := by exact prefixLift 2337525
  have htrace : WordTrace (prefixWord ++ tailWord_2337525) baseStart_2337525 baseEnd_2337525 := by
    simpa [prefixWord, tailWord_2337525, baseEnd_2337525] using wordTrace_append hprefix tailTrace_2337525
  have hstable : (prefixWord ++ tailWord_2337525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2337525).length < 2 ^ (prefixWord ++ tailWord_2337525).sum := by decide
  have hdescent : baseEnd_2337525 < baseStart_2337525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2337525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2337579 : List Nat := [1, 1, 1, 1, 2, 1, 2, 5, 3, 5]
def baseStart_2337579 : Nat := 118140960795 + 2337579 * 2 ^ 59
def prefixEnd_2337579 : Nat := 4983230072969 + 3 ^ 40 * 2337579 * 2
def baseEnd_2337579 : Nat := 800201063237609963408117

theorem tailTrace_2337579 : CollatzResearch.WordTrace tailWord_2337579 prefixEnd_2337579 800201063237609963408117 := by
  unfold tailWord_2337579
  simp only [CollatzResearch.WordTrace]
  refine ⟨85258510398357984554247791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56839006932238656369498527 85258510398357984554247791)
  ·
    refine ⟨127887765597536976831371687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85258510398357984554247791 127887765597536976831371687)
    ·
      refine ⟨191831648396305465247057531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127887765597536976831371687 191831648396305465247057531)
      ·
        refine ⟨287747472594458197870586297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191831648396305465247057531 287747472594458197870586297)
        ·
          refine ⟨215810604445843648402939723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 287747472594458197870586297 215810604445843648402939723)
          ·
            refine ⟨323715906668765472604409585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215810604445843648402939723 323715906668765472604409585)
            ·
              refine ⟨242786930001574104453307189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 323715906668765472604409585 242786930001574104453307189)
              ·
                refine ⟨22761274687647572292497549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 242786930001574104453307189 22761274687647572292497549)
                ·
                  refine ⟨8535478007867839609686581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22761274687647572292497549 8535478007867839609686581)
                  ·
                    refine ⟨800201063237609963408117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8535478007867839609686581 800201063237609963408117)
                    ·
                      rfl

theorem cell22_2337579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 3, 5].length) (baseStart_2337579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2337579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2337579 prefixEnd_2337579 := by exact prefixLift 2337579
  have htrace : WordTrace (prefixWord ++ tailWord_2337579) baseStart_2337579 baseEnd_2337579 := by
    simpa [prefixWord, tailWord_2337579, baseEnd_2337579] using wordTrace_append hprefix tailTrace_2337579
  have hstable : (prefixWord ++ tailWord_2337579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2337579).length < 2 ^ (prefixWord ++ tailWord_2337579).sum := by decide
  have hdescent : baseEnd_2337579 < baseStart_2337579 := by decide
  rcases family_descends (prefixWord ++ tailWord_2337579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2337628 : List Nat := [2, 2, 4, 2, 1, 2, 1, 1, 1, 6]
def baseStart_2337628 : Nat := 118140960795 + 2337628 * 2 ^ 59
def prefixEnd_2337628 : Nat := 4983230072969 + 3 ^ 40 * 2337628 * 2
def baseEnd_2337628 : Nat := 800217836938990168932967

theorem tailTrace_2337628 : CollatzResearch.WordTrace tailWord_2337628 prefixEnd_2337628 800217836938990168932967 := by
  unfold tailWord_2337628
  simp only [CollatzResearch.WordTrace]
  refine ⟨42630148787590232961390769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56840198383453643948521025 42630148787590232961390769)
  ·
    refine ⟨31972611590692674721043077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42630148787590232961390769 31972611590692674721043077)
    ·
      refine ⟨5994864673254876510195577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31972611590692674721043077 5994864673254876510195577)
      ·
        refine ⟨4496148504941157382646683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5994864673254876510195577 4496148504941157382646683)
        ·
          refine ⟨6744222757411736073970025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4496148504941157382646683 6744222757411736073970025)
          ·
            refine ⟨5058167068058802055477519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6744222757411736073970025 5058167068058802055477519)
            ·
              refine ⟨7587250602088203083216279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5058167068058802055477519 7587250602088203083216279)
              ·
                refine ⟨11380875903132304624824419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7587250602088203083216279 11380875903132304624824419)
                ·
                  refine ⟨17071313854698456937236629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11380875903132304624824419 17071313854698456937236629)
                  ·
                    refine ⟨800217836938990168932967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17071313854698456937236629 800217836938990168932967)
                    ·
                      rfl

theorem cell22_2337628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_2337628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2337628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2337628 prefixEnd_2337628 := by exact prefixLift 2337628
  have htrace : WordTrace (prefixWord ++ tailWord_2337628) baseStart_2337628 baseEnd_2337628 := by
    simpa [prefixWord, tailWord_2337628, baseEnd_2337628] using wordTrace_append hprefix tailTrace_2337628
  have hstable : (prefixWord ++ tailWord_2337628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2337628).length < 2 ^ (prefixWord ++ tailWord_2337628).sum := by decide
  have hdescent : baseEnd_2337628 < baseStart_2337628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2337628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2337634 : List Nat := [3, 3, 2, 1, 4, 1, 2, 1, 1, 4]
def baseStart_2337634 : Nat := 118140960795 + 2337634 * 2 ^ 59
def prefixEnd_2337634 : Nat := 4983230072969 + 3 ^ 40 * 2337634 * 2
def baseEnd_2337634 : Nat := 800219890861608153282949

theorem tailTrace_2337634 : CollatzResearch.WordTrace tailWord_2337634 prefixEnd_2337634 800219890861608153282949 := by
  unfold tailWord_2337634
  simp only [CollatzResearch.WordTrace]
  refine ⟨21315129103289682236874989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56840344275439152631666637 21315129103289682236874989)
  ·
    refine ⟨7993173413733630838828121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21315129103289682236874989 7993173413733630838828121)
    ·
      refine ⟨5994880060300223129121091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7993173413733630838828121 5994880060300223129121091)
      ·
        refine ⟨8992320090450334693681637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5994880060300223129121091 8992320090450334693681637)
        ·
          refine ⟨1686060016959437755065307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8992320090450334693681637 1686060016959437755065307)
          ·
            refine ⟨2529090025439156632597961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1686060016959437755065307 2529090025439156632597961)
            ·
              refine ⟨1896817519079367474448471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2529090025439156632597961 1896817519079367474448471)
              ·
                refine ⟨2845226278619051211672707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1896817519079367474448471 2845226278619051211672707)
                ·
                  refine ⟨4267839417928576817509061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2845226278619051211672707 4267839417928576817509061)
                  ·
                    refine ⟨800219890861608153282949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4267839417928576817509061 800219890861608153282949)
                    ·
                      rfl

theorem cell22_2337634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_2337634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2337634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2337634 prefixEnd_2337634 := by exact prefixLift 2337634
  have htrace : WordTrace (prefixWord ++ tailWord_2337634) baseStart_2337634 baseEnd_2337634 := by
    simpa [prefixWord, tailWord_2337634, baseEnd_2337634] using wordTrace_append hprefix tailTrace_2337634
  have hstable : (prefixWord ++ tailWord_2337634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2337634).length < 2 ^ (prefixWord ++ tailWord_2337634).sum := by decide
  have hdescent : baseEnd_2337634 < baseStart_2337634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2337634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2337701 : List Nat := [1, 3, 1, 2, 1, 1, 1, 1, 7, 4]
def baseStart_2337701 : Nat := 118140960795 + 2337701 * 2 ^ 59
def prefixEnd_2337701 : Nat := 4983230072969 + 3 ^ 40 * 2337701 * 2
def baseEnd_2337701 : Nat := 800242826330842311857743

theorem tailTrace_2337701 : CollatzResearch.WordTrace tailWord_2337701 prefixEnd_2337701 800242826330842311857743 := by
  unfold tailWord_2337701
  simp only [CollatzResearch.WordTrace]
  refine ⟨85262960103915999390188957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56841973402610666260125971 85262960103915999390188957)
  ·
    refine ⟨31973610038968499771320859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85262960103915999390188957 31973610038968499771320859)
    ·
      refine ⟨47960415058452749656981289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31973610038968499771320859 47960415058452749656981289)
      ·
        refine ⟨35970311293839562242735967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47960415058452749656981289 35970311293839562242735967)
        ·
          refine ⟨53955466940759343364103951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35970311293839562242735967 53955466940759343364103951)
          ·
            refine ⟨80933200411139015046155927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53955466940759343364103951 80933200411139015046155927)
            ·
              refine ⟨121399800616708522569233891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80933200411139015046155927 121399800616708522569233891)
              ·
                refine ⟨182099700925062783853850837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 121399800616708522569233891 182099700925062783853850837)
                ·
                  refine ⟨4267961740431158996574629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 182099700925062783853850837 4267961740431158996574629)
                  ·
                    refine ⟨800242826330842311857743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4267961740431158996574629 800242826330842311857743)
                    ·
                      rfl

theorem cell22_2337701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 7, 4].length) (baseStart_2337701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2337701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2337701 prefixEnd_2337701 := by exact prefixLift 2337701
  have htrace : WordTrace (prefixWord ++ tailWord_2337701) baseStart_2337701 baseEnd_2337701 := by
    simpa [prefixWord, tailWord_2337701, baseEnd_2337701] using wordTrace_append hprefix tailTrace_2337701
  have hstable : (prefixWord ++ tailWord_2337701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2337701).length < 2 ^ (prefixWord ++ tailWord_2337701).sum := by decide
  have hdescent : baseEnd_2337701 < baseStart_2337701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2337701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2337709 : List Nat := [1, 5, 2, 3, 1, 2, 1, 1, 3, 3]
def baseStart_2337709 : Nat := 118140960795 + 2337709 * 2 ^ 59
def prefixEnd_2337709 : Nat := 4983230072969 + 3 ^ 40 * 2337709 * 2
def baseEnd_2337709 : Nat := 800245564894332957657719

theorem tailTrace_2337709 : CollatzResearch.WordTrace tailWord_2337709 prefixEnd_2337709 800245564894332957657719 := by
  unfold tailWord_2337709
  simp only [CollatzResearch.WordTrace]
  refine ⟨85263251887887016756480181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56842167925258011170986787 85263251887887016756480181)
  ·
    refine ⟨7993429864489407820920017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 85263251887887016756480181 7993429864489407820920017)
    ·
      refine ⟨5995072398367055865690013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7993429864489407820920017 5995072398367055865690013)
      ·
        refine ⟨2248152149387645949633755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5995072398367055865690013 2248152149387645949633755)
        ·
          refine ⟨3372228224081468924450633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2248152149387645949633755 3372228224081468924450633)
          ·
            refine ⟨2529171168061101693337975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3372228224081468924450633 2529171168061101693337975)
            ·
              refine ⟨3793756752091652540006963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2529171168061101693337975 3793756752091652540006963)
              ·
                refine ⟨5690635128137478810010445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3793756752091652540006963 5690635128137478810010445)
                ·
                  refine ⟨2133988173051554553753917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5690635128137478810010445 2133988173051554553753917)
                  ·
                    refine ⟨800245564894332957657719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2133988173051554553753917 800245564894332957657719)
                    ·
                      rfl

theorem cell22_2337709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_2337709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2337709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2337709 prefixEnd_2337709 := by exact prefixLift 2337709
  have htrace : WordTrace (prefixWord ++ tailWord_2337709) baseStart_2337709 baseEnd_2337709 := by
    simpa [prefixWord, tailWord_2337709, baseEnd_2337709] using wordTrace_append hprefix tailTrace_2337709
  have hstable : (prefixWord ++ tailWord_2337709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2337709).length < 2 ^ (prefixWord ++ tailWord_2337709).sum := by decide
  have hdescent : baseEnd_2337709 < baseStart_2337709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2337709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2337748 : List Nat := [2, 4, 1, 2, 1, 2, 1, 1, 3, 5]
def baseStart_2337748 : Nat := 118140960795 + 2337748 * 2 ^ 59
def prefixEnd_2337748 : Nat := 4983230072969 + 3 ^ 40 * 2337748 * 2
def baseEnd_2337748 : Nat := 800258915391349855932599

theorem tailTrace_2337748 : CollatzResearch.WordTrace tailWord_2337748 prefixEnd_2337748 800258915391349855932599 := by
  unfold tailWord_2337748
  simp only [CollatzResearch.WordTrace]
  refine ⟨42632337167372863208574949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56843116223163817611433265 42632337167372863208574949)
  ·
    refine ⟨7993563218882411851607803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42632337167372863208574949 7993563218882411851607803)
    ·
      refine ⟨11990344828323617777411705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7993563218882411851607803 11990344828323617777411705)
      ·
        refine ⟨8992758621242713333058779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11990344828323617777411705 8992758621242713333058779)
        ·
          refine ⟨13489137931864069999588169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8992758621242713333058779 13489137931864069999588169)
          ·
            refine ⟨10116853448898052499691127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13489137931864069999588169 10116853448898052499691127)
            ·
              refine ⟨15175280173347078749536691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10116853448898052499691127 15175280173347078749536691)
              ·
                refine ⟨22762920260020618124305037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15175280173347078749536691 22762920260020618124305037)
                ·
                  refine ⟨8536095097507731796614389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22762920260020618124305037 8536095097507731796614389)
                  ·
                    refine ⟨800258915391349855932599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8536095097507731796614389 800258915391349855932599)
                    ·
                      rfl

theorem cell22_2337748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_2337748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2337748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2337748 prefixEnd_2337748 := by exact prefixLift 2337748
  have htrace : WordTrace (prefixWord ++ tailWord_2337748) baseStart_2337748 baseEnd_2337748 := by
    simpa [prefixWord, tailWord_2337748, baseEnd_2337748] using wordTrace_append hprefix tailTrace_2337748
  have hstable : (prefixWord ++ tailWord_2337748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2337748).length < 2 ^ (prefixWord ++ tailWord_2337748).sum := by decide
  have hdescent : baseEnd_2337748 < baseStart_2337748 := by decide
  rcases family_descends (prefixWord ++ tailWord_2337748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
