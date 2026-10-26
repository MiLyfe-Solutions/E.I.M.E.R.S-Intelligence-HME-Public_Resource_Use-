import V185TrunkScan23Chunk0181

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1078333 : List Nat := [1, 4, 1, 3, 1, 3, 1, 2, 3, 1, 3]
def baseStart_1078333 : Nat := 118140960795 + 1078333 * 2 ^ 59
def prefixEnd_1078333 : Nat := 4983230072969 + 3 ^ 40 * 1078333 * 2
def baseEnd_1078333 : Nat := 553703134604834750878343

theorem tailTrace_1078333 : CollatzResearch.WordTrace tailWord_1078333 prefixEnd_1078333 553703134604834750878343 := by
  unfold tailWord_1078333
  simp only [CollatzResearch.WordTrace]
  refine ⟨39330035602391180459415653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26220023734927453639610435 39330035602391180459415653)
  ·
    refine ⟨7374381675448346336140435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39330035602391180459415653 7374381675448346336140435)
    ·
      refine ⟨11061572513172519504210653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7374381675448346336140435 11061572513172519504210653)
      ·
        refine ⟨4148089692439694814078995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11061572513172519504210653 4148089692439694814078995)
        ·
          refine ⟨6222134538659542221118493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4148089692439694814078995 6222134538659542221118493)
          ·
            refine ⟨2333300451997328332919435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6222134538659542221118493 2333300451997328332919435)
            ·
              refine ⟨3499950677995992499379153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2333300451997328332919435 3499950677995992499379153)
              ·
                refine ⟨2624963008496994374534365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3499950677995992499379153 2624963008496994374534365)
                ·
                  refine ⟨984361128186372890450387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2624963008496994374534365 984361128186372890450387)
                  ·
                    refine ⟨1476541692279559335675581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 984361128186372890450387 1476541692279559335675581)
                    ·
                      refine ⟨553703134604834750878343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1476541692279559335675581 553703134604834750878343)
                      ·
                        rfl

theorem cell23_1078333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_1078333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1078333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1078333 prefixEnd_1078333 := by exact prefixLift 1078333
  have htrace : WordTrace (prefixWord ++ tailWord_1078333) baseStart_1078333 baseEnd_1078333 := by
    simpa [prefixWord, tailWord_1078333, baseEnd_1078333] using wordTrace_append hprefix tailTrace_1078333
  have hstable : (prefixWord ++ tailWord_1078333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078333).length < 2 ^ (prefixWord ++ tailWord_1078333).sum := by decide
  have hdescent : baseEnd_1078333 < baseStart_1078333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078339 : List Nat := [1, 1, 1, 3, 1, 2, 3, 3, 3, 1, 4]
def baseStart_1078339 : Nat := 118140960795 + 1078339 * 2 ^ 59
def prefixEnd_1078339 : Nat := 4983230072969 + 3 ^ 40 * 1078339 * 2
def baseEnd_1078339 : Nat := 553706215488761727403315

theorem tailTrace_1078339 : CollatzResearch.WordTrace tailWord_1078339 prefixEnd_1078339 553706215488761727403315 := by
  unfold tailWord_1078339
  simp only [CollatzResearch.WordTrace]
  refine ⟨39330254440369443484134071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26220169626912962322756047 39330254440369443484134071)
  ·
    refine ⟨58995381660554165226201107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39330254440369443484134071 58995381660554165226201107)
    ·
      refine ⟨88493072490831247839301661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58995381660554165226201107 88493072490831247839301661)
      ·
        refine ⟨33184902184061717939738123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88493072490831247839301661 33184902184061717939738123)
        ·
          refine ⟨49777353276092576909607185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33184902184061717939738123 49777353276092576909607185)
          ·
            refine ⟨37333014957069432682205389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49777353276092576909607185 37333014957069432682205389)
            ·
              refine ⟨13999880608901037255827021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37333014957069432682205389 13999880608901037255827021)
              ·
                refine ⟨5249955228337888970935133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13999880608901037255827021 5249955228337888970935133)
                ·
                  refine ⟨1968733210626708364100675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5249955228337888970935133 1968733210626708364100675)
                  ·
                    refine ⟨2953099815940062546151013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1968733210626708364100675 2953099815940062546151013)
                    ·
                      refine ⟨553706215488761727403315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2953099815940062546151013 553706215488761727403315)
                      ·
                        rfl

theorem cell23_1078339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 3, 3, 1, 4].length) (baseStart_1078339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1078339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1078339 prefixEnd_1078339 := by exact prefixLift 1078339
  have htrace : WordTrace (prefixWord ++ tailWord_1078339) baseStart_1078339 baseEnd_1078339 := by
    simpa [prefixWord, tailWord_1078339, baseEnd_1078339] using wordTrace_append hprefix tailTrace_1078339
  have hstable : (prefixWord ++ tailWord_1078339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078339).length < 2 ^ (prefixWord ++ tailWord_1078339).sum := by decide
  have hdescent : baseEnd_1078339 < baseStart_1078339 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078343 : List Nat := [1, 1, 4, 1, 3, 2, 3, 1, 2, 3, 2]
def baseStart_1078343 : Nat := 118140960795 + 1078343 * 2 ^ 59
def prefixEnd_1078343 : Nat := 4983230072969 + 3 ^ 40 * 1078343 * 2
def baseEnd_1078343 : Nat := 553708269411379711753297

theorem tailTrace_1078343 : CollatzResearch.WordTrace tailWord_1078343 prefixEnd_1078343 553708269411379711753297 := by
  unfold tailWord_1078343
  simp only [CollatzResearch.WordTrace]
  refine ⟨39330400332354952167279683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26220266888236634778186455 39330400332354952167279683)
  ·
    refine ⟨58995600498532428250919525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39330400332354952167279683 58995600498532428250919525)
    ·
      refine ⟨11061675093474830297047411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58995600498532428250919525 11061675093474830297047411)
      ·
        refine ⟨16592512640212245445571117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11061675093474830297047411 16592512640212245445571117)
        ·
          refine ⟨6222192240079592042089169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16592512640212245445571117 6222192240079592042089169)
          ·
            refine ⟨4666644180059694031566877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6222192240079592042089169 4666644180059694031566877)
            ·
              refine ⟨1749991567522385261837579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4666644180059694031566877 1749991567522385261837579)
              ·
                refine ⟨2624987351283577892756369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1749991567522385261837579 2624987351283577892756369)
                ·
                  refine ⟨1968740513462683419567277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2624987351283577892756369 1968740513462683419567277)
                  ·
                    refine ⟨738277692548506282337729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1968740513462683419567277 738277692548506282337729)
                    ·
                      refine ⟨553708269411379711753297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 738277692548506282337729 553708269411379711753297)
                      ·
                        rfl

theorem cell23_1078343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 1, 2, 3, 2].length) (baseStart_1078343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1078343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1078343 prefixEnd_1078343 := by exact prefixLift 1078343
  have htrace : WordTrace (prefixWord ++ tailWord_1078343) baseStart_1078343 baseEnd_1078343 := by
    simpa [prefixWord, tailWord_1078343, baseEnd_1078343] using wordTrace_append hprefix tailTrace_1078343
  have hstable : (prefixWord ++ tailWord_1078343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078343).length < 2 ^ (prefixWord ++ tailWord_1078343).sum := by decide
  have hdescent : baseEnd_1078343 < baseStart_1078343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078350 : List Nat := [4, 1, 1, 1, 1, 3, 4, 3, 1, 1, 3]
def baseStart_1078350 : Nat := 118140960795 + 1078350 * 2 ^ 59
def prefixEnd_1078350 : Nat := 4983230072969 + 3 ^ 40 * 1078350 * 2
def baseEnd_1078350 : Nat := 553711863775961184365765

theorem tailTrace_1078350 : CollatzResearch.WordTrace tailWord_1078350 prefixEnd_1078350 553711863775961184365765 := by
  unfold tailWord_1078350
  simp only [CollatzResearch.WordTrace]
  refine ⟨4916331955416199045348063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26220437095553061575189669 4916331955416199045348063)
  ·
    refine ⟨7374497933124298568022095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4916331955416199045348063 7374497933124298568022095)
    ·
      refine ⟨11061746899686447852033143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7374497933124298568022095 11061746899686447852033143)
      ·
        refine ⟨16592620349529671778049715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11061746899686447852033143 16592620349529671778049715)
        ·
          refine ⟨24888930524294507667074573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16592620349529671778049715 24888930524294507667074573)
          ·
            refine ⟨9333348946610440375152965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24888930524294507667074573 9333348946610440375152965)
            ·
              refine ⟨1750002927489457570341181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9333348946610440375152965 1750002927489457570341181)
              ·
                refine ⟨656251097808546588877943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1750002927489457570341181 656251097808546588877943)
                ·
                  refine ⟨984376646712819883316915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 656251097808546588877943 984376646712819883316915)
                  ·
                    refine ⟨1476564970069229824975373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 984376646712819883316915 1476564970069229824975373)
                    ·
                      refine ⟨553711863775961184365765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1476564970069229824975373 553711863775961184365765)
                      ·
                        rfl

theorem cell23_1078350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 3, 1, 1, 3].length) (baseStart_1078350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1078350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1078350 prefixEnd_1078350 := by exact prefixLift 1078350
  have htrace : WordTrace (prefixWord ++ tailWord_1078350) baseStart_1078350 baseEnd_1078350 := by
    simpa [prefixWord, tailWord_1078350, baseEnd_1078350] using wordTrace_append hprefix tailTrace_1078350
  have hstable : (prefixWord ++ tailWord_1078350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078350).length < 2 ^ (prefixWord ++ tailWord_1078350).sum := by decide
  have hdescent : baseEnd_1078350 < baseStart_1078350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078359 : List Nat := [1, 1, 3, 2, 2, 1, 1, 5, 1, 1, 5]
def baseStart_1078359 : Nat := 118140960795 + 1078359 * 2 ^ 59
def prefixEnd_1078359 : Nat := 4983230072969 + 3 ^ 40 * 1078359 * 2
def baseEnd_1078359 : Nat := 553716485101851649153223

theorem tailTrace_1078359 : CollatzResearch.WordTrace tailWord_1078359 prefixEnd_1078359 553716485101851649153223 := by
  unfold tailWord_1078359
  simp only [CollatzResearch.WordTrace]
  refine ⟨39330983900296986899862131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26220655933531324599908087 39330983900296986899862131)
  ·
    refine ⟨58996475850445480349793197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39330983900296986899862131 58996475850445480349793197)
    ·
      refine ⟨22123678443917055131172449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58996475850445480349793197 22123678443917055131172449)
      ·
        refine ⟨16592758832937791348379337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22123678443917055131172449 16592758832937791348379337)
        ·
          refine ⟨12444569124703343511284503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16592758832937791348379337 12444569124703343511284503)
          ·
            refine ⟨18666853687055015266926755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12444569124703343511284503 18666853687055015266926755)
            ·
              refine ⟨28000280530582522900390133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18666853687055015266926755 28000280530582522900390133)
              ·
                refine ⟨2625026299742111521911575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28000280530582522900390133 2625026299742111521911575)
                ·
                  refine ⟨3937539449613167282867363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2625026299742111521911575 3937539449613167282867363)
                  ·
                    refine ⟨5906309174419750924301045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3937539449613167282867363 5906309174419750924301045)
                    ·
                      refine ⟨553716485101851649153223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5906309174419750924301045 553716485101851649153223)
                      ·
                        rfl

theorem cell23_1078359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 5, 1, 1, 5].length) (baseStart_1078359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1078359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1078359 prefixEnd_1078359 := by exact prefixLift 1078359
  have htrace : WordTrace (prefixWord ++ tailWord_1078359) baseStart_1078359 baseEnd_1078359 := by
    simpa [prefixWord, tailWord_1078359, baseEnd_1078359] using wordTrace_append hprefix tailTrace_1078359
  have hstable : (prefixWord ++ tailWord_1078359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078359).length < 2 ^ (prefixWord ++ tailWord_1078359).sum := by decide
  have hdescent : baseEnd_1078359 < baseStart_1078359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078369 : List Nat := [1, 2, 3, 1, 1, 2, 2, 2, 3, 2, 4]
def baseStart_1078369 : Nat := 118140960795 + 1078369 * 2 ^ 59
def prefixEnd_1078369 : Nat := 4983230072969 + 3 ^ 40 * 1078369 * 2
def baseEnd_1078369 : Nat := 553721619908396610028177

theorem tailTrace_1078369 : CollatzResearch.WordTrace tailWord_1078369 prefixEnd_1078369 553721619908396610028177 := by
  unfold tailWord_1078369
  simp only [CollatzResearch.WordTrace]
  refine ⟨39331348630260758607726161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26220899086840505738484107 39331348630260758607726161)
  ·
    refine ⟨29498511472695568955794621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39331348630260758607726161 29498511472695568955794621)
    ·
      refine ⟨11061941802260838358422983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29498511472695568955794621 11061941802260838358422983)
      ·
        refine ⟨16592912703391257537634475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11061941802260838358422983 16592912703391257537634475)
        ·
          refine ⟨24889369055086886306451713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16592912703391257537634475 24889369055086886306451713)
          ·
            refine ⟨18667026791315164729838785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24889369055086886306451713 18667026791315164729838785)
            ·
              refine ⟨14000270093486373547379089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18667026791315164729838785 14000270093486373547379089)
              ·
                refine ⟨10500202570114780160534317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14000270093486373547379089 10500202570114780160534317)
                ·
                  refine ⟨3937575963793042560200369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10500202570114780160534317 3937575963793042560200369)
                  ·
                    refine ⟨2953181972844781920150277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3937575963793042560200369 2953181972844781920150277)
                    ·
                      refine ⟨553721619908396610028177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2953181972844781920150277 553721619908396610028177)
                      ·
                        rfl

theorem cell23_1078369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 3, 2, 4].length) (baseStart_1078369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1078369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1078369 prefixEnd_1078369 := by exact prefixLift 1078369
  have htrace : WordTrace (prefixWord ++ tailWord_1078369) baseStart_1078369 baseEnd_1078369 := by
    simpa [prefixWord, tailWord_1078369, baseEnd_1078369] using wordTrace_append hprefix tailTrace_1078369
  have hstable : (prefixWord ++ tailWord_1078369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078369).length < 2 ^ (prefixWord ++ tailWord_1078369).sum := by decide
  have hdescent : baseEnd_1078369 < baseStart_1078369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078383 : List Nat := [1, 1, 2, 1, 3, 3, 5, 1, 2, 4]
def baseStart_1078383 : Nat := 118140960795 + 1078383 * 2 ^ 59
def prefixEnd_1078383 : Nat := 4983230072969 + 3 ^ 40 * 1078383 * 2
def baseEnd_1078383 : Nat := 184576269545853185084371

theorem tailTrace_1078383 : CollatzResearch.WordTrace tailWord_1078383 prefixEnd_1078383 184576269545853185084371 := by
  unfold tailWord_1078383
  simp only [CollatzResearch.WordTrace]
  refine ⟨39331859252210038998735803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26221239501473359332490535 39331859252210038998735803)
  ·
    refine ⟨58997788878315058498103705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39331859252210038998735803 58997788878315058498103705)
    ·
      refine ⟨44248341658736293873577779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58997788878315058498103705 44248341658736293873577779)
      ·
        refine ⟨66372512488104440810366669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44248341658736293873577779 66372512488104440810366669)
        ·
          refine ⟨24889692183039165303887501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66372512488104440810366669 24889692183039165303887501)
          ·
            refine ⟨9333634568639686988957813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24889692183039165303887501 9333634568639686988957813)
            ·
              refine ⟨875028240809970655214795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9333634568639686988957813 875028240809970655214795)
              ·
                refine ⟨1312542361214955982822193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 875028240809970655214795 1312542361214955982822193)
                ·
                  refine ⟨984406770911216987116645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1312542361214955982822193 984406770911216987116645)
                  ·
                    refine ⟨184576269545853185084371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 984406770911216987116645 184576269545853185084371)
                    ·
                      rfl

theorem cell23_1078383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 5, 1, 2, 4].length) (baseStart_1078383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1078383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1078383 prefixEnd_1078383 := by exact prefixLift 1078383
  have htrace : WordTrace (prefixWord ++ tailWord_1078383) baseStart_1078383 baseEnd_1078383 := by
    simpa [prefixWord, tailWord_1078383, baseEnd_1078383] using wordTrace_append hprefix tailTrace_1078383
  have hstable : (prefixWord ++ tailWord_1078383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078383).length < 2 ^ (prefixWord ++ tailWord_1078383).sum := by decide
  have hdescent : baseEnd_1078383 < baseStart_1078383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078390 : List Nat := [5, 1, 1, 2, 1, 1, 1, 4, 3, 2, 2]
def baseStart_1078390 : Nat := 118140960795 + 1078390 * 2 ^ 59
def prefixEnd_1078390 : Nat := 4983230072969 + 3 ^ 40 * 1078390 * 2
def baseEnd_1078390 : Nat := 553732403002141027865581

theorem tailTrace_1078390 : CollatzResearch.WordTrace tailWord_1078390 prefixEnd_1078390 553732403002141027865581 := by
  unfold tailWord_1078390
  simp only [CollatzResearch.WordTrace]
  refine ⟨2458257160199042449640039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26221409708789786129493749 2458257160199042449640039)
  ·
    refine ⟨3687385740298563674460059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2458257160199042449640039 3687385740298563674460059)
    ·
      refine ⟨5531078610447845511690089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3687385740298563674460059 5531078610447845511690089)
      ·
        refine ⟨4148308957835884133767567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5531078610447845511690089 4148308957835884133767567)
        ·
          refine ⟨6222463436753826200651351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4148308957835884133767567 6222463436753826200651351)
          ·
            refine ⟨9333695155130739300977027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6222463436753826200651351 9333695155130739300977027)
            ·
              refine ⟨14000542732696108951465541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9333695155130739300977027 14000542732696108951465541)
              ·
                refine ⟨2625101762380520428399789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14000542732696108951465541 2625101762380520428399789)
                ·
                  refine ⟨984413160892695160649921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2625101762380520428399789 984413160892695160649921)
                  ·
                    refine ⟨738309870669521370487441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 984413160892695160649921 738309870669521370487441)
                    ·
                      refine ⟨553732403002141027865581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 738309870669521370487441 553732403002141027865581)
                      ·
                        rfl

theorem cell23_1078390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 4, 3, 2, 2].length) (baseStart_1078390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1078390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1078390 prefixEnd_1078390 := by exact prefixLift 1078390
  have htrace : WordTrace (prefixWord ++ tailWord_1078390) baseStart_1078390 baseEnd_1078390 := by
    simpa [prefixWord, tailWord_1078390, baseEnd_1078390] using wordTrace_append hprefix tailTrace_1078390
  have hstable : (prefixWord ++ tailWord_1078390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078390).length < 2 ^ (prefixWord ++ tailWord_1078390).sum := by decide
  have hdescent : baseEnd_1078390 < baseStart_1078390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078423 : List Nat := [1, 1, 3, 3, 3, 1, 2, 1, 4, 1, 3]
def baseStart_1078423 : Nat := 118140960795 + 1078423 * 2 ^ 59
def prefixEnd_1078423 : Nat := 4983230072969 + 3 ^ 40 * 1078423 * 2
def baseEnd_1078423 : Nat := 553749347863739398752929

theorem tailTrace_1078423 : CollatzResearch.WordTrace tailWord_1078423 prefixEnd_1078423 553749347863739398752929 := by
  unfold tailWord_1078423
  simp only [CollatzResearch.WordTrace]
  refine ⟨39333318172065125830191923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26222212114710083886794615 39333318172065125830191923)
  ·
    refine ⟨58999977258097688745287885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39333318172065125830191923 58999977258097688745287885)
    ·
      refine ⟨22124991471786633279482957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58999977258097688745287885 22124991471786633279482957)
      ·
        refine ⟨8296871801919987479806109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22124991471786633279482957 8296871801919987479806109)
        ·
          refine ⟨3111326925719995304927291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8296871801919987479806109 3111326925719995304927291)
          ·
            refine ⟨4666990388579992957390937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3111326925719995304927291 4666990388579992957390937)
            ·
              refine ⟨3500242791434994718043203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4666990388579992957390937 3500242791434994718043203)
              ·
                refine ⟨5250364187152492077064805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3500242791434994718043203 5250364187152492077064805)
                ·
                  refine ⟨984443285091092264449651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5250364187152492077064805 984443285091092264449651)
                  ·
                    refine ⟨1476664927636638396674477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 984443285091092264449651 1476664927636638396674477)
                    ·
                      refine ⟨553749347863739398752929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1476664927636638396674477 553749347863739398752929)
                      ·
                        rfl

theorem cell23_1078423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 1, 4, 1, 3].length) (baseStart_1078423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1078423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1078423 prefixEnd_1078423 := by exact prefixLift 1078423
  have htrace : WordTrace (prefixWord ++ tailWord_1078423) baseStart_1078423 baseEnd_1078423 := by
    simpa [prefixWord, tailWord_1078423, baseEnd_1078423] using wordTrace_append hprefix tailTrace_1078423
  have hstable : (prefixWord ++ tailWord_1078423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078423).length < 2 ^ (prefixWord ++ tailWord_1078423).sum := by decide
  have hdescent : baseEnd_1078423 < baseStart_1078423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078424 : List Nat := [2, 1, 2, 4, 2, 2, 3, 2, 1, 2, 2]
def baseStart_1078424 : Nat := 118140960795 + 1078424 * 2 ^ 59
def prefixEnd_1078424 : Nat := 4983230072969 + 3 ^ 40 * 1078424 * 2
def baseEnd_1078424 : Nat := 553749861344393894840425

theorem tailTrace_1078424 : CollatzResearch.WordTrace tailWord_1078424 prefixEnd_1078424 553749861344393894840425 := by
  unfold tailWord_1078424
  simp only [CollatzResearch.WordTrace]
  refine ⟨19666677322530751500489163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26222236430041002000652217 19666677322530751500489163)
  ·
    refine ⟨29500015983796127250733745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19666677322530751500489163 29500015983796127250733745)
    ·
      refine ⟨22125011987847095438050309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29500015983796127250733745 22125011987847095438050309)
      ·
        refine ⟨4148439747721330394634433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22125011987847095438050309 4148439747721330394634433)
        ·
          refine ⟨3111329810790997795975825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4148439747721330394634433 3111329810790997795975825)
          ·
            refine ⟨2333497358093248346981869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3111329810790997795975825 2333497358093248346981869)
            ·
              refine ⟨875061509284968130118201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2333497358093248346981869 875061509284968130118201)
              ·
                refine ⟨656296131963726097588651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 875061509284968130118201 656296131963726097588651)
                ·
                  refine ⟨984444197945589146382977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 656296131963726097588651 984444197945589146382977)
                  ·
                    refine ⟨738333148459191859787233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 984444197945589146382977 738333148459191859787233)
                    ·
                      refine ⟨553749861344393894840425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 738333148459191859787233 553749861344393894840425)
                      ·
                        rfl

theorem cell23_1078424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 3, 2, 1, 2, 2].length) (baseStart_1078424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1078424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1078424 prefixEnd_1078424 := by exact prefixLift 1078424
  have htrace : WordTrace (prefixWord ++ tailWord_1078424) baseStart_1078424 baseEnd_1078424 := by
    simpa [prefixWord, tailWord_1078424, baseEnd_1078424] using wordTrace_append hprefix tailTrace_1078424
  have hstable : (prefixWord ++ tailWord_1078424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078424).length < 2 ^ (prefixWord ++ tailWord_1078424).sum := by decide
  have hdescent : baseEnd_1078424 < baseStart_1078424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078433 : List Nat := [1, 2, 3, 3, 1, 1, 2, 2, 3, 3, 2]
def baseStart_1078433 : Nat := 118140960795 + 1078433 * 2 ^ 59
def prefixEnd_1078433 : Nat := 4983230072969 + 3 ^ 40 * 1078433 * 2
def baseEnd_1078433 : Nat := 553754482670284359627883

theorem tailTrace_1078433 : CollatzResearch.WordTrace tailWord_1078433 prefixEnd_1078433 553754482670284359627883 := by
  unfold tailWord_1078433
  simp only [CollatzResearch.WordTrace]
  refine ⟨39333682902028897538055953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26222455268019265025370635 39333682902028897538055953)
  ·
    refine ⟨29500262176521673153541965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39333682902028897538055953 29500262176521673153541965)
    ·
      refine ⟨11062598316195627432578237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29500262176521673153541965 11062598316195627432578237)
      ·
        refine ⟨4148474368573360287216839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11062598316195627432578237 4148474368573360287216839)
        ·
          refine ⟨6222711552860040430825259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4148474368573360287216839 6222711552860040430825259)
          ·
            refine ⟨9334067329290060646237889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6222711552860040430825259 9334067329290060646237889)
            ·
              refine ⟨7000550496967545484678417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9334067329290060646237889 7000550496967545484678417)
              ·
                refine ⟨5250412872725659113508813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7000550496967545484678417 5250412872725659113508813)
                ·
                  refine ⟨1968904827272122167565805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5250412872725659113508813 1968904827272122167565805)
                  ·
                    refine ⟨738339310227045812837177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1968904827272122167565805 738339310227045812837177)
                    ·
                      refine ⟨553754482670284359627883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 738339310227045812837177 553754482670284359627883)
                      ·
                        rfl

theorem cell23_1078433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 2, 3, 3, 2].length) (baseStart_1078433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1078433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1078433 prefixEnd_1078433 := by exact prefixLift 1078433
  have htrace : WordTrace (prefixWord ++ tailWord_1078433) baseStart_1078433 baseEnd_1078433 := by
    simpa [prefixWord, tailWord_1078433, baseEnd_1078433] using wordTrace_append hprefix tailTrace_1078433
  have hstable : (prefixWord ++ tailWord_1078433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078433).length < 2 ^ (prefixWord ++ tailWord_1078433).sum := by decide
  have hdescent : baseEnd_1078433 < baseStart_1078433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078434 : List Nat := [3, 3, 1, 3, 3, 1, 2, 1, 2, 4]
def baseStart_1078434 : Nat := 118140960795 + 1078434 * 2 ^ 59
def prefixEnd_1078434 : Nat := 4983230072969 + 3 ^ 40 * 1078434 * 2
def baseEnd_1078434 : Nat := 184584998716979618571793

theorem tailTrace_1078434 : CollatzResearch.WordTrace tailWord_1078434 prefixEnd_1078434 184584998716979618571793 := by
  unfold tailWord_1078434
  simp only [CollatzResearch.WordTrace]
  refine ⟨9833429843756318677210589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26222479583350183139228237 9833429843756318677210589)
  ·
    refine ⟨3687536191408619503953971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9833429843756318677210589 3687536191408619503953971)
    ·
      refine ⟨5531304287112929255930957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3687536191408619503953971 5531304287112929255930957)
      ·
        refine ⟨2074239107667348470974109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5531304287112929255930957 2074239107667348470974109)
        ·
          refine ⟨777839665375255676615291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2074239107667348470974109 777839665375255676615291)
          ·
            refine ⟨1166759498062883514922937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 777839665375255676615291 1166759498062883514922937)
            ·
              refine ⟨875069623547162636192203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1166759498062883514922937 875069623547162636192203)
              ·
                refine ⟨1312604435320743954288305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 875069623547162636192203 1312604435320743954288305)
                ·
                  refine ⟨984453326490557965716229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1312604435320743954288305 984453326490557965716229)
                  ·
                    refine ⟨184584998716979618571793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 984453326490557965716229 184584998716979618571793)
                    ·
                      rfl

theorem cell23_1078434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 2, 1, 2, 4].length) (baseStart_1078434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1078434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1078434 prefixEnd_1078434 := by exact prefixLift 1078434
  have htrace : WordTrace (prefixWord ++ tailWord_1078434) baseStart_1078434 baseEnd_1078434 := by
    simpa [prefixWord, tailWord_1078434, baseEnd_1078434] using wordTrace_append hprefix tailTrace_1078434
  have hstable : (prefixWord ++ tailWord_1078434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078434).length < 2 ^ (prefixWord ++ tailWord_1078434).sum := by decide
  have hdescent : baseEnd_1078434 < baseStart_1078434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078450 : List Nat := [3, 2, 1, 1, 1, 4, 3, 2, 1, 3, 2]
def baseStart_1078450 : Nat := 118140960795 + 1078450 * 2 ^ 59
def prefixEnd_1078450 : Nat := 4983230072969 + 3 ^ 40 * 1078450 * 2
def baseEnd_1078450 : Nat := 553763211841410793115305

theorem tailTrace_1078450 : CollatzResearch.WordTrace tailWord_1078450 prefixEnd_1078450 553763211841410793115305 := by
  unfold tailWord_1078450
  simp only [CollatzResearch.WordTrace]
  refine ⟨9833575735741827360356201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26222868628644872960949869 9833575735741827360356201)
  ·
    refine ⟨7375181801806370520267151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9833575735741827360356201 7375181801806370520267151)
    ·
      refine ⟨11062772702709555780400727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7375181801806370520267151 11062772702709555780400727)
      ·
        refine ⟨16594159054064333670601091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11062772702709555780400727 16594159054064333670601091)
        ·
          refine ⟨24891238581096500505901637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16594159054064333670601091 24891238581096500505901637)
          ·
            refine ⟨4667107233955593844856557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24891238581096500505901637 4667107233955593844856557)
            ·
              refine ⟨1750165212733347691821209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4667107233955593844856557 1750165212733347691821209)
              ·
                refine ⟨1312623909550010768865907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1750165212733347691821209 1312623909550010768865907)
                ·
                  refine ⟨1968935864325016153298861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1312623909550010768865907 1968935864325016153298861)
                  ·
                    refine ⟨738350949121881057487073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1968935864325016153298861 738350949121881057487073)
                    ·
                      refine ⟨553763211841410793115305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 738350949121881057487073 553763211841410793115305)
                      ·
                        rfl

theorem cell23_1078450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 2, 1, 3, 2].length) (baseStart_1078450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1078450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1078450 prefixEnd_1078450 := by exact prefixLift 1078450
  have htrace : WordTrace (prefixWord ++ tailWord_1078450) baseStart_1078450 baseEnd_1078450 := by
    simpa [prefixWord, tailWord_1078450, baseEnd_1078450] using wordTrace_append hprefix tailTrace_1078450
  have hstable : (prefixWord ++ tailWord_1078450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078450).length < 2 ^ (prefixWord ++ tailWord_1078450).sum := by decide
  have hdescent : baseEnd_1078450 < baseStart_1078450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078459 : List Nat := [1, 1, 1, 1, 1, 2, 4, 1, 3, 4, 4]
def baseStart_1078459 : Nat := 118140960795 + 1078459 * 2 ^ 59
def prefixEnd_1078459 : Nat := 4983230072969 + 3 ^ 40 * 1078459 * 2
def baseEnd_1078459 : Nat := 553767833167301257902763

theorem tailTrace_1078459 : CollatzResearch.WordTrace tailWord_1078459 prefixEnd_1078459 553767833167301257902763 := by
  unfold tailWord_1078459
  simp only [CollatzResearch.WordTrace]
  refine ⟨39334631199934703978502431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26223087466623135985668287 39334631199934703978502431)
  ·
    refine ⟨59001946799902055967753647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39334631199934703978502431 59001946799902055967753647)
    ·
      refine ⟨88502920199853083951630471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59001946799902055967753647 88502920199853083951630471)
      ·
        refine ⟨132754380299779625927445707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88502920199853083951630471 132754380299779625927445707)
        ·
          refine ⟨199131570449669438891168561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132754380299779625927445707 199131570449669438891168561)
          ·
            refine ⟨149348677837252079168376421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 199131570449669438891168561 149348677837252079168376421)
            ·
              refine ⟨28002877094484764844070579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 149348677837252079168376421 28002877094484764844070579)
              ·
                refine ⟨42004315641727147266105869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28002877094484764844070579 42004315641727147266105869)
                ·
                  refine ⟨15751618365647680224789701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42004315641727147266105869 15751618365647680224789701)
                  ·
                    refine ⟨2953428443558940042148069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15751618365647680224789701 2953428443558940042148069)
                    ·
                      refine ⟨553767833167301257902763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2953428443558940042148069 553767833167301257902763)
                      ·
                        rfl

theorem cell23_1078459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 4, 4].length) (baseStart_1078459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1078459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1078459 prefixEnd_1078459 := by exact prefixLift 1078459
  have htrace : WordTrace (prefixWord ++ tailWord_1078459) baseStart_1078459 baseEnd_1078459 := by
    simpa [prefixWord, tailWord_1078459, baseEnd_1078459] using wordTrace_append hprefix tailTrace_1078459
  have hstable : (prefixWord ++ tailWord_1078459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078459).length < 2 ^ (prefixWord ++ tailWord_1078459).sum := by decide
  have hdescent : baseEnd_1078459 < baseStart_1078459 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078463 : List Nat := [1, 1, 2, 2, 2, 2, 2, 1, 6, 2, 2]
def baseStart_1078463 : Nat := 118140960795 + 1078463 * 2 ^ 59
def prefixEnd_1078463 : Nat := 4983230072969 + 3 ^ 40 * 1078463 * 2
def baseEnd_1078463 : Nat := 553769887089919242252745

theorem tailTrace_1078463 : CollatzResearch.WordTrace tailWord_1078463 prefixEnd_1078463 553769887089919242252745 := by
  unfold tailWord_1078463
  simp only [CollatzResearch.WordTrace]
  refine ⟨39334777091920212661648043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26223184727946808441098695 39334777091920212661648043)
  ·
    refine ⟨59002165637880318992472065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39334777091920212661648043 59002165637880318992472065)
    ·
      refine ⟨44251624228410239244354049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59002165637880318992472065 44251624228410239244354049)
      ·
        refine ⟨33188718171307679433265537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44251624228410239244354049 33188718171307679433265537)
        ·
          refine ⟨24891538628480759574949153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33188718171307679433265537 24891538628480759574949153)
          ·
            refine ⟨18668653971360569681211865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24891538628480759574949153 18668653971360569681211865)
            ·
              refine ⟨14001490478520427260908899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18668653971360569681211865 14001490478520427260908899)
              ·
                refine ⟨21002235717780640891363349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14001490478520427260908899 21002235717780640891363349)
                ·
                  refine ⟨984479799270967541782657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 21002235717780640891363349 984479799270967541782657)
                  ·
                    refine ⟨738359849453225656336993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 984479799270967541782657 738359849453225656336993)
                    ·
                      refine ⟨553769887089919242252745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 738359849453225656336993 553769887089919242252745)
                      ·
                        rfl

theorem cell23_1078463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 6, 2, 2].length) (baseStart_1078463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1078463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1078463 prefixEnd_1078463 := by exact prefixLift 1078463
  have htrace : WordTrace (prefixWord ++ tailWord_1078463) baseStart_1078463 baseEnd_1078463 := by
    simpa [prefixWord, tailWord_1078463, baseEnd_1078463] using wordTrace_append hprefix tailTrace_1078463
  have hstable : (prefixWord ++ tailWord_1078463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078463).length < 2 ^ (prefixWord ++ tailWord_1078463).sum := by decide
  have hdescent : baseEnd_1078463 < baseStart_1078463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078489 : List Nat := [1, 2, 1, 2, 3, 1, 1, 1, 2, 1, 8]
def baseStart_1078489 : Nat := 118140960795 + 1078489 * 2 ^ 59
def prefixEnd_1078489 : Nat := 4983230072969 + 3 ^ 40 * 1078489 * 2
def baseEnd_1078489 : Nat := 553783237586936140527625

theorem tailTrace_1078489 : CollatzResearch.WordTrace tailWord_1078489 prefixEnd_1078489 553783237586936140527625 := by
  unfold tailWord_1078489
  simp only [CollatzResearch.WordTrace]
  refine ⟨39335725389826019102094521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26223816926550679401396347 39335725389826019102094521)
  ·
    refine ⟨29501794042369514326570891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39335725389826019102094521 29501794042369514326570891)
    ·
      refine ⟨44252691063554271489856337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29501794042369514326570891 44252691063554271489856337)
      ·
        refine ⟨33189518297665703617392253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44252691063554271489856337 33189518297665703617392253)
        ·
          refine ⟨12446069361624638856522095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33189518297665703617392253 12446069361624638856522095)
          ·
            refine ⟨18669104042436958284783143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12446069361624638856522095 18669104042436958284783143)
            ·
              refine ⟨28003656063655437427174715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18669104042436958284783143 28003656063655437427174715)
              ·
                refine ⟨42005484095483156140762073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28003656063655437427174715 42005484095483156140762073)
                ·
                  refine ⟨31504113071612367105571555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42005484095483156140762073 31504113071612367105571555)
                  ·
                    refine ⟨47256169607418550658357333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31504113071612367105571555 47256169607418550658357333)
                    ·
                      refine ⟨553783237586936140527625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 47256169607418550658357333 553783237586936140527625)
                      ·
                        rfl

theorem cell23_1078489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 1, 8].length) (baseStart_1078489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1078489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1078489 prefixEnd_1078489 := by exact prefixLift 1078489
  have htrace : WordTrace (prefixWord ++ tailWord_1078489) baseStart_1078489 baseEnd_1078489 := by
    simpa [prefixWord, tailWord_1078489, baseEnd_1078489] using wordTrace_append hprefix tailTrace_1078489
  have hstable : (prefixWord ++ tailWord_1078489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078489).length < 2 ^ (prefixWord ++ tailWord_1078489).sum := by decide
  have hdescent : baseEnd_1078489 < baseStart_1078489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078496 : List Nat := [2, 1, 1, 3, 1, 4, 1, 1, 1, 5, 3]
def baseStart_1078496 : Nat := 118140960795 + 1078496 * 2 ^ 59
def prefixEnd_1078496 : Nat := 4983230072969 + 3 ^ 40 * 1078496 * 2
def baseEnd_1078496 : Nat := 553786831951517613140093

theorem tailTrace_1078496 : CollatzResearch.WordTrace tailWord_1078496 prefixEnd_1078496 553786831951517613140093 := by
  unfold tailWord_1078496
  simp only [CollatzResearch.WordTrace]
  refine ⟨19667990350400329648799671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26223987133867106198399561 19667990350400329648799671)
  ·
    refine ⟨29501985525600494473199507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19667990350400329648799671 29501985525600494473199507)
    ·
      refine ⟨44252978288400741709799261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29501985525600494473199507 44252978288400741709799261)
      ·
        refine ⟨16594866858150278141174723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44252978288400741709799261 16594866858150278141174723)
        ·
          refine ⟨24892300287225417211762085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16594866858150278141174723 24892300287225417211762085)
          ·
            refine ⟨4667306303854765727205391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24892300287225417211762085 4667306303854765727205391)
            ·
              refine ⟨7000959455782148590808087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4667306303854765727205391 7000959455782148590808087)
              ·
                refine ⟨10501439183673222886212131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7000959455782148590808087 10501439183673222886212131)
                ·
                  refine ⟨15752158775509834329318197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10501439183673222886212131 15752158775509834329318197)
                  ·
                    refine ⟨1476764885204046968373581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15752158775509834329318197 1476764885204046968373581)
                    ·
                      refine ⟨553786831951517613140093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1476764885204046968373581 553786831951517613140093)
                      ·
                        rfl

theorem cell23_1078496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 1, 5, 3].length) (baseStart_1078496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1078496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1078496 prefixEnd_1078496 := by exact prefixLift 1078496
  have htrace : WordTrace (prefixWord ++ tailWord_1078496) baseStart_1078496 baseEnd_1078496 := by
    simpa [prefixWord, tailWord_1078496, baseEnd_1078496] using wordTrace_append hprefix tailTrace_1078496
  have hstable : (prefixWord ++ tailWord_1078496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078496).length < 2 ^ (prefixWord ++ tailWord_1078496).sum := by decide
  have hdescent : baseEnd_1078496 < baseStart_1078496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078503 : List Nat := [1, 1, 5, 3, 2, 1, 1, 2, 7]
def baseStart_1078503 : Nat := 118140960795 + 1078503 * 2 ^ 59
def prefixEnd_1078503 : Nat := 4983230072969 + 3 ^ 40 * 1078503 * 2
def baseEnd_1078503 : Nat := 61532269590677676194729

theorem tailTrace_1078503 : CollatzResearch.WordTrace tailWord_1078503 prefixEnd_1078503 61532269590677676194729 := by
  unfold tailWord_1078503
  simp only [CollatzResearch.WordTrace]
  refine ⟨39336236011775299493104163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26224157341183532995402775 39336236011775299493104163)
  ·
    refine ⟨59004354017662949239656245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39336236011775299493104163 59004354017662949239656245)
    ·
      refine ⟨5531658189155901491217773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 59004354017662949239656245 5531658189155901491217773)
      ·
        refine ⟨2074371820933463059206665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5531658189155901491217773 2074371820933463059206665)
        ·
          refine ⟨1555778865700097294404999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2074371820933463059206665 1555778865700097294404999)
          ·
            refine ⟨2333668298550145941607499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1555778865700097294404999 2333668298550145941607499)
            ·
              refine ⟨3500502447825218912411249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2333668298550145941607499 3500502447825218912411249)
              ·
                refine ⟨2625376835868914184308437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3500502447825218912411249 2625376835868914184308437)
                ·
                  refine ⟨61532269590677676194729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2625376835868914184308437 61532269590677676194729)
                  ·
                    rfl

theorem cell23_1078503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 2, 7].length) (baseStart_1078503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1078503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1078503 prefixEnd_1078503 := by exact prefixLift 1078503
  have htrace : WordTrace (prefixWord ++ tailWord_1078503) baseStart_1078503 baseEnd_1078503 := by
    simpa [prefixWord, tailWord_1078503, baseEnd_1078503] using wordTrace_append hprefix tailTrace_1078503
  have hstable : (prefixWord ++ tailWord_1078503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078503).length < 2 ^ (prefixWord ++ tailWord_1078503).sum := by decide
  have hdescent : baseEnd_1078503 < baseStart_1078503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078563 : List Nat := [1, 1, 1, 4, 2, 3, 2, 2, 3, 4]
def baseStart_1078563 : Nat := 118140960795 + 1078563 * 2 ^ 59
def prefixEnd_1078563 : Nat := 4983230072969 + 3 ^ 40 * 1078563 * 2
def baseEnd_1078563 : Nat := 184607078385122950334095

theorem tailTrace_1078563 : CollatzResearch.WordTrace tailWord_1078563 prefixEnd_1078563 184607078385122950334095 := by
  unfold tailWord_1078563
  simp only [CollatzResearch.WordTrace]
  refine ⟨39338424391557929740288343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26225616261038619826858895 39338424391557929740288343)
  ·
    refine ⟨59007636587336894610432515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39338424391557929740288343 59007636587336894610432515)
    ·
      refine ⟨88511454881005341915648773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59007636587336894610432515 88511454881005341915648773)
      ·
        refine ⟨16595897790188501609184145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 88511454881005341915648773 16595897790188501609184145)
        ·
          refine ⟨12446923342641376206888109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16595897790188501609184145 12446923342641376206888109)
          ·
            refine ⟨4667596253490516077583041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12446923342641376206888109 4667596253490516077583041)
            ·
              refine ⟨3500697190117887058187281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4667596253490516077583041 3500697190117887058187281)
              ·
                refine ⟨2625522892588415293640461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3500697190117887058187281 2625522892588415293640461)
                ·
                  refine ⟨984571084720655735115173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2625522892588415293640461 984571084720655735115173)
                  ·
                    refine ⟨184607078385122950334095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 984571084720655735115173 184607078385122950334095)
                    ·
                      rfl

theorem cell23_1078563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 2, 3, 4].length) (baseStart_1078563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1078563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1078563 prefixEnd_1078563 := by exact prefixLift 1078563
  have htrace : WordTrace (prefixWord ++ tailWord_1078563) baseStart_1078563 baseEnd_1078563 := by
    simpa [prefixWord, tailWord_1078563, baseEnd_1078563] using wordTrace_append hprefix tailTrace_1078563
  have hstable : (prefixWord ++ tailWord_1078563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078563).length < 2 ^ (prefixWord ++ tailWord_1078563).sum := by decide
  have hdescent : baseEnd_1078563 < baseStart_1078563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078590 : List Nat := [4, 2, 1, 2, 1, 1, 3, 2, 2, 2, 3]
def baseStart_1078590 : Nat := 118140960795 + 1078590 * 2 ^ 59
def prefixEnd_1078590 : Nat := 4983230072969 + 3 ^ 40 * 1078590 * 2
def baseEnd_1078590 : Nat := 553835099133040245364661

theorem tailTrace_1078590 : CollatzResearch.WordTrace tailWord_1078590 prefixEnd_1078590 553835099133040245364661 := by
  unfold tailWord_1078590
  simp only [CollatzResearch.WordTrace]
  refine ⟨4917426145307514168940153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26226272774973408901014149 4917426145307514168940153)
  ·
    refine ⟨3688069608980635626705115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4917426145307514168940153 3688069608980635626705115)
    ·
      refine ⟨5532104413470953440057673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3688069608980635626705115 5532104413470953440057673)
      ·
        refine ⟨4149078310103215080043255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5532104413470953440057673 4149078310103215080043255)
        ·
          refine ⟨6223617465154822620064883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4149078310103215080043255 6223617465154822620064883)
          ·
            refine ⟨9335426197732233930097325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6223617465154822620064883 9335426197732233930097325)
            ·
              refine ⟨3500784824149587723786497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9335426197732233930097325 3500784824149587723786497)
              ·
                refine ⟨2625588618112190792839873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3500784824149587723786497 2625588618112190792839873)
                ·
                  refine ⟨1969191463584143094629905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2625588618112190792839873 1969191463584143094629905)
                  ·
                    refine ⟨1476893597688107320972429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1969191463584143094629905 1476893597688107320972429)
                    ·
                      refine ⟨553835099133040245364661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1476893597688107320972429 553835099133040245364661)
                      ·
                        rfl

theorem cell23_1078590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_1078590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1078590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1078590 prefixEnd_1078590 := by exact prefixLift 1078590
  have htrace : WordTrace (prefixWord ++ tailWord_1078590) baseStart_1078590 baseEnd_1078590 := by
    simpa [prefixWord, tailWord_1078590, baseEnd_1078590] using wordTrace_append hprefix tailTrace_1078590
  have hstable : (prefixWord ++ tailWord_1078590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078590).length < 2 ^ (prefixWord ++ tailWord_1078590).sum := by decide
  have hdescent : baseEnd_1078590 < baseStart_1078590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078593 : List Nat := [1, 2, 5, 2, 1, 1, 2, 1, 8]
def baseStart_1078593 : Nat := 118140960795 + 1078593 * 2 ^ 59
def prefixEnd_1078593 : Nat := 4983230072969 + 3 ^ 40 * 1078593 * 2
def baseEnd_1078593 : Nat := 61537404397222637069683

theorem tailTrace_1078593 : CollatzResearch.WordTrace tailWord_1078593 prefixEnd_1078593 61537404397222637069683 := by
  unfold tailWord_1078593
  simp only [CollatzResearch.WordTrace]
  refine ⟨39339518581449244863880433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26226345720966163242586955 39339518581449244863880433)
  ·
    refine ⟨29504638936086933647910325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39339518581449244863880433 29504638936086933647910325)
    ·
      refine ⟨2766059900258150029491593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29504638936086933647910325 2766059900258150029491593)
      ·
        refine ⟨2074544925193612522118695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2766059900258150029491593 2074544925193612522118695)
        ·
          refine ⟨3111817387790418783178043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2074544925193612522118695 3111817387790418783178043)
          ·
            refine ⟨4667726081685628174767065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3111817387790418783178043 4667726081685628174767065)
            ·
              refine ⟨3500794561264221131075299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4667726081685628174767065 3500794561264221131075299)
              ·
                refine ⟨5251191841896331696612949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3500794561264221131075299 5251191841896331696612949)
                ·
                  refine ⟨61537404397222637069683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5251191841896331696612949 61537404397222637069683)
                  ·
                    rfl

theorem cell23_1078593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 1, 8].length) (baseStart_1078593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1078593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1078593 prefixEnd_1078593 := by exact prefixLift 1078593
  have htrace : WordTrace (prefixWord ++ tailWord_1078593) baseStart_1078593 baseEnd_1078593 := by
    simpa [prefixWord, tailWord_1078593, baseEnd_1078593] using wordTrace_append hprefix tailTrace_1078593
  have hstable : (prefixWord ++ tailWord_1078593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078593).length < 2 ^ (prefixWord ++ tailWord_1078593).sum := by decide
  have hdescent : baseEnd_1078593 < baseStart_1078593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078640 : List Nat := [2, 1, 1, 1, 4, 2, 5, 1, 1, 5]
def baseStart_1078640 : Nat := 118140960795 + 1078640 * 2 ^ 59
def prefixEnd_1078640 : Nat := 4983230072969 + 3 ^ 40 * 1078640 * 2
def baseEnd_1078640 : Nat := 184620257721921683246477

theorem tailTrace_1078640 : CollatzResearch.WordTrace tailWord_1078640 prefixEnd_1078640 184620257721921683246477 := by
  unfold tailWord_1078640
  simp only [CollatzResearch.WordTrace]
  refine ⟨19670616406139485945420687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26227488541519314593894249 19670616406139485945420687)
  ·
    refine ⟨29505924609209228918131031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19670616406139485945420687 29505924609209228918131031)
    ·
      refine ⟨44258886913813843377196547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29505924609209228918131031 44258886913813843377196547)
      ·
        refine ⟨66388330370720765065794821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44258886913813843377196547 66388330370720765065794821)
        ·
          refine ⟨12447811944510143449836529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66388330370720765065794821 12447811944510143449836529)
          ·
            refine ⟨9335858958382607587377397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12447811944510143449836529 9335858958382607587377397)
            ·
              refine ⟨875236777348369461316631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9335858958382607587377397 875236777348369461316631)
              ·
                refine ⟨1312855166022554191974947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 875236777348369461316631 1312855166022554191974947)
                ·
                  refine ⟨1969282749033831287962421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1312855166022554191974947 1969282749033831287962421)
                  ·
                    refine ⟨184620257721921683246477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1969282749033831287962421 184620257721921683246477)
                    ·
                      rfl

theorem cell23_1078640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 5, 1, 1, 5].length) (baseStart_1078640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1078640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1078640 prefixEnd_1078640 := by exact prefixLift 1078640
  have htrace : WordTrace (prefixWord ++ tailWord_1078640) baseStart_1078640 baseEnd_1078640 := by
    simpa [prefixWord, tailWord_1078640, baseEnd_1078640] using wordTrace_append hprefix tailTrace_1078640
  have hstable : (prefixWord ++ tailWord_1078640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078640).length < 2 ^ (prefixWord ++ tailWord_1078640).sum := by decide
  have hdescent : baseEnd_1078640 < baseStart_1078640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078656 : List Nat := [2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 6]
def baseStart_1078656 : Nat := 118140960795 + 1078656 * 2 ^ 59
def prefixEnd_1078656 : Nat := 4983230072969 + 3 ^ 40 * 1078656 * 2
def baseEnd_1078656 : Nat := 553868988856236987139357

theorem tailTrace_1078656 : CollatzResearch.WordTrace tailWord_1078656 prefixEnd_1078656 553868988856236987139357 := by
  unfold tailWord_1078656
  simp only [CollatzResearch.WordTrace]
  refine ⟨19670908190110503311711911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26227877586814004415615881 19670908190110503311711911)
  ·
    refine ⟨29506362285165754967567867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19670908190110503311711911 29506362285165754967567867)
    ·
      refine ⟨44259543427748632451351801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29506362285165754967567867 44259543427748632451351801)
      ·
        refine ⟨33194657570811474338513851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44259543427748632451351801 33194657570811474338513851)
        ·
          refine ⟨49791986356217211507770777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33194657570811474338513851 49791986356217211507770777)
          ·
            refine ⟨37343989767162908630828083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49791986356217211507770777 37343989767162908630828083)
            ·
              refine ⟨56015984650744362946242125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37343989767162908630828083 56015984650744362946242125)
              ·
                refine ⟨21005994244029136104840797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56015984650744362946242125 21005994244029136104840797)
                ·
                  refine ⟨7877247841510926039315299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21005994244029136104840797 7877247841510926039315299)
                  ·
                    refine ⟨11815871762266389058972949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7877247841510926039315299 11815871762266389058972949)
                    ·
                      refine ⟨553868988856236987139357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11815871762266389058972949 553868988856236987139357)
                      ·
                        rfl

theorem cell23_1078656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 6].length) (baseStart_1078656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1078656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1078656 prefixEnd_1078656 := by exact prefixLift 1078656
  have htrace : WordTrace (prefixWord ++ tailWord_1078656) baseStart_1078656 baseEnd_1078656 := by
    simpa [prefixWord, tailWord_1078656, baseEnd_1078656] using wordTrace_append hprefix tailTrace_1078656
  have hstable : (prefixWord ++ tailWord_1078656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078656).length < 2 ^ (prefixWord ++ tailWord_1078656).sum := by decide
  have hdescent : baseEnd_1078656 < baseStart_1078656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078690 : List Nat := [3, 3, 1, 2, 1, 2, 2, 2, 1, 2, 4]
def baseStart_1078690 : Nat := 118140960795 + 1078690 * 2 ^ 59
def prefixEnd_1078690 : Nat := 4983230072969 + 3 ^ 40 * 1078690 * 2
def baseEnd_1078690 : Nat := 553886447198489854114201

theorem tailTrace_1078690 : CollatzResearch.WordTrace tailWord_1078690 prefixEnd_1078690 553886447198489854114201 := by
  unfold tailWord_1078690
  simp only [CollatzResearch.WordTrace]
  refine ⟨9835764115524457607540381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26228704308065220286774349 9835764115524457607540381)
  ·
    refine ⟨3688411543321671602827643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9835764115524457607540381 3688411543321671602827643)
    ·
      refine ⟨5532617314982507404241465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3688411543321671602827643 5532617314982507404241465)
      ·
        refine ⟨4149462986236880553181099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5532617314982507404241465 4149462986236880553181099)
        ·
          refine ⟨6224194479355320829771649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4149462986236880553181099 6224194479355320829771649)
          ·
            refine ⟨4668145859516490622328737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6224194479355320829771649 4668145859516490622328737)
            ·
              refine ⟨3501109394637367966746553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4668145859516490622328737 3501109394637367966746553)
              ·
                refine ⟨2625832045978025975059915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3501109394637367966746553 2625832045978025975059915)
                ·
                  refine ⟨3938748068967038962589873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2625832045978025975059915 3938748068967038962589873)
                  ·
                    refine ⟨2954061051725279221942405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3938748068967038962589873 2954061051725279221942405)
                    ·
                      refine ⟨553886447198489854114201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2954061051725279221942405 553886447198489854114201)
                      ·
                        rfl

theorem cell23_1078690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_1078690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1078690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1078690 prefixEnd_1078690 := by exact prefixLift 1078690
  have htrace : WordTrace (prefixWord ++ tailWord_1078690) baseStart_1078690 baseEnd_1078690 := by
    simpa [prefixWord, tailWord_1078690, baseEnd_1078690] using wordTrace_append hprefix tailTrace_1078690
  have hstable : (prefixWord ++ tailWord_1078690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078690).length < 2 ^ (prefixWord ++ tailWord_1078690).sum := by decide
  have hdescent : baseEnd_1078690 < baseStart_1078690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078693 : List Nat := [1, 3, 1, 2, 1, 1, 2, 3, 3, 3, 3]
def baseStart_1078693 : Nat := 118140960795 + 1078693 * 2 ^ 59
def prefixEnd_1078693 : Nat := 4983230072969 + 3 ^ 40 * 1078693 * 2
def baseEnd_1078693 : Nat := 553887987640453342376687

theorem tailTrace_1078693 : CollatzResearch.WordTrace tailWord_1078693 prefixEnd_1078693 553887987640453342376687 := by
  unfold tailWord_1078693
  simp only [CollatzResearch.WordTrace]
  refine ⟨39343165881086961942520733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26228777254057974628347155 39343165881086961942520733)
  ·
    refine ⟨14753687205407610728445275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39343165881086961942520733 14753687205407610728445275)
    ·
      refine ⟨22130530808111416092667913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14753687205407610728445275 22130530808111416092667913)
      ·
        refine ⟨16597898106083562069500935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22130530808111416092667913 16597898106083562069500935)
        ·
          refine ⟨24896847159125343104251403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16597898106083562069500935 24896847159125343104251403)
          ·
            refine ⟨37345270738688014656377105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24896847159125343104251403 37345270738688014656377105)
            ·
              refine ⟨28008953054016010992282829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37345270738688014656377105 28008953054016010992282829)
              ·
                refine ⟨10503357395256004122106061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28008953054016010992282829 10503357395256004122106061)
                ·
                  refine ⟨3938759023221001545789773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10503357395256004122106061 3938759023221001545789773)
                  ·
                    refine ⟨1477034633707875579671165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3938759023221001545789773 1477034633707875579671165)
                    ·
                      refine ⟨553887987640453342376687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1477034633707875579671165 553887987640453342376687)
                      ·
                        rfl

theorem cell23_1078693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 3, 3, 3].length) (baseStart_1078693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1078693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1078693 prefixEnd_1078693 := by exact prefixLift 1078693
  have htrace : WordTrace (prefixWord ++ tailWord_1078693) baseStart_1078693 baseEnd_1078693 := by
    simpa [prefixWord, tailWord_1078693, baseEnd_1078693] using wordTrace_append hprefix tailTrace_1078693
  have hstable : (prefixWord ++ tailWord_1078693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078693).length < 2 ^ (prefixWord ++ tailWord_1078693).sum := by decide
  have hdescent : baseEnd_1078693 < baseStart_1078693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078720 : List Nat := [2, 1, 1, 2, 3, 1, 2, 1, 5, 3, 2]
def baseStart_1078720 : Nat := 118140960795 + 1078720 * 2 ^ 59
def prefixEnd_1078720 : Nat := 4983230072969 + 3 ^ 40 * 1078720 * 2
def baseEnd_1078720 : Nat := 553901851618124736739063

theorem tailTrace_1078720 : CollatzResearch.WordTrace tailWord_1078720 prefixEnd_1078720 553901851618124736739063 := by
  unfold tailWord_1078720
  simp only [CollatzResearch.WordTrace]
  refine ⟨19672075325994572776876807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26229433767992763702502409 19672075325994572776876807)
  ·
    refine ⟨29508112988991859165315211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19672075325994572776876807 29508112988991859165315211)
    ·
      refine ⟨44262169483487788747972817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29508112988991859165315211 44262169483487788747972817)
      ·
        refine ⟨33196627112615841560979613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44262169483487788747972817 33196627112615841560979613)
        ·
          refine ⟨12448735167230940585367355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33196627112615841560979613 12448735167230940585367355)
          ·
            refine ⟨18673102750846410878051033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12448735167230940585367355 18673102750846410878051033)
            ·
              refine ⟨14004827063134808158538275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18673102750846410878051033 14004827063134808158538275)
              ·
                refine ⟨21007240594702212237807413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14004827063134808158538275 21007240594702212237807413)
                ·
                  refine ⟨1969428805753332397294445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21007240594702212237807413 1969428805753332397294445)
                  ·
                    refine ⟨738535802157499648985417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1969428805753332397294445 738535802157499648985417)
                    ·
                      refine ⟨553901851618124736739063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 738535802157499648985417 553901851618124736739063)
                      ·
                        rfl

theorem cell23_1078720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 5, 3, 2].length) (baseStart_1078720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1078720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1078720 prefixEnd_1078720 := by exact prefixLift 1078720
  have htrace : WordTrace (prefixWord ++ tailWord_1078720) baseStart_1078720 baseEnd_1078720 := by
    simpa [prefixWord, tailWord_1078720, baseEnd_1078720] using wordTrace_append hprefix tailTrace_1078720
  have hstable : (prefixWord ++ tailWord_1078720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078720).length < 2 ^ (prefixWord ++ tailWord_1078720).sum := by decide
  have hdescent : baseEnd_1078720 < baseStart_1078720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078753 : List Nat := [1, 2, 3, 1, 2, 3, 1, 1, 1, 3, 5]
def baseStart_1078753 : Nat := 118140960795 + 1078753 * 2 ^ 59
def prefixEnd_1078753 : Nat := 4983230072969 + 3 ^ 40 * 1078753 * 2
def baseEnd_1078753 : Nat := 553918796479723107626411

theorem tailTrace_1078753 : CollatzResearch.WordTrace tailWord_1078753 prefixEnd_1078753 553918796479723107626411 := by
  unfold tailWord_1078753
  simp only [CollatzResearch.WordTrace]
  refine ⟨39345354260869592189704913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26230236173913061459803275 39345354260869592189704913)
  ·
    refine ⟨29509015695652194142278685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39345354260869592189704913 29509015695652194142278685)
    ·
      refine ⟨11065880885869572803354507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29509015695652194142278685 11065880885869572803354507)
      ·
        refine ⟨16598821328804359205031761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11065880885869572803354507 16598821328804359205031761)
        ·
          refine ⟨12449115996603269403773821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16598821328804359205031761 12449115996603269403773821)
          ·
            refine ⟨4668418498726226026415183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12449115996603269403773821 4668418498726226026415183)
            ·
              refine ⟨7002627748089339039622775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4668418498726226026415183 7002627748089339039622775)
              ·
                refine ⟨10503941622134008559434163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7002627748089339039622775 10503941622134008559434163)
                ·
                  refine ⟨15755912433201012839151245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10503941622134008559434163 15755912433201012839151245)
                  ·
                    refine ⟨5908467162450379814681717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15755912433201012839151245 5908467162450379814681717)
                    ·
                      refine ⟨553918796479723107626411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5908467162450379814681717 553918796479723107626411)
                      ·
                        rfl

theorem cell23_1078753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 3, 5].length) (baseStart_1078753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1078753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1078753 prefixEnd_1078753 := by exact prefixLift 1078753
  have htrace : WordTrace (prefixWord ++ tailWord_1078753) baseStart_1078753 baseEnd_1078753 := by
    simpa [prefixWord, tailWord_1078753, baseEnd_1078753] using wordTrace_append hprefix tailTrace_1078753
  have hstable : (prefixWord ++ tailWord_1078753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078753).length < 2 ^ (prefixWord ++ tailWord_1078753).sum := by decide
  have hdescent : baseEnd_1078753 < baseStart_1078753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078763 : List Nat := [1, 1, 1, 1, 2, 3, 2, 4, 2, 2, 4]
def baseStart_1078763 : Nat := 118140960795 + 1078763 * 2 ^ 59
def prefixEnd_1078763 : Nat := 4983230072969 + 3 ^ 40 * 1078763 * 2
def baseEnd_1078763 : Nat := 553923931286268068501365

theorem tailTrace_1078763 : CollatzResearch.WordTrace tailWord_1078763 prefixEnd_1078763 553923931286268068501365 := by
  unfold tailWord_1078763
  simp only [CollatzResearch.WordTrace]
  refine ⟨39345718990833363897568943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26230479327222242598379295 39345718990833363897568943)
  ·
    refine ⟨59018578486250045846353415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39345718990833363897568943 59018578486250045846353415)
    ·
      refine ⟨88527867729375068769530123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59018578486250045846353415 88527867729375068769530123)
      ·
        refine ⟨132791801594062603154295185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88527867729375068769530123 132791801594062603154295185)
        ·
          refine ⟨99593851195546952365721389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132791801594062603154295185 99593851195546952365721389)
          ·
            refine ⟨37347694198330107137145521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99593851195546952365721389 37347694198330107137145521)
            ·
              refine ⟨28010770648747580352859141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37347694198330107137145521 28010770648747580352859141)
              ·
                refine ⟨5252019496640171316161089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28010770648747580352859141 5252019496640171316161089)
                ·
                  refine ⟨3939014622480128487120817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5252019496640171316161089 3939014622480128487120817)
                  ·
                    refine ⟨2954260966860096365340613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3939014622480128487120817 2954260966860096365340613)
                    ·
                      refine ⟨553923931286268068501365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2954260966860096365340613 553923931286268068501365)
                      ·
                        rfl

theorem cell23_1078763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 4, 2, 2, 4].length) (baseStart_1078763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1078763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1078763 prefixEnd_1078763 := by exact prefixLift 1078763
  have htrace : WordTrace (prefixWord ++ tailWord_1078763) baseStart_1078763 baseEnd_1078763 := by
    simpa [prefixWord, tailWord_1078763, baseEnd_1078763] using wordTrace_append hprefix tailTrace_1078763
  have hstable : (prefixWord ++ tailWord_1078763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078763).length < 2 ^ (prefixWord ++ tailWord_1078763).sum := by decide
  have hdescent : baseEnd_1078763 < baseStart_1078763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078767 : List Nat := [1, 1, 2, 1, 4, 1, 4, 1, 4, 2, 2]
def baseStart_1078767 : Nat := 118140960795 + 1078767 * 2 ^ 59
def prefixEnd_1078767 : Nat := 4983230072969 + 3 ^ 40 * 1078767 * 2
def baseEnd_1078767 : Nat := 553925985208886052851347

theorem tailTrace_1078767 : CollatzResearch.WordTrace tailWord_1078767 prefixEnd_1078767 553925985208886052851347 := by
  unfold tailWord_1078767
  simp only [CollatzResearch.WordTrace]
  refine ⟨39345864882818872580714555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26230576588545915053809703 39345864882818872580714555)
  ·
    refine ⟨59018797324228308871071833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39345864882818872580714555 59018797324228308871071833)
    ·
      refine ⟨44264097993171231653303875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59018797324228308871071833 44264097993171231653303875)
      ·
        refine ⟨66396146989756847479955813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44264097993171231653303875 66396146989756847479955813)
        ·
          refine ⟨12449277560579408902491715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66396146989756847479955813 12449277560579408902491715)
          ·
            refine ⟨18673916340869113353737573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12449277560579408902491715 18673916340869113353737573)
            ·
              refine ⟨3501359313912958753825795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18673916340869113353737573 3501359313912958753825795)
              ·
                refine ⟨5252038970869438130738693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3501359313912958753825795 5252038970869438130738693)
                ·
                  refine ⟨984757307038019649513505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5252038970869438130738693 984757307038019649513505)
                  ·
                    refine ⟨738567980278514737135129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 984757307038019649513505 738567980278514737135129)
                    ·
                      refine ⟨553925985208886052851347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 738567980278514737135129 553925985208886052851347)
                      ·
                        rfl

theorem cell23_1078767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 1, 4, 2, 2].length) (baseStart_1078767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1078767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1078767 prefixEnd_1078767 := by exact prefixLift 1078767
  have htrace : WordTrace (prefixWord ++ tailWord_1078767) baseStart_1078767 baseEnd_1078767 := by
    simpa [prefixWord, tailWord_1078767, baseEnd_1078767] using wordTrace_append hprefix tailTrace_1078767
  have hstable : (prefixWord ++ tailWord_1078767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078767).length < 2 ^ (prefixWord ++ tailWord_1078767).sum := by decide
  have hdescent : baseEnd_1078767 < baseStart_1078767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078788 : List Nat := [2, 3, 2, 3, 3, 1, 1, 2, 1, 3, 2]
def baseStart_1078788 : Nat := 118140960795 + 1078788 * 2 ^ 59
def prefixEnd_1078788 : Nat := 4983230072969 + 3 ^ 40 * 1078788 * 2
def baseEnd_1078788 : Nat := 553936768302630470688751

theorem tailTrace_1078788 : CollatzResearch.WordTrace tailWord_1078788 prefixEnd_1078788 553936768302630470688751 := by
  unfold tailWord_1078788
  simp only [CollatzResearch.WordTrace]
  refine ⟨19673315407871396583614509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26231087210495195444819345 19673315407871396583614509)
  ·
    refine ⟨7377493277951773718855441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19673315407871396583614509 7377493277951773718855441)
    ·
      refine ⟨5533119958463830289141581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7377493277951773718855441 5533119958463830289141581)
      ·
        refine ⟨2074919984423936358428093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5533119958463830289141581 2074919984423936358428093)
        ·
          refine ⟨778094994158976134410535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2074919984423936358428093 778094994158976134410535)
          ·
            refine ⟨1167142491238464201615803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 778094994158976134410535 1167142491238464201615803)
            ·
              refine ⟨1750713736857696302423705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1167142491238464201615803 1750713736857696302423705)
              ·
                refine ⟨1313035302643272226817779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1750713736857696302423705 1313035302643272226817779)
                ·
                  refine ⟨1969552953964908340226669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1313035302643272226817779 1969552953964908340226669)
                  ·
                    refine ⟨738582357736840627585001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1969552953964908340226669 738582357736840627585001)
                    ·
                      refine ⟨553936768302630470688751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 738582357736840627585001 553936768302630470688751)
                      ·
                        rfl

theorem cell23_1078788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_1078788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1078788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1078788 prefixEnd_1078788 := by exact prefixLift 1078788
  have htrace : WordTrace (prefixWord ++ tailWord_1078788) baseStart_1078788 baseEnd_1078788 := by
    simpa [prefixWord, tailWord_1078788, baseEnd_1078788] using wordTrace_append hprefix tailTrace_1078788
  have hstable : (prefixWord ++ tailWord_1078788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078788).length < 2 ^ (prefixWord ++ tailWord_1078788).sum := by decide
  have hdescent : baseEnd_1078788 < baseStart_1078788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078824 : List Nat := [2, 1, 5, 2, 2, 1, 1, 4, 5]
def baseStart_1078824 : Nat := 118140960795 + 1078824 * 2 ^ 59
def prefixEnd_1078824 : Nat := 4983230072969 + 3 ^ 40 * 1078824 * 2
def baseEnd_1078824 : Nat := 61550583734021369982065

theorem tailTrace_1078824 : CollatzResearch.WordTrace tailWord_1078824 prefixEnd_1078824 61550583734021369982065 := by
  unfold tailWord_1078824
  simp only [CollatzResearch.WordTrace]
  refine ⟨19673971921806185657769763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26231962562408247543693017 19673971921806185657769763)
  ·
    refine ⟨29510957882709278486654645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19673971921806185657769763 29510957882709278486654645)
    ·
      refine ⟨2766652301503994858123873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29510957882709278486654645 2766652301503994858123873)
      ·
        refine ⟨2074989226127996143592905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2766652301503994858123873 2074989226127996143592905)
        ·
          refine ⟨1556241919595997107694679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2074989226127996143592905 1556241919595997107694679)
          ·
            refine ⟨2334362879393995661542019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1556241919595997107694679 2334362879393995661542019)
            ·
              refine ⟨3501544319090993492313029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2334362879393995661542019 3501544319090993492313029)
              ·
                refine ⟨656539559829561279808693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3501544319090993492313029 656539559829561279808693)
                ·
                  refine ⟨61550583734021369982065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 656539559829561279808693 61550583734021369982065)
                  ·
                    rfl

theorem cell23_1078824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 4, 5].length) (baseStart_1078824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1078824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1078824 prefixEnd_1078824 := by exact prefixLift 1078824
  have htrace : WordTrace (prefixWord ++ tailWord_1078824) baseStart_1078824 baseEnd_1078824 := by
    simpa [prefixWord, tailWord_1078824, baseEnd_1078824] using wordTrace_append hprefix tailTrace_1078824
  have hstable : (prefixWord ++ tailWord_1078824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078824).length < 2 ^ (prefixWord ++ tailWord_1078824).sum := by decide
  have hdescent : baseEnd_1078824 < baseStart_1078824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078833 : List Nat := [1, 2, 2, 3, 1, 1, 1, 2, 2, 8]
def baseStart_1078833 : Nat := 118140960795 + 1078833 * 2 ^ 59
def prefixEnd_1078833 : Nat := 4983230072969 + 3 ^ 40 * 1078833 * 2
def baseEnd_1078833 : Nat := 184653291644027598208681

theorem tailTrace_1078833 : CollatzResearch.WordTrace tailWord_1078833 prefixEnd_1078833 184653291644027598208681 := by
  unfold tailWord_1078833
  simp only [CollatzResearch.WordTrace]
  refine ⟨39348272100579765852617153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26232181400386510568411435 39348272100579765852617153)
  ·
    refine ⟨29511204075434824389462865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39348272100579765852617153 29511204075434824389462865)
    ·
      refine ⟨22133403056576118292097149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29511204075434824389462865 22133403056576118292097149)
      ·
        refine ⟨8300026146216044359536431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22133403056576118292097149 8300026146216044359536431)
        ·
          refine ⟨12450039219324066539304647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8300026146216044359536431 12450039219324066539304647)
          ·
            refine ⟨18675058828986099808956971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12450039219324066539304647 18675058828986099808956971)
            ·
              refine ⟨28012588243479149713435457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18675058828986099808956971 28012588243479149713435457)
              ·
                refine ⟨21009441182609362285076593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28012588243479149713435457 21009441182609362285076593)
                ·
                  refine ⟨15757080886957021713807445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21009441182609362285076593 15757080886957021713807445)
                  ·
                    refine ⟨184653291644027598208681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 15757080886957021713807445 184653291644027598208681)
                    ·
                      rfl

theorem cell23_1078833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 8].length) (baseStart_1078833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1078833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1078833 prefixEnd_1078833 := by exact prefixLift 1078833
  have htrace : WordTrace (prefixWord ++ tailWord_1078833) baseStart_1078833 baseEnd_1078833 := by
    simpa [prefixWord, tailWord_1078833, baseEnd_1078833] using wordTrace_append hprefix tailTrace_1078833
  have hstable : (prefixWord ++ tailWord_1078833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078833).length < 2 ^ (prefixWord ++ tailWord_1078833).sum := by decide
  have hdescent : baseEnd_1078833 < baseStart_1078833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078854 : List Nat := [6, 1, 1, 1, 3, 1, 1, 1, 1, 7]
def baseStart_1078854 : Nat := 118140960795 + 1078854 * 2 ^ 59
def prefixEnd_1078854 : Nat := 4983230072969 + 3 ^ 40 * 1078854 * 2
def baseEnd_1078854 : Nat := 184656886008609070821149

theorem tailTrace_1078854 : CollatzResearch.WordTrace tailWord_1078854 prefixEnd_1078854 184656886008609070821149 := by
  unfold tailWord_1078854
  simp only [CollatzResearch.WordTrace]
  refine ⟨1229657438546990201222863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 26232692022335790959421077 1229657438546990201222863)
  ·
    refine ⟨1844486157820485301834295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1229657438546990201222863 1844486157820485301834295)
    ·
      refine ⟨2766729236730727952751443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1844486157820485301834295 2766729236730727952751443)
      ·
        refine ⟨4150093855096091929127165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2766729236730727952751443 4150093855096091929127165)
        ·
          refine ⟨1556285195661034473422687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4150093855096091929127165 1556285195661034473422687)
          ·
            refine ⟨2334427793491551710134031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1556285195661034473422687 2334427793491551710134031)
            ·
              refine ⟨3501641690237327565201047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2334427793491551710134031 3501641690237327565201047)
              ·
                refine ⟨5252462535355991347801571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3501641690237327565201047 5252462535355991347801571)
                ·
                  refine ⟨7878693803033987021702357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5252462535355991347801571 7878693803033987021702357)
                  ·
                    refine ⟨184656886008609070821149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7878693803033987021702357 184656886008609070821149)
                    ·
                      rfl

theorem cell23_1078854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_1078854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1078854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1078854 prefixEnd_1078854 := by exact prefixLift 1078854
  have htrace : WordTrace (prefixWord ++ tailWord_1078854) baseStart_1078854 baseEnd_1078854 := by
    simpa [prefixWord, tailWord_1078854, baseEnd_1078854] using wordTrace_append hprefix tailTrace_1078854
  have hstable : (prefixWord ++ tailWord_1078854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078854).length < 2 ^ (prefixWord ++ tailWord_1078854).sum := by decide
  have hdescent : baseEnd_1078854 < baseStart_1078854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078863 : List Nat := [1, 1, 2, 1, 1, 2, 3, 4, 8]
def baseStart_1078863 : Nat := 118140960795 + 1078863 * 2 ^ 59
def prefixEnd_1078863 : Nat := 4983230072969 + 3 ^ 40 * 1078863 * 2
def baseEnd_1078863 : Nat := 61552808816857519694545

theorem tailTrace_1078863 : CollatzResearch.WordTrace tailWord_1078863 prefixEnd_1078863 61552808816857519694545 := by
  unfold tailWord_1078863
  simp only [CollatzResearch.WordTrace]
  refine ⟨39349366290471080976209243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26232910860314053984139495 39349366290471080976209243)
  ·
    refine ⟨59024049435706621464313865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39349366290471080976209243 59024049435706621464313865)
    ·
      refine ⟨44268037076779966098235399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59024049435706621464313865 44268037076779966098235399)
      ·
        refine ⟨66402055615169949147353099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44268037076779966098235399 66402055615169949147353099)
        ·
          refine ⟨99603083422754923721029649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66402055615169949147353099 99603083422754923721029649)
          ·
            refine ⟨74702312567066192790772237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99603083422754923721029649 74702312567066192790772237)
            ·
              refine ⟨28013367212649822296539589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74702312567066192790772237 28013367212649822296539589)
              ·
                refine ⟨5252506352371841680601173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28013367212649822296539589 5252506352371841680601173)
                ·
                  refine ⟨61552808816857519694545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5252506352371841680601173 61552808816857519694545)
                  ·
                    rfl

theorem cell23_1078863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 4, 8].length) (baseStart_1078863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1078863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1078863 prefixEnd_1078863 := by exact prefixLift 1078863
  have htrace : WordTrace (prefixWord ++ tailWord_1078863) baseStart_1078863 baseEnd_1078863 := by
    simpa [prefixWord, tailWord_1078863, baseEnd_1078863] using wordTrace_append hprefix tailTrace_1078863
  have hstable : (prefixWord ++ tailWord_1078863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078863).length < 2 ^ (prefixWord ++ tailWord_1078863).sum := by decide
  have hdescent : baseEnd_1078863 < baseStart_1078863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078884 : List Nat := [2, 3, 1, 1, 2, 3, 2, 4, 1, 4]
def baseStart_1078884 : Nat := 118140960795 + 1078884 * 2 ^ 59
def prefixEnd_1078884 : Nat := 4983230072969 + 3 ^ 40 * 1078884 * 2
def baseEnd_1078884 : Nat := 184662020815154031696103

theorem tailTrace_1078884 : CollatzResearch.WordTrace tailWord_1078884 prefixEnd_1078884 184662020815154031696103 := by
  unfold tailWord_1078884
  simp only [CollatzResearch.WordTrace]
  refine ⟨19675066111697500781361853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26233421482263334375149137 19675066111697500781361853)
  ·
    refine ⟨7378149791886562793010695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19675066111697500781361853 7378149791886562793010695)
    ·
      refine ⟨11067224687829844189516043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7378149791886562793010695 11067224687829844189516043)
      ·
        refine ⟨16600837031744766284274065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11067224687829844189516043 16600837031744766284274065)
        ·
          refine ⟨12450627773808574713205549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16600837031744766284274065 12450627773808574713205549)
          ·
            refine ⟨4668985415178215517452081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12450627773808574713205549 4668985415178215517452081)
            ·
              refine ⟨3501739061383661638089061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4668985415178215517452081 3501739061383661638089061)
              ·
                refine ⟨656576074009436557141699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3501739061383661638089061 656576074009436557141699)
                ·
                  refine ⟨984864111014154835712549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 656576074009436557141699 984864111014154835712549)
                  ·
                    refine ⟨184662020815154031696103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 984864111014154835712549 184662020815154031696103)
                    ·
                      rfl

theorem cell23_1078884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 4, 1, 4].length) (baseStart_1078884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1078884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1078884 prefixEnd_1078884 := by exact prefixLift 1078884
  have htrace : WordTrace (prefixWord ++ tailWord_1078884) baseStart_1078884 baseEnd_1078884 := by
    simpa [prefixWord, tailWord_1078884, baseEnd_1078884] using wordTrace_append hprefix tailTrace_1078884
  have hstable : (prefixWord ++ tailWord_1078884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078884).length < 2 ^ (prefixWord ++ tailWord_1078884).sum := by decide
  have hdescent : baseEnd_1078884 < baseStart_1078884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078907 : List Nat := [1, 1, 1, 1, 1, 4, 3, 4, 3, 1, 3]
def baseStart_1078907 : Nat := 118140960795 + 1078907 * 2 ^ 59
def prefixEnd_1078907 : Nat := 4983230072969 + 3 ^ 40 * 1078907 * 2
def baseEnd_1078907 : Nat := 553997872500515505100703

theorem tailTrace_1078907 : CollatzResearch.WordTrace tailWord_1078907 prefixEnd_1078907 553997872500515505100703 := by
  unfold tailWord_1078907
  simp only [CollatzResearch.WordTrace]
  refine ⟨39350971102311676490810975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26233980734874450993873983 39350971102311676490810975)
  ·
    refine ⟨59026456653467514736216463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39350971102311676490810975 59026456653467514736216463)
    ·
      refine ⟨88539684980201272104324695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59026456653467514736216463 88539684980201272104324695)
      ·
        refine ⟨132809527470301908156487043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88539684980201272104324695 132809527470301908156487043)
        ·
          refine ⟨199214291205452862234730565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132809527470301908156487043 199214291205452862234730565)
          ·
            refine ⟨37352679601022411669011981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 199214291205452862234730565 37352679601022411669011981)
            ·
              refine ⟨14007254850383404375879493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37352679601022411669011981 14007254850383404375879493)
              ·
                refine ⟨2626360284446888320477405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14007254850383404375879493 2626360284446888320477405)
                ·
                  refine ⟨984885106667583120179027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2626360284446888320477405 984885106667583120179027)
                  ·
                    refine ⟨1477327660001374680268541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 984885106667583120179027 1477327660001374680268541)
                    ·
                      refine ⟨553997872500515505100703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1477327660001374680268541 553997872500515505100703)
                      ·
                        rfl

theorem cell23_1078907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 4, 3, 1, 3].length) (baseStart_1078907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1078907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1078907 prefixEnd_1078907 := by exact prefixLift 1078907
  have htrace : WordTrace (prefixWord ++ tailWord_1078907) baseStart_1078907 baseEnd_1078907 := by
    simpa [prefixWord, tailWord_1078907, baseEnd_1078907] using wordTrace_append hprefix tailTrace_1078907
  have hstable : (prefixWord ++ tailWord_1078907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078907).length < 2 ^ (prefixWord ++ tailWord_1078907).sum := by decide
  have hdescent : baseEnd_1078907 < baseStart_1078907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078917 : List Nat := [1, 3, 1, 1, 4, 1, 1, 3, 1, 5, 2]
def baseStart_1078917 : Nat := 118140960795 + 1078917 * 2 ^ 59
def prefixEnd_1078917 : Nat := 4983230072969 + 3 ^ 40 * 1078917 * 2
def baseEnd_1078917 : Nat := 554003007307060465975657

theorem tailTrace_1078917 : CollatzResearch.WordTrace tailWord_1078917 prefixEnd_1078917 554003007307060465975657 := by
  unfold tailWord_1078917
  simp only [CollatzResearch.WordTrace]
  refine ⟨39351335832275448198675005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26234223888183632132450003 39351335832275448198675005)
  ·
    refine ⟨14756750937103293074503127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39351335832275448198675005 14756750937103293074503127)
    ·
      refine ⟨22135126405654939611754691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14756750937103293074503127 22135126405654939611754691)
      ·
        refine ⟨33202689608482409417632037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22135126405654939611754691 33202689608482409417632037)
        ·
          refine ⟨6225504301590451765806007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33202689608482409417632037 6225504301590451765806007)
          ·
            refine ⟨9338256452385677648709011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6225504301590451765806007 9338256452385677648709011)
            ·
              refine ⟨14007384678578516473063517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9338256452385677648709011 14007384678578516473063517)
              ·
                refine ⟨5252769254466943677398819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14007384678578516473063517 5252769254466943677398819)
                ·
                  refine ⟨7879153881700415516098229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5252769254466943677398819 7879153881700415516098229)
                  ·
                    refine ⟨738670676409413954634209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7879153881700415516098229 738670676409413954634209)
                    ·
                      refine ⟨554003007307060465975657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 738670676409413954634209 554003007307060465975657)
                      ·
                        rfl

theorem cell23_1078917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 3, 1, 5, 2].length) (baseStart_1078917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1078917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1078917 prefixEnd_1078917 := by exact prefixLift 1078917
  have htrace : WordTrace (prefixWord ++ tailWord_1078917) baseStart_1078917 baseEnd_1078917 := by
    simpa [prefixWord, tailWord_1078917, baseEnd_1078917] using wordTrace_append hprefix tailTrace_1078917
  have hstable : (prefixWord ++ tailWord_1078917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078917).length < 2 ^ (prefixWord ++ tailWord_1078917).sum := by decide
  have hdescent : baseEnd_1078917 < baseStart_1078917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078957 : List Nat := [1, 5, 2, 1, 1, 1, 2, 3, 1, 6]
def baseStart_1078957 : Nat := 118140960795 + 1078957 * 2 ^ 59
def prefixEnd_1078957 : Nat := 4983230072969 + 3 ^ 40 * 1078957 * 2
def baseEnd_1078957 : Nat := 184674515511080103158491

theorem tailTrace_1078957 : CollatzResearch.WordTrace tailWord_1078957 prefixEnd_1078957 184674515511080103158491 := by
  unfold tailWord_1078957
  simp only [CollatzResearch.WordTrace]
  refine ⟨39352794752130535030131125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26235196501420356686754083 39352794752130535030131125)
  ·
    refine ⟨3689324508012237659074793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39352794752130535030131125 3689324508012237659074793)
    ·
      refine ⟨2766993381009178244306095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3689324508012237659074793 2766993381009178244306095)
      ·
        refine ⟨4150490071513767366459143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2766993381009178244306095 4150490071513767366459143)
        ·
          refine ⟨6225735107270651049688715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4150490071513767366459143 6225735107270651049688715)
          ·
            refine ⟨9338602660905976574533073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6225735107270651049688715 9338602660905976574533073)
            ·
              refine ⟨7003951995679482430899805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9338602660905976574533073 7003951995679482430899805)
              ·
                refine ⟨2626481998379805911587427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7003951995679482430899805 2626481998379805911587427)
                ·
                  refine ⟨3939722997569708867381141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2626481998379805911587427 3939722997569708867381141)
                  ·
                    refine ⟨184674515511080103158491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3939722997569708867381141 184674515511080103158491)
                    ·
                      rfl

theorem cell23_1078957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_1078957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1078957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1078957 prefixEnd_1078957 := by exact prefixLift 1078957
  have htrace : WordTrace (prefixWord ++ tailWord_1078957) baseStart_1078957 baseEnd_1078957 := by
    simpa [prefixWord, tailWord_1078957, baseEnd_1078957] using wordTrace_append hprefix tailTrace_1078957
  have hstable : (prefixWord ++ tailWord_1078957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078957).length < 2 ^ (prefixWord ++ tailWord_1078957).sum := by decide
  have hdescent : baseEnd_1078957 < baseStart_1078957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078960 : List Nat := [2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 6]
def baseStart_1078960 : Nat := 118140960795 + 1078960 * 2 ^ 59
def prefixEnd_1078960 : Nat := 4983230072969 + 3 ^ 40 * 1078960 * 2
def baseEnd_1078960 : Nat := 554025086975203797737959

theorem tailTrace_1078960 : CollatzResearch.WordTrace tailWord_1078960 prefixEnd_1078960 554025086975203797737959 := by
  unfold tailWord_1078960
  simp only [CollatzResearch.WordTrace]
  refine ⟨19676452085559833271245167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26235269447413111028326889 19676452085559833271245167)
  ·
    refine ⟨29514678128339749906867751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19676452085559833271245167 29514678128339749906867751)
    ·
      refine ⟨44272017192509624860301627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29514678128339749906867751 44272017192509624860301627)
      ·
        refine ⟨66408025788764437290452441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44272017192509624860301627 66408025788764437290452441)
        ·
          refine ⟨49806019341573327967839331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66408025788764437290452441 49806019341573327967839331)
          ·
            refine ⟨74709029012359991951758997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49806019341573327967839331 74709029012359991951758997)
            ·
              refine ⟨3501985734954374622738703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 74709029012359991951758997 3501985734954374622738703)
              ·
                refine ⟨5252978602431561934108055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3501985734954374622738703 5252978602431561934108055)
                ·
                  refine ⟨7879467903647342901162083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5252978602431561934108055 7879467903647342901162083)
                  ·
                    refine ⟨11819201855471014351743125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7879467903647342901162083 11819201855471014351743125)
                    ·
                      refine ⟨554025086975203797737959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11819201855471014351743125 554025086975203797737959)
                      ·
                        rfl

theorem cell23_1078960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 6].length) (baseStart_1078960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1078960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1078960 prefixEnd_1078960 := by exact prefixLift 1078960
  have htrace : WordTrace (prefixWord ++ tailWord_1078960) baseStart_1078960 baseEnd_1078960 := by
    simpa [prefixWord, tailWord_1078960, baseEnd_1078960] using wordTrace_append hprefix tailTrace_1078960
  have hstable : (prefixWord ++ tailWord_1078960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078960).length < 2 ^ (prefixWord ++ tailWord_1078960).sum := by decide
  have hdescent : baseEnd_1078960 < baseStart_1078960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078970 : List Nat := [3, 1, 1, 1, 2, 4, 2, 9]
def baseStart_1078970 : Nat := 118140960795 + 1078970 * 2 ^ 59
def prefixEnd_1078970 : Nat := 4983230072969 + 3 ^ 40 * 1078970 * 2
def baseEnd_1078970 : Nat := 20519637843768472541219

theorem tailTrace_1078970 : CollatzResearch.WordTrace tailWord_1078970 prefixEnd_1078970 20519637843768472541219 := by
  unfold tailWord_1078970
  simp only [CollatzResearch.WordTrace]
  refine ⟨9838317225270859562588591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26235512600722292166902909 9838317225270859562588591)
  ·
    refine ⟨14757475837906289343882887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9838317225270859562588591 14757475837906289343882887)
    ·
      refine ⟨22136213756859434015824331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14757475837906289343882887 22136213756859434015824331)
      ·
        refine ⟨33204320635289151023736497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22136213756859434015824331 33204320635289151023736497)
        ·
          refine ⟨24903240476466863267802373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33204320635289151023736497 24903240476466863267802373)
          ·
            refine ⟨4669357589337536862712945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24903240476466863267802373 4669357589337536862712945)
            ·
              refine ⟨3502018192003152647034709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4669357589337536862712945 3502018192003152647034709)
              ·
                refine ⟨20519637843768472541219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3502018192003152647034709 20519637843768472541219)
                ·
                  rfl

theorem cell23_1078970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 9].length) (baseStart_1078970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1078970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1078970 prefixEnd_1078970 := by exact prefixLift 1078970
  have htrace : WordTrace (prefixWord ++ tailWord_1078970) baseStart_1078970 baseEnd_1078970 := by
    simpa [prefixWord, tailWord_1078970, baseEnd_1078970] using wordTrace_append hprefix tailTrace_1078970
  have hstable : (prefixWord ++ tailWord_1078970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078970).length < 2 ^ (prefixWord ++ tailWord_1078970).sum := by decide
  have hdescent : baseEnd_1078970 < baseStart_1078970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079000 : List Nat := [2, 1, 2, 2, 3, 1, 1, 1, 1, 9]
def baseStart_1079000 : Nat := 118140960795 + 1079000 * 2 ^ 59
def prefixEnd_1079000 : Nat := 4983230072969 + 3 ^ 40 * 1079000 * 2
def baseEnd_1079000 : Nat := 184681875400461213745925

theorem tailTrace_1079000 : CollatzResearch.WordTrace tailWord_1079000 prefixEnd_1079000 184681875400461213745925 := by
  unfold tailWord_1079000
  simp only [CollatzResearch.WordTrace]
  refine ⟨19677181545487376686973227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26236242060649835582630969 19677181545487376686973227)
  ·
    refine ⟨29515772318231065030459841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19677181545487376686973227 29515772318231065030459841)
    ·
      refine ⟨22136829238673298772844881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29515772318231065030459841 22136829238673298772844881)
      ·
        refine ⟨16602621929004974079633661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22136829238673298772844881 16602621929004974079633661)
        ·
          refine ⟨6225983223376865279862623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16602621929004974079633661 6225983223376865279862623)
          ·
            refine ⟨9338974835065297919793935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6225983223376865279862623 9338974835065297919793935)
            ·
              refine ⟨14008462252597946879690903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9338974835065297919793935 14008462252597946879690903)
              ·
                refine ⟨21012693378896920319536355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14008462252597946879690903 21012693378896920319536355)
                ·
                  refine ⟨31519040068345380479304533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21012693378896920319536355 31519040068345380479304533)
                  ·
                    refine ⟨184681875400461213745925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 31519040068345380479304533 184681875400461213745925)
                    ·
                      rfl

theorem cell23_1079000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 1, 9].length) (baseStart_1079000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1079000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1079000 prefixEnd_1079000 := by exact prefixLift 1079000
  have htrace : WordTrace (prefixWord ++ tailWord_1079000) baseStart_1079000 baseEnd_1079000 := by
    simpa [prefixWord, tailWord_1079000, baseEnd_1079000] using wordTrace_append hprefix tailTrace_1079000
  have hstable : (prefixWord ++ tailWord_1079000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079000).length < 2 ^ (prefixWord ++ tailWord_1079000).sum := by decide
  have hdescent : baseEnd_1079000 < baseStart_1079000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079054 : List Nat := [4, 1, 1, 2, 1, 1, 2, 2, 3, 4, 2]
def baseStart_1079054 : Nat := 118140960795 + 1079054 * 2 ^ 59
def prefixEnd_1079054 : Nat := 4983230072969 + 3 ^ 40 * 1079054 * 2
def baseEnd_1079054 : Nat := 554073354156726429962527

theorem tailTrace_1079054 : CollatzResearch.WordTrace tailWord_1079054 prefixEnd_1079054 554073354156726429962527 := by
  unfold tailWord_1079054
  simp only [CollatzResearch.WordTrace]
  refine ⟨4919541579097390074551527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26237555088519413730941477 4919541579097390074551527)
  ·
    refine ⟨7379312368646085111827291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4919541579097390074551527 7379312368646085111827291)
    ·
      refine ⟨11068968552969127667740937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7379312368646085111827291 11068968552969127667740937)
      ·
        refine ⟨8301726414726845750805703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11068968552969127667740937 8301726414726845750805703)
        ·
          refine ⟨12452589622090268626208555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8301726414726845750805703 12452589622090268626208555)
          ·
            refine ⟨18678884433135402939312833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12452589622090268626208555 18678884433135402939312833)
            ·
              refine ⟨14009163324851552204484625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18678884433135402939312833 14009163324851552204484625)
              ·
                refine ⟨10506872493638664153363469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14009163324851552204484625 10506872493638664153363469)
                ·
                  refine ⟨3940077185114499057511301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10506872493638664153363469 3940077185114499057511301)
                  ·
                    refine ⟨738764472208968573283369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3940077185114499057511301 738764472208968573283369)
                    ·
                      refine ⟨554073354156726429962527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 738764472208968573283369 554073354156726429962527)
                      ·
                        rfl

theorem cell23_1079054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 3, 4, 2].length) (baseStart_1079054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1079054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1079054 prefixEnd_1079054 := by exact prefixLift 1079054
  have htrace : WordTrace (prefixWord ++ tailWord_1079054) baseStart_1079054 baseEnd_1079054 := by
    simpa [prefixWord, tailWord_1079054, baseEnd_1079054] using wordTrace_append hprefix tailTrace_1079054
  have hstable : (prefixWord ++ tailWord_1079054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079054).length < 2 ^ (prefixWord ++ tailWord_1079054).sum := by decide
  have hdescent : baseEnd_1079054 < baseStart_1079054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079077 : List Nat := [1, 3, 1, 2, 3, 2, 2, 2, 7]
def baseStart_1079077 : Nat := 118140960795 + 1079077 * 2 ^ 59
def prefixEnd_1079077 : Nat := 4983230072969 + 3 ^ 40 * 1079077 * 2
def baseEnd_1079077 : Nat := 61565018245753315552769

theorem tailTrace_1079077 : CollatzResearch.WordTrace tailWord_1079077 prefixEnd_1079077 61565018245753315552769 := by
  unfold tailWord_1079077
  simp only [CollatzResearch.WordTrace]
  refine ⟨39357171511695795524499485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26238114341130530349666323 39357171511695795524499485)
  ·
    refine ⟨14758939316885923321687307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39357171511695795524499485 14758939316885923321687307)
    ·
      refine ⟨22138408975328884982530961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14758939316885923321687307 22138408975328884982530961)
      ·
        refine ⟨16603806731496663736898221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22138408975328884982530961 16603806731496663736898221)
        ·
          refine ⟨6226427524311248901336833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16603806731496663736898221 6226427524311248901336833)
          ·
            refine ⟨4669820643233436676002625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6226427524311248901336833 4669820643233436676002625)
            ·
              refine ⟨3502365482425077507001969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4669820643233436676002625 3502365482425077507001969)
              ·
                refine ⟨2626774111818808130251477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3502365482425077507001969 2626774111818808130251477)
                ·
                  refine ⟨61565018245753315552769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2626774111818808130251477 61565018245753315552769)
                  ·
                    rfl

theorem cell23_1079077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 2, 7].length) (baseStart_1079077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1079077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1079077 prefixEnd_1079077 := by exact prefixLift 1079077
  have htrace : WordTrace (prefixWord ++ tailWord_1079077) baseStart_1079077 baseEnd_1079077 := by
    simpa [prefixWord, tailWord_1079077, baseEnd_1079077] using wordTrace_append hprefix tailTrace_1079077
  have hstable : (prefixWord ++ tailWord_1079077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079077).length < 2 ^ (prefixWord ++ tailWord_1079077).sum := by decide
  have hdescent : baseEnd_1079077 < baseStart_1079077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079107 : List Nat := [1, 1, 1, 3, 1, 5, 1, 1, 4, 5]
def baseStart_1079107 : Nat := 118140960795 + 1079107 * 2 ^ 59
def prefixEnd_1079107 : Nat := 4983230072969 + 3 ^ 40 * 1079107 * 2
def baseEnd_1079107 : Nat := 184700189543804907533261

theorem tailTrace_1079107 : CollatzResearch.WordTrace tailWord_1079107 prefixEnd_1079107 184700189543804907533261 := by
  unfold tailWord_1079107
  simp only [CollatzResearch.WordTrace]
  refine ⟨39358265701587110648091575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26238843801058073765394383 39358265701587110648091575)
  ·
    refine ⟨59037398552380665972137363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39358265701587110648091575 59037398552380665972137363)
    ·
      refine ⟨88556097828570998958206045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59037398552380665972137363 88556097828570998958206045)
      ·
        refine ⟨33208536685714124609327267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88556097828570998958206045 33208536685714124609327267)
        ·
          refine ⟨49812805028571186913990901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33208536685714124609327267 49812805028571186913990901)
          ·
            refine ⟨4669950471428548773186647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49812805028571186913990901 4669950471428548773186647)
            ·
              refine ⟨7004925707142823159779971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4669950471428548773186647 7004925707142823159779971)
              ·
                refine ⟨10507388560714234739669957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7004925707142823159779971 10507388560714234739669957)
                ·
                  refine ⟨1970135355133919013688117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10507388560714234739669957 1970135355133919013688117)
                  ·
                    refine ⟨184700189543804907533261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1970135355133919013688117 184700189543804907533261)
                    ·
                      rfl

theorem cell23_1079107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 4, 5].length) (baseStart_1079107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1079107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1079107 prefixEnd_1079107 := by exact prefixLift 1079107
  have htrace : WordTrace (prefixWord ++ tailWord_1079107) baseStart_1079107 baseEnd_1079107 := by
    simpa [prefixWord, tailWord_1079107, baseEnd_1079107] using wordTrace_append hprefix tailTrace_1079107
  have hstable : (prefixWord ++ tailWord_1079107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079107).length < 2 ^ (prefixWord ++ tailWord_1079107).sum := by decide
  have hdescent : baseEnd_1079107 < baseStart_1079107 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079114 : List Nat := [3, 1, 2, 1, 1, 1, 4, 1, 2, 5, 2]
def baseStart_1079114 : Nat := 118140960795 + 1079114 * 2 ^ 59
def prefixEnd_1079114 : Nat := 4983230072969 + 3 ^ 40 * 1079114 * 2
def baseEnd_1079114 : Nat := 554104162995996195212251

theorem tailTrace_1079114 : CollatzResearch.WordTrace tailWord_1079114 prefixEnd_1079114 554104162995996195212251 := by
  unfold tailWord_1079114
  simp only [CollatzResearch.WordTrace]
  refine ⟨9839630253140437710899099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26239014008374500562397597 9839630253140437710899099)
  ·
    refine ⟨14759445379710656566348649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9839630253140437710899099 14759445379710656566348649)
    ·
      refine ⟨11069584034782992424761487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14759445379710656566348649 11069584034782992424761487)
      ·
        refine ⟨16604376052174488637142231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11069584034782992424761487 16604376052174488637142231)
        ·
          refine ⟨24906564078261732955713347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16604376052174488637142231 24906564078261732955713347)
          ·
            refine ⟨37359846117392599433570021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24906564078261732955713347 37359846117392599433570021)
            ·
              refine ⟨7004971147011112393794379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37359846117392599433570021 7004971147011112393794379)
              ·
                refine ⟨10507456720516668590691569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7004971147011112393794379 10507456720516668590691569)
                ·
                  refine ⟨7880592540387501443018677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10507456720516668590691569 7880592540387501443018677)
                  ·
                    refine ⟨738805550661328260283001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7880592540387501443018677 738805550661328260283001)
                    ·
                      refine ⟨554104162995996195212251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 738805550661328260283001 554104162995996195212251)
                      ·
                        rfl

theorem cell23_1079114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 2, 5, 2].length) (baseStart_1079114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1079114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1079114 prefixEnd_1079114 := by exact prefixLift 1079114
  have htrace : WordTrace (prefixWord ++ tailWord_1079114) baseStart_1079114 baseEnd_1079114 := by
    simpa [prefixWord, tailWord_1079114, baseEnd_1079114] using wordTrace_append hprefix tailTrace_1079114
  have hstable : (prefixWord ++ tailWord_1079114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079114).length < 2 ^ (prefixWord ++ tailWord_1079114).sum := by decide
  have hdescent : baseEnd_1079114 < baseStart_1079114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079178 : List Nat := [3, 1, 2, 4, 2, 1, 1, 1, 2, 4, 2]
def baseStart_1079178 : Nat := 118140960795 + 1079178 * 2 ^ 59
def prefixEnd_1079178 : Nat := 4983230072969 + 3 ^ 40 * 1079178 * 2
def baseEnd_1079178 : Nat := 554137025757883944811957

theorem tailTrace_1079178 : CollatzResearch.WordTrace tailWord_1079178 prefixEnd_1079178 554137025757883944811957 := by
  unfold tailWord_1079178
  simp only [CollatzResearch.WordTrace]
  refine ⟨9840213821082472443481547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26240570189553259849284125 9840213821082472443481547)
  ·
    refine ⟨14760320731623708665222321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9840213821082472443481547 14760320731623708665222321)
    ·
      refine ⟨11070240548717781498916741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14760320731623708665222321 11070240548717781498916741)
      ·
        refine ⟨2075670102884584031046889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11070240548717781498916741 2075670102884584031046889)
        ·
          refine ⟨1556752577163438023285167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2075670102884584031046889 1556752577163438023285167)
          ·
            refine ⟨2335128865745157034927751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1556752577163438023285167 2335128865745157034927751)
            ·
              refine ⟨3502693298617735552391627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2335128865745157034927751 3502693298617735552391627)
              ·
                refine ⟨5254039947926603328587441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3502693298617735552391627 5254039947926603328587441)
                ·
                  refine ⟨3940529960944952496440581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5254039947926603328587441 3940529960944952496440581)
                  ·
                    refine ⟨738849367677178593082609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3940529960944952496440581 738849367677178593082609)
                    ·
                      refine ⟨554137025757883944811957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 738849367677178593082609 554137025757883944811957)
                      ·
                        rfl

theorem cell23_1079178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_1079178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1079178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1079178 prefixEnd_1079178 := by exact prefixLift 1079178
  have htrace : WordTrace (prefixWord ++ tailWord_1079178) baseStart_1079178 baseEnd_1079178 := by
    simpa [prefixWord, tailWord_1079178, baseEnd_1079178] using wordTrace_append hprefix tailTrace_1079178
  have hstable : (prefixWord ++ tailWord_1079178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079178).length < 2 ^ (prefixWord ++ tailWord_1079178).sum := by decide
  have hdescent : baseEnd_1079178 < baseStart_1079178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079227 : List Nat := [1, 1, 1, 1, 1, 2, 2, 3, 5, 6]
def baseStart_1079227 : Nat := 118140960795 + 1079227 * 2 ^ 59
def prefixEnd_1079227 : Nat := 4983230072969 + 3 ^ 40 * 1079227 * 2
def baseEnd_1079227 : Nat := 184720728769984751033077

theorem tailTrace_1079227 : CollatzResearch.WordTrace tailWord_1079227 prefixEnd_1079227 184720728769984751033077 := by
  unfold tailWord_1079227
  simp only [CollatzResearch.WordTrace]
  refine ⟨39362642461152371142459935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26241761640768247428306623 39362642461152371142459935)
  ·
    refine ⟨59043963691728556713689903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39362642461152371142459935 59043963691728556713689903)
    ·
      refine ⟨88565945537592835070534855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59043963691728556713689903 88565945537592835070534855)
      ·
        refine ⟨132848918306389252605802283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88565945537592835070534855 132848918306389252605802283)
        ·
          refine ⟨199273377459583878908703425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132848918306389252605802283 199273377459583878908703425)
          ·
            refine ⟨149455033094687909181527569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 199273377459583878908703425 149455033094687909181527569)
            ·
              refine ⟨112091274821015931886145677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 149455033094687909181527569 112091274821015931886145677)
              ·
                refine ⟨42034228057880974457304629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 112091274821015931886145677 42034228057880974457304629)
                ·
                  refine ⟨3940708880426341355372309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42034228057880974457304629 3940708880426341355372309)
                  ·
                    refine ⟨184720728769984751033077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3940708880426341355372309 184720728769984751033077)
                    ·
                      rfl

theorem cell23_1079227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5, 6].length) (baseStart_1079227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1079227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1079227 prefixEnd_1079227 := by exact prefixLift 1079227
  have htrace : WordTrace (prefixWord ++ tailWord_1079227) baseStart_1079227 baseEnd_1079227 := by
    simpa [prefixWord, tailWord_1079227, baseEnd_1079227] using wordTrace_append hprefix tailTrace_1079227
  have hstable : (prefixWord ++ tailWord_1079227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079227).length < 2 ^ (prefixWord ++ tailWord_1079227).sum := by decide
  have hdescent : baseEnd_1079227 < baseStart_1079227 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079264 : List Nat := [2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 4]
def baseStart_1079264 : Nat := 118140960795 + 1079264 * 2 ^ 59
def prefixEnd_1079264 : Nat := 4983230072969 + 3 ^ 40 * 1079264 * 2
def baseEnd_1079264 : Nat := 554181185094170608336561

theorem tailTrace_1079264 : CollatzResearch.WordTrace tailWord_1079264 prefixEnd_1079264 554181185094170608336561 := by
  unfold tailWord_1079264
  simp only [CollatzResearch.WordTrace]
  refine ⟨19681995981009163230778423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26242661308012217641037897 19681995981009163230778423)
  ·
    refine ⟨29522993971513744846167635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19681995981009163230778423 29522993971513744846167635)
    ·
      refine ⟨44284490957270617269251453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29522993971513744846167635 44284490957270617269251453)
      ·
        refine ⟨16606684108976481475969295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44284490957270617269251453 16606684108976481475969295)
        ·
          refine ⟨24910026163464722213953943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16606684108976481475969295 24910026163464722213953943)
          ·
            refine ⟨37365039245197083320930915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24910026163464722213953943 37365039245197083320930915)
            ·
              refine ⟨56047558867795624981396373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37365039245197083320930915 56047558867795624981396373)
              ·
                refine ⟨2627229321927919921002955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 56047558867795624981396373 2627229321927919921002955)
                ·
                  refine ⟨3940843982891879881504433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2627229321927919921002955 3940843982891879881504433)
                  ·
                    refine ⟨2955632987168909911128325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3940843982891879881504433 2955632987168909911128325)
                    ·
                      refine ⟨554181185094170608336561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2955632987168909911128325 554181185094170608336561)
                      ·
                        rfl

theorem cell23_1079264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 4].length) (baseStart_1079264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1079264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1079264 prefixEnd_1079264 := by exact prefixLift 1079264
  have htrace : WordTrace (prefixWord ++ tailWord_1079264) baseStart_1079264 baseEnd_1079264 := by
    simpa [prefixWord, tailWord_1079264, baseEnd_1079264] using wordTrace_append hprefix tailTrace_1079264
  have hstable : (prefixWord ++ tailWord_1079264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079264).length < 2 ^ (prefixWord ++ tailWord_1079264).sum := by decide
  have hdescent : baseEnd_1079264 < baseStart_1079264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079392 : List Nat := [2, 1, 1, 3, 2, 5, 1, 2, 2, 2, 2]
def baseStart_1079392 : Nat := 118140960795 + 1079392 * 2 ^ 59
def prefixEnd_1079392 : Nat := 4983230072969 + 3 ^ 40 * 1079392 * 2
def baseEnd_1079392 : Nat := 554246910617946107535973

theorem tailTrace_1079392 : CollatzResearch.WordTrace tailWord_1079392 prefixEnd_1079392 554246910617946107535973 := by
  unfold tailWord_1079392
  simp only [CollatzResearch.WordTrace]
  refine ⟨19684330252777302161108215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26245773670369736214810953 19684330252777302161108215)
  ·
    refine ⟨29526495379165953241662323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19684330252777302161108215 29526495379165953241662323)
    ·
      refine ⟨44289743068748929862493485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29526495379165953241662323 44289743068748929862493485)
      ·
        refine ⟨16608653650780848698435057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44289743068748929862493485 16608653650780848698435057)
        ·
          refine ⟨12456490238085636523826293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16608653650780848698435057 12456490238085636523826293)
          ·
            refine ⟨1167795959820528424108715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12456490238085636523826293 1167795959820528424108715)
            ·
              refine ⟨1751693939730792636163073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1167795959820528424108715 1751693939730792636163073)
              ·
                refine ⟨1313770454798094477122305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1751693939730792636163073 1313770454798094477122305)
                ·
                  refine ⟨985327841098570857841729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1313770454798094477122305 985327841098570857841729)
                  ·
                    refine ⟨738995880823928143381297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 985327841098570857841729 738995880823928143381297)
                    ·
                      refine ⟨554246910617946107535973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 738995880823928143381297 554246910617946107535973)
                      ·
                        rfl

theorem cell23_1079392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 2, 2, 2, 2].length) (baseStart_1079392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1079392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1079392 prefixEnd_1079392 := by exact prefixLift 1079392
  have htrace : WordTrace (prefixWord ++ tailWord_1079392) baseStart_1079392 baseEnd_1079392 := by
    simpa [prefixWord, tailWord_1079392, baseEnd_1079392] using wordTrace_append hprefix tailTrace_1079392
  have hstable : (prefixWord ++ tailWord_1079392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079392).length < 2 ^ (prefixWord ++ tailWord_1079392).sum := by decide
  have hdescent : baseEnd_1079392 < baseStart_1079392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079424 : List Nat := [2, 1, 1, 2, 1, 3, 1, 1, 1, 10]
def baseStart_1079424 : Nat := 118140960795 + 1079424 * 2 ^ 59
def prefixEnd_1079424 : Nat := 4983230072969 + 3 ^ 40 * 1079424 * 2
def baseEnd_1079424 : Nat := 184754447332963327445275

theorem tailTrace_1079424 : CollatzResearch.WordTrace tailWord_1079424 prefixEnd_1079424 184754447332963327445275 := by
  unfold tailWord_1079424
  simp only [CollatzResearch.WordTrace]
  refine ⟨19684913820719336893690663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26246551760959115858254217 19684913820719336893690663)
  ·
    refine ⟨29527370731079005340535995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19684913820719336893690663 29527370731079005340535995)
    ·
      refine ⟨44291056096618508010803993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29527370731079005340535995 44291056096618508010803993)
      ·
        refine ⟨33218292072463881008102995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44291056096618508010803993 33218292072463881008102995)
        ·
          refine ⟨49827438108695821512154493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33218292072463881008102995 49827438108695821512154493)
          ·
            refine ⟨18685289290760933067057935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49827438108695821512154493 18685289290760933067057935)
            ·
              refine ⟨28027933936141399600586903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18685289290760933067057935 28027933936141399600586903)
              ·
                refine ⟨42041900904212099400880355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28027933936141399600586903 42041900904212099400880355)
                ·
                  refine ⟨63062851356318149101320533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42041900904212099400880355 63062851356318149101320533)
                  ·
                    refine ⟨184754447332963327445275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 63062851356318149101320533 184754447332963327445275)
                    ·
                      rfl

theorem cell23_1079424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 1, 10].length) (baseStart_1079424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1079424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1079424 prefixEnd_1079424 := by exact prefixLift 1079424
  have htrace : WordTrace (prefixWord ++ tailWord_1079424) baseStart_1079424 baseEnd_1079424 := by
    simpa [prefixWord, tailWord_1079424, baseEnd_1079424] using wordTrace_append hprefix tailTrace_1079424
  have hstable : (prefixWord ++ tailWord_1079424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079424).length < 2 ^ (prefixWord ++ tailWord_1079424).sum := by decide
  have hdescent : baseEnd_1079424 < baseStart_1079424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079431 : List Nat := [1, 1, 4, 2, 1, 1, 4, 1, 1, 3, 4]
def baseStart_1079431 : Nat := 118140960795 + 1079431 * 2 ^ 59
def prefixEnd_1079431 : Nat := 4983230072969 + 3 ^ 40 * 1079431 * 2
def baseEnd_1079431 : Nat := 554266936363471454948293

theorem tailTrace_1079431 : CollatzResearch.WordTrace tailWord_1079431 prefixEnd_1079431 554266936363471454948293 := by
  unfold tailWord_1079431
  simp only [CollatzResearch.WordTrace]
  refine ⟨39370082952413313982886147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26246721968275542655257431 39370082952413313982886147)
  ·
    refine ⟨59055124428619970974329221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39370082952413313982886147 59055124428619970974329221)
    ·
      refine ⟨11072835830366244557686729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59055124428619970974329221 11072835830366244557686729)
      ·
        refine ⟨8304626872774683418265047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11072835830366244557686729 8304626872774683418265047)
        ·
          refine ⟨12456940309162025127397571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8304626872774683418265047 12456940309162025127397571)
          ·
            refine ⟨18685410463743037691096357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12456940309162025127397571 18685410463743037691096357)
            ·
              refine ⟨3503514461951819567080567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18685410463743037691096357 3503514461951819567080567)
              ·
                refine ⟨5255271692927729350620851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3503514461951819567080567 5255271692927729350620851)
                ·
                  refine ⟨7882907539391594025931277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5255271692927729350620851 7882907539391594025931277)
                  ·
                    refine ⟨2956090327271847759724229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7882907539391594025931277 2956090327271847759724229)
                    ·
                      refine ⟨554266936363471454948293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2956090327271847759724229 554266936363471454948293)
                      ·
                        rfl

theorem cell23_1079431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_1079431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1079431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1079431 prefixEnd_1079431 := by exact prefixLift 1079431
  have htrace : WordTrace (prefixWord ++ tailWord_1079431) baseStart_1079431 baseEnd_1079431 := by
    simpa [prefixWord, tailWord_1079431, baseEnd_1079431] using wordTrace_append hprefix tailTrace_1079431
  have hstable : (prefixWord ++ tailWord_1079431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079431).length < 2 ^ (prefixWord ++ tailWord_1079431).sum := by decide
  have hdescent : baseEnd_1079431 < baseStart_1079431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079542 : List Nat := [5, 1, 1, 1, 1, 1, 5, 1, 2, 3, 2]
def baseStart_1079542 : Nat := 118140960795 + 1079542 * 2 ^ 59
def prefixEnd_1079542 : Nat := 4983230072969 + 3 ^ 40 * 1079542 * 2
def baseEnd_1079542 : Nat := 554323932716120520660283

theorem tailTrace_1079542 : CollatzResearch.WordTrace tailWord_1079542 prefixEnd_1079542 554323932716120520660283 := by
  unfold tailWord_1079542
  simp only [CollatzResearch.WordTrace]
  refine ⟨2460883215938198746261055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26249420970007453293451253 2460883215938198746261055)
  ·
    refine ⟨3691324823907298119391583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2460883215938198746261055 3691324823907298119391583)
    ·
      refine ⟨5536987235860947179087375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3691324823907298119391583 5536987235860947179087375)
      ·
        refine ⟨8305480853791420768631063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5536987235860947179087375 8305480853791420768631063)
        ·
          refine ⟨12458221280687131152946595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8305480853791420768631063 12458221280687131152946595)
          ·
            refine ⟨18687331921030696729419893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12458221280687131152946595 18687331921030696729419893)
            ·
              refine ⟨1751937367596627818383115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18687331921030696729419893 1751937367596627818383115)
              ·
                refine ⟨2627906051394941727574673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1751937367596627818383115 2627906051394941727574673)
                ·
                  refine ⟨1970929538546206295681005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2627906051394941727574673 1970929538546206295681005)
                  ·
                    refine ⟨739098576954827360880377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1970929538546206295681005 739098576954827360880377)
                    ·
                      refine ⟨554323932716120520660283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 739098576954827360880377 554323932716120520660283)
                      ·
                        rfl

theorem cell23_1079542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 1, 2, 3, 2].length) (baseStart_1079542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1079542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1079542 prefixEnd_1079542 := by exact prefixLift 1079542
  have htrace : WordTrace (prefixWord ++ tailWord_1079542) baseStart_1079542 baseEnd_1079542 := by
    simpa [prefixWord, tailWord_1079542, baseEnd_1079542] using wordTrace_append hprefix tailTrace_1079542
  have hstable : (prefixWord ++ tailWord_1079542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079542).length < 2 ^ (prefixWord ++ tailWord_1079542).sum := by decide
  have hdescent : baseEnd_1079542 < baseStart_1079542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079548 : List Nat := [2, 2, 2, 1, 4, 1, 2, 2, 1, 6]
def baseStart_1079548 : Nat := 118140960795 + 1079548 * 2 ^ 59
def prefixEnd_1079548 : Nat := 4983230072969 + 3 ^ 40 * 1079548 * 2
def baseEnd_1079548 : Nat := 184775671200015832395085

theorem tailTrace_1079548 : CollatzResearch.WordTrace tailWord_1079548 prefixEnd_1079548 184775671200015832395085 := by
  unfold tailWord_1079548
  simp only [CollatzResearch.WordTrace]
  refine ⟨19687175146494721482447649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26249566861992961976596865 19687175146494721482447649)
  ·
    refine ⟨14765381359871041111835737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19687175146494721482447649 14765381359871041111835737)
    ·
      refine ⟨11074036019903280833876803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14765381359871041111835737 11074036019903280833876803)
      ·
        refine ⟨16611054029854921250815205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11074036019903280833876803 16611054029854921250815205)
        ·
          refine ⟨3114572630597797734527851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16611054029854921250815205 3114572630597797734527851)
          ·
            refine ⟨4671858945896696601791777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3114572630597797734527851 4671858945896696601791777)
            ·
              refine ⟨3503894209422522451343833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4671858945896696601791777 3503894209422522451343833)
              ·
                refine ⟨2627920657066891838507875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3503894209422522451343833 2627920657066891838507875)
                ·
                  refine ⟨3941880985600337757761813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2627920657066891838507875 3941880985600337757761813)
                  ·
                    refine ⟨184775671200015832395085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3941880985600337757761813 184775671200015832395085)
                    ·
                      rfl

theorem cell23_1079548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 2, 1, 6].length) (baseStart_1079548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1079548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1079548 prefixEnd_1079548 := by exact prefixLift 1079548
  have htrace : WordTrace (prefixWord ++ tailWord_1079548) baseStart_1079548 baseEnd_1079548 := by
    simpa [prefixWord, tailWord_1079548, baseEnd_1079548] using wordTrace_append hprefix tailTrace_1079548
  have hstable : (prefixWord ++ tailWord_1079548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079548).length < 2 ^ (prefixWord ++ tailWord_1079548).sum := by decide
  have hdescent : baseEnd_1079548 < baseStart_1079548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079555 : List Nat := [1, 1, 1, 3, 2, 3, 1, 2, 5, 2, 2]
def baseStart_1079555 : Nat := 118140960795 + 1079555 * 2 ^ 59
def prefixEnd_1079555 : Nat := 4983230072969 + 3 ^ 40 * 1079555 * 2
def baseEnd_1079555 : Nat := 554330607964628969797723

theorem tailTrace_1079555 : CollatzResearch.WordTrace tailWord_1079555 prefixEnd_1079555 554330607964628969797723 := by
  unfold tailWord_1079555
  simp only [CollatzResearch.WordTrace]
  refine ⟨39374605603964083160400119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26249737069309388773600079 39374605603964083160400119)
  ·
    refine ⟨59061908405946124740600179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39374605603964083160400119 59061908405946124740600179)
    ·
      refine ⟨88592862608919187110900269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59061908405946124740600179 88592862608919187110900269)
      ·
        refine ⟨33222323478344695166587601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88592862608919187110900269 33222323478344695166587601)
        ·
          refine ⟨24916742608758521374940701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33222323478344695166587601 24916742608758521374940701)
          ·
            refine ⟨9343778478284445515602763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24916742608758521374940701 9343778478284445515602763)
            ·
              refine ⟨14015667717426668273404145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9343778478284445515602763 14015667717426668273404145)
              ·
                refine ⟨10511750788070001205053109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14015667717426668273404145 10511750788070001205053109)
                ·
                  refine ⟨985476636381562612973729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10511750788070001205053109 985476636381562612973729)
                  ·
                    refine ⟨739107477286171959730297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 985476636381562612973729 739107477286171959730297)
                    ·
                      refine ⟨554330607964628969797723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 739107477286171959730297 554330607964628969797723)
                      ·
                        rfl

theorem cell23_1079555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 5, 2, 2].length) (baseStart_1079555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1079555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1079555 prefixEnd_1079555 := by exact prefixLift 1079555
  have htrace : WordTrace (prefixWord ++ tailWord_1079555) baseStart_1079555 baseEnd_1079555 := by
    simpa [prefixWord, tailWord_1079555, baseEnd_1079555] using wordTrace_append hprefix tailTrace_1079555
  have hstable : (prefixWord ++ tailWord_1079555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079555).length < 2 ^ (prefixWord ++ tailWord_1079555).sum := by decide
  have hdescent : baseEnd_1079555 < baseStart_1079555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079561 : List Nat := [1, 2, 1, 1, 3, 5, 10]
def baseStart_1079561 : Nat := 118140960795 + 1079561 * 2 ^ 59
def prefixEnd_1079561 : Nat := 4983230072969 + 3 ^ 40 * 1079561 * 2
def baseEnd_1079561 : Nat := 6843625788253777115095

theorem tailTrace_1079561 : CollatzResearch.WordTrace tailWord_1079561 prefixEnd_1079561 6843625788253777115095 := by
  unfold tailWord_1079561
  simp only [CollatzResearch.WordTrace]
  refine ⟨39374824441942346185118537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26249882961294897456745691 39374824441942346185118537)
  ·
    refine ⟨29531118331456759638838903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39374824441942346185118537 29531118331456759638838903)
    ·
      refine ⟨44296677497185139458258355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29531118331456759638838903 44296677497185139458258355)
      ·
        refine ⟨66445016245777709187387533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44296677497185139458258355 66445016245777709187387533)
        ·
          refine ⟨24916881092166640945270325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66445016245777709187387533 24916881092166640945270325)
          ·
            refine ⟨2335957602390622588619093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24916881092166640945270325 2335957602390622588619093)
            ·
              refine ⟨6843625788253777115095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2335957602390622588619093 6843625788253777115095)
              ·
                rfl

theorem cell23_1079561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 10].length) (baseStart_1079561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1079561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1079561 prefixEnd_1079561 := by exact prefixLift 1079561
  have htrace : WordTrace (prefixWord ++ tailWord_1079561) baseStart_1079561 baseEnd_1079561 := by
    simpa [prefixWord, tailWord_1079561, baseEnd_1079561] using wordTrace_append hprefix tailTrace_1079561
  have hstable : (prefixWord ++ tailWord_1079561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079561).length < 2 ^ (prefixWord ++ tailWord_1079561).sum := by decide
  have hdescent : baseEnd_1079561 < baseStart_1079561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079582 : List Nat := [4, 3, 2, 1, 1, 1, 3, 1, 1, 6]
def baseStart_1079582 : Nat := 118140960795 + 1079582 * 2 ^ 59
def prefixEnd_1079582 : Nat := 4983230072969 + 3 ^ 40 * 1079582 * 2
def baseEnd_1079582 : Nat := 184781490647433454720033

theorem tailTrace_1079582 : CollatzResearch.WordTrace tailWord_1079582 prefixEnd_1079582 184781490647433454720033 := by
  unfold tailWord_1079582
  simp only [CollatzResearch.WordTrace]
  refine ⟨4921948796858283346454125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26250393583244177847755333 4921948796858283346454125)
  ·
    refine ⟨1845730798821856254920297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4921948796858283346454125 1845730798821856254920297)
    ·
      refine ⟨1384298099116392191190223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1845730798821856254920297 1384298099116392191190223)
      ·
        refine ⟨2076447148674588286785335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1384298099116392191190223 2076447148674588286785335)
        ·
          refine ⟨3114670723011882430178003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2076447148674588286785335 3114670723011882430178003)
          ·
            refine ⟨4672006084517823645267005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3114670723011882430178003 4672006084517823645267005)
            ·
              refine ⟨1752002281694183866975127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4672006084517823645267005 1752002281694183866975127)
              ·
                refine ⟨2628003422541275800462691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1752002281694183866975127 2628003422541275800462691)
                ·
                  refine ⟨3942005133811913700694037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2628003422541275800462691 3942005133811913700694037)
                  ·
                    refine ⟨184781490647433454720033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3942005133811913700694037 184781490647433454720033)
                    ·
                      rfl

theorem cell23_1079582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_1079582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1079582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1079582 prefixEnd_1079582 := by exact prefixLift 1079582
  have htrace : WordTrace (prefixWord ++ tailWord_1079582) baseStart_1079582 baseEnd_1079582 := by
    simpa [prefixWord, tailWord_1079582, baseEnd_1079582] using wordTrace_append hprefix tailTrace_1079582
  have hstable : (prefixWord ++ tailWord_1079582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079582).length < 2 ^ (prefixWord ++ tailWord_1079582).sum := by decide
  have hdescent : baseEnd_1079582 < baseStart_1079582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079605 : List Nat := [1, 3, 3, 1, 2, 1, 1, 1, 6, 1, 3]
def baseStart_1079605 : Nat := 118140960795 + 1079605 * 2 ^ 59
def prefixEnd_1079605 : Nat := 4983230072969 + 3 ^ 40 * 1079605 * 2
def baseEnd_1079605 : Nat := 554356281997353774172493

theorem tailTrace_1079605 : CollatzResearch.WordTrace tailWord_1079605 prefixEnd_1079605 554356281997353774172493 := by
  unfold tailWord_1079605
  simp only [CollatzResearch.WordTrace]
  refine ⟨39376429253782941699720269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26250952835855294466480179 39376429253782941699720269)
  ·
    refine ⟨14766160970168603137395101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39376429253782941699720269 14766160970168603137395101)
    ·
      refine ⟨5537310363813226176523163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14766160970168603137395101 5537310363813226176523163)
      ·
        refine ⟨8305965545719839264784745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5537310363813226176523163 8305965545719839264784745)
        ·
          refine ⟨6229474159289879448588559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8305965545719839264784745 6229474159289879448588559)
          ·
            refine ⟨9344211238934819172882839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6229474159289879448588559 9344211238934819172882839)
            ·
              refine ⟨14016316858402228759324259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9344211238934819172882839 14016316858402228759324259)
              ·
                refine ⟨21024475287603343138986389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14016316858402228759324259 21024475287603343138986389)
                ·
                  refine ⟨985522279106406709639987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 21024475287603343138986389 985522279106406709639987)
                  ·
                    refine ⟨1478283418659610064459981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 985522279106406709639987 1478283418659610064459981)
                    ·
                      refine ⟨554356281997353774172493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1478283418659610064459981 554356281997353774172493)
                      ·
                        rfl

theorem cell23_1079605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 6, 1, 3].length) (baseStart_1079605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1079605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1079605 prefixEnd_1079605 := by exact prefixLift 1079605
  have htrace : WordTrace (prefixWord ++ tailWord_1079605) baseStart_1079605 baseEnd_1079605 := by
    simpa [prefixWord, tailWord_1079605, baseEnd_1079605] using wordTrace_append hprefix tailTrace_1079605
  have hstable : (prefixWord ++ tailWord_1079605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079605).length < 2 ^ (prefixWord ++ tailWord_1079605).sum := by decide
  have hdescent : baseEnd_1079605 < baseStart_1079605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079628 : List Nat := [2, 2, 1, 3, 2, 1, 2, 1, 2, 3, 4]
def baseStart_1079628 : Nat := 118140960795 + 1079628 * 2 ^ 59
def prefixEnd_1079628 : Nat := 4983230072969 + 3 ^ 40 * 1079628 * 2
def baseEnd_1079628 : Nat := 554368092052407184184887

theorem tailTrace_1079628 : CollatzResearch.WordTrace tailWord_1079628 prefixEnd_1079628 554368092052407184184887 := by
  unfold tailWord_1079628
  simp only [CollatzResearch.WordTrace]
  refine ⟨19688634066349808313903769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26251512088466411085205025 19688634066349808313903769)
  ·
    refine ⟨14766475549762356235427827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19688634066349808313903769 14766475549762356235427827)
    ·
      refine ⟨22149713324643534353141741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14766475549762356235427827 22149713324643534353141741)
      ·
        refine ⟨8306142496741325382428153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22149713324643534353141741 8306142496741325382428153)
        ·
          refine ⟨6229606872555994036821115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8306142496741325382428153 6229606872555994036821115)
          ·
            refine ⟨9344410308833991055231673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6229606872555994036821115 9344410308833991055231673)
            ·
              refine ⟨7008307731625493291423755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9344410308833991055231673 7008307731625493291423755)
              ·
                refine ⟨10512461597438239937135633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7008307731625493291423755 10512461597438239937135633)
                ·
                  refine ⟨7884346198078679952851725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10512461597438239937135633 7884346198078679952851725)
                  ·
                    refine ⟨2956629824279504982319397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7884346198078679952851725 2956629824279504982319397)
                    ·
                      refine ⟨554368092052407184184887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2956629824279504982319397 554368092052407184184887)
                      ·
                        rfl

theorem cell23_1079628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_1079628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1079628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1079628 prefixEnd_1079628 := by exact prefixLift 1079628
  have htrace : WordTrace (prefixWord ++ tailWord_1079628) baseStart_1079628 baseEnd_1079628 := by
    simpa [prefixWord, tailWord_1079628, baseEnd_1079628] using wordTrace_append hprefix tailTrace_1079628
  have hstable : (prefixWord ++ tailWord_1079628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079628).length < 2 ^ (prefixWord ++ tailWord_1079628).sum := by decide
  have hdescent : baseEnd_1079628 < baseStart_1079628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079705 : List Nat := [1, 2, 1, 2, 1, 4, 1, 2, 2, 5, 2]
def baseStart_1079705 : Nat := 118140960795 + 1079705 * 2 ^ 59
def prefixEnd_1079705 : Nat := 4983230072969 + 3 ^ 40 * 1079705 * 2
def baseEnd_1079705 : Nat := 554407630062803382922033

theorem tailTrace_1079705 : CollatzResearch.WordTrace tailWord_1079705 prefixEnd_1079705 554407630062803382922033 := by
  unfold tailWord_1079705
  simp only [CollatzResearch.WordTrace]
  refine ⟨39380076553420658778360569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26253384368947105852240379 39380076553420658778360569)
  ·
    refine ⟨29535057415065494083770427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39380076553420658778360569 29535057415065494083770427)
    ·
      refine ⟨44302586122598241125655641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29535057415065494083770427 44302586122598241125655641)
      ·
        refine ⟨33226939591948680844241731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44302586122598241125655641 33226939591948680844241731)
        ·
          refine ⟨49840409387923021266362597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33226939591948680844241731 49840409387923021266362597)
          ·
            refine ⟨9345076760235566487442987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49840409387923021266362597 9345076760235566487442987)
            ·
              refine ⟨14017615140353349731164481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9345076760235566487442987 14017615140353349731164481)
              ·
                refine ⟨10513211355265012298373361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14017615140353349731164481 10513211355265012298373361)
                ·
                  refine ⟨7884908516448759223780021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10513211355265012298373361 7884908516448759223780021)
                  ·
                    refine ⟨739210173417071177229377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7884908516448759223780021 739210173417071177229377)
                    ·
                      refine ⟨554407630062803382922033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 739210173417071177229377 554407630062803382922033)
                      ·
                        rfl

theorem cell23_1079705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 2, 5, 2].length) (baseStart_1079705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1079705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1079705 prefixEnd_1079705 := by exact prefixLift 1079705
  have htrace : WordTrace (prefixWord ++ tailWord_1079705) baseStart_1079705 baseEnd_1079705 := by
    simpa [prefixWord, tailWord_1079705, baseEnd_1079705] using wordTrace_append hprefix tailTrace_1079705
  have hstable : (prefixWord ++ tailWord_1079705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079705).length < 2 ^ (prefixWord ++ tailWord_1079705).sum := by decide
  have hdescent : baseEnd_1079705 < baseStart_1079705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079715 : List Nat := [1, 1, 1, 4, 1, 4, 3, 1, 2, 5]
def baseStart_1079715 : Nat := 118140960795 + 1079715 * 2 ^ 59
def prefixEnd_1079715 : Nat := 4983230072969 + 3 ^ 40 * 1079715 * 2
def baseEnd_1079715 : Nat := 184804254956449447932329

theorem tailTrace_1079715 : CollatzResearch.WordTrace tailWord_1079715 prefixEnd_1079715 184804254956449447932329 := by
  unfold tailWord_1079715
  simp only [CollatzResearch.WordTrace]
  refine ⟨39380441283384430486224599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26253627522256286990816399 39380441283384430486224599)
  ·
    refine ⟨59070661925076645729336899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39380441283384430486224599 59070661925076645729336899)
    ·
      refine ⟨88605992887614968594005349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59070661925076645729336899 88605992887614968594005349)
      ·
        refine ⟨16613623666427806611376003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 88605992887614968594005349 16613623666427806611376003)
        ·
          refine ⟨24920435499641709917064005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16613623666427806611376003 24920435499641709917064005)
          ·
            refine ⟨4672581656182820609449501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24920435499641709917064005 4672581656182820609449501)
            ·
              refine ⟨1752218121068557728543563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4672581656182820609449501 1752218121068557728543563)
              ·
                refine ⟨2628327181602836592815345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1752218121068557728543563 2628327181602836592815345)
                ·
                  refine ⟨1971245386202127444611509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2628327181602836592815345 1971245386202127444611509)
                  ·
                    refine ⟨184804254956449447932329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1971245386202127444611509 184804254956449447932329)
                    ·
                      rfl

theorem cell23_1079715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 1, 2, 5].length) (baseStart_1079715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1079715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1079715 prefixEnd_1079715 := by exact prefixLift 1079715
  have htrace : WordTrace (prefixWord ++ tailWord_1079715) baseStart_1079715 baseEnd_1079715 := by
    simpa [prefixWord, tailWord_1079715, baseEnd_1079715] using wordTrace_append hprefix tailTrace_1079715
  have hstable : (prefixWord ++ tailWord_1079715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079715).length < 2 ^ (prefixWord ++ tailWord_1079715).sum := by decide
  have hdescent : baseEnd_1079715 < baseStart_1079715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079738 : List Nat := [3, 1, 1, 1, 2, 1, 1, 3, 2, 3, 5]
def baseStart_1079738 : Nat := 118140960795 + 1079738 * 2 ^ 59
def prefixEnd_1079738 : Nat := 4983230072969 + 3 ^ 40 * 1079738 * 2
def baseEnd_1079738 : Nat := 554424574924401753809381

theorem tailTrace_1079738 : CollatzResearch.WordTrace tailWord_1079738 prefixEnd_1079738 554424574924401753809381 := by
  unfold tailWord_1079738
  simp only [CollatzResearch.WordTrace]
  refine ⟨9845320040575276353577967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26254186774867403609541245 9845320040575276353577967)
  ·
    refine ⟨14767980060862914530366951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9845320040575276353577967 14767980060862914530366951)
    ·
      refine ⟨22151970091294371795550427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14767980060862914530366951 22151970091294371795550427)
      ·
        refine ⟨33227955136941557693325641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22151970091294371795550427 33227955136941557693325641)
        ·
          refine ⟨24920966352706168269994231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33227955136941557693325641 24920966352706168269994231)
          ·
            refine ⟨37381449529059252404991347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24920966352706168269994231 37381449529059252404991347)
            ·
              refine ⟨56072174293588878607487021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37381449529059252404991347 56072174293588878607487021)
              ·
                refine ⟨21027065360095829477807633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56072174293588878607487021 21027065360095829477807633)
                ·
                  refine ⟨15770299020071872108355725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21027065360095829477807633 15770299020071872108355725)
                  ·
                    refine ⟨5913862132526952040633397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15770299020071872108355725 5913862132526952040633397)
                    ·
                      refine ⟨554424574924401753809381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5913862132526952040633397 554424574924401753809381)
                      ·
                        rfl

theorem cell23_1079738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 2, 3, 5].length) (baseStart_1079738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1079738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1079738 prefixEnd_1079738 := by exact prefixLift 1079738
  have htrace : WordTrace (prefixWord ++ tailWord_1079738) baseStart_1079738 baseEnd_1079738 := by
    simpa [prefixWord, tailWord_1079738, baseEnd_1079738] using wordTrace_append hprefix tailTrace_1079738
  have hstable : (prefixWord ++ tailWord_1079738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079738).length < 2 ^ (prefixWord ++ tailWord_1079738).sum := by decide
  have hdescent : baseEnd_1079738 < baseStart_1079738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079752 : List Nat := [2, 1, 3, 1, 3, 2, 2, 1, 2, 4, 2]
def baseStart_1079752 : Nat := 118140960795 + 1079752 * 2 ^ 59
def prefixEnd_1079752 : Nat := 4983230072969 + 3 ^ 40 * 1079752 * 2
def baseEnd_1079752 : Nat := 554431763653564699034317

theorem tailTrace_1079752 : CollatzResearch.WordTrace tailWord_1079752 prefixEnd_1079752 554431763653564699034317 := by
  unfold tailWord_1079752
  simp only [CollatzResearch.WordTrace]
  refine ⟨19690895392125192902660755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26254527189500257203547673 19690895392125192902660755)
  ·
    refine ⟨29536343088187789353991133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19690895392125192902660755 29536343088187789353991133)
    ·
      refine ⟨11076128658070421007746675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29536343088187789353991133 11076128658070421007746675)
      ·
        refine ⟨16614192987105631511620013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11076128658070421007746675 16614192987105631511620013)
        ·
          refine ⟨6230322370164611816857505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16614192987105631511620013 6230322370164611816857505)
          ·
            refine ⟨4672741777623458862643129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6230322370164611816857505 4672741777623458862643129)
            ·
              refine ⟨3504556333217594146982347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4672741777623458862643129 3504556333217594146982347)
              ·
                refine ⟨5256834499826391220473521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3504556333217594146982347 5256834499826391220473521)
                ·
                  refine ⟨3942625874869793415355141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5256834499826391220473521 3942625874869793415355141)
                  ·
                    refine ⟨739242351538086265379089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3942625874869793415355141 739242351538086265379089)
                    ·
                      refine ⟨554431763653564699034317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 739242351538086265379089 554431763653564699034317)
                      ·
                        rfl

theorem cell23_1079752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 1, 2, 4, 2].length) (baseStart_1079752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1079752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1079752 prefixEnd_1079752 := by exact prefixLift 1079752
  have htrace : WordTrace (prefixWord ++ tailWord_1079752) baseStart_1079752 baseEnd_1079752 := by
    simpa [prefixWord, tailWord_1079752, baseEnd_1079752] using wordTrace_append hprefix tailTrace_1079752
  have hstable : (prefixWord ++ tailWord_1079752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079752).length < 2 ^ (prefixWord ++ tailWord_1079752).sum := by decide
  have hdescent : baseEnd_1079752 < baseStart_1079752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079789 : List Nat := [1, 5, 1, 3, 1, 2, 1, 2, 2, 2, 3]
def baseStart_1079789 : Nat := 118140960795 + 1079789 * 2 ^ 59
def prefixEnd_1079789 : Nat := 4983230072969 + 3 ^ 40 * 1079789 * 2
def baseEnd_1079789 : Nat := 554450762437781054271647

theorem tailTrace_1079789 : CollatzResearch.WordTrace tailWord_1079789 prefixEnd_1079789 554450762437781054271647 := by
  unfold tailWord_1079789
  simp only [CollatzResearch.WordTrace]
  refine ⟨39383140285116341124418421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26255426856744227416278947 39383140285116341124418421)
  ·
    refine ⟨3692169401729656980414227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39383140285116341124418421 3692169401729656980414227)
    ·
      refine ⟨5538254102594485470621341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3692169401729656980414227 5538254102594485470621341)
      ·
        refine ⟨2076845288472932051483003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5538254102594485470621341 2076845288472932051483003)
        ·
          refine ⟨3115267932709398077224505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2076845288472932051483003 3115267932709398077224505)
          ·
            refine ⟨2336450949532048557918379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3115267932709398077224505 2336450949532048557918379)
            ·
              refine ⟨3504676424298072836877569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2336450949532048557918379 3504676424298072836877569)
              ·
                refine ⟨2628507318223554627658177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3504676424298072836877569 2628507318223554627658177)
                ·
                  refine ⟨1971380488667665970743633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2628507318223554627658177 1971380488667665970743633)
                  ·
                    refine ⟨1478535366500749478057725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1971380488667665970743633 1478535366500749478057725)
                    ·
                      refine ⟨554450762437781054271647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1478535366500749478057725 554450762437781054271647)
                      ·
                        rfl

theorem cell23_1079789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_1079789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1079789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1079789 prefixEnd_1079789 := by exact prefixLift 1079789
  have htrace : WordTrace (prefixWord ++ tailWord_1079789) baseStart_1079789 baseEnd_1079789 := by
    simpa [prefixWord, tailWord_1079789, baseEnd_1079789] using wordTrace_append hprefix tailTrace_1079789
  have hstable : (prefixWord ++ tailWord_1079789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079789).length < 2 ^ (prefixWord ++ tailWord_1079789).sum := by decide
  have hdescent : baseEnd_1079789 < baseStart_1079789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079802 : List Nat := [3, 1, 1, 1, 1, 2, 2, 5, 3, 1, 3]
def baseStart_1079802 : Nat := 118140960795 + 1079802 * 2 ^ 59
def prefixEnd_1079802 : Nat := 4983230072969 + 3 ^ 40 * 1079802 * 2
def baseEnd_1079802 : Nat := 554457437686289503409087

theorem tailTrace_1079802 : CollatzResearch.WordTrace tailWord_1079802 prefixEnd_1079802 554457437686289503409087 := by
  unfold tailWord_1079802
  simp only [CollatzResearch.WordTrace]
  refine ⟨9845903608517311086160415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26255742956046162896427773 9845903608517311086160415)
  ·
    refine ⟨14768855412775966629240623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9845903608517311086160415 14768855412775966629240623)
    ·
      refine ⟨22153283119163949943860935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14768855412775966629240623 22153283119163949943860935)
      ·
        refine ⟨33229924678745924915791403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22153283119163949943860935 33229924678745924915791403)
        ·
          refine ⟨49844887018118887373687105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33229924678745924915791403 49844887018118887373687105)
          ·
            refine ⟨37383665263589165530265329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49844887018118887373687105 37383665263589165530265329)
            ·
              refine ⟨28037748947691874147698997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37383665263589165530265329 28037748947691874147698997)
              ·
                refine ⟨2628538963846113201346781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28037748947691874147698997 2628538963846113201346781)
                ·
                  refine ⟨985702111442292450505043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2628538963846113201346781 985702111442292450505043)
                  ·
                    refine ⟨1478553167163438675757565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 985702111442292450505043 1478553167163438675757565)
                    ·
                      refine ⟨554457437686289503409087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1478553167163438675757565 554457437686289503409087)
                      ·
                        rfl

theorem cell23_1079802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 5, 3, 1, 3].length) (baseStart_1079802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1079802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1079802 prefixEnd_1079802 := by exact prefixLift 1079802
  have htrace : WordTrace (prefixWord ++ tailWord_1079802) baseStart_1079802 baseEnd_1079802 := by
    simpa [prefixWord, tailWord_1079802, baseEnd_1079802] using wordTrace_append hprefix tailTrace_1079802
  have hstable : (prefixWord ++ tailWord_1079802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079802).length < 2 ^ (prefixWord ++ tailWord_1079802).sum := by decide
  have hdescent : baseEnd_1079802 < baseStart_1079802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079805 : List Nat := [1, 4, 1, 1, 1, 3, 2, 2, 3, 5]
def baseStart_1079805 : Nat := 118140960795 + 1079805 * 2 ^ 59
def prefixEnd_1079805 : Nat := 4983230072969 + 3 ^ 40 * 1079805 * 2
def baseEnd_1079805 : Nat := 184819659376084330557191

theorem tailTrace_1079805 : CollatzResearch.WordTrace tailWord_1079805 prefixEnd_1079805 184819659376084330557191 := by
  unfold tailWord_1079805
  simp only [CollatzResearch.WordTrace]
  refine ⟨39383723853058375857000869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26255815902038917238000579 39383723853058375857000869)
  ·
    refine ⟨7384448222448445473187663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39383723853058375857000869 7384448222448445473187663)
    ·
      refine ⟨11076672333672668209781495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7384448222448445473187663 11076672333672668209781495)
      ·
        refine ⟨16615008500509002314672243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11076672333672668209781495 16615008500509002314672243)
        ·
          refine ⟨24922512750763503472008365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16615008500509002314672243 24922512750763503472008365)
          ·
            refine ⟨9345942281536313802003137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24922512750763503472008365 9345942281536313802003137)
            ·
              refine ⟨7009456711152235351502353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9345942281536313802003137 7009456711152235351502353)
              ·
                refine ⟨5257092533364176513626765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7009456711152235351502353 5257092533364176513626765)
                ·
                  refine ⟨1971409700011566192610037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5257092533364176513626765 1971409700011566192610037)
                  ·
                    refine ⟨184819659376084330557191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1971409700011566192610037 184819659376084330557191)
                    ·
                      rfl

theorem cell23_1079805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 2, 3, 5].length) (baseStart_1079805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1079805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1079805 prefixEnd_1079805 := by exact prefixLift 1079805
  have htrace : WordTrace (prefixWord ++ tailWord_1079805) baseStart_1079805 baseEnd_1079805 := by
    simpa [prefixWord, tailWord_1079805, baseEnd_1079805] using wordTrace_append hprefix tailTrace_1079805
  have hstable : (prefixWord ++ tailWord_1079805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079805).length < 2 ^ (prefixWord ++ tailWord_1079805).sum := by decide
  have hdescent : baseEnd_1079805 < baseStart_1079805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079808 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 10]
def baseStart_1079808 : Nat := 118140960795 + 1079808 * 2 ^ 59
def prefixEnd_1079808 : Nat := 4983230072969 + 3 ^ 40 * 1079808 * 2
def baseEnd_1079808 : Nat := 554460518570216479934059

theorem tailTrace_1079808 : CollatzResearch.WordTrace tailWord_1079808 prefixEnd_1079808 554460518570216479934059 := by
  unfold tailWord_1079808
  simp only [CollatzResearch.WordTrace]
  refine ⟨19691916636023753684680039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26255888848031671579573385 19691916636023753684680039)
  ·
    refine ⟨29537874954035630527020059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19691916636023753684680039 29537874954035630527020059)
    ·
      refine ⟨44306812431053445790530089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29537874954035630527020059 44306812431053445790530089)
      ·
        refine ⟨33230109323290084342897567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44306812431053445790530089 33230109323290084342897567)
        ·
          refine ⟨49845163984935126514346351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33230109323290084342897567 49845163984935126514346351)
          ·
            refine ⟨74767745977402689771519527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49845163984935126514346351 74767745977402689771519527)
            ·
              refine ⟨112151618966104034657279291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74767745977402689771519527 112151618966104034657279291)
              ·
                refine ⟨168227428449156051985918937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 112151618966104034657279291 168227428449156051985918937)
                ·
                  refine ⟨126170571336867038989439203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 168227428449156051985918937 126170571336867038989439203)
                  ·
                    refine ⟨189255857005300558484158805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 126170571336867038989439203 189255857005300558484158805)
                    ·
                      refine ⟨554460518570216479934059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 189255857005300558484158805 554460518570216479934059)
                      ·
                        rfl

theorem cell23_1079808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 10].length) (baseStart_1079808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1079808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1079808 prefixEnd_1079808 := by exact prefixLift 1079808
  have htrace : WordTrace (prefixWord ++ tailWord_1079808) baseStart_1079808 baseEnd_1079808 := by
    simpa [prefixWord, tailWord_1079808, baseEnd_1079808] using wordTrace_append hprefix tailTrace_1079808
  have hstable : (prefixWord ++ tailWord_1079808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079808).length < 2 ^ (prefixWord ++ tailWord_1079808).sum := by decide
  have hdescent : baseEnd_1079808 < baseStart_1079808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079809 : List Nat := [1, 2, 4, 1, 3, 3, 2, 1, 6]
def baseStart_1079809 : Nat := 118140960795 + 1079809 * 2 ^ 59
def prefixEnd_1079809 : Nat := 4983230072969 + 3 ^ 40 * 1079809 * 2
def baseEnd_1079809 : Nat := 61606781338985664002395

theorem tailTrace_1079809 : CollatzResearch.WordTrace tailWord_1079809 prefixEnd_1079809 61606781338985664002395 := by
  unfold tailWord_1079809
  simp only [CollatzResearch.WordTrace]
  refine ⟨39383869745043884540146481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26255913163362589693430987 39383869745043884540146481)
  ·
    refine ⟨29537902308782913405109861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39383869745043884540146481 29537902308782913405109861)
    ·
      refine ⟨5538356682896796263458099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29537902308782913405109861 5538356682896796263458099)
      ·
        refine ⟨8307535024345194395187149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5538356682896796263458099 8307535024345194395187149)
        ·
          refine ⟨3115325634129447898195181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8307535024345194395187149 3115325634129447898195181)
          ·
            refine ⟨1168247112798542961823193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3115325634129447898195181 1168247112798542961823193)
            ·
              refine ⟨876185334598907221367395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1168247112798542961823193 876185334598907221367395)
              ·
                refine ⟨1314278001898360832051093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 876185334598907221367395 1314278001898360832051093)
                ·
                  refine ⟨61606781338985664002395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1314278001898360832051093 61606781338985664002395)
                  ·
                    rfl

theorem cell23_1079809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 2, 1, 6].length) (baseStart_1079809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1079809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1079809 prefixEnd_1079809 := by exact prefixLift 1079809
  have htrace : WordTrace (prefixWord ++ tailWord_1079809) baseStart_1079809 baseEnd_1079809 := by
    simpa [prefixWord, tailWord_1079809, baseEnd_1079809] using wordTrace_append hprefix tailTrace_1079809
  have hstable : (prefixWord ++ tailWord_1079809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079809).length < 2 ^ (prefixWord ++ tailWord_1079809).sum := by decide
  have hdescent : baseEnd_1079809 < baseStart_1079809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079822 : List Nat := [4, 1, 1, 2, 3, 2, 1, 1, 3, 5]
def baseStart_1079822 : Nat := 118140960795 + 1079822 * 2 ^ 59
def prefixEnd_1079822 : Nat := 4983230072969 + 3 ^ 40 * 1079822 * 2
def baseEnd_1079822 : Nat := 184822569099793141719665

theorem tailTrace_1079822 : CollatzResearch.WordTrace tailWord_1079822 prefixEnd_1079822 184822569099793141719665 := by
  unfold tailWord_1079822
  simp only [CollatzResearch.WordTrace]
  refine ⟨4923042986749598470046215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26256229262664525173579813 4923042986749598470046215)
  ·
    refine ⟨7384564480124397705069323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4923042986749598470046215 7384564480124397705069323)
    ·
      refine ⟨11076846720186596557603985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7384564480124397705069323 11076846720186596557603985)
      ·
        refine ⟨8307635040139947418202989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11076846720186596557603985 8307635040139947418202989)
        ·
          refine ⟨3115363140052480281826121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8307635040139947418202989 3115363140052480281826121)
          ·
            refine ⟨2336522355039360211369591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3115363140052480281826121 2336522355039360211369591)
            ·
              refine ⟨3504783532559040317054387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2336522355039360211369591 3504783532559040317054387)
              ·
                refine ⟨5257175298838560475581581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3504783532559040317054387 5257175298838560475581581)
                ·
                  refine ⟨1971440737064460178343093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5257175298838560475581581 1971440737064460178343093)
                  ·
                    refine ⟨184822569099793141719665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1971440737064460178343093 184822569099793141719665)
                    ·
                      rfl

theorem cell23_1079822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 1, 3, 5].length) (baseStart_1079822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1079822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1079822 prefixEnd_1079822 := by exact prefixLift 1079822
  have htrace : WordTrace (prefixWord ++ tailWord_1079822) baseStart_1079822 baseEnd_1079822 := by
    simpa [prefixWord, tailWord_1079822, baseEnd_1079822] using wordTrace_append hprefix tailTrace_1079822
  have hstable : (prefixWord ++ tailWord_1079822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079822).length < 2 ^ (prefixWord ++ tailWord_1079822).sum := by decide
  have hdescent : baseEnd_1079822 < baseStart_1079822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079829 : List Nat := [1, 3, 2, 1, 3, 1, 4, 1, 2, 3, 2]
def baseStart_1079829 : Nat := 118140960795 + 1079829 * 2 ^ 59
def prefixEnd_1079829 : Nat := 4983230072969 + 3 ^ 40 * 1079829 * 2
def baseEnd_1079829 : Nat := 554471301663960897771463

theorem tailTrace_1079829 : CollatzResearch.WordTrace tailWord_1079829 prefixEnd_1079829 554471301663960897771463 := by
  unfold tailWord_1079829
  simp only [CollatzResearch.WordTrace]
  refine ⟨39384599204971427955874541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26256399469980951970583027 39384599204971427955874541)
  ·
    refine ⟨14769224701864285483452953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39384599204971427955874541 14769224701864285483452953)
    ·
      refine ⟨11076918526398214112589715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14769224701864285483452953 11076918526398214112589715)
      ·
        refine ⟨16615377789597321168884573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11076918526398214112589715 16615377789597321168884573)
        ·
          refine ⟨6230766671098995438331715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16615377789597321168884573 6230766671098995438331715)
          ·
            refine ⟨9346150006648493157497573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6230766671098995438331715 9346150006648493157497573)
            ·
              refine ⟨1752403126246592467030795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9346150006648493157497573 1752403126246592467030795)
              ·
                refine ⟨2628604689369888700546193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1752403126246592467030795 2628604689369888700546193)
                ·
                  refine ⟨1971453517027416525409645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2628604689369888700546193 1971453517027416525409645)
                  ·
                    refine ⟨739295068885281197028617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1971453517027416525409645 739295068885281197028617)
                    ·
                      refine ⟨554471301663960897771463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 739295068885281197028617 554471301663960897771463)
                      ·
                        rfl

theorem cell23_1079829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 1, 2, 3, 2].length) (baseStart_1079829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1079829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1079829 prefixEnd_1079829 := by exact prefixLift 1079829
  have htrace : WordTrace (prefixWord ++ tailWord_1079829) baseStart_1079829 baseEnd_1079829 := by
    simpa [prefixWord, tailWord_1079829, baseEnd_1079829] using wordTrace_append hprefix tailTrace_1079829
  have hstable : (prefixWord ++ tailWord_1079829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079829).length < 2 ^ (prefixWord ++ tailWord_1079829).sum := by decide
  have hdescent : baseEnd_1079829 < baseStart_1079829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079847 : List Nat := [1, 1, 7, 2, 2, 1, 2, 2, 1, 4]
def baseStart_1079847 : Nat := 118140960795 + 1079847 * 2 ^ 59
def prefixEnd_1079847 : Nat := 4983230072969 + 3 ^ 40 * 1079847 * 2
def baseEnd_1079847 : Nat := 184826848105247275782127

theorem tailTrace_1079847 : CollatzResearch.WordTrace tailWord_1079847 prefixEnd_1079847 184826848105247275782127 := by
  unfold tailWord_1079847
  simp only [CollatzResearch.WordTrace]
  refine ⟨39385255718906217030029795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26256837145937478020019863 39385255718906217030029795)
  ·
    refine ⟨59077883578359325545044693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39385255718906217030029795 59077883578359325545044693)
    ·
      refine ⟨1384637896367796692461985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 59077883578359325545044693 1384637896367796692461985)
      ·
        refine ⟨1038478422275847519346489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1384637896367796692461985 1038478422275847519346489)
        ·
          refine ⟨778858816706885639509867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1038478422275847519346489 778858816706885639509867)
          ·
            refine ⟨1168288225060328459264801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 778858816706885639509867 1168288225060328459264801)
            ·
              refine ⟨876216168795246344448601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1168288225060328459264801 876216168795246344448601)
              ·
                refine ⟨657162126596434758336451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 876216168795246344448601 657162126596434758336451)
                ·
                  refine ⟨985743189894652137504677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 657162126596434758336451 985743189894652137504677)
                  ·
                    refine ⟨184826848105247275782127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 985743189894652137504677 184826848105247275782127)
                    ·
                      rfl

theorem cell23_1079847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_1079847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1079847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1079847 prefixEnd_1079847 := by exact prefixLift 1079847
  have htrace : WordTrace (prefixWord ++ tailWord_1079847) baseStart_1079847 baseEnd_1079847 := by
    simpa [prefixWord, tailWord_1079847, baseEnd_1079847] using wordTrace_append hprefix tailTrace_1079847
  have hstable : (prefixWord ++ tailWord_1079847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079847).length < 2 ^ (prefixWord ++ tailWord_1079847).sum := by decide
  have hdescent : baseEnd_1079847 < baseStart_1079847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079859 : List Nat := [1, 1, 1, 2, 4, 2, 2, 3, 3, 2, 2]
def baseStart_1079859 : Nat := 118140960795 + 1079859 * 2 ^ 59
def prefixEnd_1079859 : Nat := 4983230072969 + 3 ^ 40 * 1079859 * 2
def baseEnd_1079859 : Nat := 554486706083595780396325

theorem tailTrace_1079859 : CollatzResearch.WordTrace tailWord_1079859 prefixEnd_1079859 554486706083595780396325 := by
  unfold tailWord_1079859
  simp only [CollatzResearch.WordTrace]
  refine ⟨39385693394862743079466631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26257128929908495386311087 39385693394862743079466631)
  ·
    refine ⟨59078540092294114619199947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39385693394862743079466631 59078540092294114619199947)
    ·
      refine ⟨88617810138441171928799921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59078540092294114619199947 88617810138441171928799921)
      ·
        refine ⟨66463357603830878946599941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88617810138441171928799921 66463357603830878946599941)
        ·
          refine ⟨12461879550718289802487489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66463357603830878946599941 12461879550718289802487489)
          ·
            refine ⟨9346409663038717351865617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12461879550718289802487489 9346409663038717351865617)
            ·
              refine ⟨7009807247279038013899213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9346409663038717351865617 7009807247279038013899213)
              ·
                refine ⟨2628677717729639255212205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7009807247279038013899213 2628677717729639255212205)
                ·
                  refine ⟨985754144148614720704577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2628677717729639255212205 985754144148614720704577)
                  ·
                    refine ⟨739315608111461040528433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 985754144148614720704577 739315608111461040528433)
                    ·
                      refine ⟨554486706083595780396325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 739315608111461040528433 554486706083595780396325)
                      ·
                        rfl

theorem cell23_1079859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 3, 3, 2, 2].length) (baseStart_1079859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1079859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1079859 prefixEnd_1079859 := by exact prefixLift 1079859
  have htrace : WordTrace (prefixWord ++ tailWord_1079859) baseStart_1079859 baseEnd_1079859 := by
    simpa [prefixWord, tailWord_1079859, baseEnd_1079859] using wordTrace_append hprefix tailTrace_1079859
  have hstable : (prefixWord ++ tailWord_1079859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079859).length < 2 ^ (prefixWord ++ tailWord_1079859).sum := by decide
  have hdescent : baseEnd_1079859 < baseStart_1079859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079869 : List Nat := [1, 4, 1, 3, 2, 1, 2, 3, 2, 4]
def baseStart_1079869 : Nat := 118140960795 + 1079869 * 2 ^ 59
def prefixEnd_1079869 : Nat := 4983230072969 + 3 ^ 40 * 1079869 * 2
def baseEnd_1079869 : Nat := 184830613630046913757093

theorem tailTrace_1079869 : CollatzResearch.WordTrace tailWord_1079869 prefixEnd_1079869 184830613630046913757093 := by
  unfold tailWord_1079869
  simp only [CollatzResearch.WordTrace]
  refine ⟨39386058124826514787330661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26257372083217676524887107 39386058124826514787330661)
  ·
    refine ⟨7384885898404971522624499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39386058124826514787330661 7384885898404971522624499)
    ·
      refine ⟨11077328847607457283936749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7384885898404971522624499 11077328847607457283936749)
      ·
        refine ⟨4153998317852796481476281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11077328847607457283936749 4153998317852796481476281)
        ·
          refine ⟨3115498738389597361107211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4153998317852796481476281 3115498738389597361107211)
          ·
            refine ⟨4673248107584396041660817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3115498738389597361107211 4673248107584396041660817)
            ·
              refine ⟨3504936080688297031245613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4673248107584396041660817 3504936080688297031245613)
              ·
                refine ⟨1314351030258111386717105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3504936080688297031245613 1314351030258111386717105)
                ·
                  refine ⟨985763272693583540037829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1314351030258111386717105 985763272693583540037829)
                  ·
                    refine ⟨184830613630046913757093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 985763272693583540037829 184830613630046913757093)
                    ·
                      rfl

theorem cell23_1079869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 3, 2, 4].length) (baseStart_1079869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1079869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1079869 prefixEnd_1079869 := by exact prefixLift 1079869
  have htrace : WordTrace (prefixWord ++ tailWord_1079869) baseStart_1079869 baseEnd_1079869 := by
    simpa [prefixWord, tailWord_1079869, baseEnd_1079869] using wordTrace_append hprefix tailTrace_1079869
  have hstable : (prefixWord ++ tailWord_1079869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079869).length < 2 ^ (prefixWord ++ tailWord_1079869).sum := by decide
  have hdescent : baseEnd_1079869 < baseStart_1079869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079882 : List Nat := [3, 1, 2, 1, 1, 5, 3, 7]
def baseStart_1079882 : Nat := 118140960795 + 1079882 * 2 ^ 59
def prefixEnd_1079882 : Nat := 4983230072969 + 3 ^ 40 * 1079882 * 2
def baseEnd_1079882 : Nat := 20536982079209229274397

theorem tailTrace_1079882 : CollatzResearch.WordTrace tailWord_1079882 prefixEnd_1079882 20536982079209229274397 := by
  unfold tailWord_1079882
  simp only [CollatzResearch.WordTrace]
  refine ⟨9846633068444854501888475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26257688182519612005035933 9846633068444854501888475)
  ·
    refine ⟨14769949602667281752832713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9846633068444854501888475 14769949602667281752832713)
    ·
      refine ⟨11077462202000461314624535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14769949602667281752832713 11077462202000461314624535)
      ·
        refine ⟨16616193303000691971936803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11077462202000461314624535 16616193303000691971936803)
        ·
          refine ⟨24924289954501037957905205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16616193303000691971936803 24924289954501037957905205)
          ·
            refine ⟨2336652183234472308553613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24924289954501037957905205 2336652183234472308553613)
            ·
              refine ⟨876244568712927115707605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2336652183234472308553613 876244568712927115707605)
              ·
                refine ⟨20536982079209229274397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 876244568712927115707605 20536982079209229274397)
                ·
                  rfl

theorem cell23_1079882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 3, 7].length) (baseStart_1079882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1079882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1079882 prefixEnd_1079882 := by exact prefixLift 1079882
  have htrace : WordTrace (prefixWord ++ tailWord_1079882) baseStart_1079882 baseEnd_1079882 := by
    simpa [prefixWord, tailWord_1079882, baseEnd_1079882] using wordTrace_append hprefix tailTrace_1079882
  have hstable : (prefixWord ++ tailWord_1079882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079882).length < 2 ^ (prefixWord ++ tailWord_1079882).sum := by decide
  have hdescent : baseEnd_1079882 < baseStart_1079882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079915 : List Nat := [1, 1, 1, 1, 2, 2, 1, 5, 2, 3, 4]
def baseStart_1079915 : Nat := 118140960795 + 1079915 * 2 ^ 59
def prefixEnd_1079915 : Nat := 4983230072969 + 3 ^ 40 * 1079915 * 2
def baseEnd_1079915 : Nat := 554515461000247561296067

theorem tailTrace_1079915 : CollatzResearch.WordTrace tailWord_1079915 prefixEnd_1079915 554515461000247561296067 := by
  unfold tailWord_1079915
  simp only [CollatzResearch.WordTrace]
  refine ⟨39387735882659864643505199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26258490588439909762336799 39387735882659864643505199)
  ·
    refine ⟨59081603823989796965257799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39387735882659864643505199 59081603823989796965257799)
    ·
      refine ⟨88622405735984695447886699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59081603823989796965257799 88622405735984695447886699)
      ·
        refine ⟨132933608603977043171830049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88622405735984695447886699 132933608603977043171830049)
        ·
          refine ⟨99700206452982782378872537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132933608603977043171830049 99700206452982782378872537)
          ·
            refine ⟨74775154839737086784154403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99700206452982782378872537 74775154839737086784154403)
            ·
              refine ⟨112162732259605630176231605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74775154839737086784154403 112162732259605630176231605)
              ·
                refine ⟨10515256149338027829021713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 112162732259605630176231605 10515256149338027829021713)
                ·
                  refine ⟨7886442112003520871766285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10515256149338027829021713 7886442112003520871766285)
                  ·
                    refine ⟨2957415792001320326912357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7886442112003520871766285 2957415792001320326912357)
                    ·
                      refine ⟨554515461000247561296067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2957415792001320326912357 554515461000247561296067)
                      ·
                        rfl

theorem cell23_1079915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 2, 3, 4].length) (baseStart_1079915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1079915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1079915 prefixEnd_1079915 := by exact prefixLift 1079915
  have htrace : WordTrace (prefixWord ++ tailWord_1079915) baseStart_1079915 baseEnd_1079915 := by
    simpa [prefixWord, tailWord_1079915, baseEnd_1079915] using wordTrace_append hprefix tailTrace_1079915
  have hstable : (prefixWord ++ tailWord_1079915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079915).length < 2 ^ (prefixWord ++ tailWord_1079915).sum := by decide
  have hdescent : baseEnd_1079915 < baseStart_1079915 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079936 : List Nat := [2, 1, 1, 2, 1, 6, 2, 2, 1, 3, 2]
def baseStart_1079936 : Nat := 118140960795 + 1079936 * 2 ^ 59
def prefixEnd_1079936 : Nat := 4983230072969 + 3 ^ 40 * 1079936 * 2
def baseEnd_1079936 : Nat := 554526244093991979133471

theorem tailTrace_1079936 : CollatzResearch.WordTrace tailWord_1079936 prefixEnd_1079936 554526244093991979133471 := by
  unfold tailWord_1079936
  simp only [CollatzResearch.WordTrace]
  refine ⟨19694250907791892615009831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26259001210389190153346441 19694250907791892615009831)
  ·
    refine ⟨29541376361687838922514747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19694250907791892615009831 29541376361687838922514747)
    ·
      refine ⟨44312064542531758383772121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29541376361687838922514747 44312064542531758383772121)
      ·
        refine ⟨33234048406898818787829091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44312064542531758383772121 33234048406898818787829091)
        ·
          refine ⟨49851072610348228181743637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33234048406898818787829091 49851072610348228181743637)
          ·
            refine ⟨2336769028610073196019233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 49851072610348228181743637 2336769028610073196019233)
            ·
              refine ⟨1752576771457554897014425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2336769028610073196019233 1752576771457554897014425)
              ·
                refine ⟨1314432578593166172760819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1752576771457554897014425 1314432578593166172760819)
                ·
                  refine ⟨1971648867889749259141229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1314432578593166172760819 1971648867889749259141229)
                  ·
                    refine ⟨739368325458655972177961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1971648867889749259141229 739368325458655972177961)
                    ·
                      refine ⟨554526244093991979133471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 739368325458655972177961 554526244093991979133471)
                      ·
                        rfl

theorem cell23_1079936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 2, 1, 3, 2].length) (baseStart_1079936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1079936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1079936 prefixEnd_1079936 := by exact prefixLift 1079936
  have htrace : WordTrace (prefixWord ++ tailWord_1079936) baseStart_1079936 baseEnd_1079936 := by
    simpa [prefixWord, tailWord_1079936, baseEnd_1079936] using wordTrace_append hprefix tailTrace_1079936
  have hstable : (prefixWord ++ tailWord_1079936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079936).length < 2 ^ (prefixWord ++ tailWord_1079936).sum := by decide
  have hdescent : baseEnd_1079936 < baseStart_1079936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079983 : List Nat := [1, 1, 2, 1, 2, 5, 4, 1, 2, 2, 2]
def baseStart_1079983 : Nat := 118140960795 + 1079983 * 2 ^ 59
def prefixEnd_1079983 : Nat := 4983230072969 + 3 ^ 40 * 1079983 * 2
def baseEnd_1079983 : Nat := 554550377684753295245755

theorem tailTrace_1079983 : CollatzResearch.WordTrace tailWord_1079983 prefixEnd_1079983 554550377684753295245755 := by
  unfold tailWord_1079983
  simp only [CollatzResearch.WordTrace]
  refine ⟨39390216046413512256980603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26260144030942341504653735 39390216046413512256980603)
  ·
    refine ⟨59085324069620268385470905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39390216046413512256980603 59085324069620268385470905)
    ·
      refine ⟨44313993052215201289103179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59085324069620268385470905 44313993052215201289103179)
      ·
        refine ⟨66470989578322801933654769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44313993052215201289103179 66470989578322801933654769)
        ·
          refine ⟨49853242183742101450241077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66470989578322801933654769 49853242183742101450241077)
          ·
            refine ⟨4673741454725822010960101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49853242183742101450241077 4673741454725822010960101)
            ·
              refine ⟨876326522761091627055019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4673741454725822010960101 876326522761091627055019)
              ·
                refine ⟨1314489784141637440582529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 876326522761091627055019 1314489784141637440582529)
                ·
                  refine ⟨985867338106228080436897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1314489784141637440582529 985867338106228080436897)
                  ·
                    refine ⟨739400503579671060327673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 985867338106228080436897 739400503579671060327673)
                    ·
                      refine ⟨554550377684753295245755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 739400503579671060327673 554550377684753295245755)
                      ·
                        rfl

theorem cell23_1079983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 4, 1, 2, 2, 2].length) (baseStart_1079983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1079983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1079983 prefixEnd_1079983 := by exact prefixLift 1079983
  have htrace : WordTrace (prefixWord ++ tailWord_1079983) baseStart_1079983 baseEnd_1079983 := by
    simpa [prefixWord, tailWord_1079983, baseEnd_1079983] using wordTrace_append hprefix tailTrace_1079983
  have hstable : (prefixWord ++ tailWord_1079983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079983).length < 2 ^ (prefixWord ++ tailWord_1079983).sum := by decide
  have hdescent : baseEnd_1079983 < baseStart_1079983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080049 : List Nat := [1, 2, 2, 2, 2, 2, 3, 2, 3, 4]
def baseStart_1080049 : Nat := 118140960795 + 1080049 * 2 ^ 59
def prefixEnd_1080049 : Nat := 4983230072969 + 3 ^ 40 * 1080049 * 2
def baseEnd_1080049 : Nat := 184861422469316679006817

theorem tailTrace_1080049 : CollatzResearch.WordTrace tailWord_1080049 prefixEnd_1080049 184861422469316679006817 := by
  unfold tailWord_1080049
  simp only [CollatzResearch.WordTrace]
  refine ⟨39392623264174405528883201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26261748842782937019255467 39392623264174405528883201)
  ·
    refine ⟨29544467448130804146662401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39392623264174405528883201 29544467448130804146662401)
    ·
      refine ⟨22158350586098103109996801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29544467448130804146662401 22158350586098103109996801)
      ·
        refine ⟨16618762939573577332497601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22158350586098103109996801 16618762939573577332497601)
        ·
          refine ⟨12464072204680182999373201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16618762939573577332497601 12464072204680182999373201)
          ·
            refine ⟨9348054153510137249529901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12464072204680182999373201 9348054153510137249529901)
            ·
              refine ⟨3505520307566301468573713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9348054153510137249529901 3505520307566301468573713)
              ·
                refine ⟨2629140230674726101430285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3505520307566301468573713 2629140230674726101430285)
                ·
                  refine ⟨985927586503022288036357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2629140230674726101430285 985927586503022288036357)
                  ·
                    refine ⟨184861422469316679006817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 985927586503022288036357 184861422469316679006817)
                    ·
                      rfl

theorem cell23_1080049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 2, 3, 4].length) (baseStart_1080049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1080049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1080049 prefixEnd_1080049 := by exact prefixLift 1080049
  have htrace : WordTrace (prefixWord ++ tailWord_1080049) baseStart_1080049 baseEnd_1080049 := by
    simpa [prefixWord, tailWord_1080049, baseEnd_1080049] using wordTrace_append hprefix tailTrace_1080049
  have hstable : (prefixWord ++ tailWord_1080049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080049).length < 2 ^ (prefixWord ++ tailWord_1080049).sum := by decide
  have hdescent : baseEnd_1080049 < baseStart_1080049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080053 : List Nat := [1, 3, 6, 1, 1, 1, 1, 1, 1, 7]
def baseStart_1080053 : Nat := 118140960795 + 1080053 * 2 ^ 59
def prefixEnd_1080053 : Nat := 4983230072969 + 3 ^ 40 * 1080053 * 2
def baseEnd_1080053 : Nat := 184862107110189340456811

theorem tailTrace_1080053 : CollatzResearch.WordTrace tailWord_1080053 prefixEnd_1080053 184862107110189340456811 := by
  unfold tailWord_1080053
  simp only [CollatzResearch.WordTrace]
  refine ⟨39392769156159914212028813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26261846104106609474685875 39392769156159914212028813)
  ·
    refine ⟨14772288433559967829510805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39392769156159914212028813 14772288433559967829510805)
    ·
      refine ⟨692451020323123492008319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 14772288433559967829510805 692451020323123492008319)
      ·
        refine ⟨1038676530484685238012479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 692451020323123492008319 1038676530484685238012479)
        ·
          refine ⟨1558014795727027857018719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1038676530484685238012479 1558014795727027857018719)
          ·
            refine ⟨2337022193590541785528079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1558014795727027857018719 2337022193590541785528079)
            ·
              refine ⟨3505533290385812678292119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2337022193590541785528079 3505533290385812678292119)
              ·
                refine ⟨5258299935578719017438179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3505533290385812678292119 5258299935578719017438179)
                ·
                  refine ⟨7887449903368078526157269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5258299935578719017438179 7887449903368078526157269)
                  ·
                    refine ⟨184862107110189340456811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7887449903368078526157269 184862107110189340456811)
                    ·
                      rfl

theorem cell23_1080053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_1080053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1080053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1080053 prefixEnd_1080053 := by exact prefixLift 1080053
  have htrace : WordTrace (prefixWord ++ tailWord_1080053) baseStart_1080053 baseEnd_1080053 := by
    simpa [prefixWord, tailWord_1080053, baseEnd_1080053] using wordTrace_append hprefix tailTrace_1080053
  have hstable : (prefixWord ++ tailWord_1080053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080053).length < 2 ^ (prefixWord ++ tailWord_1080053).sum := by decide
  have hdescent : baseEnd_1080053 < baseStart_1080053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080096 : List Nat := [2, 1, 1, 5, 1, 3, 3, 1, 6]
def baseStart_1080096 : Nat := 118140960795 + 1080096 * 2 ^ 59
def prefixEnd_1080096 : Nat := 4983230072969 + 3 ^ 40 * 1080096 * 2
def baseEnd_1080096 : Nat := 61623155666523483681415

theorem tailTrace_1080096 : CollatzResearch.WordTrace tailWord_1080096 prefixEnd_1080096 61623155666523483681415 := by
  unfold tailWord_1080096
  simp only [CollatzResearch.WordTrace]
  refine ⟨19697168747502066277922071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26262891663336088370562761 19697168747502066277922071)
  ·
    refine ⟨29545753121253099416883107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19697168747502066277922071 29545753121253099416883107)
    ·
      refine ⟨44318629681879649125324661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29545753121253099416883107 44318629681879649125324661)
      ·
        refine ⟨4154871532676217105499187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 44318629681879649125324661 4154871532676217105499187)
        ·
          refine ⟨6232307299014325658248781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4154871532676217105499187 6232307299014325658248781)
          ·
            refine ⟨2337115237130372121843293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6232307299014325658248781 2337115237130372121843293)
            ·
              refine ⟨876418213923889545691235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2337115237130372121843293 876418213923889545691235)
              ·
                refine ⟨1314627320885834318536853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 876418213923889545691235 1314627320885834318536853)
                ·
                  refine ⟨61623155666523483681415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1314627320885834318536853 61623155666523483681415)
                  ·
                    rfl

theorem cell23_1080096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 3, 1, 6].length) (baseStart_1080096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1080096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1080096 prefixEnd_1080096 := by exact prefixLift 1080096
  have htrace : WordTrace (prefixWord ++ tailWord_1080096) baseStart_1080096 baseEnd_1080096 := by
    simpa [prefixWord, tailWord_1080096, baseEnd_1080096] using wordTrace_append hprefix tailTrace_1080096
  have hstable : (prefixWord ++ tailWord_1080096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080096).length < 2 ^ (prefixWord ++ tailWord_1080096).sum := by decide
  have hdescent : baseEnd_1080096 < baseStart_1080096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080112 : List Nat := [2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 4]
def baseStart_1080112 : Nat := 118140960795 + 1080112 * 2 ^ 59
def prefixEnd_1080112 : Nat := 4983230072969 + 3 ^ 40 * 1080112 * 2
def baseEnd_1080112 : Nat := 554616616689183290532661

theorem tailTrace_1080112 : CollatzResearch.WordTrace tailWord_1080112 prefixEnd_1080112 554616616689183290532661 := by
  unfold tailWord_1080112
  simp only [CollatzResearch.WordTrace]
  refine ⟨19697460531473083644213295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26263280708630778192284393 19697460531473083644213295)
  ·
    refine ⟨29546190797209625466319943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19697460531473083644213295 29546190797209625466319943)
    ·
      refine ⟨44319286195814438199479915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29546190797209625466319943 44319286195814438199479915)
      ·
        refine ⟨66478929293721657299219873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44319286195814438199479915 66478929293721657299219873)
        ·
          refine ⟨49859196970291242974414905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66478929293721657299219873 49859196970291242974414905)
          ·
            refine ⟨37394397727718432230811179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49859196970291242974414905 37394397727718432230811179)
            ·
              refine ⟨56091596591577648346216769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37394397727718432230811179 56091596591577648346216769)
              ·
                refine ⟨42068697443683236259662577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56091596591577648346216769 42068697443683236259662577)
                ·
                  refine ⟨31551523082762427194746933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42068697443683236259662577 31551523082762427194746933)
                  ·
                    refine ⟨2957955289008977549507525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31551523082762427194746933 2957955289008977549507525)
                    ·
                      refine ⟨554616616689183290532661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2957955289008977549507525 554616616689183290532661)
                      ·
                        rfl

theorem cell23_1080112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 4].length) (baseStart_1080112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1080112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1080112 prefixEnd_1080112 := by exact prefixLift 1080112
  have htrace : WordTrace (prefixWord ++ tailWord_1080112) baseStart_1080112 baseEnd_1080112 := by
    simpa [prefixWord, tailWord_1080112, baseEnd_1080112] using wordTrace_append hprefix tailTrace_1080112
  have hstable : (prefixWord ++ tailWord_1080112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080112).length < 2 ^ (prefixWord ++ tailWord_1080112).sum := by decide
  have hdescent : baseEnd_1080112 < baseStart_1080112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080134 : List Nat := [6, 1, 1, 2, 2, 1, 3, 2, 1, 4]
def baseStart_1080134 : Nat := 118140960795 + 1080134 * 2 ^ 59
def prefixEnd_1080134 : Nat := 4983230072969 + 3 ^ 40 * 1080134 * 2
def baseEnd_1080134 : Nat := 184875971087860734819187

theorem tailTrace_1080134 : CollatzResearch.WordTrace tailWord_1080134 prefixEnd_1080134 184875971087860734819187 := by
  unfold tailWord_1080134
  simp only [CollatzResearch.WordTrace]
  refine ⟨1231116358402077032678983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 26263815645910976697151637 1231116358402077032678983)
  ·
    refine ⟨1846674537603115549018475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1231116358402077032678983 1846674537603115549018475)
    ·
      refine ⟨2770011806404673323527713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1846674537603115549018475 2770011806404673323527713)
      ·
        refine ⟨2077508854803504992645785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2770011806404673323527713 2077508854803504992645785)
        ·
          refine ⟨1558131641102628744484339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2077508854803504992645785 1558131641102628744484339)
          ·
            refine ⟨2337197461653943116726509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1558131641102628744484339 2337197461653943116726509)
            ·
              refine ⟨876449048120228668772441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2337197461653943116726509 876449048120228668772441)
              ·
                refine ⟨657336786090171501579331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 876449048120228668772441 657336786090171501579331)
                ·
                  refine ⟨986005179135257252368997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 657336786090171501579331 986005179135257252368997)
                  ·
                    refine ⟨184875971087860734819187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 986005179135257252368997 184875971087860734819187)
                    ·
                      rfl

theorem cell23_1080134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_1080134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1080134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1080134 prefixEnd_1080134 := by exact prefixLift 1080134
  have htrace : WordTrace (prefixWord ++ tailWord_1080134) baseStart_1080134 baseEnd_1080134 := by
    simpa [prefixWord, tailWord_1080134, baseEnd_1080134] using wordTrace_append hprefix tailTrace_1080134
  have hstable : (prefixWord ++ tailWord_1080134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080134).length < 2 ^ (prefixWord ++ tailWord_1080134).sum := by decide
  have hdescent : baseEnd_1080134 < baseStart_1080134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080149 : List Nat := [1, 3, 2, 2, 2, 1, 1, 4, 1, 1, 5]
def baseStart_1080149 : Nat := 118140960795 + 1080149 * 2 ^ 59
def prefixEnd_1080149 : Nat := 4983230072969 + 3 ^ 40 * 1080149 * 2
def baseEnd_1080149 : Nat := 554635615473399645769991

theorem tailTrace_1080149 : CollatzResearch.WordTrace tailWord_1080149 prefixEnd_1080149 554635615473399645769991 := by
  unfold tailWord_1080149
  simp only [CollatzResearch.WordTrace]
  refine ⟨39396270563812122607523501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26264180375874748405015667 39396270563812122607523501)
  ·
    refine ⟨14773601461429545977821313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39396270563812122607523501 14773601461429545977821313)
    ·
      refine ⟨11080201096072159483365985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14773601461429545977821313 11080201096072159483365985)
      ·
        refine ⟨8310150822054119612524489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11080201096072159483365985 8310150822054119612524489)
        ·
          refine ⟨6232613116540589709393367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8310150822054119612524489 6232613116540589709393367)
          ·
            refine ⟨9348919674810884564090051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6232613116540589709393367 9348919674810884564090051)
            ·
              refine ⟨14023379512216326846135077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9348919674810884564090051 14023379512216326846135077)
              ·
                refine ⟨2629383658540561283650327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14023379512216326846135077 2629383658540561283650327)
                ·
                  refine ⟨3944075487810841925475491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2629383658540561283650327 3944075487810841925475491)
                  ·
                    refine ⟨5916113231716262888213237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3944075487810841925475491 5916113231716262888213237)
                    ·
                      refine ⟨554635615473399645769991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5916113231716262888213237 554635615473399645769991)
                      ·
                        rfl

theorem cell23_1080149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_1080149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1080149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1080149 prefixEnd_1080149 := by exact prefixLift 1080149
  have htrace : WordTrace (prefixWord ++ tailWord_1080149) baseStart_1080149 baseEnd_1080149 := by
    simpa [prefixWord, tailWord_1080149, baseEnd_1080149] using wordTrace_append hprefix tailTrace_1080149
  have hstable : (prefixWord ++ tailWord_1080149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080149).length < 2 ^ (prefixWord ++ tailWord_1080149).sum := by decide
  have hdescent : baseEnd_1080149 < baseStart_1080149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080159 : List Nat := [1, 1, 2, 3, 1, 3, 2, 3, 1, 2, 4]
def baseStart_1080159 : Nat := 118140960795 + 1080159 * 2 ^ 59
def prefixEnd_1080159 : Nat := 4983230072969 + 3 ^ 40 * 1080159 * 2
def baseEnd_1080159 : Nat := 554640750279944606644945

theorem tailTrace_1080159 : CollatzResearch.WordTrace tailWord_1080159 prefixEnd_1080159 554640750279944606644945 := by
  unfold tailWord_1080159
  simp only [CollatzResearch.WordTrace]
  refine ⟨39396635293775894315387531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26264423529183929543591687 39396635293775894315387531)
  ·
    refine ⟨59094952940663841473081297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39396635293775894315387531 59094952940663841473081297)
    ·
      refine ⟨44321214705497881104810973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59094952940663841473081297 44321214705497881104810973)
      ·
        refine ⟨16620455514561705414304115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44321214705497881104810973 16620455514561705414304115)
        ·
          refine ⟨24930683271842558121456173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16620455514561705414304115 24930683271842558121456173)
          ·
            refine ⟨9349006226940959295546065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24930683271842558121456173 9349006226940959295546065)
            ·
              refine ⟨7011754670205719471659549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9349006226940959295546065 7011754670205719471659549)
              ·
                refine ⟨2629408001327144801872331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7011754670205719471659549 2629408001327144801872331)
                ·
                  refine ⟨3944112001990717202808497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2629408001327144801872331 3944112001990717202808497)
                  ·
                    refine ⟨2958084001493037902106373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3944112001990717202808497 2958084001493037902106373)
                    ·
                      refine ⟨554640750279944606644945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2958084001493037902106373 554640750279944606644945)
                      ·
                        rfl

theorem cell23_1080159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 3, 1, 2, 4].length) (baseStart_1080159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1080159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1080159 prefixEnd_1080159 := by exact prefixLift 1080159
  have htrace : WordTrace (prefixWord ++ tailWord_1080159) baseStart_1080159 baseEnd_1080159 := by
    simpa [prefixWord, tailWord_1080159, baseEnd_1080159] using wordTrace_append hprefix tailTrace_1080159
  have hstable : (prefixWord ++ tailWord_1080159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080159).length < 2 ^ (prefixWord ++ tailWord_1080159).sum := by decide
  have hdescent : baseEnd_1080159 < baseStart_1080159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080163 : List Nat := [1, 1, 1, 5, 3, 3, 1, 2, 1, 1, 4]
def baseStart_1080163 : Nat := 118140960795 + 1080163 * 2 ^ 59
def prefixEnd_1080163 : Nat := 4983230072969 + 3 ^ 40 * 1080163 * 2
def baseEnd_1080163 : Nat := 554642804202562590994927

theorem tailTrace_1080163 : CollatzResearch.WordTrace tailWord_1080163 prefixEnd_1080163 554642804202562590994927 := by
  unfold tailWord_1080163
  simp only [CollatzResearch.WordTrace]
  refine ⟨39396781185761402998533143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26264520790507601999022095 39396781185761402998533143)
  ·
    refine ⟨59095171778642104497799715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39396781185761402998533143 59095171778642104497799715)
    ·
      refine ⟨88642757667963156746699573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59095171778642104497799715 88642757667963156746699573)
      ·
        refine ⟨8310258531371545945003085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 88642757667963156746699573 8310258531371545945003085)
        ·
          refine ⟨3116346949264329729376157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8310258531371545945003085 3116346949264329729376157)
          ·
            refine ⟨1168630105974123648516059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3116346949264329729376157 1168630105974123648516059)
            ·
              refine ⟨1752945158961185472774089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1168630105974123648516059 1752945158961185472774089)
              ·
                refine ⟨1314708869220889104580567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1752945158961185472774089 1314708869220889104580567)
                ·
                  refine ⟨1972063303831333656870851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1314708869220889104580567 1972063303831333656870851)
                  ·
                    refine ⟨2958094955747000485306277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1972063303831333656870851 2958094955747000485306277)
                    ·
                      refine ⟨554642804202562590994927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2958094955747000485306277 554642804202562590994927)
                      ·
                        rfl

theorem cell23_1080163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 2, 1, 1, 4].length) (baseStart_1080163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1080163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1080163 prefixEnd_1080163 := by exact prefixLift 1080163
  have htrace : WordTrace (prefixWord ++ tailWord_1080163) baseStart_1080163 baseEnd_1080163 := by
    simpa [prefixWord, tailWord_1080163, baseEnd_1080163] using wordTrace_append hprefix tailTrace_1080163
  have hstable : (prefixWord ++ tailWord_1080163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080163).length < 2 ^ (prefixWord ++ tailWord_1080163).sum := by decide
  have hdescent : baseEnd_1080163 < baseStart_1080163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080179 : List Nat := [1, 1, 1, 2, 2, 1, 5, 1, 3, 3, 3]
def baseStart_1080179 : Nat := 118140960795 + 1080179 * 2 ^ 59
def prefixEnd_1080179 : Nat := 4983230072969 + 3 ^ 40 * 1080179 * 2
def baseEnd_1080179 : Nat := 554651019893034528394853

theorem tailTrace_1080179 : CollatzResearch.WordTrace tailWord_1080179 prefixEnd_1080179 554651019893034528394853 := by
  unfold tailWord_1080179
  simp only [CollatzResearch.WordTrace]
  refine ⟨39397364753703437731115591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26264909835802291820743727 39397364753703437731115591)
  ·
    refine ⟨59096047130555156596673387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39397364753703437731115591 59096047130555156596673387)
    ·
      refine ⟨88644070695832734895010081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59096047130555156596673387 88644070695832734895010081)
      ·
        refine ⟨66483053021874551171257561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88644070695832734895010081 66483053021874551171257561)
        ·
          refine ⟨49862289766405913378443171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66483053021874551171257561 49862289766405913378443171)
          ·
            refine ⟨74793434649608870067664757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49862289766405913378443171 74793434649608870067664757)
            ·
              refine ⟨7011884498400831568843571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 74793434649608870067664757 7011884498400831568843571)
              ·
                refine ⟨10517826747601247353265357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7011884498400831568843571 10517826747601247353265357)
                ·
                  refine ⟨3944185030350467757474509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10517826747601247353265357 3944185030350467757474509)
                  ·
                    refine ⟨1479069386381425409052941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3944185030350467757474509 1479069386381425409052941)
                    ·
                      refine ⟨554651019893034528394853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1479069386381425409052941 554651019893034528394853)
                      ·
                        rfl

theorem cell23_1080179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 3, 3, 3].length) (baseStart_1080179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1080179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1080179 prefixEnd_1080179 := by exact prefixLift 1080179
  have htrace : WordTrace (prefixWord ++ tailWord_1080179) baseStart_1080179 baseEnd_1080179 := by
    simpa [prefixWord, tailWord_1080179, baseEnd_1080179] using wordTrace_append hprefix tailTrace_1080179
  have hstable : (prefixWord ++ tailWord_1080179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080179).length < 2 ^ (prefixWord ++ tailWord_1080179).sum := by decide
  have hdescent : baseEnd_1080179 < baseStart_1080179 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080197 : List Nat := [1, 3, 1, 1, 3, 3, 4, 2, 1, 2, 2]
def baseStart_1080197 : Nat := 118140960795 + 1080197 * 2 ^ 59
def prefixEnd_1080197 : Nat := 4983230072969 + 3 ^ 40 * 1080197 * 2
def baseEnd_1080197 : Nat := 554660262544815457969771

theorem tailTrace_1080197 : CollatzResearch.WordTrace tailWord_1080197 prefixEnd_1080197 554660262544815457969771 := by
  unfold tailWord_1080197
  simp only [CollatzResearch.WordTrace]
  refine ⟨39398021267638226805270845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26265347511758817870180563 39398021267638226805270845)
  ·
    refine ⟨14774257975364335051976567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39398021267638226805270845 14774257975364335051976567)
    ·
      refine ⟨22161386963046502577964851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14774257975364335051976567 22161386963046502577964851)
      ·
        refine ⟨33242080444569753866947277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22161386963046502577964851 33242080444569753866947277)
        ·
          refine ⟨12465780166713657700105229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33242080444569753866947277 12465780166713657700105229)
          ·
            refine ⟨4674667562517621637539461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12465780166713657700105229 4674667562517621637539461)
            ·
              refine ⟨876500167972054057038649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4674667562517621637539461 876500167972054057038649)
              ·
                refine ⟨657375125979040542778987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 876500167972054057038649 657375125979040542778987)
                ·
                  refine ⟨986062688968560814168481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 657375125979040542778987 986062688968560814168481)
                  ·
                    refine ⟨739547016726420610626361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 986062688968560814168481 739547016726420610626361)
                    ·
                      refine ⟨554660262544815457969771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 739547016726420610626361 554660262544815457969771)
                      ·
                        rfl

theorem cell23_1080197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 4, 2, 1, 2, 2].length) (baseStart_1080197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1080197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1080197 prefixEnd_1080197 := by exact prefixLift 1080197
  have htrace : WordTrace (prefixWord ++ tailWord_1080197) baseStart_1080197 baseEnd_1080197 := by
    simpa [prefixWord, tailWord_1080197, baseEnd_1080197] using wordTrace_append hprefix tailTrace_1080197
  have hstable : (prefixWord ++ tailWord_1080197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080197).length < 2 ^ (prefixWord ++ tailWord_1080197).sum := by decide
  have hdescent : baseEnd_1080197 < baseStart_1080197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080199 : List Nat := [1, 1, 4, 2, 3, 1, 1, 1, 2, 7]
def baseStart_1080199 : Nat := 118140960795 + 1080199 * 2 ^ 59
def prefixEnd_1080199 : Nat := 4983230072969 + 3 ^ 40 * 1080199 * 2
def baseEnd_1080199 : Nat := 184887096502041483381587

theorem tailTrace_1080199 : CollatzResearch.WordTrace tailWord_1080199 prefixEnd_1080199 184887096502041483381587 := by
  unfold tailWord_1080199
  simp only [CollatzResearch.WordTrace]
  refine ⟨39398094213630981146843651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26265396142420654097895767 39398094213630981146843651)
  ·
    refine ⟨59097141320446471720265477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39398094213630981146843651 59097141320446471720265477)
    ·
      refine ⟨11080713997583713447549777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59097141320446471720265477 11080713997583713447549777)
      ·
        refine ⟨8310535498187785085662333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11080713997583713447549777 8310535498187785085662333)
        ·
          refine ⟨3116450811820419407123375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8310535498187785085662333 3116450811820419407123375)
          ·
            refine ⟨4674676217730629110685063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3116450811820419407123375 4674676217730629110685063)
            ·
              refine ⟨7012014326595943666027595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4674676217730629110685063 7012014326595943666027595)
              ·
                refine ⟨10518021489893915499041393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7012014326595943666027595 10518021489893915499041393)
                ·
                  refine ⟨7888516117420436624281045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10518021489893915499041393 7888516117420436624281045)
                  ·
                    refine ⟨184887096502041483381587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7888516117420436624281045 184887096502041483381587)
                    ·
                      rfl

theorem cell23_1080199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 2, 7].length) (baseStart_1080199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1080199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1080199 prefixEnd_1080199 := by exact prefixLift 1080199
  have htrace : WordTrace (prefixWord ++ tailWord_1080199) baseStart_1080199 baseEnd_1080199 := by
    simpa [prefixWord, tailWord_1080199, baseEnd_1080199] using wordTrace_append hprefix tailTrace_1080199
  have hstable : (prefixWord ++ tailWord_1080199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080199).length < 2 ^ (prefixWord ++ tailWord_1080199).sum := by decide
  have hdescent : baseEnd_1080199 < baseStart_1080199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080213 : List Nat := [1, 3, 2, 1, 1, 4, 2, 3, 2, 1, 3]
def baseStart_1080213 : Nat := 118140960795 + 1080213 * 2 ^ 59
def prefixEnd_1080213 : Nat := 4983230072969 + 3 ^ 40 * 1080213 * 2
def baseEnd_1080213 : Nat := 554668478235287395369697

theorem tailTrace_1080213 : CollatzResearch.WordTrace tailWord_1080213 prefixEnd_1080213 554668478235287395369697 := by
  unfold tailWord_1080213
  simp only [CollatzResearch.WordTrace]
  refine ⟨39398604835580261537853293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26265736557053507691902195 39398604835580261537853293)
  ·
    refine ⟨14774476813342598076694985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39398604835580261537853293 14774476813342598076694985)
    ·
      refine ⟨11080857610006948557521239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14774476813342598076694985 11080857610006948557521239)
      ·
        refine ⟨16621286415010422836281859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11080857610006948557521239 16621286415010422836281859)
        ·
          refine ⟨24931929622515634254422789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16621286415010422836281859 24931929622515634254422789)
          ·
            refine ⟨4674736804221681422704273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24931929622515634254422789 4674736804221681422704273)
            ·
              refine ⟨3506052603166261067028205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4674736804221681422704273 3506052603166261067028205)
              ·
                refine ⟨1314769726187347900135577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3506052603166261067028205 1314769726187347900135577)
                ·
                  refine ⟨986077294640510925101683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1314769726187347900135577 986077294640510925101683)
                  ·
                    refine ⟨1479115941960766387652525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 986077294640510925101683 1479115941960766387652525)
                    ·
                      refine ⟨554668478235287395369697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1479115941960766387652525 554668478235287395369697)
                      ·
                        rfl

theorem cell23_1080213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 3, 2, 1, 3].length) (baseStart_1080213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1080213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1080213 prefixEnd_1080213 := by exact prefixLift 1080213
  have htrace : WordTrace (prefixWord ++ tailWord_1080213) baseStart_1080213 baseEnd_1080213 := by
    simpa [prefixWord, tailWord_1080213, baseEnd_1080213] using wordTrace_append hprefix tailTrace_1080213
  have hstable : (prefixWord ++ tailWord_1080213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080213).length < 2 ^ (prefixWord ++ tailWord_1080213).sum := by decide
  have hdescent : baseEnd_1080213 < baseStart_1080213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080214 : List Nat := [5, 3, 1, 1, 1, 2, 1, 2, 3, 2, 2]
def baseStart_1080214 : Nat := 118140960795 + 1080214 * 2 ^ 59
def prefixEnd_1080214 : Nat := 4983230072969 + 3 ^ 40 * 1080214 * 2
def baseEnd_1080214 : Nat := 554668991715941891457193

theorem tailTrace_1080214 : CollatzResearch.WordTrace tailWord_1080214 prefixEnd_1080214 554668991715941891457193 := by
  unfold tailWord_1080214
  simp only [CollatzResearch.WordTrace]
  refine ⟨2462415081786039919289981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26265760872384425805759797 2462415081786039919289981)
  ·
    refine ⟨923405655669764969733743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2462415081786039919289981 923405655669764969733743)
    ·
      refine ⟨1385108483504647454600615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 923405655669764969733743 1385108483504647454600615)
      ·
        refine ⟨2077662725256971181900923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1385108483504647454600615 2077662725256971181900923)
        ·
          refine ⟨3116494087885456772851385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2077662725256971181900923 3116494087885456772851385)
          ·
            refine ⟨2337370565914092579638539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3116494087885456772851385 2337370565914092579638539)
            ·
              refine ⟨3506055848871138869457809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2337370565914092579638539 3506055848871138869457809)
              ·
                refine ⟨2629541886653354152093357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3506055848871138869457809 2629541886653354152093357)
                ·
                  refine ⟨986078207495007807035009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2629541886653354152093357 986078207495007807035009)
                  ·
                    refine ⟨739558655621255855276257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 986078207495007807035009 739558655621255855276257)
                    ·
                      refine ⟨554668991715941891457193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 739558655621255855276257 554668991715941891457193)
                      ·
                        rfl

theorem cell23_1080214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_1080214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1080214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1080214 prefixEnd_1080214 := by exact prefixLift 1080214
  have htrace : WordTrace (prefixWord ++ tailWord_1080214) baseStart_1080214 baseEnd_1080214 := by
    simpa [prefixWord, tailWord_1080214, baseEnd_1080214] using wordTrace_append hprefix tailTrace_1080214
  have hstable : (prefixWord ++ tailWord_1080214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080214).length < 2 ^ (prefixWord ++ tailWord_1080214).sum := by decide
  have hdescent : baseEnd_1080214 < baseStart_1080214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080223 : List Nat := [1, 1, 2, 5, 2, 1, 2, 1, 3, 3, 2]
def baseStart_1080223 : Nat := 118140960795 + 1080223 * 2 ^ 59
def prefixEnd_1080223 : Nat := 4983230072969 + 3 ^ 40 * 1080223 * 2
def baseEnd_1080223 : Nat := 554673613041832356244651

theorem tailTrace_1080223 : CollatzResearch.WordTrace tailWord_1080223 prefixEnd_1080223 554673613041832356244651 := by
  unfold tailWord_1080223
  simp only [CollatzResearch.WordTrace]
  refine ⟨39398969565544033245717323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26265979710362688830478215 39398969565544033245717323)
  ·
    refine ⟨59098454348316049868575985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39398969565544033245717323 59098454348316049868575985)
    ·
      refine ⟨44323840761237037401431989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59098454348316049868575985 44323840761237037401431989)
      ·
        refine ⟨4155360071365972256384249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 44323840761237037401431989 4155360071365972256384249)
        ·
          refine ⟨3116520053524479192288187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4155360071365972256384249 3116520053524479192288187)
          ·
            refine ⟨4674780080286718788432281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3116520053524479192288187 4674780080286718788432281)
            ·
              refine ⟨3506085060215039091324211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4674780080286718788432281 3506085060215039091324211)
              ·
                refine ⟨5259127590322558636986317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3506085060215039091324211 5259127590322558636986317)
                ·
                  refine ⟨1972172846370959488869869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5259127590322558636986317 1972172846370959488869869)
                  ·
                    refine ⟨739564817389109808326201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1972172846370959488869869 739564817389109808326201)
                    ·
                      refine ⟨554673613041832356244651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 739564817389109808326201 554673613041832356244651)
                      ·
                        rfl

theorem cell23_1080223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 1, 3, 3, 2].length) (baseStart_1080223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1080223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1080223 prefixEnd_1080223 := by exact prefixLift 1080223
  have htrace : WordTrace (prefixWord ++ tailWord_1080223) baseStart_1080223 baseEnd_1080223 := by
    simpa [prefixWord, tailWord_1080223, baseEnd_1080223] using wordTrace_append hprefix tailTrace_1080223
  have hstable : (prefixWord ++ tailWord_1080223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080223).length < 2 ^ (prefixWord ++ tailWord_1080223).sum := by decide
  have hdescent : baseEnd_1080223 < baseStart_1080223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080239 : List Nat := [1, 1, 2, 1, 2, 2, 2, 2, 1, 6, 3]
def baseStart_1080239 : Nat := 118140960795 + 1080239 * 2 ^ 59
def prefixEnd_1080239 : Nat := 4983230072969 + 3 ^ 40 * 1080239 * 2
def baseEnd_1080239 : Nat := 554681828732304293644577

theorem tailTrace_1080239 : CollatzResearch.WordTrace tailWord_1080239 prefixEnd_1080239 554681828732304293644577 := by
  unfold tailWord_1080239
  simp only [CollatzResearch.WordTrace]
  refine ⟨39399553133486067978299771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26266368755657378652199847 39399553133486067978299771)
  ·
    refine ⟨59099329700229101967449657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39399553133486067978299771 59099329700229101967449657)
    ·
      refine ⟨44324497275171826475587243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59099329700229101967449657 44324497275171826475587243)
      ·
        refine ⟨66486745912757739713380865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44324497275171826475587243 66486745912757739713380865)
        ·
          refine ⟨49865059434568304785035649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66486745912757739713380865 49865059434568304785035649)
          ·
            refine ⟨37398794575926228588776737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49865059434568304785035649 37398794575926228588776737)
            ·
              refine ⟨28049095931944671441582553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37398794575926228588776737 28049095931944671441582553)
              ·
                refine ⟨21036821948958503581186915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28049095931944671441582553 21036821948958503581186915)
                ·
                  refine ⟨31555232923437755371780373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21036821948958503581186915 31555232923437755371780373)
                  ·
                    refine ⟨1479151543286144783052205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 31555232923437755371780373 1479151543286144783052205)
                    ·
                      refine ⟨554681828732304293644577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1479151543286144783052205 554681828732304293644577)
                      ·
                        rfl

theorem cell23_1080239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 6, 3].length) (baseStart_1080239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1080239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1080239 prefixEnd_1080239 := by exact prefixLift 1080239
  have htrace : WordTrace (prefixWord ++ tailWord_1080239) baseStart_1080239 baseEnd_1080239 := by
    simpa [prefixWord, tailWord_1080239, baseEnd_1080239] using wordTrace_append hprefix tailTrace_1080239
  have hstable : (prefixWord ++ tailWord_1080239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080239).length < 2 ^ (prefixWord ++ tailWord_1080239).sum := by decide
  have hdescent : baseEnd_1080239 < baseStart_1080239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080270 : List Nat := [4, 1, 1, 1, 2, 5, 1, 1, 1, 4, 2]
def baseStart_1080270 : Nat := 118140960795 + 1080270 * 2 ^ 59
def prefixEnd_1080270 : Nat := 4983230072969 + 3 ^ 40 * 1080270 * 2
def baseEnd_1080270 : Nat := 554697746632593672356935

theorem tailTrace_1080270 : CollatzResearch.WordTrace tailWord_1080270 prefixEnd_1080270 554697746632593672356935 := by
  unfold tailWord_1080270
  simp only [CollatzResearch.WordTrace]
  refine ⟨4925085474546720034084783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26267122530915840181785509 4925085474546720034084783)
  ·
    refine ⟨7387628211820080051127175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4925085474546720034084783 7387628211820080051127175)
    ·
      refine ⟨11081442317730120076690763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7387628211820080051127175 11081442317730120076690763)
      ·
        refine ⟨16622163476595180115036145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11081442317730120076690763 16622163476595180115036145)
        ·
          refine ⟨12466622607446385086277109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16622163476595180115036145 12466622607446385086277109)
          ·
            refine ⟨1168745869448098601838479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12466622607446385086277109 1168745869448098601838479)
            ·
              refine ⟨1753118804172147902757719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1168745869448098601838479 1753118804172147902757719)
              ·
                refine ⟨2629678206258221854136579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1753118804172147902757719 2629678206258221854136579)
                ·
                  refine ⟨3944517309387332781204869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2629678206258221854136579 3944517309387332781204869)
                  ·
                    refine ⟨739596995510124896475913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3944517309387332781204869 739596995510124896475913)
                    ·
                      refine ⟨554697746632593672356935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 739596995510124896475913 554697746632593672356935)
                      ·
                        rfl

theorem cell23_1080270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 1, 1, 4, 2].length) (baseStart_1080270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1080270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1080270 prefixEnd_1080270 := by exact prefixLift 1080270
  have htrace : WordTrace (prefixWord ++ tailWord_1080270) baseStart_1080270 baseEnd_1080270 := by
    simpa [prefixWord, tailWord_1080270, baseEnd_1080270] using wordTrace_append hprefix tailTrace_1080270
  have hstable : (prefixWord ++ tailWord_1080270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080270).length < 2 ^ (prefixWord ++ tailWord_1080270).sum := by decide
  have hdescent : baseEnd_1080270 < baseStart_1080270 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080276 : List Nat := [2, 4, 1, 2, 1, 2, 2, 2, 7]
def baseStart_1080276 : Nat := 118140960795 + 1080276 * 2 ^ 59
def prefixEnd_1080276 : Nat := 4983230072969 + 3 ^ 40 * 1080276 * 2
def baseEnd_1080276 : Nat := 61633425279613405431323

theorem tailTrace_1080276 : CollatzResearch.WordTrace tailWord_1080276 prefixEnd_1080276 61633425279613405431323 := by
  unfold tailWord_1080276
  simp only [CollatzResearch.WordTrace]
  refine ⟨19700451317176011648698341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26267268422901348864931121 19700451317176011648698341)
  ·
    refine ⟨3693834621970502184130939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19700451317176011648698341 3693834621970502184130939)
    ·
      refine ⟨5540751932955753276196409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3693834621970502184130939 5540751932955753276196409)
      ·
        refine ⟨4155563949716814957147307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5540751932955753276196409 4155563949716814957147307)
        ·
          refine ⟨6233345924575222435720961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4155563949716814957147307 6233345924575222435720961)
          ·
            refine ⟨4675009443431416826790721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6233345924575222435720961 4675009443431416826790721)
            ·
              refine ⟨3506257082573562620093041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4675009443431416826790721 3506257082573562620093041)
              ·
                refine ⟨2629692811930171965069781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3506257082573562620093041 2629692811930171965069781)
                ·
                  refine ⟨61633425279613405431323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2629692811930171965069781 61633425279613405431323)
                  ·
                    rfl

theorem cell23_1080276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 2, 7].length) (baseStart_1080276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1080276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1080276 prefixEnd_1080276 := by exact prefixLift 1080276
  have htrace : WordTrace (prefixWord ++ tailWord_1080276) baseStart_1080276 baseEnd_1080276 := by
    simpa [prefixWord, tailWord_1080276, baseEnd_1080276] using wordTrace_append hprefix tailTrace_1080276
  have hstable : (prefixWord ++ tailWord_1080276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080276).length < 2 ^ (prefixWord ++ tailWord_1080276).sum := by decide
  have hdescent : baseEnd_1080276 < baseStart_1080276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080316 : List Nat := [2, 2, 2, 1, 2, 4, 1, 1, 1, 2, 5]
def baseStart_1080316 : Nat := 118140960795 + 1080316 * 2 ^ 59
def prefixEnd_1080316 : Nat := 4983230072969 + 3 ^ 40 * 1080316 * 2
def baseEnd_1080316 : Nat := 554721366742700492381723

theorem tailTrace_1080316 : CollatzResearch.WordTrace tailWord_1080316 prefixEnd_1080316 554721366742700492381723 := by
  unfold tailWord_1080316
  simp only [CollatzResearch.WordTrace]
  refine ⟨19701180777103555064426401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26268241036138073419235201 19701180777103555064426401)
  ·
    refine ⟨14775885582827666298319801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19701180777103555064426401 14775885582827666298319801)
    ·
      refine ⟨11081914187120749723739851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14775885582827666298319801 11081914187120749723739851)
      ·
        refine ⟨16622871280681124585609777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11081914187120749723739851 16622871280681124585609777)
        ·
          refine ⟨12467153460510843439207333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16622871280681124585609777 12467153460510843439207333)
          ·
            refine ⟨2337591273845783144851375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12467153460510843439207333 2337591273845783144851375)
            ·
              refine ⟨3506386910768674717277063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2337591273845783144851375 3506386910768674717277063)
              ·
                refine ⟨5259580366153012075915595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3506386910768674717277063 5259580366153012075915595)
                ·
                  refine ⟨7889370549229518113873393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5259580366153012075915595 7889370549229518113873393)
                  ·
                    refine ⟨5917027911922138585405045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7889370549229518113873393 5917027911922138585405045)
                    ·
                      refine ⟨554721366742700492381723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5917027911922138585405045 554721366742700492381723)
                      ·
                        rfl

theorem cell23_1080316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 1, 1, 2, 5].length) (baseStart_1080316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1080316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1080316 prefixEnd_1080316 := by exact prefixLift 1080316
  have htrace : WordTrace (prefixWord ++ tailWord_1080316) baseStart_1080316 baseEnd_1080316 := by
    simpa [prefixWord, tailWord_1080316, baseEnd_1080316] using wordTrace_append hprefix tailTrace_1080316
  have hstable : (prefixWord ++ tailWord_1080316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080316).length < 2 ^ (prefixWord ++ tailWord_1080316).sum := by decide
  have hdescent : baseEnd_1080316 < baseStart_1080316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080329 : List Nat := [1, 2, 1, 1, 3, 1, 1, 2, 1, 5, 5]
def baseStart_1080329 : Nat := 118140960795 + 1080329 * 2 ^ 59
def prefixEnd_1080329 : Nat := 4983230072969 + 3 ^ 40 * 1080329 * 2
def baseEnd_1080329 : Nat := 554728041991208941519163

theorem tailTrace_1080329 : CollatzResearch.WordTrace tailWord_1080329 prefixEnd_1080329 554728041991208941519163 := by
  unfold tailWord_1080329
  simp only [CollatzResearch.WordTrace]
  refine ⟨39402835703160013349076041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26268557135440008899384027 39402835703160013349076041)
  ·
    refine ⟨29552126777370010011807031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39402835703160013349076041 29552126777370010011807031)
    ·
      refine ⟨44328190166055015017710547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29552126777370010011807031 44328190166055015017710547)
      ·
        refine ⟨66492285249082522526565821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44328190166055015017710547 66492285249082522526565821)
        ·
          refine ⟨24934606968405945947462183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66492285249082522526565821 24934606968405945947462183)
          ·
            refine ⟨37401910452608918921193275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24934606968405945947462183 37401910452608918921193275)
            ·
              refine ⟨56102865678913378381789913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37401910452608918921193275 56102865678913378381789913)
              ·
                refine ⟨42077149259185033786342435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56102865678913378381789913 42077149259185033786342435)
                ·
                  refine ⟨63115723888777550679513653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42077149259185033786342435 63115723888777550679513653)
                  ·
                    refine ⟨5917099114572895376204405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 63115723888777550679513653 5917099114572895376204405)
                    ·
                      refine ⟨554728041991208941519163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5917099114572895376204405 554728041991208941519163)
                      ·
                        rfl

theorem cell23_1080329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 5, 5].length) (baseStart_1080329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1080329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1080329 prefixEnd_1080329 := by exact prefixLift 1080329
  have htrace : WordTrace (prefixWord ++ tailWord_1080329) baseStart_1080329 baseEnd_1080329 := by
    simpa [prefixWord, tailWord_1080329, baseEnd_1080329] using wordTrace_append hprefix tailTrace_1080329
  have hstable : (prefixWord ++ tailWord_1080329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080329).length < 2 ^ (prefixWord ++ tailWord_1080329).sum := by decide
  have hdescent : baseEnd_1080329 < baseStart_1080329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080339 : List Nat := [1, 1, 1, 2, 1, 4, 1, 2, 1, 3, 6]
def baseStart_1080339 : Nat := 118140960795 + 1080339 * 2 ^ 59
def prefixEnd_1080339 : Nat := 4983230072969 + 3 ^ 40 * 1080339 * 2
def baseEnd_1080339 : Nat := 554733176797753902394117

theorem tailTrace_1080339 : CollatzResearch.WordTrace tailWord_1080339 prefixEnd_1080339 554733176797753902394117 := by
  unfold tailWord_1080339
  simp only [CollatzResearch.WordTrace]
  refine ⟨39403200433123785056940071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26268800288749190037960047 39403200433123785056940071)
  ·
    refine ⟨59104800649685677585410107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39403200433123785056940071 59104800649685677585410107)
    ·
      refine ⟨88657200974528516378115161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59104800649685677585410107 88657200974528516378115161)
      ·
        refine ⟨66492900730896387283586371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88657200974528516378115161 66492900730896387283586371)
        ·
          refine ⟨99739351096344580925379557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66492900730896387283586371 99739351096344580925379557)
          ·
            refine ⟨18701128330564608923508667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 99739351096344580925379557 18701128330564608923508667)
            ·
              refine ⟨28051692495846913385263001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18701128330564608923508667 28051692495846913385263001)
              ·
                refine ⟨21038769371885185038947251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28051692495846913385263001 21038769371885185038947251)
                ·
                  refine ⟨31558154057827777558420877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21038769371885185038947251 31558154057827777558420877)
                  ·
                    refine ⟨11834307771685416584407829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31558154057827777558420877 11834307771685416584407829)
                    ·
                      refine ⟨554733176797753902394117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11834307771685416584407829 554733176797753902394117)
                      ·
                        rfl

theorem cell23_1080339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 3, 6].length) (baseStart_1080339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1080339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1080339 prefixEnd_1080339 := by exact prefixLift 1080339
  have htrace : WordTrace (prefixWord ++ tailWord_1080339) baseStart_1080339 baseEnd_1080339 := by
    simpa [prefixWord, tailWord_1080339, baseEnd_1080339] using wordTrace_append hprefix tailTrace_1080339
  have hstable : (prefixWord ++ tailWord_1080339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080339).length < 2 ^ (prefixWord ++ tailWord_1080339).sum := by decide
  have hdescent : baseEnd_1080339 < baseStart_1080339 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080343 : List Nat := [1, 1, 3, 5, 1, 1, 1, 3, 2, 1, 4]
def baseStart_1080343 : Nat := 118140960795 + 1080343 * 2 ^ 59
def prefixEnd_1080343 : Nat := 4983230072969 + 3 ^ 40 * 1080343 * 2
def baseEnd_1080343 : Nat := 554735230720371886744099

theorem tailTrace_1080343 : CollatzResearch.WordTrace tailWord_1080343 prefixEnd_1080343 554735230720371886744099 := by
  unfold tailWord_1080343
  simp only [CollatzResearch.WordTrace]
  refine ⟨39403346325109293740085683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26268897550072862493390455 39403346325109293740085683)
  ·
    refine ⟨59105019487663940610128525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39403346325109293740085683 59105019487663940610128525)
    ·
      refine ⟨22164382307873977728798197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59105019487663940610128525 22164382307873977728798197)
      ·
        refine ⟨2077910841363185412074831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22164382307873977728798197 2077910841363185412074831)
        ·
          refine ⟨3116866262044778118112247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2077910841363185412074831 3116866262044778118112247)
          ·
            refine ⟨4675299393067167177168371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3116866262044778118112247 4675299393067167177168371)
            ·
              refine ⟨7012949089600750765752557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4675299393067167177168371 7012949089600750765752557)
              ·
                refine ⟨2629855908600281537157209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7012949089600750765752557 2629855908600281537157209)
                ·
                  refine ⟨1972391931450211152867907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2629855908600281537157209 1972391931450211152867907)
                  ·
                    refine ⟨2958587897175316729301861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1972391931450211152867907 2958587897175316729301861)
                    ·
                      refine ⟨554735230720371886744099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2958587897175316729301861 554735230720371886744099)
                      ·
                        rfl

theorem cell23_1080343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_1080343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1080343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1080343 prefixEnd_1080343 := by exact prefixLift 1080343
  have htrace : WordTrace (prefixWord ++ tailWord_1080343) baseStart_1080343 baseEnd_1080343 := by
    simpa [prefixWord, tailWord_1080343, baseEnd_1080343] using wordTrace_append hprefix tailTrace_1080343
  have hstable : (prefixWord ++ tailWord_1080343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080343).length < 2 ^ (prefixWord ++ tailWord_1080343).sum := by decide
  have hdescent : baseEnd_1080343 < baseStart_1080343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080370 : List Nat := [3, 2, 1, 1, 2, 2, 3, 4, 1, 4]
def baseStart_1080370 : Nat := 118140960795 + 1080370 * 2 ^ 59
def prefixEnd_1080370 : Nat := 4983230072969 + 3 ^ 40 * 1080370 * 2
def baseEnd_1080370 : Nat := 184916364899347760368825

theorem tailTrace_1080370 : CollatzResearch.WordTrace tailWord_1080370 prefixEnd_1080370 184916364899347760368825 := by
  unfold tailWord_1080370
  simp only [CollatzResearch.WordTrace]
  refine ⟨9851082774002869337829641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26269554064007651567545709 9851082774002869337829641)
  ·
    refine ⟨7388312080502152003372231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9851082774002869337829641 7388312080502152003372231)
    ·
      refine ⟨11082468120753228005058347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7388312080502152003372231 11082468120753228005058347)
      ·
        refine ⟨16623702181129842007587521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11082468120753228005058347 16623702181129842007587521)
        ·
          refine ⟨12467776635847381505690641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16623702181129842007587521 12467776635847381505690641)
          ·
            refine ⟨9350832476885536129267981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12467776635847381505690641 9350832476885536129267981)
            ·
              refine ⟨3506562178832076048475493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9350832476885536129267981 3506562178832076048475493)
              ·
                refine ⟨657480408531014259089155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3506562178832076048475493 657480408531014259089155)
                ·
                  refine ⟨986220612796521388633733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 657480408531014259089155 986220612796521388633733)
                  ·
                    refine ⟨184916364899347760368825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 986220612796521388633733 184916364899347760368825)
                    ·
                      rfl

theorem cell23_1080370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 4, 1, 4].length) (baseStart_1080370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1080370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1080370 prefixEnd_1080370 := by exact prefixLift 1080370
  have htrace : WordTrace (prefixWord ++ tailWord_1080370) baseStart_1080370 baseEnd_1080370 := by
    simpa [prefixWord, tailWord_1080370, baseEnd_1080370] using wordTrace_append hprefix tailTrace_1080370
  have hstable : (prefixWord ++ tailWord_1080370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080370).length < 2 ^ (prefixWord ++ tailWord_1080370).sum := by decide
  have hdescent : baseEnd_1080370 < baseStart_1080370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080379 : List Nat := [1, 1, 1, 1, 1, 2, 1, 3, 1, 11]
def baseStart_1080379 : Nat := 118140960795 + 1080379 * 2 ^ 59
def prefixEnd_1080379 : Nat := 4983230072969 + 3 ^ 40 * 1080379 * 2
def baseEnd_1080379 : Nat := 184917905341311248631311

theorem tailTrace_1080379 : CollatzResearch.WordTrace tailWord_1080379 prefixEnd_1080379 184917905341311248631311 := by
  unfold tailWord_1080379
  simp only [CollatzResearch.WordTrace]
  refine ⟨39404659352978871888396191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26269772901985914592264127 39404659352978871888396191)
  ·
    refine ⟨59106989029468307832594287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39404659352978871888396191 59106989029468307832594287)
    ·
      refine ⟨88660483544202461748891431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59106989029468307832594287 88660483544202461748891431)
      ·
        refine ⟨132990725316303692623337147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88660483544202461748891431 132990725316303692623337147)
        ·
          refine ⟨199486087974455538935005721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132990725316303692623337147 199486087974455538935005721)
          ·
            refine ⟨149614565980841654201254291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 199486087974455538935005721 149614565980841654201254291)
            ·
              refine ⟨224421848971262481301881437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149614565980841654201254291 224421848971262481301881437)
              ·
                refine ⟨84158193364223430488205539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 224421848971262481301881437 84158193364223430488205539)
                ·
                  refine ⟨126237290046335145732308309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84158193364223430488205539 126237290046335145732308309)
                  ·
                    refine ⟨184917905341311248631311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 126237290046335145732308309 184917905341311248631311)
                    ·
                      rfl

theorem cell23_1080379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 11].length) (baseStart_1080379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1080379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1080379 prefixEnd_1080379 := by exact prefixLift 1080379
  have htrace : WordTrace (prefixWord ++ tailWord_1080379) baseStart_1080379 baseEnd_1080379 := by
    simpa [prefixWord, tailWord_1080379, baseEnd_1080379] using wordTrace_append hprefix tailTrace_1080379
  have hstable : (prefixWord ++ tailWord_1080379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080379).length < 2 ^ (prefixWord ++ tailWord_1080379).sum := by decide
  have hdescent : baseEnd_1080379 < baseStart_1080379 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080397 : List Nat := [1, 6, 1, 1, 1, 4, 1, 1, 2, 2, 3]
def baseStart_1080397 : Nat := 118140960795 + 1080397 * 2 ^ 59
def prefixEnd_1080397 : Nat := 4983230072969 + 3 ^ 40 * 1080397 * 2
def baseEnd_1080397 : Nat := 554762958675714675468851

theorem tailTrace_1080397 : CollatzResearch.WordTrace tailWord_1080397 prefixEnd_1080397 554762958675714675468851 := by
  unfold tailWord_1080397
  simp only [CollatzResearch.WordTrace]
  refine ⟨39405315866913660962551445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26270210577942440641700963 39405315866913660962551445)
  ·
    refine ⟨1847124181261577857619599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 39405315866913660962551445 1847124181261577857619599)
    ·
      refine ⟨2770686271892366786429399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1847124181261577857619599 2770686271892366786429399)
      ·
        refine ⟨4156029407838550179644099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2770686271892366786429399 4156029407838550179644099)
        ·
          refine ⟨6234044111757825269466149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4156029407838550179644099 6234044111757825269466149)
          ·
            refine ⟨1168883270954592238024903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6234044111757825269466149 1168883270954592238024903)
            ·
              refine ⟨1753324906431888357037355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1168883270954592238024903 1753324906431888357037355)
              ·
                refine ⟨2629987359647832535556033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1753324906431888357037355 2629987359647832535556033)
                ·
                  refine ⟨1972490519735874401667025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2629987359647832535556033 1972490519735874401667025)
                  ·
                    refine ⟨1479367889801905801250269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1972490519735874401667025 1479367889801905801250269)
                    ·
                      refine ⟨554762958675714675468851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1479367889801905801250269 554762958675714675468851)
                      ·
                        rfl

theorem cell23_1080397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_1080397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1080397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1080397 prefixEnd_1080397 := by exact prefixLift 1080397
  have htrace : WordTrace (prefixWord ++ tailWord_1080397) baseStart_1080397 baseEnd_1080397 := by
    simpa [prefixWord, tailWord_1080397, baseEnd_1080397] using wordTrace_append hprefix tailTrace_1080397
  have hstable : (prefixWord ++ tailWord_1080397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080397).length < 2 ^ (prefixWord ++ tailWord_1080397).sum := by decide
  have hdescent : baseEnd_1080397 < baseStart_1080397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080443 : List Nat := [1, 1, 1, 1, 1, 4, 1, 7, 2, 4]
def baseStart_1080443 : Nat := 118140960795 + 1080443 * 2 ^ 59
def prefixEnd_1080443 : Nat := 4983230072969 + 3 ^ 40 * 1080443 * 2
def baseEnd_1080443 : Nat := 184928859595273831831213

theorem tailTrace_1080443 : CollatzResearch.WordTrace tailWord_1080443 prefixEnd_1080443 184928859595273831831213 := by
  unfold tailWord_1080443
  simp only [CollatzResearch.WordTrace]
  refine ⟨39406993624747010818725983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26271329083164673879150655 39406993624747010818725983)
  ·
    refine ⟨59110490437120516228088975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39406993624747010818725983 59110490437120516228088975)
    ·
      refine ⟨88665735655680774342133463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59110490437120516228088975 88665735655680774342133463)
      ·
        refine ⟨132998603483521161513200195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88665735655680774342133463 132998603483521161513200195)
        ·
          refine ⟨199497905225281742269800293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132998603483521161513200195 199497905225281742269800293)
          ·
            refine ⟨37405857229740326675587555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 199497905225281742269800293 37405857229740326675587555)
            ·
              refine ⟨56108785844610490013381333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37405857229740326675587555 56108785844610490013381333)
              ·
                refine ⟨1315049668233058359688625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 56108785844610490013381333 1315049668233058359688625)
                ·
                  refine ⟨986287251174793769766469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1315049668233058359688625 986287251174793769766469)
                  ·
                    refine ⟨184928859595273831831213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 986287251174793769766469 184928859595273831831213)
                    ·
                      rfl

theorem cell23_1080443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 7, 2, 4].length) (baseStart_1080443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1080443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1080443 prefixEnd_1080443 := by exact prefixLift 1080443
  have htrace : WordTrace (prefixWord ++ tailWord_1080443) baseStart_1080443 baseEnd_1080443 := by
    simpa [prefixWord, tailWord_1080443, baseEnd_1080443] using wordTrace_append hprefix tailTrace_1080443
  have hstable : (prefixWord ++ tailWord_1080443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080443).length < 2 ^ (prefixWord ++ tailWord_1080443).sum := by decide
  have hdescent : baseEnd_1080443 < baseStart_1080443 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080484 : List Nat := [2, 3, 1, 2, 3, 3, 1, 1, 3, 2, 2]
def baseStart_1080484 : Nat := 118140960795 + 1080484 * 2 ^ 59
def prefixEnd_1080484 : Nat := 4983230072969 + 3 ^ 40 * 1080484 * 2
def baseEnd_1080484 : Nat := 554807631492655835080951

theorem tailTrace_1080484 : CollatzResearch.WordTrace tailWord_1080484 prefixEnd_1080484 554807631492655835080951 := by
  unfold tailWord_1080484
  simp only [CollatzResearch.WordTrace]
  refine ⟨19704244508799237410484253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26272326011732316547312337 19704244508799237410484253)
  ·
    refine ⟨7389091690799714028931595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19704244508799237410484253 7389091690799714028931595)
    ·
      refine ⟨11083637536199571043397393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7389091690799714028931595 11083637536199571043397393)
      ·
        refine ⟨8312728152149678282548045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11083637536199571043397393 8312728152149678282548045)
        ·
          refine ⟨3117273057056129355955517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8312728152149678282548045 3117273057056129355955517)
          ·
            refine ⟨1168977396396048508483319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3117273057056129355955517 1168977396396048508483319)
            ·
              refine ⟨1753466094594072762724979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1168977396396048508483319 1753466094594072762724979)
              ·
                refine ⟨2630199141891109144087469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1753466094594072762724979 2630199141891109144087469)
                ·
                  refine ⟨986324678209165929032801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2630199141891109144087469 986324678209165929032801)
                  ·
                    refine ⟨739743508656874446774601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 986324678209165929032801 739743508656874446774601)
                    ·
                      refine ⟨554807631492655835080951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 739743508656874446774601 554807631492655835080951)
                      ·
                        rfl

theorem cell23_1080484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 1, 3, 2, 2].length) (baseStart_1080484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1080484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1080484 prefixEnd_1080484 := by exact prefixLift 1080484
  have htrace : WordTrace (prefixWord ++ tailWord_1080484) baseStart_1080484 baseEnd_1080484 := by
    simpa [prefixWord, tailWord_1080484, baseEnd_1080484] using wordTrace_append hprefix tailTrace_1080484
  have hstable : (prefixWord ++ tailWord_1080484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080484).length < 2 ^ (prefixWord ++ tailWord_1080484).sum := by decide
  have hdescent : baseEnd_1080484 < baseStart_1080484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080490 : List Nat := [3, 1, 5, 1, 1, 2, 2, 8]
def baseStart_1080490 : Nat := 118140960795 + 1080490 * 2 ^ 59
def prefixEnd_1080490 : Nat := 4983230072969 + 3 ^ 40 * 1080490 * 2
def baseEnd_1080490 : Nat := 20548544902836400429849

theorem tailTrace_1080490 : CollatzResearch.WordTrace tailWord_1080490 prefixEnd_1080490 20548544902836400429849 := by
  unfold tailWord_1080490
  simp only [CollatzResearch.WordTrace]
  refine ⟨9852176963894184461421731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26272471903717825230457949 9852176963894184461421731)
  ·
    refine ⟨14778265445841276692132597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9852176963894184461421731 14778265445841276692132597)
    ·
      refine ⟨1385462385547619689887431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14778265445841276692132597 1385462385547619689887431)
      ·
        refine ⟨2078193578321429534831147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1385462385547619689887431 2078193578321429534831147)
        ·
          refine ⟨3117290367482144302246721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2078193578321429534831147 3117290367482144302246721)
          ·
            refine ⟨2337967775611608226685041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3117290367482144302246721 2337967775611608226685041)
            ·
              refine ⟨1753475831708706170013781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2337967775611608226685041 1753475831708706170013781)
              ·
                refine ⟨20548544902836400429849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1753475831708706170013781 20548544902836400429849)
                ·
                  rfl

theorem cell23_1080490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 8].length) (baseStart_1080490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1080490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1080490 prefixEnd_1080490 := by exact prefixLift 1080490
  have htrace : WordTrace (prefixWord ++ tailWord_1080490) baseStart_1080490 baseEnd_1080490 := by
    simpa [prefixWord, tailWord_1080490, baseEnd_1080490] using wordTrace_append hprefix tailTrace_1080490
  have hstable : (prefixWord ++ tailWord_1080490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080490).length < 2 ^ (prefixWord ++ tailWord_1080490).sum := by decide
  have hdescent : baseEnd_1080490 < baseStart_1080490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080496 : List Nat := [2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 5]
def baseStart_1080496 : Nat := 118140960795 + 1080496 * 2 ^ 59
def prefixEnd_1080496 : Nat := 4983230072969 + 3 ^ 40 * 1080496 * 2
def baseEnd_1080496 : Nat := 554813793260509788130895

theorem tailTrace_1080496 : CollatzResearch.WordTrace tailWord_1080496 prefixEnd_1080496 554813793260509788130895 := by
  unfold tailWord_1080496
  simp only [CollatzResearch.WordTrace]
  refine ⟨19704463346777500435202671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26272617795703333913603561 19704463346777500435202671)
  ·
    refine ⟨29556695020166250652804007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19704463346777500435202671 29556695020166250652804007)
    ·
      refine ⟨44335042530249375979206011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29556695020166250652804007 44335042530249375979206011)
      ·
        refine ⟨66502563795374063968809017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44335042530249375979206011 66502563795374063968809017)
        ·
          refine ⟨49876922846530547976606763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66502563795374063968809017 49876922846530547976606763)
          ·
            refine ⟨74815384269795821964910145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49876922846530547976606763 74815384269795821964910145)
            ·
              refine ⟨56111538202346866473682609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74815384269795821964910145 56111538202346866473682609)
              ·
                refine ⟨42083653651760149855261957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56111538202346866473682609 42083653651760149855261957)
                ·
                  refine ⟨7890685059705028097861617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42083653651760149855261957 7890685059705028097861617)
                  ·
                    refine ⟨5918013794778771073396213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7890685059705028097861617 5918013794778771073396213)
                    ·
                      refine ⟨554813793260509788130895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5918013794778771073396213 554813793260509788130895)
                      ·
                        rfl

theorem cell23_1080496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 5].length) (baseStart_1080496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1080496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1080496 prefixEnd_1080496 := by exact prefixLift 1080496
  have htrace : WordTrace (prefixWord ++ tailWord_1080496) baseStart_1080496 baseEnd_1080496 := by
    simpa [prefixWord, tailWord_1080496, baseEnd_1080496] using wordTrace_append hprefix tailTrace_1080496
  have hstable : (prefixWord ++ tailWord_1080496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080496).length < 2 ^ (prefixWord ++ tailWord_1080496).sum := by decide
  have hdescent : baseEnd_1080496 < baseStart_1080496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080506 : List Nat := [3, 1, 1, 1, 2, 2, 1, 1, 1, 2, 8]
def baseStart_1080506 : Nat := 118140960795 + 1080506 * 2 ^ 59
def prefixEnd_1080506 : Nat := 4983230072969 + 3 ^ 40 * 1080506 * 2
def baseEnd_1080506 : Nat := 554818928067054749005849

theorem tailTrace_1080506 : CollatzResearch.WordTrace tailWord_1080506 prefixEnd_1080506 554818928067054749005849 := by
  unfold tailWord_1080506
  simp only [CollatzResearch.WordTrace]
  refine ⟨9852322855879693144567343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26272860949012515052179581 9852322855879693144567343)
  ·
    refine ⟨14778484283819539716851015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9852322855879693144567343 14778484283819539716851015)
    ·
      refine ⟨22167726425729309575276523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14778484283819539716851015 22167726425729309575276523)
      ·
        refine ⟨33251589638593964362914785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22167726425729309575276523 33251589638593964362914785)
        ·
          refine ⟨24938692228945473272186089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33251589638593964362914785 24938692228945473272186089)
          ·
            refine ⟨18704019171709104954139567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24938692228945473272186089 18704019171709104954139567)
            ·
              refine ⟨28056028757563657431209351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18704019171709104954139567 28056028757563657431209351)
              ·
                refine ⟨42084043136345486146814027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28056028757563657431209351 42084043136345486146814027)
                ·
                  refine ⟨63126064704518229220221041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42084043136345486146814027 63126064704518229220221041)
                  ·
                    refine ⟨47344548528388671915165781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 63126064704518229220221041 47344548528388671915165781)
                    ·
                      refine ⟨554818928067054749005849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 47344548528388671915165781 554818928067054749005849)
                      ·
                        rfl

theorem cell23_1080506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 1, 2, 8].length) (baseStart_1080506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1080506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1080506 prefixEnd_1080506 := by exact prefixLift 1080506
  have htrace : WordTrace (prefixWord ++ tailWord_1080506) baseStart_1080506 baseEnd_1080506 := by
    simpa [prefixWord, tailWord_1080506, baseEnd_1080506] using wordTrace_append hprefix tailTrace_1080506
  have hstable : (prefixWord ++ tailWord_1080506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080506).length < 2 ^ (prefixWord ++ tailWord_1080506).sum := by decide
  have hdescent : baseEnd_1080506 < baseStart_1080506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080514 : List Nat := [3, 5, 1, 1, 2, 1, 1, 2, 1, 2, 4]
def baseStart_1080514 : Nat := 118140960795 + 1080514 * 2 ^ 59
def prefixEnd_1080514 : Nat := 4983230072969 + 3 ^ 40 * 1080514 * 2
def baseEnd_1080514 : Nat := 554823035912290717705813

theorem tailTrace_1080514 : CollatzResearch.WordTrace tailWord_1080514 prefixEnd_1080514 554823035912290717705813 := by
  unfold tailWord_1080514
  simp only [CollatzResearch.WordTrace]
  refine ⟨9852395801872447486140149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26273055471659859963040397 9852395801872447486140149)
  ·
    refine ⟨923662106425541951825639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9852395801872447486140149 923662106425541951825639)
    ·
      refine ⟨1385493159638312927738459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 923662106425541951825639 1385493159638312927738459)
      ·
        refine ⟨2078239739457469391607689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1385493159638312927738459 2078239739457469391607689)
        ·
          refine ⟨1558679804593102043705767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2078239739457469391607689 1558679804593102043705767)
          ·
            refine ⟨2338019706889653065558651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1558679804593102043705767 2338019706889653065558651)
            ·
              refine ⟨3507029560334479598337977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2338019706889653065558651 3507029560334479598337977)
              ·
                refine ⟨2630272170250859698753483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3507029560334479598337977 2630272170250859698753483)
                ·
                  refine ⟨3945408255376289548130225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2630272170250859698753483 3945408255376289548130225)
                  ·
                    refine ⟨2959056191532217161097669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3945408255376289548130225 2959056191532217161097669)
                    ·
                      refine ⟨554823035912290717705813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2959056191532217161097669 554823035912290717705813)
                      ·
                        rfl

theorem cell23_1080514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_1080514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1080514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1080514 prefixEnd_1080514 := by exact prefixLift 1080514
  have htrace : WordTrace (prefixWord ++ tailWord_1080514) baseStart_1080514 baseEnd_1080514 := by
    simpa [prefixWord, tailWord_1080514, baseEnd_1080514] using wordTrace_append hprefix tailTrace_1080514
  have hstable : (prefixWord ++ tailWord_1080514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080514).length < 2 ^ (prefixWord ++ tailWord_1080514).sum := by decide
  have hdescent : baseEnd_1080514 < baseStart_1080514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080518 : List Nat := [6, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4]
def baseStart_1080518 : Nat := 118140960795 + 1080518 * 2 ^ 59
def prefixEnd_1080518 : Nat := 4983230072969 + 3 ^ 40 * 1080518 * 2
def baseEnd_1080518 : Nat := 554825089834908702055795

theorem tailTrace_1080518 : CollatzResearch.WordTrace tailWord_1080518 prefixEnd_1080518 554825089834908702055795 := by
  unfold tailWord_1080518
  simp only [CollatzResearch.WordTrace]
  refine ⟨1231554034358603082115819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 26273152732983532418470805 1231554034358603082115819)
  ·
    refine ⟨1847331051537904623173729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1231554034358603082115819 1847331051537904623173729)
    ·
      refine ⟨1385498288653428467380297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1847331051537904623173729 1385498288653428467380297)
      ·
        refine ⟨1039123716490071350535223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1385498288653428467380297 1039123716490071350535223)
        ·
          refine ⟨1558685574735107025802835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1039123716490071350535223 1558685574735107025802835)
          ·
            refine ⟨2338028362102660538704253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1558685574735107025802835 2338028362102660538704253)
            ·
              refine ⟨876760635788497702014095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2338028362102660538704253 876760635788497702014095)
              ·
                refine ⟨1315140953682746553021143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 876760635788497702014095 1315140953682746553021143)
                ·
                  refine ⟨1972711430524119829531715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1315140953682746553021143 1972711430524119829531715)
                  ·
                    refine ⟨2959067145786179744297573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1972711430524119829531715 2959067145786179744297573)
                    ·
                      refine ⟨554825089834908702055795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2959067145786179744297573 554825089834908702055795)
                      ·
                        rfl

theorem cell23_1080518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_1080518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1080518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1080518 prefixEnd_1080518 := by exact prefixLift 1080518
  have htrace : WordTrace (prefixWord ++ tailWord_1080518) baseStart_1080518 baseEnd_1080518 := by
    simpa [prefixWord, tailWord_1080518, baseEnd_1080518] using wordTrace_append hprefix tailTrace_1080518
  have hstable : (prefixWord ++ tailWord_1080518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080518).length < 2 ^ (prefixWord ++ tailWord_1080518).sum := by decide
  have hdescent : baseEnd_1080518 < baseStart_1080518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080543 : List Nat := [1, 1, 2, 3, 2, 1, 3, 1, 2, 4, 3]
def baseStart_1080543 : Nat := 118140960795 + 1080543 * 2 ^ 59
def prefixEnd_1080543 : Nat := 4983230072969 + 3 ^ 40 * 1080543 * 2
def baseEnd_1080543 : Nat := 554837926851271104243179

theorem tailTrace_1080543 : CollatzResearch.WordTrace tailWord_1080543 prefixEnd_1080543 554837926851271104243179 := by
  unfold tailWord_1080543
  simp only [CollatzResearch.WordTrace]
  refine ⟨39410640924384727897366283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26273760616256485264910855 39410640924384727897366283)
  ·
    refine ⟨59115961386577091846049425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39410640924384727897366283 59115961386577091846049425)
    ·
      refine ⟨44336971039932818884537069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59115961386577091846049425 44336971039932818884537069)
      ·
        refine ⟨16626364139974807081701401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44336971039932818884537069 16626364139974807081701401)
        ·
          refine ⟨12469773104981105311276051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16626364139974807081701401 12469773104981105311276051)
          ·
            refine ⟨18704659657471657966914077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12469773104981105311276051 18704659657471657966914077)
            ·
              refine ⟨7014247371551871737592779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18704659657471657966914077 7014247371551871737592779)
              ·
                refine ⟨10521371057327807606389169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7014247371551871737592779 10521371057327807606389169)
                ·
                  refine ⟨7891028292995855704791877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10521371057327807606389169 7891028292995855704791877)
                  ·
                    refine ⟨1479567804936722944648477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7891028292995855704791877 1479567804936722944648477)
                    ·
                      refine ⟨554837926851271104243179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1479567804936722944648477 554837926851271104243179)
                      ·
                        rfl

theorem cell23_1080543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 2, 4, 3].length) (baseStart_1080543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1080543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1080543 prefixEnd_1080543 := by exact prefixLift 1080543
  have htrace : WordTrace (prefixWord ++ tailWord_1080543) baseStart_1080543 baseEnd_1080543 := by
    simpa [prefixWord, tailWord_1080543, baseEnd_1080543] using wordTrace_append hprefix tailTrace_1080543
  have hstable : (prefixWord ++ tailWord_1080543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080543).length < 2 ^ (prefixWord ++ tailWord_1080543).sum := by decide
  have hdescent : baseEnd_1080543 < baseStart_1080543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080557 : List Nat := [1, 5, 1, 2, 2, 1, 1, 3, 1, 4, 2]
def baseStart_1080557 : Nat := 118140960795 + 1080557 * 2 ^ 59
def prefixEnd_1080557 : Nat := 4983230072969 + 3 ^ 40 * 1080557 * 2
def baseEnd_1080557 : Nat := 554845115580434049468115

theorem tailTrace_1080557 : CollatzResearch.WordTrace tailWord_1080557 prefixEnd_1080557 554845115580434049468115 := by
  unfold tailWord_1080557
  simp only [CollatzResearch.WordTrace]
  refine ⟨39411151546334008288375925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26274101030889338858917283 39411151546334008288375925)
  ·
    refine ⟨3694795457468813277035243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39411151546334008288375925 3694795457468813277035243)
    ·
      refine ⟨5542193186203219915552865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3694795457468813277035243 5542193186203219915552865)
      ·
        refine ⟨4156644889652414936664649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5542193186203219915552865 4156644889652414936664649)
        ·
          refine ⟨3117483667239311202498487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4156644889652414936664649 3117483667239311202498487)
          ·
            refine ⟨4676225500858966803747731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3117483667239311202498487 4676225500858966803747731)
            ·
              refine ⟨7014338251288450205621597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4676225500858966803747731 7014338251288450205621597)
              ·
                refine ⟨2630376844233168827108099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7014338251288450205621597 2630376844233168827108099)
                ·
                  refine ⟨3945565266349753240662149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2630376844233168827108099 3945565266349753240662149)
                  ·
                    refine ⟨739793487440578732624153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3945565266349753240662149 739793487440578732624153)
                    ·
                      refine ⟨554845115580434049468115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 739793487440578732624153 554845115580434049468115)
                      ·
                        rfl

theorem cell23_1080557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 3, 1, 4, 2].length) (baseStart_1080557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1080557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1080557 prefixEnd_1080557 := by exact prefixLift 1080557
  have htrace : WordTrace (prefixWord ++ tailWord_1080557) baseStart_1080557 baseEnd_1080557 := by
    simpa [prefixWord, tailWord_1080557, baseEnd_1080557] using wordTrace_append hprefix tailTrace_1080557
  have hstable : (prefixWord ++ tailWord_1080557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080557).length < 2 ^ (prefixWord ++ tailWord_1080557).sum := by decide
  have hdescent : baseEnd_1080557 < baseStart_1080557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080563 : List Nat := [1, 1, 1, 2, 2, 6, 1, 2, 7]
def baseStart_1080563 : Nat := 118140960795 + 1080563 * 2 ^ 59
def prefixEnd_1080563 : Nat := 4983230072969 + 3 ^ 40 * 1080563 * 2
def baseEnd_1080563 : Nat := 61649799607151225110343

theorem tailTrace_1080563 : CollatzResearch.WordTrace tailWord_1080563 prefixEnd_1080563 61649799607151225110343 := by
  unfold tailWord_1080563
  simp only [CollatzResearch.WordTrace]
  refine ⟨39411370384312271313094343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26274246922874847542062895 39411370384312271313094343)
  ·
    refine ⟨59117055576468406969641515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39411370384312271313094343 59117055576468406969641515)
    ·
      refine ⟨88675583364702610454462273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59117055576468406969641515 88675583364702610454462273)
      ·
        refine ⟨66506687523526957840846705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88675583364702610454462273 66506687523526957840846705)
        ·
          refine ⟨49880015642645218380635029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66506687523526957840846705 49880015642645218380635029)
          ·
            refine ⟨2338125733248994611592267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 49880015642645218380635029 2338125733248994611592267)
            ·
              refine ⟨3507188599873491917388401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2338125733248994611592267 3507188599873491917388401)
              ·
                refine ⟨2630391449905118938041301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3507188599873491917388401 2630391449905118938041301)
                ·
                  refine ⟨61649799607151225110343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2630391449905118938041301 61649799607151225110343)
                  ·
                    rfl

theorem cell23_1080563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 2, 7].length) (baseStart_1080563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1080563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1080563 prefixEnd_1080563 := by exact prefixLift 1080563
  have htrace : WordTrace (prefixWord ++ tailWord_1080563) baseStart_1080563 baseEnd_1080563 := by
    simpa [prefixWord, tailWord_1080563, baseEnd_1080563] using wordTrace_append hprefix tailTrace_1080563
  have hstable : (prefixWord ++ tailWord_1080563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080563).length < 2 ^ (prefixWord ++ tailWord_1080563).sum := by decide
  have hdescent : baseEnd_1080563 < baseStart_1080563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080578 : List Nat := [3, 4, 1, 1, 3, 2, 2, 1, 1, 3, 2]
def baseStart_1080578 : Nat := 118140960795 + 1080578 * 2 ^ 59
def prefixEnd_1080578 : Nat := 4983230072969 + 3 ^ 40 * 1080578 * 2
def baseEnd_1080578 : Nat := 554855898674178467305519

theorem tailTrace_1080578 : CollatzResearch.WordTrace tailWord_1080578 prefixEnd_1080578 554855898674178467305519 := by
  unfold tailWord_1080578
  simp only [CollatzResearch.WordTrace]
  refine ⟨9852979369814482218722597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26274611652838619249926925 9852979369814482218722597)
  ·
    refine ⟨1847433631840215416010487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9852979369814482218722597 1847433631840215416010487)
    ·
      refine ⟨2771150447760323124015731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1847433631840215416010487 2771150447760323124015731)
      ·
        refine ⟨4156725671640484686023597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2771150447760323124015731 4156725671640484686023597)
        ·
          refine ⟨1558772126865181757258849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4156725671640484686023597 1558772126865181757258849)
          ·
            refine ⟨1169079095148886317944137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1558772126865181757258849 1169079095148886317944137)
            ·
              refine ⟨876809321361664738458103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1169079095148886317944137 876809321361664738458103)
              ·
                refine ⟨1315213982042497107687155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 876809321361664738458103 1315213982042497107687155)
                ·
                  refine ⟨1972820973063745661530733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1315213982042497107687155 1972820973063745661530733)
                  ·
                    refine ⟨739807864898904623074025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1972820973063745661530733 739807864898904623074025)
                    ·
                      refine ⟨554855898674178467305519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 739807864898904623074025 554855898674178467305519)
                      ·
                        rfl

theorem cell23_1080578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 2, 1, 1, 3, 2].length) (baseStart_1080578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1080578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1080578 prefixEnd_1080578 := by exact prefixLift 1080578
  have htrace : WordTrace (prefixWord ++ tailWord_1080578) baseStart_1080578 baseEnd_1080578 := by
    simpa [prefixWord, tailWord_1080578, baseEnd_1080578] using wordTrace_append hprefix tailTrace_1080578
  have hstable : (prefixWord ++ tailWord_1080578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080578).length < 2 ^ (prefixWord ++ tailWord_1080578).sum := by decide
  have hdescent : baseEnd_1080578 < baseStart_1080578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080590 : List Nat := [4, 1, 1, 2, 1, 3, 1, 2, 2, 3, 3]
def baseStart_1080590 : Nat := 118140960795 + 1080590 * 2 ^ 59
def prefixEnd_1080590 : Nat := 4983230072969 + 3 ^ 40 * 1080590 * 2
def baseEnd_1080590 : Nat := 554862060442032420355463

theorem tailTrace_1080590 : CollatzResearch.WordTrace tailWord_1080590 prefixEnd_1080590 554862060442032420355463 := by
  unfold tailWord_1080590
  simp only [CollatzResearch.WordTrace]
  refine ⟨4926544394401806865540903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26274903436809636616218149 4926544394401806865540903)
  ·
    refine ⟨7389816591602710298311355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4926544394401806865540903 7389816591602710298311355)
    ·
      refine ⟨11084724887404065447467033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7389816591602710298311355 11084724887404065447467033)
      ·
        refine ⟨8313543665553049085600275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11084724887404065447467033 8313543665553049085600275)
        ·
          refine ⟨12470315498329573628400413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8313543665553049085600275 12470315498329573628400413)
          ·
            refine ⟨4676368311873590110650155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12470315498329573628400413 4676368311873590110650155)
            ·
              refine ⟨7014552467810385165975233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4676368311873590110650155 7014552467810385165975233)
              ·
                refine ⟨5260914350857788874481425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7014552467810385165975233 5260914350857788874481425)
                ·
                  refine ⟨3945685763143341655861069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5260914350857788874481425 3945685763143341655861069)
                  ·
                    refine ⟨1479632161178753120947901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3945685763143341655861069 1479632161178753120947901)
                    ·
                      refine ⟨554862060442032420355463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1479632161178753120947901 554862060442032420355463)
                      ·
                        rfl

theorem cell23_1080590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 2, 2, 3, 3].length) (baseStart_1080590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1080590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1080590 prefixEnd_1080590 := by exact prefixLift 1080590
  have htrace : WordTrace (prefixWord ++ tailWord_1080590) baseStart_1080590 baseEnd_1080590 := by
    simpa [prefixWord, tailWord_1080590, baseEnd_1080590] using wordTrace_append hprefix tailTrace_1080590
  have hstable : (prefixWord ++ tailWord_1080590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080590).length < 2 ^ (prefixWord ++ tailWord_1080590).sum := by decide
  have hdescent : baseEnd_1080590 < baseStart_1080590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080593 : List Nat := [1, 2, 2, 1, 1, 4, 2, 1, 4, 5]
def baseStart_1080593 : Nat := 118140960795 + 1080593 * 2 ^ 59
def prefixEnd_1080593 : Nat := 4983230072969 + 3 ^ 40 * 1080593 * 2
def baseEnd_1080593 : Nat := 184954533627998636205983

theorem tailTrace_1080593 : CollatzResearch.WordTrace tailWord_1080593 prefixEnd_1080593 184954533627998636205983 := by
  unfold tailWord_1080593
  simp only [CollatzResearch.WordTrace]
  refine ⟨39412464574203586436686433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26274976382802390957790955 39412464574203586436686433)
  ·
    refine ⟨29559348430652689827514825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39412464574203586436686433 29559348430652689827514825)
    ·
      refine ⟨22169511322989517370636119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29559348430652689827514825 22169511322989517370636119)
      ·
        refine ⟨33254266984484276055954179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22169511322989517370636119 33254266984484276055954179)
        ·
          refine ⟨49881400476726414083931269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33254266984484276055954179 49881400476726414083931269)
          ·
            refine ⟨9352762589386202640737113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49881400476726414083931269 9352762589386202640737113)
            ·
              refine ⟨7014571942039651980552835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9352762589386202640737113 7014571942039651980552835)
              ·
                refine ⟨10521857913059477970829253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7014571942039651980552835 10521857913059477970829253)
                ·
                  refine ⟨1972848358698652119530485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10521857913059477970829253 1972848358698652119530485)
                  ·
                    refine ⟨184954533627998636205983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1972848358698652119530485 184954533627998636205983)
                    ·
                      rfl

theorem cell23_1080593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 5].length) (baseStart_1080593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1080593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1080593 prefixEnd_1080593 := by exact prefixLift 1080593
  have htrace : WordTrace (prefixWord ++ tailWord_1080593) baseStart_1080593 baseEnd_1080593 := by
    simpa [prefixWord, tailWord_1080593, baseEnd_1080593] using wordTrace_append hprefix tailTrace_1080593
  have hstable : (prefixWord ++ tailWord_1080593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080593).length < 2 ^ (prefixWord ++ tailWord_1080593).sum := by decide
  have hdescent : baseEnd_1080593 < baseStart_1080593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080673 : List Nat := [1, 2, 3, 1, 1, 1, 1, 4, 1, 2, 6]
def baseStart_1080673 : Nat := 118140960795 + 1080673 * 2 ^ 59
def prefixEnd_1080673 : Nat := 4983230072969 + 3 ^ 40 * 1080673 * 2
def baseEnd_1080673 : Nat := 554904679336355595617581

theorem tailTrace_1080673 : CollatzResearch.WordTrace tailWord_1080673 prefixEnd_1080673 554904679336355595617581 := by
  unfold tailWord_1080673
  simp only [CollatzResearch.WordTrace]
  refine ⟨39415382413913760099598673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26276921609275840066399115 39415382413913760099598673)
  ·
    refine ⟨29561536810435320074699005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39415382413913760099598673 29561536810435320074699005)
    ·
      refine ⟨11085576303913245028012127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29561536810435320074699005 11085576303913245028012127)
      ·
        refine ⟨16628364455869867542018191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11085576303913245028012127 16628364455869867542018191)
        ·
          refine ⟨24942546683804801313027287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16628364455869867542018191 24942546683804801313027287)
          ·
            refine ⟨37413820025707201969540931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24942546683804801313027287 37413820025707201969540931)
            ·
              refine ⟨56120730038560802954311397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37413820025707201969540931 56120730038560802954311397)
              ·
                refine ⟨10522636882230150553933387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56120730038560802954311397 10522636882230150553933387)
                ·
                  refine ⟨15783955323345225830900081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10522636882230150553933387 15783955323345225830900081)
                  ·
                    refine ⟨11837966492508919373175061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15783955323345225830900081 11837966492508919373175061)
                    ·
                      refine ⟨554904679336355595617581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11837966492508919373175061 554904679336355595617581)
                      ·
                        rfl

theorem cell23_1080673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 2, 6].length) (baseStart_1080673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1080673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1080673 prefixEnd_1080673 := by exact prefixLift 1080673
  have htrace : WordTrace (prefixWord ++ tailWord_1080673) baseStart_1080673 baseEnd_1080673 := by
    simpa [prefixWord, tailWord_1080673, baseEnd_1080673] using wordTrace_append hprefix tailTrace_1080673
  have hstable : (prefixWord ++ tailWord_1080673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080673).length < 2 ^ (prefixWord ++ tailWord_1080673).sum := by decide
  have hdescent : baseEnd_1080673 < baseStart_1080673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080764 : List Nat := [2, 2, 2, 4, 2, 1, 1, 1, 4, 4]
def baseStart_1080764 : Nat := 118140960795 + 1080764 * 2 ^ 59
def prefixEnd_1080764 : Nat := 4983230072969 + 3 ^ 40 * 1080764 * 2
def baseEnd_1080764 : Nat := 184983802025304913193221

theorem tailTrace_1080764 : CollatzResearch.WordTrace tailWord_1080764 prefixEnd_1080764 184983802025304913193221 := by
  unfold tailWord_1080764
  simp only [CollatzResearch.WordTrace]
  refine ⟨19709350728292041320580673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26279134304389388427440897 19709350728292041320580673)
  ·
    refine ⟨14782013046219030990435505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19709350728292041320580673 14782013046219030990435505)
    ·
      refine ⟨11086509784664273242826629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14782013046219030990435505 11086509784664273242826629)
      ·
        refine ⟨2078720584624551233029993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11086509784664273242826629 2078720584624551233029993)
        ·
          refine ⟨1559040438468413424772495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2078720584624551233029993 1559040438468413424772495)
          ·
            refine ⟨2338560657702620137158743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1559040438468413424772495 2338560657702620137158743)
            ·
              refine ⟨3507840986553930205738115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2338560657702620137158743 3507840986553930205738115)
              ·
                refine ⟨5261761479830895308607173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3507840986553930205738115 5261761479830895308607173)
                ·
                  refine ⟨986580277468292870363845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5261761479830895308607173 986580277468292870363845)
                  ·
                    refine ⟨184983802025304913193221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 986580277468292870363845 184983802025304913193221)
                    ·
                      rfl

theorem cell23_1080764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 1, 4, 4].length) (baseStart_1080764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1080764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1080764 prefixEnd_1080764 := by exact prefixLift 1080764
  have htrace : WordTrace (prefixWord ++ tailWord_1080764) baseStart_1080764 baseEnd_1080764 := by
    simpa [prefixWord, tailWord_1080764, baseEnd_1080764] using wordTrace_append hprefix tailTrace_1080764
  have hstable : (prefixWord ++ tailWord_1080764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080764).length < 2 ^ (prefixWord ++ tailWord_1080764).sum := by decide
  have hdescent : baseEnd_1080764 < baseStart_1080764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080771 : List Nat := [1, 1, 1, 3, 1, 1, 6, 4, 1, 2, 2]
def baseStart_1080771 : Nat := 118140960795 + 1080771 * 2 ^ 59
def prefixEnd_1080771 : Nat := 4983230072969 + 3 ^ 40 * 1080771 * 2
def baseEnd_1080771 : Nat := 554955000440496212192131

theorem tailTrace_1080771 : CollatzResearch.WordTrace tailWord_1080771 prefixEnd_1080771 554955000440496212192131 := by
  unfold tailWord_1080771
  simp only [CollatzResearch.WordTrace]
  refine ⟨39418956767558722836666167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26279304511705815224444111 39418956767558722836666167)
  ·
    refine ⟨59128435151338084254999251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39418956767558722836666167 59128435151338084254999251)
    ·
      refine ⟨88692652727007126382498877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59128435151338084254999251 88692652727007126382498877)
      ·
        refine ⟨33259744772627672393437079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88692652727007126382498877 33259744772627672393437079)
        ·
          refine ⟨49889617158941508590155619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33259744772627672393437079 49889617158941508590155619)
          ·
            refine ⟨74834425738412262885233429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49889617158941508590155619 74834425738412262885233429)
            ·
              refine ⟨3507863706488074822745317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 74834425738412262885233429 3507863706488074822745317)
              ·
                refine ⟨657724444966514029264747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3507863706488074822745317 657724444966514029264747)
                ·
                  refine ⟨986586667449771043897121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 657724444966514029264747 986586667449771043897121)
                  ·
                    refine ⟨739940000587328282922841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 986586667449771043897121 739940000587328282922841)
                    ·
                      refine ⟨554955000440496212192131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 739940000587328282922841 554955000440496212192131)
                      ·
                        rfl

theorem cell23_1080771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 4, 1, 2, 2].length) (baseStart_1080771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1080771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1080771 prefixEnd_1080771 := by exact prefixLift 1080771
  have htrace : WordTrace (prefixWord ++ tailWord_1080771) baseStart_1080771 baseEnd_1080771 := by
    simpa [prefixWord, tailWord_1080771, baseEnd_1080771] using wordTrace_append hprefix tailTrace_1080771
  have hstable : (prefixWord ++ tailWord_1080771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080771).length < 2 ^ (prefixWord ++ tailWord_1080771).sum := by decide
  have hdescent : baseEnd_1080771 < baseStart_1080771 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080805 : List Nat := [1, 3, 1, 5, 1, 3, 1, 3, 1, 2, 2]
def baseStart_1080805 : Nat := 118140960795 + 1080805 * 2 ^ 59
def prefixEnd_1080805 : Nat := 4983230072969 + 3 ^ 40 * 1080805 * 2
def baseEnd_1080805 : Nat := 554972458782749079166975

theorem tailTrace_1080805 : CollatzResearch.WordTrace tailWord_1080805 prefixEnd_1080805 554972458782749079166975 := by
  unfold tailWord_1080805
  simp only [CollatzResearch.WordTrace]
  refine ⟨39420196849435546643403869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26280131232957031095602579 39420196849435546643403869)
  ·
    refine ⟨14782573818538329991276451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39420196849435546643403869 14782573818538329991276451)
    ·
      refine ⟨22173860727807494986914677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14782573818538329991276451 22173860727807494986914677)
      ·
        refine ⟨2078799443231952655023251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22173860727807494986914677 2078799443231952655023251)
        ·
          refine ⟨3118199164847928982534877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2078799443231952655023251 3118199164847928982534877)
          ·
            refine ⟨1169324686817973368450579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3118199164847928982534877 1169324686817973368450579)
            ·
              refine ⟨1753987030226960052675869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1169324686817973368450579 1753987030226960052675869)
              ·
                refine ⟨657745136335110019753451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1753987030226960052675869 657745136335110019753451)
                ·
                  refine ⟨986617704502665029630177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 657745136335110019753451 986617704502665029630177)
                  ·
                    refine ⟨739963278376998772222633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 986617704502665029630177 739963278376998772222633)
                    ·
                      refine ⟨554972458782749079166975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 739963278376998772222633 554972458782749079166975)
                      ·
                        rfl

theorem cell23_1080805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_1080805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1080805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1080805 prefixEnd_1080805 := by exact prefixLift 1080805
  have htrace : WordTrace (prefixWord ++ tailWord_1080805) baseStart_1080805 baseEnd_1080805 := by
    simpa [prefixWord, tailWord_1080805, baseEnd_1080805] using wordTrace_append hprefix tailTrace_1080805
  have hstable : (prefixWord ++ tailWord_1080805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080805).length < 2 ^ (prefixWord ++ tailWord_1080805).sum := by decide
  have hdescent : baseEnd_1080805 < baseStart_1080805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080821 : List Nat := [1, 3, 5, 1, 1, 1, 2, 1, 4, 1, 3]
def baseStart_1080821 : Nat := 118140960795 + 1080821 * 2 ^ 59
def prefixEnd_1080821 : Nat := 4983230072969 + 3 ^ 40 * 1080821 * 2
def baseEnd_1080821 : Nat := 554980674473221016566901

theorem tailTrace_1080821 : CollatzResearch.WordTrace tailWord_1080821 prefixEnd_1080821 554980674473221016566901 := by
  unfold tailWord_1080821
  simp only [CollatzResearch.WordTrace]
  refine ⟨39420780417377581375986317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26280520278251720917324211 39420780417377581375986317)
  ·
    refine ⟨14782792656516593015994869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39420780417377581375986317 14782792656516593015994869)
    ·
      refine ⟨1385886811548430595249519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14782792656516593015994869 1385886811548430595249519)
      ·
        refine ⟨2078830217322645892874279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1385886811548430595249519 2078830217322645892874279)
        ·
          refine ⟨3118245325983968839311419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2078830217322645892874279 3118245325983968839311419)
          ·
            refine ⟨4677367988975953258967129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3118245325983968839311419 4677367988975953258967129)
            ·
              refine ⟨3508025991731964944225347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4677367988975953258967129 3508025991731964944225347)
              ·
                refine ⟨5262038987597947416338021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3508025991731964944225347 5262038987597947416338021)
                ·
                  refine ⟨986632310174615140563379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5262038987597947416338021 986632310174615140563379)
                  ·
                    refine ⟨1479948465261922710845069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 986632310174615140563379 1479948465261922710845069)
                    ·
                      refine ⟨554980674473221016566901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1479948465261922710845069 554980674473221016566901)
                      ·
                        rfl

theorem cell23_1080821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_1080821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1080821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1080821 prefixEnd_1080821 := by exact prefixLift 1080821
  have htrace : WordTrace (prefixWord ++ tailWord_1080821) baseStart_1080821 baseEnd_1080821 := by
    simpa [prefixWord, tailWord_1080821, baseEnd_1080821] using wordTrace_append hprefix tailTrace_1080821
  have hstable : (prefixWord ++ tailWord_1080821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080821).length < 2 ^ (prefixWord ++ tailWord_1080821).sum := by decide
  have hdescent : baseEnd_1080821 < baseStart_1080821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080827 : List Nat := [1, 1, 1, 1, 1, 3, 2, 4, 3, 4, 2]
def baseStart_1080827 : Nat := 118140960795 + 1080827 * 2 ^ 59
def prefixEnd_1080827 : Nat := 4983230072969 + 3 ^ 40 * 1080827 * 2
def baseEnd_1080827 : Nat := 554983755357147993091873

theorem tailTrace_1080827 : CollatzResearch.WordTrace tailWord_1080827 prefixEnd_1080827 554983755357147993091873 := by
  unfold tailWord_1080827
  simp only [CollatzResearch.WordTrace]
  refine ⟨39420999255355844400704735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26280666170237229600469823 39420999255355844400704735)
  ·
    refine ⟨59131498883033766601057103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39420999255355844400704735 59131498883033766601057103)
    ·
      refine ⟨88697248324550649901585655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59131498883033766601057103 88697248324550649901585655)
      ·
        refine ⟨133045872486825974852378483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88697248324550649901585655 133045872486825974852378483)
        ·
          refine ⟨199568808730238962278567725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133045872486825974852378483 199568808730238962278567725)
          ·
            refine ⟨74838303273839610854462897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 199568808730238962278567725 74838303273839610854462897)
            ·
              refine ⟨56128727455379708140847173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74838303273839610854462897 56128727455379708140847173)
              ·
                refine ⟨10524136397883695276408845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56128727455379708140847173 10524136397883695276408845)
                ·
                  refine ⟨3946551149206385728653317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10524136397883695276408845 3946551149206385728653317)
                  ·
                    refine ⟨739978340476197324122497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3946551149206385728653317 739978340476197324122497)
                    ·
                      refine ⟨554983755357147993091873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 739978340476197324122497 554983755357147993091873)
                      ·
                        rfl

theorem cell23_1080827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 3, 4, 2].length) (baseStart_1080827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1080827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1080827 prefixEnd_1080827 := by exact prefixLift 1080827
  have htrace : WordTrace (prefixWord ++ tailWord_1080827) baseStart_1080827 baseEnd_1080827 := by
    simpa [prefixWord, tailWord_1080827, baseEnd_1080827] using wordTrace_append hprefix tailTrace_1080827
  have hstable : (prefixWord ++ tailWord_1080827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080827).length < 2 ^ (prefixWord ++ tailWord_1080827).sum := by decide
  have hdescent : baseEnd_1080827 < baseStart_1080827 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080878 : List Nat := [4, 1, 3, 1, 2, 1, 1, 4, 2, 2, 2]
def baseStart_1080878 : Nat := 118140960795 + 1080878 * 2 ^ 59
def prefixEnd_1080878 : Nat := 4983230072969 + 3 ^ 40 * 1080878 * 2
def baseEnd_1080878 : Nat := 555009942870527293554139

theorem tailTrace_1080878 : CollatzResearch.WordTrace tailWord_1080878 prefixEnd_1080878 555009942870527293554139 := by
  unfold tailWord_1080878
  simp only [CollatzResearch.WordTrace]
  refine ⟨4927857422271385013851411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26281906252114053407207525 4927857422271385013851411)
  ·
    refine ⟨7391786133407077520777117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4927857422271385013851411 7391786133407077520777117)
    ·
      refine ⟨2771919800027654070291419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7391786133407077520777117 2771919800027654070291419)
      ·
        refine ⟨4157879700041481105437129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2771919800027654070291419 4157879700041481105437129)
        ·
          refine ⟨3118409775031110829077847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4157879700041481105437129 3118409775031110829077847)
          ·
            refine ⟨4677614662546666243616771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3118409775031110829077847 4677614662546666243616771)
            ·
              refine ⟨7016421993819999365425157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4677614662546666243616771 7016421993819999365425157)
              ·
                refine ⟨1315579123841249881017217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7016421993819999365425157 1315579123841249881017217)
                ·
                  refine ⟨986684342880937410762913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1315579123841249881017217 986684342880937410762913)
                  ·
                    refine ⟨740013257160703058072185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 986684342880937410762913 740013257160703058072185)
                    ·
                      refine ⟨555009942870527293554139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 740013257160703058072185 555009942870527293554139)
                      ·
                        rfl

theorem cell23_1080878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 4, 2, 2, 2].length) (baseStart_1080878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1080878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1080878 prefixEnd_1080878 := by exact prefixLift 1080878
  have htrace : WordTrace (prefixWord ++ tailWord_1080878) baseStart_1080878 baseEnd_1080878 := by
    simpa [prefixWord, tailWord_1080878, baseEnd_1080878] using wordTrace_append hprefix tailTrace_1080878
  have hstable : (prefixWord ++ tailWord_1080878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080878).length < 2 ^ (prefixWord ++ tailWord_1080878).sum := by decide
  have hdescent : baseEnd_1080878 < baseStart_1080878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080880 : List Nat := [2, 1, 1, 1, 2, 3, 1, 2, 3, 7]
def baseStart_1080880 : Nat := 118140960795 + 1080880 * 2 ^ 59
def prefixEnd_1080880 : Nat := 4983230072969 + 3 ^ 40 * 1080880 * 2
def baseEnd_1080880 : Nat := 185003656610612095243043

theorem tailTrace_1080880 : CollatzResearch.WordTrace tailWord_1080880 prefixEnd_1080880 185003656610612095243043 := by
  unfold tailWord_1080880
  simp only [CollatzResearch.WordTrace]
  refine ⟨19711466162081917226192047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26281954882775889634922729 19711466162081917226192047)
  ·
    refine ⟨29567199243122875839288071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19711466162081917226192047 29567199243122875839288071)
    ·
      refine ⟨44350798864684313758932107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29567199243122875839288071 44350798864684313758932107)
      ·
        refine ⟨66526198297026470638398161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44350798864684313758932107 66526198297026470638398161)
        ·
          refine ⟨49894648722769852978798621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66526198297026470638398161 49894648722769852978798621)
          ·
            refine ⟨18710493271038694867049483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49894648722769852978798621 18710493271038694867049483)
            ·
              refine ⟨28065739906558042300574225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18710493271038694867049483 28065739906558042300574225)
              ·
                refine ⟨21049304929918531725430669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28065739906558042300574225 21049304929918531725430669)
                ·
                  refine ⟨7893489348719449397036501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21049304929918531725430669 7893489348719449397036501)
                  ·
                    refine ⟨185003656610612095243043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7893489348719449397036501 185003656610612095243043)
                    ·
                      rfl

theorem cell23_1080880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 3, 7].length) (baseStart_1080880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1080880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1080880 prefixEnd_1080880 := by exact prefixLift 1080880
  have htrace : WordTrace (prefixWord ++ tailWord_1080880) baseStart_1080880 baseEnd_1080880 := by
    simpa [prefixWord, tailWord_1080880, baseEnd_1080880] using wordTrace_append hprefix tailTrace_1080880
  have hstable : (prefixWord ++ tailWord_1080880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080880).length < 2 ^ (prefixWord ++ tailWord_1080880).sum := by decide
  have hdescent : baseEnd_1080880 < baseStart_1080880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080897 : List Nat := [1, 2, 5, 1, 1, 1, 2, 2, 1, 7]
def baseStart_1080897 : Nat := 118140960795 + 1080897 * 2 ^ 59
def prefixEnd_1080897 : Nat := 4983230072969 + 3 ^ 40 * 1080897 * 2
def baseEnd_1080897 : Nat := 185006566334320906405517

theorem tailTrace_1080897 : CollatzResearch.WordTrace tailWord_1080897 prefixEnd_1080897 185006566334320906405517 := by
  unfold tailWord_1080897
  simp only [CollatzResearch.WordTrace]
  refine ⟨39423552365102246355752945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26282368243401497570501963 39423552365102246355752945)
  ·
    refine ⟨29567664273826684766814709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39423552365102246355752945 29567664273826684766814709)
    ·
      refine ⟨2771968525671251696888879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29567664273826684766814709 2771968525671251696888879)
      ·
        refine ⟨4157952788506877545333319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2771968525671251696888879 4157952788506877545333319)
        ·
          refine ⟨6236929182760316317999979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4157952788506877545333319 6236929182760316317999979)
          ·
            refine ⟨9355393774140474476999969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6236929182760316317999979 9355393774140474476999969)
            ·
              refine ⟨7016545330605355857749977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9355393774140474476999969 7016545330605355857749977)
              ·
                refine ⟨5262408997954016893312483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7016545330605355857749977 5262408997954016893312483)
                ·
                  refine ⟨7893613496931025339968725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5262408997954016893312483 7893613496931025339968725)
                  ·
                    refine ⟨185006566334320906405517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7893613496931025339968725 185006566334320906405517)
                    ·
                      rfl

theorem cell23_1080897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_1080897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1080897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1080897 prefixEnd_1080897 := by exact prefixLift 1080897
  have htrace : WordTrace (prefixWord ++ tailWord_1080897) baseStart_1080897 baseEnd_1080897 := by
    simpa [prefixWord, tailWord_1080897, baseEnd_1080897] using wordTrace_append hprefix tailTrace_1080897
  have hstable : (prefixWord ++ tailWord_1080897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080897).length < 2 ^ (prefixWord ++ tailWord_1080897).sum := by decide
  have hdescent : baseEnd_1080897 < baseStart_1080897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080914 : List Nat := [3, 2, 2, 1, 2, 2, 3, 1, 2, 5]
def baseStart_1080914 : Nat := 118140960795 + 1080914 * 2 ^ 59
def prefixEnd_1080914 : Nat := 4983230072969 + 3 ^ 40 * 1080914 * 2
def baseEnd_1080914 : Nat := 185009476058029717567991

theorem tailTrace_1080914 : CollatzResearch.WordTrace tailWord_1080914 prefixEnd_1080914 185009476058029717567991 := by
  unfold tailWord_1080914
  simp only [CollatzResearch.WordTrace]
  refine ⟨9856043101510164564780449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26282781604027105506081197 9856043101510164564780449)
  ·
    refine ⟨7392032326132623423585337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9856043101510164564780449 7392032326132623423585337)
    ·
      refine ⟨5544024244599467567689003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7392032326132623423585337 5544024244599467567689003)
      ·
        refine ⟨8316036366899201351533505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5544024244599467567689003 8316036366899201351533505)
        ·
          refine ⟨6237027275174401013650129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8316036366899201351533505 6237027275174401013650129)
          ·
            refine ⟨4677770456380800760237597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6237027275174401013650129 4677770456380800760237597)
            ·
              refine ⟨1754163921142800285089099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4677770456380800760237597 1754163921142800285089099)
              ·
                refine ⟨2631245881714200427633649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1754163921142800285089099 2631245881714200427633649)
                ·
                  refine ⟨1973434411285650320725237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2631245881714200427633649 1973434411285650320725237)
                  ·
                    refine ⟨185009476058029717567991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1973434411285650320725237 185009476058029717567991)
                    ·
                      rfl

theorem cell23_1080914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 1, 2, 5].length) (baseStart_1080914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1080914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1080914 prefixEnd_1080914 := by exact prefixLift 1080914
  have htrace : WordTrace (prefixWord ++ tailWord_1080914) baseStart_1080914 baseEnd_1080914 := by
    simpa [prefixWord, tailWord_1080914, baseEnd_1080914] using wordTrace_append hprefix tailTrace_1080914
  have hstable : (prefixWord ++ tailWord_1080914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080914).length < 2 ^ (prefixWord ++ tailWord_1080914).sum := by decide
  have hdescent : baseEnd_1080914 < baseStart_1080914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080944 : List Nat := [2, 1, 1, 1, 6, 1, 1, 3, 3, 4]
def baseStart_1080944 : Nat := 118140960795 + 1080944 * 2 ^ 59
def prefixEnd_1080944 : Nat := 4983230072969 + 3 ^ 40 * 1080944 * 2
def baseEnd_1080944 : Nat := 185014610864574678442945

theorem tailTrace_1080944 : CollatzResearch.WordTrace tailWord_1080944 prefixEnd_1080944 185014610864574678442945 := by
  unfold tailWord_1080944
  simp only [CollatzResearch.WordTrace]
  refine ⟨19712633297965986691356943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26283511063954648921809257 19712633297965986691356943)
  ·
    refine ⟨29568949946948980037035415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19712633297965986691356943 29568949946948980037035415)
    ·
      refine ⟨44353424920423470055553123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29568949946948980037035415 44353424920423470055553123)
      ·
        refine ⟨66530137380635205083329685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44353424920423470055553123 66530137380635205083329685)
        ·
          refine ⟨3118600189717275238281079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 66530137380635205083329685 3118600189717275238281079)
          ·
            refine ⟨4677900284575912857421619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3118600189717275238281079 4677900284575912857421619)
            ·
              refine ⟨7016850426863869286132429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4677900284575912857421619 7016850426863869286132429)
              ·
                refine ⟨2631318910073950982299661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7016850426863869286132429 2631318910073950982299661)
                ·
                  refine ⟨986744591277731618362373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2631318910073950982299661 986744591277731618362373)
                  ·
                    refine ⟨185014610864574678442945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 986744591277731618362373 185014610864574678442945)
                    ·
                      rfl

theorem cell23_1080944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 3, 3, 4].length) (baseStart_1080944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1080944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1080944 prefixEnd_1080944 := by exact prefixLift 1080944
  have htrace : WordTrace (prefixWord ++ tailWord_1080944) baseStart_1080944 baseEnd_1080944 := by
    simpa [prefixWord, tailWord_1080944, baseEnd_1080944] using wordTrace_append hprefix tailTrace_1080944
  have hstable : (prefixWord ++ tailWord_1080944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080944).length < 2 ^ (prefixWord ++ tailWord_1080944).sum := by decide
  have hdescent : baseEnd_1080944 < baseStart_1080944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081024 : List Nat := [2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 4]
def baseStart_1081024 : Nat := 118140960795 + 1081024 * 2 ^ 59
def prefixEnd_1081024 : Nat := 4983230072969 + 3 ^ 40 * 1081024 * 2
def baseEnd_1081024 : Nat := 555084911046083722328467

theorem tailTrace_1081024 : CollatzResearch.WordTrace tailWord_1081024 prefixEnd_1081024 555084911046083722328467 := by
  unfold tailWord_1081024
  simp only [CollatzResearch.WordTrace]
  refine ⟨19714092217821073522813063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26285456290428098030417417 19714092217821073522813063)
  ·
    refine ⟨29571138326731610284219595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19714092217821073522813063 29571138326731610284219595)
    ·
      refine ⟨44356707490097415426329393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29571138326731610284219595 44356707490097415426329393)
      ·
        refine ⟨33267530617573061569747045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44356707490097415426329393 33267530617573061569747045)
        ·
          refine ⟨6237661990794949044327571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33267530617573061569747045 6237661990794949044327571)
          ·
            refine ⟨9356492986192423566491357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6237661990794949044327571 9356492986192423566491357)
            ·
              refine ⟨3508684869822158837434259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9356492986192423566491357 3508684869822158837434259)
              ·
                refine ⟨5263027304733238256151389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3508684869822158837434259 5263027304733238256151389)
                ·
                  refine ⟨1973635239274964346056771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5263027304733238256151389 1973635239274964346056771)
                  ·
                    refine ⟨2960452858912446519085157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1973635239274964346056771 2960452858912446519085157)
                    ·
                      refine ⟨555084911046083722328467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2960452858912446519085157 555084911046083722328467)
                      ·
                        rfl

theorem cell23_1081024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 4].length) (baseStart_1081024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1081024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1081024 prefixEnd_1081024 := by exact prefixLift 1081024
  have htrace : WordTrace (prefixWord ++ tailWord_1081024) baseStart_1081024 baseEnd_1081024 := by
    simpa [prefixWord, tailWord_1081024, baseEnd_1081024] using wordTrace_append hprefix tailTrace_1081024
  have hstable : (prefixWord ++ tailWord_1081024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081024).length < 2 ^ (prefixWord ++ tailWord_1081024).sum := by decide
  have hdescent : baseEnd_1081024 < baseStart_1081024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081028 : List Nat := [2, 3, 3, 1, 1, 1, 4, 1, 2, 3, 2]
def baseStart_1081028 : Nat := 118140960795 + 1081028 * 2 ^ 59
def prefixEnd_1081028 : Nat := 4983230072969 + 3 ^ 40 * 1081028 * 2
def baseEnd_1081028 : Nat := 555086964968701706678449

theorem tailTrace_1081028 : CollatzResearch.WordTrace tailWord_1081028 prefixEnd_1081028 555086964968701706678449 := by
  unfold tailWord_1081028
  simp only [CollatzResearch.WordTrace]
  refine ⟨19714165163813827864385869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26285553551751770485847825 19714165163813827864385869)
  ·
    refine ⟨7392811936430185449144701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19714165163813827864385869 7392811936430185449144701)
    ·
      refine ⟨2772304476161319543429263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7392811936430185449144701 2772304476161319543429263)
      ·
        refine ⟨4158456714241979315143895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2772304476161319543429263 4158456714241979315143895)
        ·
          refine ⟨6237685071362968972715843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4158456714241979315143895 6237685071362968972715843)
          ·
            refine ⟨9356527607044453459073765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6237685071362968972715843 9356527607044453459073765)
            ·
              refine ⟨1754348926320835023576331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9356527607044453459073765 1754348926320835023576331)
              ·
                refine ⟨2631523389481252535364497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1754348926320835023576331 2631523389481252535364497)
                ·
                  refine ⟨1973642542110939401523373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2631523389481252535364497 1973642542110939401523373)
                  ·
                    refine ⟨740115953291602275571265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1973642542110939401523373 740115953291602275571265)
                    ·
                      refine ⟨555086964968701706678449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 740115953291602275571265 555086964968701706678449)
                      ·
                        rfl

theorem cell23_1081028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 1, 2, 3, 2].length) (baseStart_1081028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1081028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1081028 prefixEnd_1081028 := by exact prefixLift 1081028
  have htrace : WordTrace (prefixWord ++ tailWord_1081028) baseStart_1081028 baseEnd_1081028 := by
    simpa [prefixWord, tailWord_1081028, baseEnd_1081028] using wordTrace_append hprefix tailTrace_1081028
  have hstable : (prefixWord ++ tailWord_1081028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081028).length < 2 ^ (prefixWord ++ tailWord_1081028).sum := by decide
  have hdescent : baseEnd_1081028 < baseStart_1081028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081046 : List Nat := [5, 2, 1, 3, 2, 1, 2, 2, 1, 4]
def baseStart_1081046 : Nat := 118140960795 + 1081046 * 2 ^ 59
def prefixEnd_1081046 : Nat := 4983230072969 + 3 ^ 40 * 1081046 * 2
def baseEnd_1081046 : Nat := 185032069206827545417789

theorem tailTrace_1081046 : CollatzResearch.WordTrace tailWord_1081046 prefixEnd_1081046 185032069206827545417789 := by
  unfold tailWord_1081046
  simp only [CollatzResearch.WordTrace]
  refine ⟨2464311677597652800182937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26285991227708296535284661 2464311677597652800182937)
  ·
    refine ⟨1848233758198239600137203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2464311677597652800182937 1848233758198239600137203)
    ·
      refine ⟨2772350637297359400205805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1848233758198239600137203 2772350637297359400205805)
      ·
        refine ⟨1039631488986509775077177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2772350637297359400205805 1039631488986509775077177)
        ·
          refine ⟨779723616739882331307883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1039631488986509775077177 779723616739882331307883)
          ·
            refine ⟨1169585425109823496961825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 779723616739882331307883 1169585425109823496961825)
            ·
              refine ⟨877189068832367622721369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1169585425109823496961825 877189068832367622721369)
              ·
                refine ⟨657891801624275717041027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 877189068832367622721369 657891801624275717041027)
                ·
                  refine ⟨986837702436413575561541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 657891801624275717041027 986837702436413575561541)
                  ·
                    refine ⟨185032069206827545417789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 986837702436413575561541 185032069206827545417789)
                    ·
                      rfl

theorem cell23_1081046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_1081046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1081046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1081046 prefixEnd_1081046 := by exact prefixLift 1081046
  have htrace : WordTrace (prefixWord ++ tailWord_1081046) baseStart_1081046 baseEnd_1081046 := by
    simpa [prefixWord, tailWord_1081046, baseEnd_1081046] using wordTrace_append hprefix tailTrace_1081046
  have hstable : (prefixWord ++ tailWord_1081046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081046).length < 2 ^ (prefixWord ++ tailWord_1081046).sum := by decide
  have hdescent : baseEnd_1081046 < baseStart_1081046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081052 : List Nat := [2, 2, 5, 1, 2, 1, 1, 4, 1, 1, 3]
def baseStart_1081052 : Nat := 118140960795 + 1081052 * 2 ^ 59
def prefixEnd_1081052 : Nat := 4983230072969 + 3 ^ 40 * 1081052 * 2
def baseEnd_1081052 : Nat := 555099288504409612778339

theorem tailTrace_1081052 : CollatzResearch.WordTrace tailWord_1081052 prefixEnd_1081052 555099288504409612778339 := by
  unfold tailWord_1081052
  simp only [CollatzResearch.WordTrace]
  refine ⟨19714602839770353913822705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26286137119693805218430273 19714602839770353913822705)
  ·
    refine ⟨14785952129827765435367029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19714602839770353913822705 14785952129827765435367029)
    ·
      refine ⟨1386183012171353009565659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14785952129827765435367029 1386183012171353009565659)
      ·
        refine ⟨2079274518257029514348489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1386183012171353009565659 2079274518257029514348489)
        ·
          refine ⟨1559455888692772135761367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2079274518257029514348489 1559455888692772135761367)
          ·
            refine ⟨2339183833039158203642051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1559455888692772135761367 2339183833039158203642051)
            ·
              refine ⟨3508775749558737305463077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2339183833039158203642051 3508775749558737305463077)
              ·
                refine ⟨657895453042263244774327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3508775749558737305463077 657895453042263244774327)
                ·
                  refine ⟨986843179563394867161491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 657895453042263244774327 986843179563394867161491)
                  ·
                    refine ⟨1480264769345092300742237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 986843179563394867161491 1480264769345092300742237)
                    ·
                      refine ⟨555099288504409612778339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1480264769345092300742237 555099288504409612778339)
                      ·
                        rfl

theorem cell23_1081052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_1081052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1081052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1081052 prefixEnd_1081052 := by exact prefixLift 1081052
  have htrace : WordTrace (prefixWord ++ tailWord_1081052) baseStart_1081052 baseEnd_1081052 := by
    simpa [prefixWord, tailWord_1081052, baseEnd_1081052] using wordTrace_append hprefix tailTrace_1081052
  have hstable : (prefixWord ++ tailWord_1081052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081052).length < 2 ^ (prefixWord ++ tailWord_1081052).sum := by decide
  have hdescent : baseEnd_1081052 < baseStart_1081052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081064 : List Nat := [2, 1, 4, 1, 3, 1, 3, 8]
def baseStart_1081064 : Nat := 118140960795 + 1081064 * 2 ^ 59
def prefixEnd_1081064 : Nat := 4983230072969 + 3 ^ 40 * 1081064 * 2
def baseEnd_1081064 : Nat := 20559461121194946882529

theorem tailTrace_1081064 : CollatzResearch.WordTrace tailWord_1081064 prefixEnd_1081064 20559461121194946882529 := by
  unfold tailWord_1081064
  simp only [CollatzResearch.WordTrace]
  refine ⟨19714821677748616938541123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26286428903664822584721497 19714821677748616938541123)
  ·
    refine ⟨29572232516622925407811685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19714821677748616938541123 29572232516622925407811685)
    ·
      refine ⟨5544793596866798513964691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29572232516622925407811685 5544793596866798513964691)
      ·
        refine ⟨8317190395300197770947037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5544793596866798513964691 8317190395300197770947037)
        ·
          refine ⟨3118946398237574164105139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8317190395300197770947037 3118946398237574164105139)
          ·
            refine ⟨4678419597356361246157709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3118946398237574164105139 4678419597356361246157709)
            ·
              refine ⟨1754407349008635467309141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4678419597356361246157709 1754407349008635467309141)
              ·
                refine ⟨20559461121194946882529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1754407349008635467309141 20559461121194946882529)
                ·
                  rfl

theorem cell23_1081064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 8].length) (baseStart_1081064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1081064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1081064 prefixEnd_1081064 := by exact prefixLift 1081064
  have htrace : WordTrace (prefixWord ++ tailWord_1081064) baseStart_1081064 baseEnd_1081064 := by
    simpa [prefixWord, tailWord_1081064, baseEnd_1081064] using wordTrace_append hprefix tailTrace_1081064
  have hstable : (prefixWord ++ tailWord_1081064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081064).length < 2 ^ (prefixWord ++ tailWord_1081064).sum := by decide
  have hdescent : baseEnd_1081064 < baseStart_1081064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081067 : List Nat := [1, 1, 1, 1, 2, 4, 2, 1, 2, 2, 6]
def baseStart_1081067 : Nat := 118140960795 + 1081067 * 2 ^ 59
def prefixEnd_1081067 : Nat := 4983230072969 + 3 ^ 40 * 1081067 * 2
def baseEnd_1081067 : Nat := 555106990714227054090769

theorem tailTrace_1081067 : CollatzResearch.WordTrace tailWord_1081067 prefixEnd_1081067 555106990714227054090769 := by
  unfold tailWord_1081067
  simp only [CollatzResearch.WordTrace]
  refine ⟨39429752774486365389441455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26286501849657576926294303 39429752774486365389441455)
  ·
    refine ⟨59144629161729548084162183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39429752774486365389441455 59144629161729548084162183)
    ·
      refine ⟨88716943742594322126243275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59144629161729548084162183 88716943742594322126243275)
      ·
        refine ⟨133075415613891483189364913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88716943742594322126243275 133075415613891483189364913)
        ·
          refine ⟨99806561710418612392023685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133075415613891483189364913 99806561710418612392023685)
          ·
            refine ⟨18713730320703489823504441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 99806561710418612392023685 18713730320703489823504441)
            ·
              refine ⟨14035297740527617367628331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18713730320703489823504441 14035297740527617367628331)
              ·
                refine ⟨21052946610791426051442497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14035297740527617367628331 21052946610791426051442497)
                ·
                  refine ⟨15789709958093569538581873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21052946610791426051442497 15789709958093569538581873)
                  ·
                    refine ⟨11842282468570177153936405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15789709958093569538581873 11842282468570177153936405)
                    ·
                      refine ⟨555106990714227054090769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11842282468570177153936405 555106990714227054090769)
                      ·
                        rfl

theorem cell23_1081067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 2, 6].length) (baseStart_1081067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1081067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1081067 prefixEnd_1081067 := by exact prefixLift 1081067
  have htrace : WordTrace (prefixWord ++ tailWord_1081067) baseStart_1081067 baseEnd_1081067 := by
    simpa [prefixWord, tailWord_1081067, baseEnd_1081067] using wordTrace_append hprefix tailTrace_1081067
  have hstable : (prefixWord ++ tailWord_1081067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081067).length < 2 ^ (prefixWord ++ tailWord_1081067).sum := by decide
  have hdescent : baseEnd_1081067 < baseStart_1081067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081092 : List Nat := [2, 3, 2, 2, 1, 3, 2, 3, 1, 2, 2]
def baseStart_1081092 : Nat := 118140960795 + 1081092 * 2 ^ 59
def prefixEnd_1081092 : Nat := 4983230072969 + 3 ^ 40 * 1081092 * 2
def baseEnd_1081092 : Nat := 555119827730589456278155

theorem tailTrace_1081092 : CollatzResearch.WordTrace tailWord_1081092 prefixEnd_1081092 555119827730589456278155 := by
  unfold tailWord_1081092
  simp only [CollatzResearch.WordTrace]
  refine ⟨19715332299697897329550765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26287109732930529772734353 19715332299697897329550765)
  ·
    refine ⟨7393249612386711498581537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19715332299697897329550765 7393249612386711498581537)
    ·
      refine ⟨5544937209290033623936153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7393249612386711498581537 5544937209290033623936153)
      ·
        refine ⟨4158702906967525217952115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5544937209290033623936153 4158702906967525217952115)
        ·
          refine ⟨6238054360451287826928173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4158702906967525217952115 6238054360451287826928173)
          ·
            refine ⟨2339270385169232935098065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6238054360451287826928173 2339270385169232935098065)
            ·
              refine ⟨1754452788876924701323549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2339270385169232935098065 1754452788876924701323549)
              ·
                refine ⟨657919795828846762996331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1754452788876924701323549 657919795828846762996331)
                ·
                  refine ⟨986879693743270144494497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 657919795828846762996331 986879693743270144494497)
                  ·
                    refine ⟨740159770307452608370873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 986879693743270144494497 740159770307452608370873)
                    ·
                      refine ⟨555119827730589456278155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 740159770307452608370873 555119827730589456278155)
                      ·
                        rfl

theorem cell23_1081092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 3, 1, 2, 2].length) (baseStart_1081092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1081092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1081092 prefixEnd_1081092 := by exact prefixLift 1081092
  have htrace : WordTrace (prefixWord ++ tailWord_1081092) baseStart_1081092 baseEnd_1081092 := by
    simpa [prefixWord, tailWord_1081092, baseEnd_1081092] using wordTrace_append hprefix tailTrace_1081092
  have hstable : (prefixWord ++ tailWord_1081092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081092).length < 2 ^ (prefixWord ++ tailWord_1081092).sum := by decide
  have hdescent : baseEnd_1081092 < baseStart_1081092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081125 : List Nat := [1, 3, 1, 2, 3, 3, 3, 1, 2, 1, 3]
def baseStart_1081125 : Nat := 118140960795 + 1081125 * 2 ^ 59
def prefixEnd_1081125 : Nat := 4983230072969 + 3 ^ 40 * 1081125 * 2
def baseEnd_1081125 : Nat := 555136772592187827165503

theorem tailTrace_1081125 : CollatzResearch.WordTrace tailWord_1081125 prefixEnd_1081125 555136772592187827165503 := by
  unfold tailWord_1081125
  simp only [CollatzResearch.WordTrace]
  refine ⟨39431868208276241295052829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26287912138850827530035219 39431868208276241295052829)
  ·
    refine ⟨14786950578103590485644811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39431868208276241295052829 14786950578103590485644811)
    ·
      refine ⟨22180425867155385728467217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14786950578103590485644811 22180425867155385728467217)
      ·
        refine ⟨16635319400366539296350413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22180425867155385728467217 16635319400366539296350413)
        ·
          refine ⟨6238244775137452236131405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16635319400366539296350413 6238244775137452236131405)
          ·
            refine ⟨2339341790676544588549277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6238244775137452236131405 2339341790676544588549277)
            ·
              refine ⟨877253171503704220705979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2339341790676544588549277 877253171503704220705979)
              ·
                refine ⟨1315879757255556331058969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 877253171503704220705979 1315879757255556331058969)
                ·
                  refine ⟨986909817941667248294227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1315879757255556331058969 986909817941667248294227)
                  ·
                    refine ⟨1480364726912500872441341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 986909817941667248294227 1480364726912500872441341)
                    ·
                      refine ⟨555136772592187827165503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1480364726912500872441341 555136772592187827165503)
                      ·
                        rfl

theorem cell23_1081125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 3, 1, 2, 1, 3].length) (baseStart_1081125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1081125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1081125 prefixEnd_1081125 := by exact prefixLift 1081125
  have htrace : WordTrace (prefixWord ++ tailWord_1081125) baseStart_1081125 baseEnd_1081125 := by
    simpa [prefixWord, tailWord_1081125, baseEnd_1081125] using wordTrace_append hprefix tailTrace_1081125
  have hstable : (prefixWord ++ tailWord_1081125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081125).length < 2 ^ (prefixWord ++ tailWord_1081125).sum := by decide
  have hdescent : baseEnd_1081125 < baseStart_1081125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081148 : List Nat := [2, 2, 2, 2, 1, 1, 3, 2, 4, 2, 2]
def baseStart_1081148 : Nat := 118140960795 + 1081148 * 2 ^ 59
def prefixEnd_1081148 : Nat := 4983230072969 + 3 ^ 40 * 1081148 * 2
def baseEnd_1081148 : Nat := 555148582647241237177897

theorem tailTrace_1081148 : CollatzResearch.WordTrace tailWord_1081148 prefixEnd_1081148 555148582647241237177897 := by
  unfold tailWord_1081148
  simp only [CollatzResearch.WordTrace]
  refine ⟨19716353543596458111570049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26288471391461944148760065 19716353543596458111570049)
  ·
    refine ⟨14787265157697343583677537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19716353543596458111570049 14787265157697343583677537)
    ·
      refine ⟨11090448868273007687758153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14787265157697343583677537 11090448868273007687758153)
      ·
        refine ⟨8317836651204755765818615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11090448868273007687758153 8317836651204755765818615)
        ·
          refine ⟨12476754976807133648727923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8317836651204755765818615 12476754976807133648727923)
          ·
            refine ⟨18715132465210700473091885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12476754976807133648727923 18715132465210700473091885)
            ·
              refine ⟨7018174674454012677409457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18715132465210700473091885 7018174674454012677409457)
              ·
                refine ⟨5263631005840509508057093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7018174674454012677409457 5263631005840509508057093)
                ·
                  refine ⟨986930813595095532760705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5263631005840509508057093 986930813595095532760705)
                  ·
                    refine ⟨740198110196321649570529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 986930813595095532760705 740198110196321649570529)
                    ·
                      refine ⟨555148582647241237177897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 740198110196321649570529 555148582647241237177897)
                      ·
                        rfl

theorem cell23_1081148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 2, 4, 2, 2].length) (baseStart_1081148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1081148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1081148 prefixEnd_1081148 := by exact prefixLift 1081148
  have htrace : WordTrace (prefixWord ++ tailWord_1081148) baseStart_1081148 baseEnd_1081148 := by
    simpa [prefixWord, tailWord_1081148, baseEnd_1081148] using wordTrace_append hprefix tailTrace_1081148
  have hstable : (prefixWord ++ tailWord_1081148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081148).length < 2 ^ (prefixWord ++ tailWord_1081148).sum := by decide
  have hdescent : baseEnd_1081148 < baseStart_1081148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081151 : List Nat := [1, 1, 2, 2, 6, 1, 1, 1, 2, 1, 5]
def baseStart_1081151 : Nat := 118140960795 + 1081151 * 2 ^ 59
def prefixEnd_1081151 : Nat := 4983230072969 + 3 ^ 40 * 1081151 * 2
def baseEnd_1081151 : Nat := 555150123089204725440383

theorem tailTrace_1081151 : CollatzResearch.WordTrace tailWord_1081151 prefixEnd_1081151 555150123089204725440383 := by
  unfold tailWord_1081151
  simp only [CollatzResearch.WordTrace]
  refine ⟨39432816506182047735499307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26288544337454698490332871 39432816506182047735499307)
  ·
    refine ⟨59149224759273071603248961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39432816506182047735499307 59149224759273071603248961)
    ·
      refine ⟨44361918569454803702436721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59149224759273071603248961 44361918569454803702436721)
      ·
        refine ⟨33271438927091102776827541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44361918569454803702436721 33271438927091102776827541)
        ·
          refine ⟨1559598699707395442663791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 33271438927091102776827541 1559598699707395442663791)
          ·
            refine ⟨2339398049561093163995687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1559598699707395442663791 2339398049561093163995687)
            ·
              refine ⟨3509097074341639745993531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2339398049561093163995687 3509097074341639745993531)
              ·
                refine ⟨5263645611512459618990297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3509097074341639745993531 5263645611512459618990297)
                ·
                  refine ⟨3947734208634344714242723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5263645611512459618990297 3947734208634344714242723)
                  ·
                    refine ⟨5921601312951517071364085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3947734208634344714242723 5921601312951517071364085)
                    ·
                      refine ⟨555150123089204725440383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5921601312951517071364085 555150123089204725440383)
                      ·
                        rfl

theorem cell23_1081151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 1, 2, 1, 5].length) (baseStart_1081151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1081151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1081151 prefixEnd_1081151 := by exact prefixLift 1081151
  have htrace : WordTrace (prefixWord ++ tailWord_1081151) baseStart_1081151 baseEnd_1081151 := by
    simpa [prefixWord, tailWord_1081151, baseEnd_1081151] using wordTrace_append hprefix tailTrace_1081151
  have hstable : (prefixWord ++ tailWord_1081151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081151).length < 2 ^ (prefixWord ++ tailWord_1081151).sum := by decide
  have hdescent : baseEnd_1081151 < baseStart_1081151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081201 : List Nat := [1, 2, 2, 2, 1, 3, 4, 1, 2, 5]
def baseStart_1081201 : Nat := 118140960795 + 1081201 * 2 ^ 59
def prefixEnd_1081201 : Nat := 4983230072969 + 3 ^ 40 * 1081201 * 2
def baseEnd_1081201 : Nat := 185058599040643176605051

theorem tailTrace_1081201 : CollatzResearch.WordTrace tailWord_1081201 prefixEnd_1081201 185058599040643176605051 := by
  unfold tailWord_1081201
  simp only [CollatzResearch.WordTrace]
  refine ⟨39434640156000906274819457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26289760104000604183212971 39434640156000906274819457)
  ·
    refine ⟨29575980117000679706114593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39434640156000906274819457 29575980117000679706114593)
    ·
      refine ⟨22181985087750509779585945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29575980117000679706114593 22181985087750509779585945)
      ·
        refine ⟨16636488815812882334689459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22181985087750509779585945 16636488815812882334689459)
        ·
          refine ⟨24954733223719323502034189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16636488815812882334689459 24954733223719323502034189)
          ·
            refine ⟨9358024958894746313262821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24954733223719323502034189 9358024958894746313262821)
            ·
              refine ⟨1754629679792764933736779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9358024958894746313262821 1754629679792764933736779)
              ·
                refine ⟨2631944519689147400605169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1754629679792764933736779 2631944519689147400605169)
                ·
                  refine ⟨1973958389766860550453877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2631944519689147400605169 1973958389766860550453877)
                  ·
                    refine ⟨185058599040643176605051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1973958389766860550453877 185058599040643176605051)
                    ·
                      rfl

theorem cell23_1081201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 1, 2, 5].length) (baseStart_1081201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1081201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1081201 prefixEnd_1081201 := by exact prefixLift 1081201
  have htrace : WordTrace (prefixWord ++ tailWord_1081201) baseStart_1081201 baseEnd_1081201 := by
    simpa [prefixWord, tailWord_1081201, baseEnd_1081201] using wordTrace_append hprefix tailTrace_1081201
  have hstable : (prefixWord ++ tailWord_1081201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081201).length < 2 ^ (prefixWord ++ tailWord_1081201).sum := by decide
  have hdescent : baseEnd_1081201 < baseStart_1081201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081221 : List Nat := [1, 3, 1, 1, 3, 2, 1, 4, 2, 1, 4]
def baseStart_1081221 : Nat := 118140960795 + 1081221 * 2 ^ 59
def prefixEnd_1081221 : Nat := 4983230072969 + 3 ^ 40 * 1081221 * 2
def baseEnd_1081221 : Nat := 555186066735019451565061

theorem tailTrace_1081221 : CollatzResearch.WordTrace tailWord_1081221 prefixEnd_1081221 555186066735019451565061 := by
  unfold tailWord_1081221
  simp only [CollatzResearch.WordTrace]
  refine ⟨39435369615928449690547517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26290246410618966460365011 39435369615928449690547517)
  ·
    refine ⟨14788263605973168633955319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39435369615928449690547517 14788263605973168633955319)
    ·
      refine ⟨22182395408959752950932979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14788263605973168633955319 22182395408959752950932979)
      ·
        refine ⟨33273593113439629426399469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22182395408959752950932979 33273593113439629426399469)
        ·
          refine ⟨12477597417539861034899801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33273593113439629426399469 12477597417539861034899801)
          ·
            refine ⟨9358198063154895776174851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12477597417539861034899801 9358198063154895776174851)
            ·
              refine ⟨14037297094732343664262277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9358198063154895776174851 14037297094732343664262277)
              ·
                refine ⟨2631993205262314437049177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14037297094732343664262277 2631993205262314437049177)
                ·
                  refine ⟨1973994903946735827786883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2631993205262314437049177 1973994903946735827786883)
                  ·
                    refine ⟨2960992355920103741680325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1973994903946735827786883 2960992355920103741680325)
                    ·
                      refine ⟨555186066735019451565061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2960992355920103741680325 555186066735019451565061)
                      ·
                        rfl

theorem cell23_1081221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 4, 2, 1, 4].length) (baseStart_1081221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1081221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1081221 prefixEnd_1081221 := by exact prefixLift 1081221
  have htrace : WordTrace (prefixWord ++ tailWord_1081221) baseStart_1081221 baseEnd_1081221 := by
    simpa [prefixWord, tailWord_1081221, baseEnd_1081221] using wordTrace_append hprefix tailTrace_1081221
  have hstable : (prefixWord ++ tailWord_1081221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081221).length < 2 ^ (prefixWord ++ tailWord_1081221).sum := by decide
  have hdescent : baseEnd_1081221 < baseStart_1081221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081241 : List Nat := [1, 2, 1, 2, 1, 3, 2, 2, 4, 2, 3]
def baseStart_1081241 : Nat := 118140960795 + 1081241 * 2 ^ 59
def prefixEnd_1081241 : Nat := 4983230072969 + 3 ^ 40 * 1081241 * 2
def baseEnd_1081241 : Nat := 555196336348109373314969

theorem tailTrace_1081241 : CollatzResearch.WordTrace tailWord_1081241 prefixEnd_1081241 555196336348109373314969 := by
  unfold tailWord_1081241
  simp only [CollatzResearch.WordTrace]
  refine ⟨39436099075855993106275577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26290732717237328737517051 39436099075855993106275577)
  ·
    refine ⟨29577074306891994829706683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39436099075855993106275577 29577074306891994829706683)
    ·
      refine ⟨44365611460337992244560025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29577074306891994829706683 44365611460337992244560025)
      ·
        refine ⟨33274208595253494183420019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44365611460337992244560025 33274208595253494183420019)
        ·
          refine ⟨49911312892880241275130029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33274208595253494183420019 49911312892880241275130029)
          ·
            refine ⟨18716742334830090478173761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49911312892880241275130029 18716742334830090478173761)
            ·
              refine ⟨14037556751122567858630321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18716742334830090478173761 14037556751122567858630321)
              ·
                refine ⟨10528167563341925893972741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14037556751122567858630321 10528167563341925893972741)
                ·
                  refine ⟨1974031418126611105119889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10528167563341925893972741 1974031418126611105119889)
                  ·
                    refine ⟨1480523563594958328839917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1974031418126611105119889 1480523563594958328839917)
                    ·
                      refine ⟨555196336348109373314969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1480523563594958328839917 555196336348109373314969)
                      ·
                        rfl

theorem cell23_1081241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 4, 2, 3].length) (baseStart_1081241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1081241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1081241 prefixEnd_1081241 := by exact prefixLift 1081241
  have htrace : WordTrace (prefixWord ++ tailWord_1081241) baseStart_1081241 baseEnd_1081241 := by
    simpa [prefixWord, tailWord_1081241, baseEnd_1081241] using wordTrace_append hprefix tailTrace_1081241
  have hstable : (prefixWord ++ tailWord_1081241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081241).length < 2 ^ (prefixWord ++ tailWord_1081241).sum := by decide
  have hdescent : baseEnd_1081241 < baseStart_1081241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081255 : List Nat := [1, 1, 6, 1, 2, 3, 1, 1, 2, 1, 4]
def baseStart_1081255 : Nat := 118140960795 + 1081255 * 2 ^ 59
def prefixEnd_1081255 : Nat := 4983230072969 + 3 ^ 40 * 1081255 * 2
def baseEnd_1081255 : Nat := 555203525077272318539905

theorem tailTrace_1081255 : CollatzResearch.WordTrace tailWord_1081255 prefixEnd_1081255 555203525077272318539905 := by
  unfold tailWord_1081255
  simp only [CollatzResearch.WordTrace]
  refine ⟨39436609697805273497285219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26291073131870182331523479 39436609697805273497285219)
  ·
    refine ⟨59154914546707910245927829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39436609697805273497285219 59154914546707910245927829)
    ·
      refine ⟨2772886619376933292777867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 59154914546707910245927829 2772886619376933292777867)
      ·
        refine ⟨4159329929065399939166801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2772886619376933292777867 4159329929065399939166801)
        ·
          refine ⟨3119497446799049954375101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4159329929065399939166801 3119497446799049954375101)
          ·
            refine ⟨1169811542549643732890663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3119497446799049954375101 1169811542549643732890663)
            ·
              refine ⟨1754717313824465599335995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1169811542549643732890663 1754717313824465599335995)
              ·
                refine ⟨2632075970736698399003993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1754717313824465599335995 2632075970736698399003993)
                ·
                  refine ⟨1974056978052523799252995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2632075970736698399003993 1974056978052523799252995)
                  ·
                    refine ⟨2961085467078785698879493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1974056978052523799252995 2961085467078785698879493)
                    ·
                      refine ⟨555203525077272318539905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2961085467078785698879493 555203525077272318539905)
                      ·
                        rfl

theorem cell23_1081255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_1081255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1081255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1081255 prefixEnd_1081255 := by exact prefixLift 1081255
  have htrace : WordTrace (prefixWord ++ tailWord_1081255) baseStart_1081255 baseEnd_1081255 := by
    simpa [prefixWord, tailWord_1081255, baseEnd_1081255] using wordTrace_append hprefix tailTrace_1081255
  have hstable : (prefixWord ++ tailWord_1081255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081255).length < 2 ^ (prefixWord ++ tailWord_1081255).sum := by decide
  have hdescent : baseEnd_1081255 < baseStart_1081255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081264 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 6]
def baseStart_1081264 : Nat := 118140960795 + 1081264 * 2 ^ 59
def prefixEnd_1081264 : Nat := 4983230072969 + 3 ^ 40 * 1081264 * 2
def baseEnd_1081264 : Nat := 555208146403162783327363

theorem tailTrace_1081264 : CollatzResearch.WordTrace tailWord_1081264 prefixEnd_1081264 555208146403162783327363 := by
  unfold tailWord_1081264
  simp only [CollatzResearch.WordTrace]
  refine ⟨19718468977386334017181423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26291291969848445356241897 19718468977386334017181423)
  ·
    refine ⟨29577703466079501025772135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19718468977386334017181423 29577703466079501025772135)
    ·
      refine ⟨44366555199119251538658203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29577703466079501025772135 44366555199119251538658203)
      ·
        refine ⟨66549832798678877307987305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44366555199119251538658203 66549832798678877307987305)
        ·
          refine ⟨49912374599009157980990479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66549832798678877307987305 49912374599009157980990479)
          ·
            refine ⟨74868561898513736971485719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49912374599009157980990479 74868561898513736971485719)
            ·
              refine ⟨112302842847770605457228579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74868561898513736971485719 112302842847770605457228579)
              ·
                refine ⟨168454264271655908185842869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 112302842847770605457228579 168454264271655908185842869)
                ·
                  refine ⟨15792587275467741392422769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 168454264271655908185842869 15792587275467741392422769)
                  ·
                    refine ⟨11844440456600806044317077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15792587275467741392422769 11844440456600806044317077)
                    ·
                      refine ⟨555208146403162783327363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11844440456600806044317077 555208146403162783327363)
                      ·
                        rfl

theorem cell23_1081264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 6].length) (baseStart_1081264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1081264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1081264 prefixEnd_1081264 := by exact prefixLift 1081264
  have htrace : WordTrace (prefixWord ++ tailWord_1081264) baseStart_1081264 baseEnd_1081264 := by
    simpa [prefixWord, tailWord_1081264, baseEnd_1081264] using wordTrace_append hprefix tailTrace_1081264
  have hstable : (prefixWord ++ tailWord_1081264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081264).length < 2 ^ (prefixWord ++ tailWord_1081264).sum := by decide
  have hdescent : baseEnd_1081264 < baseStart_1081264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081265 : List Nat := [1, 2, 2, 4, 2, 1, 1, 5, 1, 4]
def baseStart_1081265 : Nat := 118140960795 + 1081265 * 2 ^ 59
def prefixEnd_1081265 : Nat := 4983230072969 + 3 ^ 40 * 1081265 * 2
def baseEnd_1081265 : Nat := 185069553294605759804953

theorem tailTrace_1081265 : CollatzResearch.WordTrace tailWord_1081265 prefixEnd_1081265 185069553294605759804953 := by
  unfold tailWord_1081265
  simp only [CollatzResearch.WordTrace]
  refine ⟨39436974427769045205149249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26291316285179363470099499 39436974427769045205149249)
  ·
    refine ⟨29577730820826783903861937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39436974427769045205149249 29577730820826783903861937)
    ·
      refine ⟨22183298115620087927896453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29577730820826783903861937 22183298115620087927896453)
      ·
        refine ⟨4159368396678766486480585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22183298115620087927896453 4159368396678766486480585)
        ·
          refine ⟨3119526297509074864860439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4159368396678766486480585 3119526297509074864860439)
          ·
            refine ⟨4679289446263612297290659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3119526297509074864860439 4679289446263612297290659)
            ·
              refine ⟨7018934169395418445935989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4679289446263612297290659 7018934169395418445935989)
              ·
                refine ⟨658025078380820479306499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7018934169395418445935989 658025078380820479306499)
                ·
                  refine ⟨987037617571230718959749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 658025078380820479306499 987037617571230718959749)
                  ·
                    refine ⟨185069553294605759804953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 987037617571230718959749 185069553294605759804953)
                    ·
                      rfl

theorem cell23_1081265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 5, 1, 4].length) (baseStart_1081265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1081265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1081265 prefixEnd_1081265 := by exact prefixLift 1081265
  have htrace : WordTrace (prefixWord ++ tailWord_1081265) baseStart_1081265 baseEnd_1081265 := by
    simpa [prefixWord, tailWord_1081265, baseEnd_1081265] using wordTrace_append hprefix tailTrace_1081265
  have hstable : (prefixWord ++ tailWord_1081265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081265).length < 2 ^ (prefixWord ++ tailWord_1081265).sum := by decide
  have hdescent : baseEnd_1081265 < baseStart_1081265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081278 : List Nat := [4, 2, 1, 1, 1, 3, 3, 2, 6]
def baseStart_1081278 : Nat := 118140960795 + 1081278 * 2 ^ 59
def prefixEnd_1081278 : Nat := 4983230072969 + 3 ^ 40 * 1081278 * 2
def baseEnd_1081278 : Nat := 61690592792480636505811

theorem tailTrace_1081278 : CollatzResearch.WordTrace tailWord_1081278 prefixEnd_1081278 61690592792480636505811 := by
  unfold tailWord_1081278
  simp only [CollatzResearch.WordTrace]
  refine ⟨4929681072090243553171561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26291632384481298950248325 4929681072090243553171561)
  ·
    refine ⟨3697260804067682664878671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4929681072090243553171561 3697260804067682664878671)
    ·
      refine ⟨5545891206101523997318007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3697260804067682664878671 5545891206101523997318007)
      ·
        refine ⟨8318836809152285995977011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5545891206101523997318007 8318836809152285995977011)
        ·
          refine ⟨12478255213728428993965517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8318836809152285995977011 12478255213728428993965517)
          ·
            refine ⟨4679345705148160872737069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12478255213728428993965517 4679345705148160872737069)
            ·
              refine ⟨1754754639430560327276401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4679345705148160872737069 1754754639430560327276401)
              ·
                refine ⟨1316065979572920245457301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1754754639430560327276401 1316065979572920245457301)
                ·
                  refine ⟨61690592792480636505811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1316065979572920245457301 61690592792480636505811)
                  ·
                    rfl

theorem cell23_1081278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 2, 6].length) (baseStart_1081278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1081278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1081278 prefixEnd_1081278 := by exact prefixLift 1081278
  have htrace : WordTrace (prefixWord ++ tailWord_1081278) baseStart_1081278 baseEnd_1081278 := by
    simpa [prefixWord, tailWord_1081278, baseEnd_1081278] using wordTrace_append hprefix tailTrace_1081278
  have hstable : (prefixWord ++ tailWord_1081278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081278).length < 2 ^ (prefixWord ++ tailWord_1081278).sum := by decide
  have hdescent : baseEnd_1081278 < baseStart_1081278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081328 : List Nat := [2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 4]
def baseStart_1081328 : Nat := 118140960795 + 1081328 * 2 ^ 59
def prefixEnd_1081328 : Nat := 4983230072969 + 3 ^ 40 * 1081328 * 2
def baseEnd_1081328 : Nat := 555241009165050532927069

theorem tailTrace_1081328 : CollatzResearch.WordTrace tailWord_1081328 prefixEnd_1081328 555241009165050532927069 := by
  unfold tailWord_1081328
  simp only [CollatzResearch.WordTrace]
  refine ⟨19719636113270403482346319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26292848151027204643128425 19719636113270403482346319)
  ·
    refine ⟨29579454169905605223519479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19719636113270403482346319 29579454169905605223519479)
    ·
      refine ⟨44369181254858407835279219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29579454169905605223519479 44369181254858407835279219)
      ·
        refine ⟨66553771882287611752918829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44369181254858407835279219 66553771882287611752918829)
        ·
          refine ⟨24957664455857854407344561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66553771882287611752918829 24957664455857854407344561)
          ·
            refine ⟨18718248341893390805508421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24957664455857854407344561 18718248341893390805508421)
            ·
              refine ⟨3509671564105010776032829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18718248341893390805508421 3509671564105010776032829)
              ·
                refine ⟨1316126836539379041012311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3509671564105010776032829 1316126836539379041012311)
                ·
                  refine ⟨1974190254809068561518467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1316126836539379041012311 1974190254809068561518467)
                  ·
                    refine ⟨2961285382213602842277701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1974190254809068561518467 2961285382213602842277701)
                    ·
                      refine ⟨555241009165050532927069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2961285382213602842277701 555241009165050532927069)
                      ·
                        rfl

theorem cell23_1081328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 4].length) (baseStart_1081328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1081328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1081328 prefixEnd_1081328 := by exact prefixLift 1081328
  have htrace : WordTrace (prefixWord ++ tailWord_1081328) baseStart_1081328 baseEnd_1081328 := by
    simpa [prefixWord, tailWord_1081328, baseEnd_1081328] using wordTrace_append hprefix tailTrace_1081328
  have hstable : (prefixWord ++ tailWord_1081328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081328).length < 2 ^ (prefixWord ++ tailWord_1081328).sum := by decide
  have hdescent : baseEnd_1081328 < baseStart_1081328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081341 : List Nat := [1, 4, 1, 1, 1, 2, 3, 2, 1, 1, 6]
def baseStart_1081341 : Nat := 118140960795 + 1081341 * 2 ^ 59
def prefixEnd_1081341 : Nat := 4983230072969 + 3 ^ 40 * 1081341 * 2
def baseEnd_1081341 : Nat := 555247684413558982064509

theorem tailTrace_1081341 : CollatzResearch.WordTrace tailWord_1081341 prefixEnd_1081341 555247684413558982064509 := by
  unfold tailWord_1081341
  simp only [CollatzResearch.WordTrace]
  refine ⟨39439746375493710184915877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26293164250329140123277251 39439746375493710184915877)
  ·
    refine ⟨7394952445405070659671727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39439746375493710184915877 7394952445405070659671727)
    ·
      refine ⟨11092428668107605989507591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7394952445405070659671727 11092428668107605989507591)
      ·
        refine ⟨16638643002161408984261387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11092428668107605989507591 16638643002161408984261387)
        ·
          refine ⟨24957964503242113476392081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16638643002161408984261387 24957964503242113476392081)
          ·
            refine ⟨18718473377431585107294061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24957964503242113476392081 18718473377431585107294061)
            ·
              refine ⟨7019427516536844415235273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18718473377431585107294061 7019427516536844415235273)
              ·
                refine ⟨5264570637402633311426455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7019427516536844415235273 5264570637402633311426455)
                ·
                  refine ⟨7896855956103949967139683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5264570637402633311426455 7896855956103949967139683)
                  ·
                    refine ⟨11845283934155924950709525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7896855956103949967139683 11845283934155924950709525)
                    ·
                      refine ⟨555247684413558982064509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11845283934155924950709525 555247684413558982064509)
                      ·
                        rfl

theorem cell23_1081341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 2, 1, 1, 6].length) (baseStart_1081341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1081341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1081341 prefixEnd_1081341 := by exact prefixLift 1081341
  have htrace : WordTrace (prefixWord ++ tailWord_1081341) baseStart_1081341 baseEnd_1081341 := by
    simpa [prefixWord, tailWord_1081341, baseEnd_1081341] using wordTrace_append hprefix tailTrace_1081341
  have hstable : (prefixWord ++ tailWord_1081341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081341).length < 2 ^ (prefixWord ++ tailWord_1081341).sum := by decide
  have hdescent : baseEnd_1081341 < baseStart_1081341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081351 : List Nat := [1, 1, 4, 3, 1, 2, 1, 10]
def baseStart_1081351 : Nat := 118140960795 + 1081351 * 2 ^ 59
def prefixEnd_1081351 : Nat := 4983230072969 + 3 ^ 40 * 1081351 * 2
def baseEnd_1081351 : Nat := 20564919230374220108869

theorem tailTrace_1081351 : CollatzResearch.WordTrace tailWord_1081351 prefixEnd_1081351 20564919230374220108869 := by
  unfold tailWord_1081351
  simp only [CollatzResearch.WordTrace]
  refine ⟨39440111105457481892779907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26293407403638321261853271 39440111105457481892779907)
  ·
    refine ⟨59160166658186222839169861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39440111105457481892779907 59160166658186222839169861)
    ·
      refine ⟨11092531248409916782344349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59160166658186222839169861 11092531248409916782344349)
      ·
        refine ⟨4159699218153718793379131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11092531248409916782344349 4159699218153718793379131)
        ·
          refine ⟨6239548827230578190068697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4159699218153718793379131 6239548827230578190068697)
          ·
            refine ⟨4679661620422933642551523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6239548827230578190068697 4679661620422933642551523)
            ·
              refine ⟨7019492430634400463827285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4679661620422933642551523 7019492430634400463827285)
              ·
                refine ⟨20564919230374220108869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 7019492430634400463827285 20564919230374220108869)
                ·
                  rfl

theorem cell23_1081351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 10].length) (baseStart_1081351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1081351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1081351 prefixEnd_1081351 := by exact prefixLift 1081351
  have htrace : WordTrace (prefixWord ++ tailWord_1081351) baseStart_1081351 baseEnd_1081351 := by
    simpa [prefixWord, tailWord_1081351, baseEnd_1081351] using wordTrace_append hprefix tailTrace_1081351
  have hstable : (prefixWord ++ tailWord_1081351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081351).length < 2 ^ (prefixWord ++ tailWord_1081351).sum := by decide
  have hdescent : baseEnd_1081351 < baseStart_1081351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081358 : List Nat := [4, 1, 1, 2, 2, 1, 2, 3, 1, 2, 4]
def baseStart_1081358 : Nat := 118140960795 + 1081358 * 2 ^ 59
def prefixEnd_1081358 : Nat := 4983230072969 + 3 ^ 40 * 1081358 * 2
def baseEnd_1081358 : Nat := 555256413584685415551931

theorem tailTrace_1081358 : CollatzResearch.WordTrace tailWord_1081358 prefixEnd_1081358 555256413584685415551931 := by
  unfold tailWord_1081358
  simp only [CollatzResearch.WordTrace]
  refine ⟨4930045802054015261035591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26293577610954748058856485 4930045802054015261035591)
  ·
    refine ⟨7395068703081022891553387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4930045802054015261035591 7395068703081022891553387)
    ·
      refine ⟨11092603054621534337330081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7395068703081022891553387 11092603054621534337330081)
      ·
        refine ⟨8319452290966150752997561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11092603054621534337330081 8319452290966150752997561)
        ·
          refine ⟨6239589218224613064748171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8319452290966150752997561 6239589218224613064748171)
          ·
            refine ⟨9359383827336919597122257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6239589218224613064748171 9359383827336919597122257)
            ·
              refine ⟨7019537870502689697841693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9359383827336919597122257 7019537870502689697841693)
              ·
                refine ⟨2632326701438508636690635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7019537870502689697841693 2632326701438508636690635)
                ·
                  refine ⟨3948490052157762955035953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2632326701438508636690635 3948490052157762955035953)
                  ·
                    refine ⟨2961367539118322216276965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3948490052157762955035953 2961367539118322216276965)
                    ·
                      refine ⟨555256413584685415551931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2961367539118322216276965 555256413584685415551931)
                      ·
                        rfl

theorem cell23_1081358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_1081358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1081358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1081358 prefixEnd_1081358 := by exact prefixLift 1081358
  have htrace : WordTrace (prefixWord ++ tailWord_1081358) baseStart_1081358 baseEnd_1081358 := by
    simpa [prefixWord, tailWord_1081358, baseEnd_1081358] using wordTrace_append hprefix tailTrace_1081358
  have hstable : (prefixWord ++ tailWord_1081358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081358).length < 2 ^ (prefixWord ++ tailWord_1081358).sum := by decide
  have hdescent : baseEnd_1081358 < baseStart_1081358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081365 : List Nat := [1, 3, 2, 1, 5, 1, 1, 1, 3, 2, 3]
def baseStart_1081365 : Nat := 118140960795 + 1081365 * 2 ^ 59
def prefixEnd_1081365 : Nat := 4983230072969 + 3 ^ 40 * 1081365 * 2
def baseEnd_1081365 : Nat := 555260007949266888164399

theorem tailTrace_1081365 : CollatzResearch.WordTrace tailWord_1081365 prefixEnd_1081365 555260007949266888164399 := by
  unfold tailWord_1081365
  simp only [CollatzResearch.WordTrace]
  refine ⟨39440621727406762283789549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26293747818271174855859699 39440621727406762283789549)
  ·
    refine ⟨14790233147777535856421081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39440621727406762283789549 14790233147777535856421081)
    ·
      refine ⟨11092674860833151892315811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14790233147777535856421081 11092674860833151892315811)
      ·
        refine ⟨16639012291249727838473717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11092674860833151892315811 16639012291249727838473717)
        ·
          refine ⟨1559907402304661984856911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16639012291249727838473717 1559907402304661984856911)
          ·
            refine ⟨2339861103456992977285367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1559907402304661984856911 2339861103456992977285367)
            ·
              refine ⟨3509791655185489465928051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2339861103456992977285367 3509791655185489465928051)
              ·
                refine ⟨5264687482778234198892077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3509791655185489465928051 5264687482778234198892077)
                ·
                  refine ⟨1974257806041837824584529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5264687482778234198892077 1974257806041837824584529)
                  ·
                    refine ⟨1480693354531378368438397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1974257806041837824584529 1480693354531378368438397)
                    ·
                      refine ⟨555260007949266888164399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1480693354531378368438397 555260007949266888164399)
                      ·
                        rfl

theorem cell23_1081365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 1, 3, 2, 3].length) (baseStart_1081365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1081365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1081365 prefixEnd_1081365 := by exact prefixLift 1081365
  have htrace : WordTrace (prefixWord ++ tailWord_1081365) baseStart_1081365 baseEnd_1081365 := by
    simpa [prefixWord, tailWord_1081365, baseEnd_1081365] using wordTrace_append hprefix tailTrace_1081365
  have hstable : (prefixWord ++ tailWord_1081365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081365).length < 2 ^ (prefixWord ++ tailWord_1081365).sum := by decide
  have hdescent : baseEnd_1081365 < baseStart_1081365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081395 : List Nat := [1, 1, 1, 2, 4, 1, 3, 4, 2, 1, 3]
def baseStart_1081395 : Nat := 118140960795 + 1081395 * 2 ^ 59
def prefixEnd_1081395 : Nat := 4983230072969 + 3 ^ 40 * 1081395 * 2
def baseEnd_1081395 : Nat := 555275412368901770789261

theorem tailTrace_1081395 : CollatzResearch.WordTrace tailWord_1081395 prefixEnd_1081395 555275412368901770789261 := by
  unfold tailWord_1081395
  simp only [CollatzResearch.WordTrace]
  refine ⟨39441715917298077407381639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26294477278198718271587759 39441715917298077407381639)
  ·
    refine ⟨59162573875947116111072459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39441715917298077407381639 59162573875947116111072459)
    ·
      refine ⟨88743860813920674166608689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59162573875947116111072459 88743860813920674166608689)
      ·
        refine ⟨66557895610440505624956517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88743860813920674166608689 66557895610440505624956517)
        ·
          refine ⟨12479605426957594804679347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66557895610440505624956517 12479605426957594804679347)
          ·
            refine ⟨18719408140436392207019021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12479605426957594804679347 18719408140436392207019021)
            ·
              refine ⟨7019778052663647077632133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18719408140436392207019021 7019778052663647077632133)
              ·
                refine ⟨1316208384874433827056025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7019778052663647077632133 1316208384874433827056025)
                ·
                  refine ⟨987156288655825370292019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1316208384874433827056025 987156288655825370292019)
                  ·
                    refine ⟨1480734432983738055438029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 987156288655825370292019 1480734432983738055438029)
                    ·
                      refine ⟨555275412368901770789261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1480734432983738055438029 555275412368901770789261)
                      ·
                        rfl

theorem cell23_1081395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 4, 2, 1, 3].length) (baseStart_1081395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1081395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1081395 prefixEnd_1081395 := by exact prefixLift 1081395
  have htrace : WordTrace (prefixWord ++ tailWord_1081395) baseStart_1081395 baseEnd_1081395 := by
    simpa [prefixWord, tailWord_1081395, baseEnd_1081395] using wordTrace_append hprefix tailTrace_1081395
  have hstable : (prefixWord ++ tailWord_1081395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081395).length < 2 ^ (prefixWord ++ tailWord_1081395).sum := by decide
  have hdescent : baseEnd_1081395 < baseStart_1081395 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081398 : List Nat := [5, 1, 2, 1, 1, 1, 1, 1, 1, 9]
def baseStart_1081398 : Nat := 118140960795 + 1081398 * 2 ^ 59
def prefixEnd_1081398 : Nat := 4983230072969 + 3 ^ 40 * 1081398 * 2
def baseEnd_1081398 : Nat := 185092317603621753017249

theorem tailTrace_1081398 : CollatzResearch.WordTrace tailWord_1081398 prefixEnd_1081398 185092317603621753017249 := by
  unfold tailWord_1081398
  simp only [CollatzResearch.WordTrace]
  refine ⟨2465114083517950557483803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26294550224191472613160565 2465114083517950557483803)
  ·
    refine ⟨3697671125276925836225705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2465114083517950557483803 3697671125276925836225705)
    ·
      refine ⟨2773253343957694377169279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3697671125276925836225705 2773253343957694377169279)
      ·
        refine ⟨4159880015936541565753919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2773253343957694377169279 4159880015936541565753919)
        ·
          refine ⟨6239820023904812348630879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4159880015936541565753919 6239820023904812348630879)
          ·
            refine ⟨9359730035857218522946319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6239820023904812348630879 9359730035857218522946319)
            ·
              refine ⟨14039595053785827784419479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9359730035857218522946319 14039595053785827784419479)
              ·
                refine ⟨21059392580678741676629219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14039595053785827784419479 21059392580678741676629219)
                ·
                  refine ⟨31589088871018112514943829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21059392580678741676629219 31589088871018112514943829)
                  ·
                    refine ⟨185092317603621753017249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 31589088871018112514943829 185092317603621753017249)
                    ·
                      rfl

theorem cell23_1081398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_1081398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1081398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1081398 prefixEnd_1081398 := by exact prefixLift 1081398
  have htrace : WordTrace (prefixWord ++ tailWord_1081398) baseStart_1081398 baseEnd_1081398 := by
    simpa [prefixWord, tailWord_1081398, baseEnd_1081398] using wordTrace_append hprefix tailTrace_1081398
  have hstable : (prefixWord ++ tailWord_1081398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081398).length < 2 ^ (prefixWord ++ tailWord_1081398).sum := by decide
  have hdescent : baseEnd_1081398 < baseStart_1081398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081405 : List Nat := [1, 4, 1, 3, 1, 1, 1, 1, 5, 3, 2]
def baseStart_1081405 : Nat := 118140960795 + 1081405 * 2 ^ 59
def prefixEnd_1081405 : Nat := 4983230072969 + 3 ^ 40 * 1081405 * 2
def baseEnd_1081405 : Nat := 555280547175446731664215

theorem tailTrace_1081405 : CollatzResearch.WordTrace tailWord_1081405 prefixEnd_1081405 555280547175446731664215 := by
  unfold tailWord_1081405
  simp only [CollatzResearch.WordTrace]
  refine ⟨39442080647261849115245669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26294720431507899410163779 39442080647261849115245669)
  ·
    refine ⟨7395390121361596709108563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39442080647261849115245669 7395390121361596709108563)
    ·
      refine ⟨11093085182042395063662845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7395390121361596709108563 11093085182042395063662845)
      ·
        refine ⟨4159906943265898148873567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11093085182042395063662845 4159906943265898148873567)
        ·
          refine ⟨6239860414898847223310351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4159906943265898148873567 6239860414898847223310351)
          ·
            refine ⟨9359790622348270834965527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6239860414898847223310351 9359790622348270834965527)
            ·
              refine ⟨14039685933522406252448291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9359790622348270834965527 14039685933522406252448291)
              ·
                refine ⟨21059528900283609378672437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14039685933522406252448291 21059528900283609378672437)
                ·
                  refine ⟨1974330834401588379250541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21059528900283609378672437 1974330834401588379250541)
                  ·
                    refine ⟨740374062900595642218953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1974330834401588379250541 740374062900595642218953)
                    ·
                      refine ⟨555280547175446731664215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 740374062900595642218953 555280547175446731664215)
                      ·
                        rfl

theorem cell23_1081405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 5, 3, 2].length) (baseStart_1081405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1081405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1081405 prefixEnd_1081405 := by exact prefixLift 1081405
  have htrace : WordTrace (prefixWord ++ tailWord_1081405) baseStart_1081405 baseEnd_1081405 := by
    simpa [prefixWord, tailWord_1081405, baseEnd_1081405] using wordTrace_append hprefix tailTrace_1081405
  have hstable : (prefixWord ++ tailWord_1081405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081405).length < 2 ^ (prefixWord ++ tailWord_1081405).sum := by decide
  have hdescent : baseEnd_1081405 < baseStart_1081405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081441 : List Nat := [1, 2, 3, 1, 1, 2, 1, 1, 11]
def baseStart_1081441 : Nat := 118140960795 + 1081441 * 2 ^ 59
def prefixEnd_1081441 : Nat := 4983230072969 + 3 ^ 40 * 1081441 * 2
def baseEnd_1081441 : Nat := 61699892497667621201561

theorem tailTrace_1081441 : CollatzResearch.WordTrace tailWord_1081441 prefixEnd_1081441 61699892497667621201561 := by
  unfold tailWord_1081441
  simp only [CollatzResearch.WordTrace]
  refine ⟨39443393675131427263556177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26295595783420951509037451 39443393675131427263556177)
  ·
    refine ⟨29582545256348570447667133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39443393675131427263556177 29582545256348570447667133)
    ·
      refine ⟨11093454471130713917875175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29582545256348570447667133 11093454471130713917875175)
      ·
        refine ⟨16640181706696070876812763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11093454471130713917875175 16640181706696070876812763)
        ·
          refine ⟨24960272560044106315219145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16640181706696070876812763 24960272560044106315219145)
          ·
            refine ⟨18720204420033079736414359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24960272560044106315219145 18720204420033079736414359)
            ·
              refine ⟨28080306630049619604621539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18720204420033079736414359 28080306630049619604621539)
              ·
                refine ⟨42120459945074429406932309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28080306630049619604621539 42120459945074429406932309)
                ·
                  refine ⟨61699892497667621201561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 42120459945074429406932309 61699892497667621201561)
                  ·
                    rfl

theorem cell23_1081441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 11].length) (baseStart_1081441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1081441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1081441 prefixEnd_1081441 := by exact prefixLift 1081441
  have htrace : WordTrace (prefixWord ++ tailWord_1081441) baseStart_1081441 baseEnd_1081441 := by
    simpa [prefixWord, tailWord_1081441, baseEnd_1081441] using wordTrace_append hprefix tailTrace_1081441
  have hstable : (prefixWord ++ tailWord_1081441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081441).length < 2 ^ (prefixWord ++ tailWord_1081441).sum := by decide
  have hdescent : baseEnd_1081441 < baseStart_1081441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081452 : List Nat := [2, 2, 1, 1, 3, 4, 1, 1, 4, 2, 2]
def baseStart_1081452 : Nat := 118140960795 + 1081452 * 2 ^ 59
def prefixEnd_1081452 : Nat := 4983230072969 + 3 ^ 40 * 1081452 * 2
def baseEnd_1081452 : Nat := 555304680766208047776499

theorem tailTrace_1081452 : CollatzResearch.WordTrace tailWord_1081452 prefixEnd_1081452 555304680766208047776499 := by
  unfold tailWord_1081452
  simp only [CollatzResearch.WordTrace]
  refine ⟨19721897439045788071103305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26295863252061050761471073 19721897439045788071103305)
  ·
    refine ⟨14791423079284341053327479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19721897439045788071103305 14791423079284341053327479)
    ·
      refine ⟨22187134618926511579991219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14791423079284341053327479 22187134618926511579991219)
      ·
        refine ⟨33280701928389767369986829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22187134618926511579991219 33280701928389767369986829)
        ·
          refine ⟨12480263223146162763745061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33280701928389767369986829 12480263223146162763745061)
          ·
            refine ⟨2340049354339905518202199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12480263223146162763745061 2340049354339905518202199)
            ·
              refine ⟨3510074031509858277303299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2340049354339905518202199 3510074031509858277303299)
              ·
                refine ⟨5265111047264787415954949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3510074031509858277303299 5265111047264787415954949)
                ·
                  refine ⟨987208321362147640491553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5265111047264787415954949 987208321362147640491553)
                  ·
                    refine ⟨740406241021610730368665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 987208321362147640491553 740406241021610730368665)
                    ·
                      refine ⟨555304680766208047776499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 740406241021610730368665 555304680766208047776499)
                      ·
                        rfl

theorem cell23_1081452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 2, 2].length) (baseStart_1081452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1081452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1081452 prefixEnd_1081452 := by exact prefixLift 1081452
  have htrace : WordTrace (prefixWord ++ tailWord_1081452) baseStart_1081452 baseEnd_1081452 := by
    simpa [prefixWord, tailWord_1081452, baseEnd_1081452] using wordTrace_append hprefix tailTrace_1081452
  have hstable : (prefixWord ++ tailWord_1081452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081452).length < 2 ^ (prefixWord ++ tailWord_1081452).sum := by decide
  have hdescent : baseEnd_1081452 < baseStart_1081452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081458 : List Nat := [3, 2, 1, 2, 2, 2, 1, 3, 7]
def baseStart_1081458 : Nat := 118140960795 + 1081458 * 2 ^ 59
def prefixEnd_1081458 : Nat := 4983230072969 + 3 ^ 40 * 1081458 * 2
def baseEnd_1081458 : Nat := 61700862405570558255719

theorem tailTrace_1081458 : CollatzResearch.WordTrace tailWord_1081458 prefixEnd_1081458 61700862405570558255719 := by
  unfold tailWord_1081458
  simp only [CollatzResearch.WordTrace]
  refine ⟨9861003429017459791731257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26296009144046559444616685 9861003429017459791731257)
  ·
    refine ⟨7395752571763094843798443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9861003429017459791731257 7395752571763094843798443)
    ·
      refine ⟨11093628857644642265697665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7395752571763094843798443 11093628857644642265697665)
      ·
        refine ⟨8320221643233481699273249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11093628857644642265697665 8320221643233481699273249)
        ·
          refine ⟨6240166232425111274454937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8320221643233481699273249 6240166232425111274454937)
          ·
            refine ⟨4680124674318833455841203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6240166232425111274454937 4680124674318833455841203)
            ·
              refine ⟨7020187011478250183761805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4680124674318833455841203 7020187011478250183761805)
              ·
                refine ⟨2632570129304343818910677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7020187011478250183761805 2632570129304343818910677)
                ·
                  refine ⟨61700862405570558255719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2632570129304343818910677 61700862405570558255719)
                  ·
                    rfl

theorem cell23_1081458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 3, 7].length) (baseStart_1081458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1081458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1081458 prefixEnd_1081458 := by exact prefixLift 1081458
  have htrace : WordTrace (prefixWord ++ tailWord_1081458) baseStart_1081458 baseEnd_1081458 := by
    simpa [prefixWord, tailWord_1081458, baseEnd_1081458] using wordTrace_append hprefix tailTrace_1081458
  have hstable : (prefixWord ++ tailWord_1081458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081458).length < 2 ^ (prefixWord ++ tailWord_1081458).sum := by decide
  have hdescent : baseEnd_1081458 < baseStart_1081458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081488 : List Nat := [2, 1, 1, 1, 1, 1, 6, 3, 2, 5]
def baseStart_1081488 : Nat := 118140960795 + 1081488 * 2 ^ 59
def prefixEnd_1081488 : Nat := 4983230072969 + 3 ^ 40 * 1081488 * 2
def baseEnd_1081488 : Nat := 185107722023256635642111

theorem tailTrace_1081488 : CollatzResearch.WordTrace tailWord_1081488 prefixEnd_1081488 185107722023256635642111 := by
  unfold tailWord_1081488
  simp only [CollatzResearch.WordTrace]
  refine ⟨19722553952980577145258559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26296738603974102860344745 19722553952980577145258559)
  ·
    refine ⟨29583830929470865717887839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19722553952980577145258559 29583830929470865717887839)
    ·
      refine ⟨44375746394206298576831759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29583830929470865717887839 44375746394206298576831759)
      ·
        refine ⟨66563619591309447865247639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44375746394206298576831759 66563619591309447865247639)
        ·
          refine ⟨99845429386964171797871459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66563619591309447865247639 99845429386964171797871459)
          ·
            refine ⟨149768144080446257696807189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99845429386964171797871459 149768144080446257696807189)
            ·
              refine ⟨7020381753770918329537837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 149768144080446257696807189 7020381753770918329537837)
              ·
                refine ⟨2632643157664094373576689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7020381753770918329537837 2632643157664094373576689)
                ·
                  refine ⟨1974482368248070780182517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2632643157664094373576689 1974482368248070780182517)
                  ·
                    refine ⟨185107722023256635642111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1974482368248070780182517 185107722023256635642111)
                    ·
                      rfl

theorem cell23_1081488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 3, 2, 5].length) (baseStart_1081488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1081488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1081488 prefixEnd_1081488 := by exact prefixLift 1081488
  have htrace : WordTrace (prefixWord ++ tailWord_1081488) baseStart_1081488 baseEnd_1081488 := by
    simpa [prefixWord, tailWord_1081488, baseEnd_1081488] using wordTrace_append hprefix tailTrace_1081488
  have hstable : (prefixWord ++ tailWord_1081488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081488).length < 2 ^ (prefixWord ++ tailWord_1081488).sum := by decide
  have hdescent : baseEnd_1081488 < baseStart_1081488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081505 : List Nat := [1, 2, 3, 3, 1, 3, 1, 2, 2, 5]
def baseStart_1081505 : Nat := 118140960795 + 1081505 * 2 ^ 59
def prefixEnd_1081505 : Nat := 4983230072969 + 3 ^ 40 * 1081505 * 2
def baseEnd_1081505 : Nat := 185110631746965446804585

theorem tailTrace_1081505 : CollatzResearch.WordTrace tailWord_1081505 prefixEnd_1081505 185110631746965446804585 := by
  unfold tailWord_1081505
  simp only [CollatzResearch.WordTrace]
  refine ⟨39445727946899566193885969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26297151964599710795923979 39445727946899566193885969)
  ·
    refine ⟨29584295960174674645414477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39445727946899566193885969 29584295960174674645414477)
    ·
      refine ⟨11094110985065502992030429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29584295960174674645414477 11094110985065502992030429)
      ·
        refine ⟨4160291619399563622011411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11094110985065502992030429 4160291619399563622011411)
        ·
          refine ⟨6240437429099345433017117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4160291619399563622011411 6240437429099345433017117)
          ·
            refine ⟨2340164035912254537381419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6240437429099345433017117 2340164035912254537381419)
            ·
              refine ⟨3510246053868381806072129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2340164035912254537381419 3510246053868381806072129)
              ·
                refine ⟨2632684540401286354554097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3510246053868381806072129 2632684540401286354554097)
                ·
                  refine ⟨1974513405300964765915573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2632684540401286354554097 1974513405300964765915573)
                  ·
                    refine ⟨185110631746965446804585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1974513405300964765915573 185110631746965446804585)
                    ·
                      rfl

theorem cell23_1081505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 2, 2, 5].length) (baseStart_1081505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1081505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1081505 prefixEnd_1081505 := by exact prefixLift 1081505
  have htrace : WordTrace (prefixWord ++ tailWord_1081505) baseStart_1081505 baseEnd_1081505 := by
    simpa [prefixWord, tailWord_1081505, baseEnd_1081505] using wordTrace_append hprefix tailTrace_1081505
  have hstable : (prefixWord ++ tailWord_1081505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081505).length < 2 ^ (prefixWord ++ tailWord_1081505).sum := by decide
  have hdescent : baseEnd_1081505 < baseStart_1081505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081568 : List Nat := [2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 6]
def baseStart_1081568 : Nat := 118140960795 + 1081568 * 2 ^ 59
def prefixEnd_1081568 : Nat := 4983230072969 + 3 ^ 40 * 1081568 * 2
def baseEnd_1081568 : Nat := 555364244522129593925965

theorem tailTrace_1081568 : CollatzResearch.WordTrace tailWord_1081568 prefixEnd_1081568 555364244522129593925965 := by
  unfold tailWord_1081568
  simp only [CollatzResearch.WordTrace]
  refine ⟨19724012872835663976714679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26298683830447551968952905 19724012872835663976714679)
  ·
    refine ⟨29586019309253495965072019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19724012872835663976714679 29586019309253495965072019)
    ·
      refine ⟨44379028963880243947608029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29586019309253495965072019 44379028963880243947608029)
      ·
        refine ⟨16642135861455091480353011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44379028963880243947608029 16642135861455091480353011)
        ·
          refine ⟨24963203792182637220529517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16642135861455091480353011 24963203792182637220529517)
          ·
            refine ⟨9361201422068488957698569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24963203792182637220529517 9361201422068488957698569)
            ·
              refine ⟨7020901066551366718273927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9361201422068488957698569 7020901066551366718273927)
              ·
                refine ⟨10531351599827050077410891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7020901066551366718273927 10531351599827050077410891)
                ·
                  refine ⟨15797027399740575116116337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10531351599827050077410891 15797027399740575116116337)
                  ·
                    refine ⟨11847770549805431337087253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15797027399740575116116337 11847770549805431337087253)
                    ·
                      refine ⟨555364244522129593925965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11847770549805431337087253 555364244522129593925965)
                      ·
                        rfl

theorem cell23_1081568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 6].length) (baseStart_1081568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1081568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1081568 prefixEnd_1081568 := by exact prefixLift 1081568
  have htrace : WordTrace (prefixWord ++ tailWord_1081568) baseStart_1081568 baseEnd_1081568 := by
    simpa [prefixWord, tailWord_1081568, baseEnd_1081568] using wordTrace_append hprefix tailTrace_1081568
  have hstable : (prefixWord ++ tailWord_1081568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081568).length < 2 ^ (prefixWord ++ tailWord_1081568).sum := by decide
  have hdescent : baseEnd_1081568 < baseStart_1081568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081609 : List Nat := [1, 2, 1, 1, 3, 4, 1, 5, 1, 1, 3]
def baseStart_1081609 : Nat := 118140960795 + 1081609 * 2 ^ 59
def prefixEnd_1081609 : Nat := 4983230072969 + 3 ^ 40 * 1081609 * 2
def baseEnd_1081609 : Nat := 555385297228963933513277

theorem tailTrace_1081609 : CollatzResearch.WordTrace tailWord_1081609 prefixEnd_1081609 555385297228963933513277 := by
  unfold tailWord_1081609
  simp only [CollatzResearch.WordTrace]
  refine ⟨39449521138522791955671881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26299680759015194637114587 39449521138522791955671881)
  ·
    refine ⟨29587140853892093966753911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39449521138522791955671881 29587140853892093966753911)
    ·
      refine ⟨44380711280838140950130867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29587140853892093966753911 44380711280838140950130867)
      ·
        refine ⟨66571066921257211425196301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44380711280838140950130867 66571066921257211425196301)
        ·
          refine ⟨24964150095471454284448613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66571066921257211425196301 24964150095471454284448613)
          ·
            refine ⟨4680778142900897678334115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24964150095471454284448613 4680778142900897678334115)
            ·
              refine ⟨7021167214351346517501173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4680778142900897678334115 7021167214351346517501173)
              ·
                refine ⟨658234426345438736015735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7021167214351346517501173 658234426345438736015735)
                ·
                  refine ⟨987351639518158104023603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 658234426345438736015735 987351639518158104023603)
                  ·
                    refine ⟨1481027459277237156035405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 987351639518158104023603 1481027459277237156035405)
                    ·
                      refine ⟨555385297228963933513277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1481027459277237156035405 555385297228963933513277)
                      ·
                        rfl

theorem cell23_1081609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 5, 1, 1, 3].length) (baseStart_1081609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1081609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1081609 prefixEnd_1081609 := by exact prefixLift 1081609
  have htrace : WordTrace (prefixWord ++ tailWord_1081609) baseStart_1081609 baseEnd_1081609 := by
    simpa [prefixWord, tailWord_1081609, baseEnd_1081609] using wordTrace_append hprefix tailTrace_1081609
  have hstable : (prefixWord ++ tailWord_1081609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081609).length < 2 ^ (prefixWord ++ tailWord_1081609).sum := by decide
  have hdescent : baseEnd_1081609 < baseStart_1081609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081615 : List Nat := [1, 1, 2, 1, 1, 1, 3, 2, 1, 8, 2]
def baseStart_1081615 : Nat := 118140960795 + 1081615 * 2 ^ 59
def prefixEnd_1081615 : Nat := 4983230072969 + 3 ^ 40 * 1081615 * 2
def baseEnd_1081615 : Nat := 555388378112890910038249

theorem tailTrace_1081615 : CollatzResearch.WordTrace tailWord_1081615 prefixEnd_1081615 555388378112890910038249 := by
  unfold tailWord_1081615
  simp only [CollatzResearch.WordTrace]
  refine ⟨39449739976501054980390299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26299826651000703320260199 39449739976501054980390299)
  ·
    refine ⟨59174609964751582470585449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39449739976501054980390299 59174609964751582470585449)
    ·
      refine ⟨44380957473563686852939087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59174609964751582470585449 44380957473563686852939087)
      ·
        refine ⟨66571436210345530279408631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44380957473563686852939087 66571436210345530279408631)
        ·
          refine ⟨99857154315518295419112947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66571436210345530279408631 99857154315518295419112947)
          ·
            refine ⟨149785731473277443128669421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99857154315518295419112947 149785731473277443128669421)
            ·
              refine ⟨56169649302479041173251033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 149785731473277443128669421 56169649302479041173251033)
              ·
                refine ⟨42127236976859280879938275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56169649302479041173251033 42127236976859280879938275)
                ·
                  refine ⟨63190855465288921319907413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42127236976859280879938275 63190855465288921319907413)
                  ·
                    refine ⟨740517837483854546717665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 63190855465288921319907413 740517837483854546717665)
                    ·
                      refine ⟨555388378112890910038249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 740517837483854546717665 555388378112890910038249)
                      ·
                        rfl

theorem cell23_1081615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 8, 2].length) (baseStart_1081615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1081615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1081615 prefixEnd_1081615 := by exact prefixLift 1081615
  have htrace : WordTrace (prefixWord ++ tailWord_1081615) baseStart_1081615 baseEnd_1081615 := by
    simpa [prefixWord, tailWord_1081615, baseEnd_1081615] using wordTrace_append hprefix tailTrace_1081615
  have hstable : (prefixWord ++ tailWord_1081615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081615).length < 2 ^ (prefixWord ++ tailWord_1081615).sum := by decide
  have hdescent : baseEnd_1081615 < baseStart_1081615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081635 : List Nat := [1, 1, 1, 4, 2, 2, 3, 2, 1, 1, 5]
def baseStart_1081635 : Nat := 118140960795 + 1081635 * 2 ^ 59
def prefixEnd_1081635 : Nat := 4983230072969 + 3 ^ 40 * 1081635 * 2
def baseEnd_1081635 : Nat := 555398647725980831788157

theorem tailTrace_1081635 : CollatzResearch.WordTrace tailWord_1081635 prefixEnd_1081635 555398647725980831788157 := by
  unfold tailWord_1081635
  simp only [CollatzResearch.WordTrace]
  refine ⟨39450469436428598396118359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26300312957619065597412239 39450469436428598396118359)
  ·
    refine ⟨59175704154642897594177539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39450469436428598396118359 59175704154642897594177539)
    ·
      refine ⟨88763556231964346391266309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59175704154642897594177539 88763556231964346391266309)
      ·
        refine ⟨16643166793493314948362433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 88763556231964346391266309 16643166793493314948362433)
        ·
          refine ⟨12482375095119986211271825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16643166793493314948362433 12482375095119986211271825)
          ·
            refine ⟨9361781321339989658453869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12482375095119986211271825 9361781321339989658453869)
            ·
              refine ⟨3510667995502496121920201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9361781321339989658453869 3510667995502496121920201)
              ·
                refine ⟨2633000996626872091440151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3510667995502496121920201 2633000996626872091440151)
                ·
                  refine ⟨3949501494940308137160227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2633000996626872091440151 3949501494940308137160227)
                  ·
                    refine ⟨5924252242410462205740341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3949501494940308137160227 5924252242410462205740341)
                    ·
                      refine ⟨555398647725980831788157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5924252242410462205740341 555398647725980831788157)
                      ·
                        rfl

theorem cell23_1081635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 2, 1, 1, 5].length) (baseStart_1081635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1081635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1081635 prefixEnd_1081635 := by exact prefixLift 1081635
  have htrace : WordTrace (prefixWord ++ tailWord_1081635) baseStart_1081635 baseEnd_1081635 := by
    simpa [prefixWord, tailWord_1081635, baseEnd_1081635] using wordTrace_append hprefix tailTrace_1081635
  have hstable : (prefixWord ++ tailWord_1081635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081635).length < 2 ^ (prefixWord ++ tailWord_1081635).sum := by decide
  have hdescent : baseEnd_1081635 < baseStart_1081635 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081646 : List Nat := [4, 1, 3, 3, 1, 1, 2, 2, 1, 5]
def baseStart_1081646 : Nat := 118140960795 + 1081646 * 2 ^ 59
def prefixEnd_1081646 : Nat := 4983230072969 + 3 ^ 40 * 1081646 * 2
def baseEnd_1081646 : Nat := 185134765337726762916869

theorem tailTrace_1081646 : CollatzResearch.WordTrace tailWord_1081646 prefixEnd_1081646 185134765337726762916869 := by
  unfold tailWord_1081646
  simp only [CollatzResearch.WordTrace]
  refine ⟨4931358829923593409346099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26300580426259164849845861 4931358829923593409346099)
  ·
    refine ⟨7397038244885390114019149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4931358829923593409346099 7397038244885390114019149)
    ·
      refine ⟨2773889341832021292757181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7397038244885390114019149 2773889341832021292757181)
      ·
        refine ⟨1040208503187007984783943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2773889341832021292757181 1040208503187007984783943)
        ·
          refine ⟨1560312754780511977175915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1040208503187007984783943 1560312754780511977175915)
          ·
            refine ⟨2340469132170767965763873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1560312754780511977175915 2340469132170767965763873)
            ·
              refine ⟨1755351849128075974322905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2340469132170767965763873 1755351849128075974322905)
              ·
                refine ⟨1316513886846056980742179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1755351849128075974322905 1316513886846056980742179)
                ·
                  refine ⟨1974770830269085471113269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1316513886846056980742179 1974770830269085471113269)
                  ·
                    refine ⟨185134765337726762916869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1974770830269085471113269 185134765337726762916869)
                    ·
                      rfl

theorem cell23_1081646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_1081646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1081646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1081646 prefixEnd_1081646 := by exact prefixLift 1081646
  have htrace : WordTrace (prefixWord ++ tailWord_1081646) baseStart_1081646 baseEnd_1081646 := by
    simpa [prefixWord, tailWord_1081646, baseEnd_1081646] using wordTrace_append hprefix tailTrace_1081646
  have hstable : (prefixWord ++ tailWord_1081646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081646).length < 2 ^ (prefixWord ++ tailWord_1081646).sum := by decide
  have hdescent : baseEnd_1081646 < baseStart_1081646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081649 : List Nat := [1, 2, 2, 3, 4, 1, 2, 2, 1, 1, 4]
def baseStart_1081649 : Nat := 118140960795 + 1081649 * 2 ^ 59
def prefixEnd_1081649 : Nat := 4983230072969 + 3 ^ 40 * 1081649 * 2
def baseEnd_1081649 : Nat := 555405836455143777013093

theorem tailTrace_1081649 : CollatzResearch.WordTrace tailWord_1081649 prefixEnd_1081649 555405836455143777013093 := by
  unfold tailWord_1081649
  simp only [CollatzResearch.WordTrace]
  refine ⟨39450980058377878787128001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26300653372251919191418667 39450980058377878787128001)
  ·
    refine ⟨29588235043783409090346001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39450980058377878787128001 29588235043783409090346001)
    ·
      refine ⟨22191176282837556817759501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29588235043783409090346001 22191176282837556817759501)
      ·
        refine ⟨8321691106064083806659813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22191176282837556817759501 8321691106064083806659813)
        ·
          refine ⟨1560317082387015713748715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8321691106064083806659813 1560317082387015713748715)
          ·
            refine ⟨2340475623580523570623073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1560317082387015713748715 2340475623580523570623073)
            ·
              refine ⟨1755356717685392677967305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2340475623580523570623073 1755356717685392677967305)
              ·
                refine ⟨1316517538264044508475479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1755356717685392677967305 1316517538264044508475479)
                ·
                  refine ⟨1974776307396066762713219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1316517538264044508475479 1974776307396066762713219)
                  ·
                    refine ⟨2962164461094100144069829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1974776307396066762713219 2962164461094100144069829)
                    ·
                      refine ⟨555405836455143777013093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2962164461094100144069829 555405836455143777013093)
                      ·
                        rfl

theorem cell23_1081649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 2, 1, 1, 4].length) (baseStart_1081649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1081649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1081649 prefixEnd_1081649 := by exact prefixLift 1081649
  have htrace : WordTrace (prefixWord ++ tailWord_1081649) baseStart_1081649 baseEnd_1081649 := by
    simpa [prefixWord, tailWord_1081649, baseEnd_1081649] using wordTrace_append hprefix tailTrace_1081649
  have hstable : (prefixWord ++ tailWord_1081649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081649).length < 2 ^ (prefixWord ++ tailWord_1081649).sum := by decide
  have hdescent : baseEnd_1081649 < baseStart_1081649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081699 : List Nat := [1, 1, 1, 5, 2, 1, 3, 3, 2, 1, 3]
def baseStart_1081699 : Nat := 118140960795 + 1081699 * 2 ^ 59
def prefixEnd_1081699 : Nat := 4983230072969 + 3 ^ 40 * 1081699 * 2
def baseEnd_1081699 : Nat := 555431510487868581387863

theorem tailTrace_1081699 : CollatzResearch.WordTrace tailWord_1081699 prefixEnd_1081699 555431510487868581387863 := by
  unfold tailWord_1081699
  simp only [CollatzResearch.WordTrace]
  refine ⟨39452803708196737326448151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26301869138797824884298767 39452803708196737326448151)
  ·
    refine ⟨59179205562295105989672227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39452803708196737326448151 59179205562295105989672227)
    ·
      refine ⟨88768808343442658984508341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59179205562295105989672227 88768808343442658984508341)
      ·
        refine ⟨8322075782197749279797657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 88768808343442658984508341 8322075782197749279797657)
        ·
          refine ⟨6241556836648311959848243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8322075782197749279797657 6241556836648311959848243)
          ·
            refine ⟨9362335254972467939772365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6241556836648311959848243 9362335254972467939772365)
            ·
              refine ⟨3510875720614675477414637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9362335254972467939772365 3510875720614675477414637)
              ·
                refine ⟨1316578395230503304030489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3510875720614675477414637 1316578395230503304030489)
                ·
                  refine ⟨987433796422877478022867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1316578395230503304030489 987433796422877478022867)
                  ·
                    refine ⟨1481150694634316217034301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 987433796422877478022867 1481150694634316217034301)
                    ·
                      refine ⟨555431510487868581387863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1481150694634316217034301 555431510487868581387863)
                      ·
                        rfl

theorem cell23_1081699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 3, 2, 1, 3].length) (baseStart_1081699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1081699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1081699 prefixEnd_1081699 := by exact prefixLift 1081699
  have htrace : WordTrace (prefixWord ++ tailWord_1081699) baseStart_1081699 baseEnd_1081699 := by
    simpa [prefixWord, tailWord_1081699, baseEnd_1081699] using wordTrace_append hprefix tailTrace_1081699
  have hstable : (prefixWord ++ tailWord_1081699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081699).length < 2 ^ (prefixWord ++ tailWord_1081699).sum := by decide
  have hdescent : baseEnd_1081699 < baseStart_1081699 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081709 : List Nat := [1, 5, 1, 1, 1, 2, 3, 1, 3, 3, 2]
def baseStart_1081709 : Nat := 118140960795 + 1081709 * 2 ^ 59
def prefixEnd_1081709 : Nat := 4983230072969 + 3 ^ 40 * 1081709 * 2
def baseEnd_1081709 : Nat := 555436645294413542262817

theorem tailTrace_1081709 : CollatzResearch.WordTrace tailWord_1081709 prefixEnd_1081709 555436645294413542262817 := by
  unfold tailWord_1081709
  simp only [CollatzResearch.WordTrace]
  refine ⟨39453168438160509034312181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26302112292107006022874787 39453168438160509034312181)
  ·
    refine ⟨3698734541077547721966767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39453168438160509034312181 3698734541077547721966767)
    ·
      refine ⟨5548101811616321582950151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3698734541077547721966767 5548101811616321582950151)
      ·
        refine ⟨8322152717424482374425227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5548101811616321582950151 8322152717424482374425227)
        ·
          refine ⟨12483229076136723561637841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8322152717424482374425227 12483229076136723561637841)
          ·
            refine ⟨9362421807102542671228381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12483229076136723561637841 9362421807102542671228381)
            ·
              refine ⟨3510908177663453501710643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9362421807102542671228381 3510908177663453501710643)
              ·
                refine ⟨5266362266495180252565965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3510908177663453501710643 5266362266495180252565965)
                ·
                  refine ⟨1974885849935692594712237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5266362266495180252565965 1974885849935692594712237)
                  ·
                    refine ⟨740582193725884723017089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1974885849935692594712237 740582193725884723017089)
                    ·
                      refine ⟨555436645294413542262817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 740582193725884723017089 555436645294413542262817)
                      ·
                        rfl

theorem cell23_1081709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 1, 3, 3, 2].length) (baseStart_1081709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1081709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1081709 prefixEnd_1081709 := by exact prefixLift 1081709
  have htrace : WordTrace (prefixWord ++ tailWord_1081709) baseStart_1081709 baseEnd_1081709 := by
    simpa [prefixWord, tailWord_1081709, baseEnd_1081709] using wordTrace_append hprefix tailTrace_1081709
  have hstable : (prefixWord ++ tailWord_1081709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081709).length < 2 ^ (prefixWord ++ tailWord_1081709).sum := by decide
  have hdescent : baseEnd_1081709 < baseStart_1081709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081750 : List Nat := [5, 3, 1, 2, 1, 1, 2, 1, 1, 3, 3]
def baseStart_1081750 : Nat := 118140960795 + 1081750 * 2 ^ 59
def prefixEnd_1081750 : Nat := 4983230072969 + 3 ^ 40 * 1081750 * 2
def baseEnd_1081750 : Nat := 555457698001247881850129

theorem tailTrace_1081750 : CollatzResearch.WordTrace tailWord_1081750 prefixEnd_1081750 555457698001247881850129 := by
  unfold tailWord_1081750
  simp only [CollatzResearch.WordTrace]
  refine ⟨2465916489438248314784669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26303109220674648691036469 2465916489438248314784669)
  ·
    refine ⟨924718683539343118044251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2465916489438248314784669 924718683539343118044251)
    ·
      refine ⟨1387078025309014677066377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 924718683539343118044251 1387078025309014677066377)
      ·
        refine ⟨1040308518981761007799783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1387078025309014677066377 1040308518981761007799783)
        ·
          refine ⟨1560462778472641511699675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1040308518981761007799783 1560462778472641511699675)
          ·
            refine ⟨2340694167708962267549513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1560462778472641511699675 2340694167708962267549513)
            ·
              refine ⟨1755520625781721700662135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2340694167708962267549513 1755520625781721700662135)
              ·
                refine ⟨2633280938672582550993203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1755520625781721700662135 2633280938672582550993203)
                ·
                  refine ⟨3949921408008873826489805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2633280938672582550993203 3949921408008873826489805)
                  ·
                    refine ⟨1481220528003327684933677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3949921408008873826489805 1481220528003327684933677)
                    ·
                      refine ⟨555457698001247881850129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1481220528003327684933677 555457698001247881850129)
                      ·
                        rfl

theorem cell23_1081750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_1081750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1081750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1081750 prefixEnd_1081750 := by exact prefixLift 1081750
  have htrace : WordTrace (prefixWord ++ tailWord_1081750) baseStart_1081750 baseEnd_1081750 := by
    simpa [prefixWord, tailWord_1081750, baseEnd_1081750] using wordTrace_append hprefix tailTrace_1081750
  have hstable : (prefixWord ++ tailWord_1081750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081750).length < 2 ^ (prefixWord ++ tailWord_1081750).sum := by decide
  have hdescent : baseEnd_1081750 < baseStart_1081750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081752 : List Nat := [2, 1, 2, 5, 1, 1, 1, 1, 1, 4, 4]
def baseStart_1081752 : Nat := 118140960795 + 1081752 * 2 ^ 59
def prefixEnd_1081752 : Nat := 4983230072969 + 3 ^ 40 * 1081752 * 2
def baseEnd_1081752 : Nat := 555458724962556874025119

theorem tailTrace_1081752 : CollatzResearch.WordTrace tailWord_1081752 prefixEnd_1081752 555458724962556874025119 := by
  unfold tailWord_1081752
  simp only [CollatzResearch.WordTrace]
  refine ⟨19727368388502363689063755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26303157851336484918751673 19727368388502363689063755)
  ·
    refine ⟨29591052582753545533595633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19727368388502363689063755 29591052582753545533595633)
    ·
      refine ⟨22193289437065159150196725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29591052582753545533595633 22193289437065159150196725)
      ·
        refine ⟨2080620884724858670330943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22193289437065159150196725 2080620884724858670330943)
        ·
          refine ⟨3120931327087288005496415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2080620884724858670330943 3120931327087288005496415)
          ·
            refine ⟨4681396990630932008244623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3120931327087288005496415 4681396990630932008244623)
            ·
              refine ⟨7022095485946398012366935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4681396990630932008244623 7022095485946398012366935)
              ·
                refine ⟨10533143228919597018550403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7022095485946398012366935 10533143228919597018550403)
                ·
                  refine ⟨15799714843379395527825605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10533143228919597018550403 15799714843379395527825605)
                  ·
                    refine ⟨2962446533133636661467301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15799714843379395527825605 2962446533133636661467301)
                    ·
                      refine ⟨555458724962556874025119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2962446533133636661467301 555458724962556874025119)
                      ·
                        rfl

theorem cell23_1081752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_1081752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1081752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1081752 prefixEnd_1081752 := by exact prefixLift 1081752
  have htrace : WordTrace (prefixWord ++ tailWord_1081752) baseStart_1081752 baseEnd_1081752 := by
    simpa [prefixWord, tailWord_1081752, baseEnd_1081752] using wordTrace_append hprefix tailTrace_1081752
  have hstable : (prefixWord ++ tailWord_1081752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081752).length < 2 ^ (prefixWord ++ tailWord_1081752).sum := by decide
  have hdescent : baseEnd_1081752 < baseStart_1081752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081762 : List Nat := [3, 3, 1, 2, 1, 1, 3, 2, 7]
def baseStart_1081762 : Nat := 118140960795 + 1081762 * 2 ^ 59
def prefixEnd_1081762 : Nat := 4983230072969 + 3 ^ 40 * 1081762 * 2
def baseEnd_1081762 : Nat := 61718206641011314988897

theorem tailTrace_1081762 : CollatzResearch.WordTrace tailWord_1081762 prefixEnd_1081762 61718206641011314988897 := by
  unfold tailWord_1081762
  simp only [CollatzResearch.WordTrace]
  refine ⟨9863775376742124771497885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26303401004645666057327693 9863775376742124771497885)
  ·
    refine ⟨3698915766278296789311707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9863775376742124771497885 3698915766278296789311707)
    ·
      refine ⟨5548373649417445183967561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3698915766278296789311707 5548373649417445183967561)
      ·
        refine ⟨4161280237063083887975671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5548373649417445183967561 4161280237063083887975671)
        ·
          refine ⟨6241920355594625831963507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4161280237063083887975671 6241920355594625831963507)
          ·
            refine ⟨9362880533391938747945261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6241920355594625831963507 9362880533391938747945261)
            ·
              refine ⟨3511080200021977030479473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9362880533391938747945261 3511080200021977030479473)
              ·
                refine ⟨2633310150016482772859605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3511080200021977030479473 2633310150016482772859605)
                ·
                  refine ⟨61718206641011314988897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2633310150016482772859605 61718206641011314988897)
                  ·
                    rfl

theorem cell23_1081762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 2, 7].length) (baseStart_1081762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1081762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1081762 prefixEnd_1081762 := by exact prefixLift 1081762
  have htrace : WordTrace (prefixWord ++ tailWord_1081762) baseStart_1081762 baseEnd_1081762 := by
    simpa [prefixWord, tailWord_1081762, baseEnd_1081762] using wordTrace_append hprefix tailTrace_1081762
  have hstable : (prefixWord ++ tailWord_1081762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081762).length < 2 ^ (prefixWord ++ tailWord_1081762).sum := by decide
  have hdescent : baseEnd_1081762 < baseStart_1081762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081835 : List Nat := [1, 1, 1, 1, 2, 3, 3, 1, 10]
def baseStart_1081835 : Nat := 118140960795 + 1081835 * 2 ^ 59
def prefixEnd_1081835 : Nat := 4983230072969 + 3 ^ 40 * 1081835 * 2
def baseEnd_1081835 : Nat := 61722371539653338809693

theorem tailTrace_1081835 : CollatzResearch.WordTrace tailWord_1081835 prefixEnd_1081835 61722371539653338809693 := by
  unfold tailWord_1081835
  simp only [CollatzResearch.WordTrace]
  refine ⟨39457764035704032553398959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26305176023802688368932639 39457764035704032553398959)
  ·
    refine ⟨59186646053556048830098439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39457764035704032553398959 59186646053556048830098439)
    ·
      refine ⟨88779969080334073245147659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59186646053556048830098439 88779969080334073245147659)
      ·
        refine ⟨133169953620501109867721489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88779969080334073245147659 133169953620501109867721489)
        ·
          refine ⟨99877465215375832400791117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133169953620501109867721489 99877465215375832400791117)
          ·
            refine ⟨37454049455765937150296669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99877465215375832400791117 37454049455765937150296669)
            ·
              refine ⟨14045268545912226431361251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37454049455765937150296669 14045268545912226431361251)
              ·
                refine ⟨21067902818868339647041877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14045268545912226431361251 21067902818868339647041877)
                ·
                  refine ⟨61722371539653338809693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 21067902818868339647041877 61722371539653338809693)
                  ·
                    rfl

theorem cell23_1081835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 10].length) (baseStart_1081835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1081835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1081835 prefixEnd_1081835 := by exact prefixLift 1081835
  have htrace : WordTrace (prefixWord ++ tailWord_1081835) baseStart_1081835 baseEnd_1081835 := by
    simpa [prefixWord, tailWord_1081835, baseEnd_1081835] using wordTrace_append hprefix tailTrace_1081835
  have hstable : (prefixWord ++ tailWord_1081835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081835).length < 2 ^ (prefixWord ++ tailWord_1081835).sum := by decide
  have hdescent : baseEnd_1081835 < baseStart_1081835 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081852 : List Nat := [2, 2, 2, 1, 2, 1, 1, 6, 6]
def baseStart_1081852 : Nat := 118140960795 + 1081852 * 2 ^ 59
def prefixEnd_1081852 : Nat := 4983230072969 + 3 ^ 40 * 1081852 * 2
def baseEnd_1081852 : Nat := 61723341447556275863851

theorem tailTrace_1081852 : CollatzResearch.WordTrace tailWord_1081852 prefixEnd_1081852 61723341447556275863851 := by
  unfold tailWord_1081852
  simp only [CollatzResearch.WordTrace]
  refine ⟨19729192038321222228383905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26305589384428296304511873 19729192038321222228383905)
  ·
    refine ⟨14796894028740916671287929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19729192038321222228383905 14796894028740916671287929)
    ·
      refine ⟨11097670521555687503465947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14796894028740916671287929 11097670521555687503465947)
      ·
        refine ⟨16646505782333531255198921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11097670521555687503465947 16646505782333531255198921)
        ·
          refine ⟨12484879336750148441399191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16646505782333531255198921 12484879336750148441399191)
          ·
            refine ⟨18727319005125222662098787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12484879336750148441399191 18727319005125222662098787)
            ·
              refine ⟨28090978507687833993148181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18727319005125222662098787 28090978507687833993148181)
              ·
                refine ⟨1316764617547867218428821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 28090978507687833993148181 1316764617547867218428821)
                ·
                  refine ⟨61723341447556275863851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1316764617547867218428821 61723341447556275863851)
                  ·
                    rfl

theorem cell23_1081852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 6, 6].length) (baseStart_1081852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1081852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1081852 prefixEnd_1081852 := by exact prefixLift 1081852
  have htrace : WordTrace (prefixWord ++ tailWord_1081852) baseStart_1081852 baseEnd_1081852 := by
    simpa [prefixWord, tailWord_1081852, baseEnd_1081852] using wordTrace_append hprefix tailTrace_1081852
  have hstable : (prefixWord ++ tailWord_1081852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081852).length < 2 ^ (prefixWord ++ tailWord_1081852).sum := by decide
  have hdescent : baseEnd_1081852 < baseStart_1081852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081906 : List Nat := [3, 2, 1, 1, 2, 1, 4, 2, 2, 3, 2]
def baseStart_1081906 : Nat := 118140960795 + 1081906 * 2 ^ 59
def prefixEnd_1081906 : Nat := 4983230072969 + 3 ^ 40 * 1081906 * 2
def baseEnd_1081906 : Nat := 555537800983349271499411

theorem tailTrace_1081906 : CollatzResearch.WordTrace tailWord_1081906 prefixEnd_1081906 555537800983349271499411 := by
  unfold tailWord_1081906
  simp only [CollatzResearch.WordTrace]
  refine ⟨9865088404611702919808393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26306902412297874452822381 9865088404611702919808393)
  ·
    refine ⟨7398816303458777189856295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9865088404611702919808393 7398816303458777189856295)
    ·
      refine ⟨11098224455188165784784443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7398816303458777189856295 11098224455188165784784443)
      ·
        refine ⟨16647336682782248677176665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11098224455188165784784443 16647336682782248677176665)
        ·
          refine ⟨12485502512086686507882499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16647336682782248677176665 12485502512086686507882499)
          ·
            refine ⟨18728253768130029761823749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12485502512086686507882499 18728253768130029761823749)
            ·
              refine ⟨3511547581524380580341953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18728253768130029761823749 3511547581524380580341953)
              ·
                refine ⟨2633660686143285435256465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3511547581524380580341953 2633660686143285435256465)
                ·
                  refine ⟨1975245514607464076442349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2633660686143285435256465 1975245514607464076442349)
                  ·
                    refine ⟨740717067977799028665881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1975245514607464076442349 740717067977799028665881)
                    ·
                      refine ⟨555537800983349271499411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 740717067977799028665881 555537800983349271499411)
                      ·
                        rfl

theorem cell23_1081906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 2, 2, 3, 2].length) (baseStart_1081906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1081906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1081906 prefixEnd_1081906 := by exact prefixLift 1081906
  have htrace : WordTrace (prefixWord ++ tailWord_1081906) baseStart_1081906 baseEnd_1081906 := by
    simpa [prefixWord, tailWord_1081906, baseEnd_1081906] using wordTrace_append hprefix tailTrace_1081906
  have hstable : (prefixWord ++ tailWord_1081906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081906).length < 2 ^ (prefixWord ++ tailWord_1081906).sum := by decide
  have hdescent : baseEnd_1081906 < baseStart_1081906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081912 : List Nat := [2, 1, 2, 1, 4, 1, 1, 2, 3, 6]
def baseStart_1081912 : Nat := 118140960795 + 1081912 * 2 ^ 59
def prefixEnd_1081912 : Nat := 4983230072969 + 3 ^ 40 * 1081912 * 2
def baseEnd_1081912 : Nat := 185180293955758749341461

theorem tailTrace_1081912 : CollatzResearch.WordTrace tailWord_1081912 prefixEnd_1081912 185180293955758749341461 := by
  unfold tailWord_1081912
  simp only [CollatzResearch.WordTrace]
  refine ⟨19730286228212537351975995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26307048304283383135967993 19730286228212537351975995)
  ·
    refine ⟨29595429342318806027963993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19730286228212537351975995 29595429342318806027963993)
    ·
      refine ⟨22196572006739104520972995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29595429342318806027963993 22196572006739104520972995)
      ·
        refine ⟨33294858010108656781459493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22196572006739104520972995 33294858010108656781459493)
        ·
          refine ⟨6242785876895373146523655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33294858010108656781459493 6242785876895373146523655)
          ·
            refine ⟨9364178815343059719785483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6242785876895373146523655 9364178815343059719785483)
            ·
              refine ⟨14046268223014589579678225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9364178815343059719785483 14046268223014589579678225)
              ·
                refine ⟨10534701167260942184758669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14046268223014589579678225 10534701167260942184758669)
                ·
                  refine ⟨3950512937722853319284501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10534701167260942184758669 3950512937722853319284501)
                  ·
                    refine ⟨185180293955758749341461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3950512937722853319284501 185180293955758749341461)
                    ·
                      rfl

theorem cell23_1081912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 3, 6].length) (baseStart_1081912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1081912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1081912 prefixEnd_1081912 := by exact prefixLift 1081912
  have htrace : WordTrace (prefixWord ++ tailWord_1081912) baseStart_1081912 baseEnd_1081912 := by
    simpa [prefixWord, tailWord_1081912, baseEnd_1081912] using wordTrace_append hprefix tailTrace_1081912
  have hstable : (prefixWord ++ tailWord_1081912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081912).length < 2 ^ (prefixWord ++ tailWord_1081912).sum := by decide
  have hdescent : baseEnd_1081912 < baseStart_1081912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081913 : List Nat := [1, 2, 1, 5, 1, 1, 3, 4, 1, 1, 3]
def baseStart_1081913 : Nat := 118140960795 + 1081913 * 2 ^ 59
def prefixEnd_1081913 : Nat := 4983230072969 + 3 ^ 40 * 1081913 * 2
def baseEnd_1081913 : Nat := 555541395347930744111879

theorem tailTrace_1081913 : CollatzResearch.WordTrace tailWord_1081913 prefixEnd_1081913 555541395347930744111879 := by
  unfold tailWord_1081913
  simp only [CollatzResearch.WordTrace]
  refine ⟨39460608929421451874738393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26307072619614301249825595 39460608929421451874738393)
  ·
    refine ⟨29595456697066088906053795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39460608929421451874738393 29595456697066088906053795)
    ·
      refine ⟨44393185045599133359080693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29595456697066088906053795 44393185045599133359080693)
      ·
        refine ⟨4161861098024918752413815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 44393185045599133359080693 4161861098024918752413815)
        ·
          refine ⟨6242791647037378128620723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4161861098024918752413815 6242791647037378128620723)
          ·
            refine ⟨9364187470556067192931085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6242791647037378128620723 9364187470556067192931085)
            ·
              refine ⟨3511570301458525197349157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9364187470556067192931085 3511570301458525197349157)
              ·
                refine ⟨658419431523473474502967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3511570301458525197349157 658419431523473474502967)
                ·
                  refine ⟨987629147285210211754451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 658419431523473474502967 987629147285210211754451)
                  ·
                    refine ⟨1481443720927815317631677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 987629147285210211754451 1481443720927815317631677)
                    ·
                      refine ⟨555541395347930744111879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1481443720927815317631677 555541395347930744111879)
                      ·
                        rfl

theorem cell23_1081913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 4, 1, 1, 3].length) (baseStart_1081913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1081913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1081913 prefixEnd_1081913 := by exact prefixLift 1081913
  have htrace : WordTrace (prefixWord ++ tailWord_1081913) baseStart_1081913 baseEnd_1081913 := by
    simpa [prefixWord, tailWord_1081913, baseEnd_1081913] using wordTrace_append hprefix tailTrace_1081913
  have hstable : (prefixWord ++ tailWord_1081913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081913).length < 2 ^ (prefixWord ++ tailWord_1081913).sum := by decide
  have hdescent : baseEnd_1081913 < baseStart_1081913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081953 : List Nat := [1, 2, 3, 1, 1, 6, 2, 1, 1, 1, 4]
def baseStart_1081953 : Nat := 118140960795 + 1081953 * 2 ^ 59
def prefixEnd_1081953 : Nat := 4983230072969 + 3 ^ 40 * 1081953 * 2
def baseEnd_1081953 : Nat := 555561934574110587611695

theorem tailTrace_1081953 : CollatzResearch.WordTrace tailWord_1081953 prefixEnd_1081953 555561934574110587611695 := by
  unfold tailWord_1081953
  simp only [CollatzResearch.WordTrace]
  refine ⟨39462067849276538706194513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26308045232851025804129675 39462067849276538706194513)
  ·
    refine ⟨29596550886957404029645885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39462067849276538706194513 29596550886957404029645885)
    ·
      refine ⟨11098706582609026511117207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29596550886957404029645885 11098706582609026511117207)
      ·
        refine ⟨16648059873913539766675811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11098706582609026511117207 16648059873913539766675811)
        ·
          refine ⟨24972089810870309650013717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16648059873913539766675811 24972089810870309650013717)
          ·
            refine ⟨1170566709884545764844393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 24972089810870309650013717 1170566709884545764844393)
            ·
              refine ⟨877925032413409323633295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1170566709884545764844393 877925032413409323633295)
              ·
                refine ⟨1316887548620113985449943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 877925032413409323633295 1316887548620113985449943)
                ·
                  refine ⟨1975331322930170978174915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1316887548620113985449943 1975331322930170978174915)
                  ·
                    refine ⟨2962996984395256467262373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1975331322930170978174915 2962996984395256467262373)
                    ·
                      refine ⟨555561934574110587611695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2962996984395256467262373 555561934574110587611695)
                      ·
                        rfl

theorem cell23_1081953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 2, 1, 1, 1, 4].length) (baseStart_1081953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1081953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1081953 prefixEnd_1081953 := by exact prefixLift 1081953
  have htrace : WordTrace (prefixWord ++ tailWord_1081953) baseStart_1081953 baseEnd_1081953 := by
    simpa [prefixWord, tailWord_1081953, baseEnd_1081953] using wordTrace_append hprefix tailTrace_1081953
  have hstable : (prefixWord ++ tailWord_1081953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081953).length < 2 ^ (prefixWord ++ tailWord_1081953).sum := by decide
  have hdescent : baseEnd_1081953 < baseStart_1081953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081956 : List Nat := [2, 3, 1, 1, 2, 2, 3, 3, 1, 2, 3]
def baseStart_1081956 : Nat := 118140960795 + 1081956 * 2 ^ 59
def prefixEnd_1081956 : Nat := 4983230072969 + 3 ^ 40 * 1081956 * 2
def baseEnd_1081956 : Nat := 555563475016074075874181

theorem tailTrace_1081956 : CollatzResearch.WordTrace tailWord_1081956 prefixEnd_1081956 555563475016074075874181 := by
  unfold tailWord_1081956
  simp only [CollatzResearch.WordTrace]
  refine ⟨19731088634132835109276861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26308118178843780145702481 19731088634132835109276861)
  ·
    refine ⟨7399158237799813165978823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19731088634132835109276861 7399158237799813165978823)
    ·
      refine ⟨11098737356699719748968235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7399158237799813165978823 11098737356699719748968235)
      ·
        refine ⟨16648106035049579623452353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11098737356699719748968235 16648106035049579623452353)
        ·
          refine ⟨12486079526287184717589265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16648106035049579623452353 12486079526287184717589265)
          ·
            refine ⟨9364559644715388538191949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12486079526287184717589265 9364559644715388538191949)
            ·
              refine ⟨3511709866768270701821981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9364559644715388538191949 3511709866768270701821981)
              ·
                refine ⟨1316891200038101513183243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3511709866768270701821981 1316891200038101513183243)
                ·
                  refine ⟨1975336800057152269774865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1316891200038101513183243 1975336800057152269774865)
                  ·
                    refine ⟨1481502600042864202331149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1975336800057152269774865 1481502600042864202331149)
                    ·
                      refine ⟨555563475016074075874181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1481502600042864202331149 555563475016074075874181)
                      ·
                        rfl

theorem cell23_1081956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 3, 1, 2, 3].length) (baseStart_1081956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1081956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1081956 prefixEnd_1081956 := by exact prefixLift 1081956
  have htrace : WordTrace (prefixWord ++ tailWord_1081956) baseStart_1081956 baseEnd_1081956 := by
    simpa [prefixWord, tailWord_1081956, baseEnd_1081956] using wordTrace_append hprefix tailTrace_1081956
  have hstable : (prefixWord ++ tailWord_1081956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081956).length < 2 ^ (prefixWord ++ tailWord_1081956).sum := by decide
  have hdescent : baseEnd_1081956 < baseStart_1081956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081970 : List Nat := [3, 2, 1, 2, 4, 1, 2, 1, 3, 2, 2]
def baseStart_1081970 : Nat := 118140960795 + 1081970 * 2 ^ 59
def prefixEnd_1081970 : Nat := 4983230072969 + 3 ^ 40 * 1081970 * 2
def baseEnd_1081970 : Nat := 555570663745237021099117

theorem tailTrace_1081970 : CollatzResearch.WordTrace tailWord_1081970 prefixEnd_1081970 555570663745237021099117 := by
  unfold tailWord_1081970
  simp only [CollatzResearch.WordTrace]
  refine ⟨9865671972553737652390841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26308458593476633739708909 9865671972553737652390841)
  ·
    refine ⟨7399253979415303239293131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9865671972553737652390841 7399253979415303239293131)
    ·
      refine ⟨11098880969122954858939697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7399253979415303239293131 11098880969122954858939697)
      ·
        refine ⟨8324160726842216144204773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11098880969122954858939697 8324160726842216144204773)
        ·
          refine ⟨1560780136282915527038395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8324160726842216144204773 1560780136282915527038395)
          ·
            refine ⟨2341170204424373290557593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1560780136282915527038395 2341170204424373290557593)
            ·
              refine ⟨1755877653318279967918195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2341170204424373290557593 1755877653318279967918195)
              ·
                refine ⟨2633816479977419951877293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1755877653318279967918195 2633816479977419951877293)
                ·
                  refine ⟨987681179991532481953985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2633816479977419951877293 987681179991532481953985)
                  ·
                    refine ⟨740760884993649361465489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 987681179991532481953985 740760884993649361465489)
                    ·
                      refine ⟨555570663745237021099117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 740760884993649361465489 555570663745237021099117)
                      ·
                        rfl

theorem cell23_1081970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 1, 3, 2, 2].length) (baseStart_1081970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1081970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1081970 prefixEnd_1081970 := by exact prefixLift 1081970
  have htrace : WordTrace (prefixWord ++ tailWord_1081970) baseStart_1081970 baseEnd_1081970 := by
    simpa [prefixWord, tailWord_1081970, baseEnd_1081970] using wordTrace_append hprefix tailTrace_1081970
  have hstable : (prefixWord ++ tailWord_1081970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081970).length < 2 ^ (prefixWord ++ tailWord_1081970).sum := by decide
  have hdescent : baseEnd_1081970 < baseStart_1081970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081979 : List Nat := [1, 1, 1, 1, 1, 4, 2, 1, 2, 7, 2]
def baseStart_1081979 : Nat := 118140960795 + 1081979 * 2 ^ 59
def prefixEnd_1081979 : Nat := 4983230072969 + 3 ^ 40 * 1081979 * 2
def baseEnd_1081979 : Nat := 555575285071127485886575

theorem tailTrace_1081979 : CollatzResearch.WordTrace tailWord_1081979 prefixEnd_1081979 555575285071127485886575 := by
  unfold tailWord_1081979
  simp only [CollatzResearch.WordTrace]
  refine ⟨39463016147182345146640991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26308677431454896764427327 39463016147182345146640991)
  ·
    refine ⟨59194524220773517719961487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39463016147182345146640991 59194524220773517719961487)
    ·
      refine ⟨88791786331160276579942231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59194524220773517719961487 88791786331160276579942231)
      ·
        refine ⟨133187679496740414869913347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88791786331160276579942231 133187679496740414869913347)
        ·
          refine ⟨199781519245110622304870021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133187679496740414869913347 199781519245110622304870021)
          ·
            refine ⟨37459034858458241682163129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 199781519245110622304870021 37459034858458241682163129)
            ·
              refine ⟨28094276143843681261622347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37459034858458241682163129 28094276143843681261622347)
              ·
                refine ⟨42141414215765521892433521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28094276143843681261622347 42141414215765521892433521)
                ·
                  refine ⟨31606060661824141419325141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42141414215765521892433521 31606060661824141419325141)
                  ·
                    refine ⟨740767046761503314515433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31606060661824141419325141 740767046761503314515433)
                    ·
                      refine ⟨555575285071127485886575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 740767046761503314515433 555575285071127485886575)
                      ·
                        rfl

theorem cell23_1081979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 7, 2].length) (baseStart_1081979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1081979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1081979 prefixEnd_1081979 := by exact prefixLift 1081979
  have htrace : WordTrace (prefixWord ++ tailWord_1081979) baseStart_1081979 baseEnd_1081979 := by
    simpa [prefixWord, tailWord_1081979, baseEnd_1081979] using wordTrace_append hprefix tailTrace_1081979
  have hstable : (prefixWord ++ tailWord_1081979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081979).length < 2 ^ (prefixWord ++ tailWord_1081979).sum := by decide
  have hdescent : baseEnd_1081979 < baseStart_1081979 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082004 : List Nat := [2, 4, 2, 2, 1, 3, 1, 3, 1, 2, 2]
def baseStart_1082004 : Nat := 118140960795 + 1082004 * 2 ^ 59
def prefixEnd_1082004 : Nat := 4983230072969 + 3 ^ 40 * 1082004 * 2
def baseEnd_1082004 : Nat := 555588122087489888073961

theorem tailTrace_1082004 : CollatzResearch.WordTrace tailWord_1082004 prefixEnd_1082004 555588122087489888073961 := by
  unfold tailWord_1082004
  simp only [CollatzResearch.WordTrace]
  refine ⟨19731963986045887208150533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26309285314727849610867377 19731963986045887208150533)
  ·
    refine ⟨3699743247383603851528225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19731963986045887208150533 3699743247383603851528225)
    ·
      refine ⟨2774807435537702888646169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3699743247383603851528225 2774807435537702888646169)
      ·
        refine ⟨2081105576653277166484627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2774807435537702888646169 2081105576653277166484627)
        ·
          refine ⟨3121658364979915749726941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2081105576653277166484627 3121658364979915749726941)
          ·
            refine ⟨1170621886867468406147603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3121658364979915749726941 1170621886867468406147603)
            ·
              refine ⟨1755932830301202609221405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1170621886867468406147603 1755932830301202609221405)
              ·
                refine ⟨658474811362950978458027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1755932830301202609221405 658474811362950978458027)
                ·
                  refine ⟨987712217044426467687041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 658474811362950978458027 987712217044426467687041)
                  ·
                    refine ⟨740784162783319850765281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 987712217044426467687041 740784162783319850765281)
                    ·
                      refine ⟨555588122087489888073961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 740784162783319850765281 555588122087489888073961)
                      ·
                        rfl

theorem cell23_1082004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_1082004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1082004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1082004 prefixEnd_1082004 := by exact prefixLift 1082004
  have htrace : WordTrace (prefixWord ++ tailWord_1082004) baseStart_1082004 baseEnd_1082004 := by
    simpa [prefixWord, tailWord_1082004, baseEnd_1082004] using wordTrace_append hprefix tailTrace_1082004
  have hstable : (prefixWord ++ tailWord_1082004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082004).length < 2 ^ (prefixWord ++ tailWord_1082004).sum := by decide
  have hdescent : baseEnd_1082004 < baseStart_1082004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082013 : List Nat := [1, 4, 2, 1, 1, 1, 4, 3, 1, 3, 2]
def baseStart_1082013 : Nat := 118140960795 + 1082013 * 2 ^ 59
def prefixEnd_1082013 : Nat := 4983230072969 + 3 ^ 40 * 1082013 * 2
def baseEnd_1082013 : Nat := 555592743413380352861419

theorem tailTrace_1082013 : CollatzResearch.WordTrace tailWord_1082013 prefixEnd_1082013 555592743413380352861419 := by
  unfold tailWord_1082013
  simp only [CollatzResearch.WordTrace]
  refine ⟨39464256229059168953378693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26309504152706112635585795 39464256229059168953378693)
  ·
    refine ⟨7399548042948594178758505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39464256229059168953378693 7399548042948594178758505)
    ·
      refine ⟨5549661032211445634068879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7399548042948594178758505 5549661032211445634068879)
      ·
        refine ⟨8324491548317168451103319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5549661032211445634068879 8324491548317168451103319)
        ·
          refine ⟨12486737322475752676654979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8324491548317168451103319 12486737322475752676654979)
          ·
            refine ⟨18730105983713629014982469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12486737322475752676654979 18730105983713629014982469)
            ·
              refine ⟨3511894871946305440309213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18730105983713629014982469 3511894871946305440309213)
              ·
                refine ⟨1316960576979864540115955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3511894871946305440309213 1316960576979864540115955)
                ·
                  refine ⟨1975440865469796810173933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1316960576979864540115955 1975440865469796810173933)
                  ·
                    refine ⟨740790324551173803815225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1975440865469796810173933 740790324551173803815225)
                    ·
                      refine ⟨555592743413380352861419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 740790324551173803815225 555592743413380352861419)
                      ·
                        rfl

theorem cell23_1082013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 3, 1, 3, 2].length) (baseStart_1082013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1082013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1082013 prefixEnd_1082013 := by exact prefixLift 1082013
  have htrace : WordTrace (prefixWord ++ tailWord_1082013) baseStart_1082013 baseEnd_1082013 := by
    simpa [prefixWord, tailWord_1082013, baseEnd_1082013] using wordTrace_append hprefix tailTrace_1082013
  have hstable : (prefixWord ++ tailWord_1082013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082013).length < 2 ^ (prefixWord ++ tailWord_1082013).sum := by decide
  have hdescent : baseEnd_1082013 < baseStart_1082013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082037 : List Nat := [1, 3, 3, 3, 1, 3, 2, 1, 2, 1, 3]
def baseStart_1082037 : Nat := 118140960795 + 1082037 * 2 ^ 59
def prefixEnd_1082037 : Nat := 4983230072969 + 3 ^ 40 * 1082037 * 2
def baseEnd_1082037 : Nat := 555605066949088258961309

theorem tailTrace_1082037 : CollatzResearch.WordTrace tailWord_1082037 prefixEnd_1082037 555605066949088258961309 := by
  unfold tailWord_1082037
  simp only [CollatzResearch.WordTrace]
  refine ⟨39465131580972221052252365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26310087720648147368168243 39465131580972221052252365)
  ·
    refine ⟨14799424342864582894594637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39465131580972221052252365 14799424342864582894594637)
    ·
      refine ⟨5549784128574218585472989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14799424342864582894594637 5549784128574218585472989)
      ·
        refine ⟨2081169048215331969552371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5549784128574218585472989 2081169048215331969552371)
        ·
          refine ⟨3121753572322997954328557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2081169048215331969552371 3121753572322997954328557)
          ·
            refine ⟨1170657589621124232873209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3121753572322997954328557 1170657589621124232873209)
            ·
              refine ⟨877993192215843174654907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1170657589621124232873209 877993192215843174654907)
              ·
                refine ⟨1316989788323764761982361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 877993192215843174654907 1316989788323764761982361)
                ·
                  refine ⟨987742341242823571486771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1316989788323764761982361 987742341242823571486771)
                  ·
                    refine ⟨1481613511864235357230157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 987742341242823571486771 1481613511864235357230157)
                    ·
                      refine ⟨555605066949088258961309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1481613511864235357230157 555605066949088258961309)
                      ·
                        rfl

theorem cell23_1082037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_1082037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1082037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1082037 prefixEnd_1082037 := by exact prefixLift 1082037
  have htrace : WordTrace (prefixWord ++ tailWord_1082037) baseStart_1082037 baseEnd_1082037 := by
    simpa [prefixWord, tailWord_1082037, baseEnd_1082037] using wordTrace_append hprefix tailTrace_1082037
  have hstable : (prefixWord ++ tailWord_1082037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082037).length < 2 ^ (prefixWord ++ tailWord_1082037).sum := by decide
  have hdescent : baseEnd_1082037 < baseStart_1082037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082059 : List Nat := [1, 1, 1, 1, 3, 2, 1, 1, 6, 3, 3]
def baseStart_1082059 : Nat := 118140960795 + 1082059 * 2 ^ 59
def prefixEnd_1082059 : Nat := 4983230072969 + 3 ^ 40 * 1082059 * 2
def baseEnd_1082059 : Nat := 555616363523487172886207

theorem tailTrace_1082059 : CollatzResearch.WordTrace tailWord_1082059 prefixEnd_1082059 555616363523487172886207 := by
  unfold tailWord_1082059
  simp only [CollatzResearch.WordTrace]
  refine ⟨39465933986892518809553231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26310622657928345873035487 39465933986892518809553231)
  ·
    refine ⟨59198900980338778214329847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39465933986892518809553231 59198900980338778214329847)
    ·
      refine ⟨88798351470508167321494771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59198900980338778214329847 88798351470508167321494771)
      ·
        refine ⟨133197527205762250982242157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88798351470508167321494771 133197527205762250982242157)
        ·
          refine ⟨49949072702160844118340809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 133197527205762250982242157 49949072702160844118340809)
          ·
            refine ⟨37461804526620633088755607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49949072702160844118340809 37461804526620633088755607)
            ·
              refine ⟨56192706789930949633133411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37461804526620633088755607 56192706789930949633133411)
              ·
                refine ⟨84289060184896424449700117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56192706789930949633133411 84289060184896424449700117)
                ·
                  refine ⟨3951049696167019896079693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 84289060184896424449700117 3951049696167019896079693)
                  ·
                    refine ⟨1481643636062632461029885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3951049696167019896079693 1481643636062632461029885)
                    ·
                      refine ⟨555616363523487172886207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1481643636062632461029885 555616363523487172886207)
                      ·
                        rfl

theorem cell23_1082059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 6, 3, 3].length) (baseStart_1082059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1082059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1082059 prefixEnd_1082059 := by exact prefixLift 1082059
  have htrace : WordTrace (prefixWord ++ tailWord_1082059) baseStart_1082059 baseEnd_1082059 := by
    simpa [prefixWord, tailWord_1082059, baseEnd_1082059] using wordTrace_append hprefix tailTrace_1082059
  have hstable : (prefixWord ++ tailWord_1082059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082059).length < 2 ^ (prefixWord ++ tailWord_1082059).sum := by decide
  have hdescent : baseEnd_1082059 < baseStart_1082059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082083 : List Nat := [1, 1, 1, 7, 1, 2, 1, 4, 5]
def baseStart_1082083 : Nat := 118140960795 + 1082083 * 2 ^ 59
def prefixEnd_1082083 : Nat := 4983230072969 + 3 ^ 40 * 1082083 * 2
def baseEnd_1082083 : Nat := 61736520784355008776233

theorem tailTrace_1082083 : CollatzResearch.WordTrace tailWord_1082083 prefixEnd_1082083 61736520784355008776233 := by
  unfold tailWord_1082083
  simp only [CollatzResearch.WordTrace]
  refine ⟨39466809338805570908426903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26311206225870380605617935 39466809338805570908426903)
  ·
    refine ⟨59200214008208356362640355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39466809338805570908426903 59200214008208356362640355)
    ·
      refine ⟨88800321012312534543960533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59200214008208356362640355 88800321012312534543960533)
      ·
        refine ⟨2081257523726075028374075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 88800321012312534543960533 2081257523726075028374075)
        ·
          refine ⟨3121886285589112542561113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2081257523726075028374075 3121886285589112542561113)
          ·
            refine ⟨2341414714191834406920835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3121886285589112542561113 2341414714191834406920835)
            ·
              refine ⟨3512122071287751610381253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2341414714191834406920835 3512122071287751610381253)
              ·
                refine ⟨658522888366453426946485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3512122071287751610381253 658522888366453426946485)
                ·
                  refine ⟨61736520784355008776233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 658522888366453426946485 61736520784355008776233)
                  ·
                    rfl

theorem cell23_1082083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 4, 5].length) (baseStart_1082083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1082083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1082083 prefixEnd_1082083 := by exact prefixLift 1082083
  have htrace : WordTrace (prefixWord ++ tailWord_1082083) baseStart_1082083 baseEnd_1082083 := by
    simpa [prefixWord, tailWord_1082083, baseEnd_1082083] using wordTrace_append hprefix tailTrace_1082083
  have hstable : (prefixWord ++ tailWord_1082083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082083).length < 2 ^ (prefixWord ++ tailWord_1082083).sum := by decide
  have hdescent : baseEnd_1082083 < baseStart_1082083 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082089 : List Nat := [1, 2, 1, 1, 1, 2, 6, 1, 1, 2, 5]
def baseStart_1082089 : Nat := 118140960795 + 1082089 * 2 ^ 59
def prefixEnd_1082089 : Nat := 4983230072969 + 3 ^ 40 * 1082089 * 2
def baseEnd_1082089 : Nat := 555631767943122055511069

theorem tailTrace_1082089 : CollatzResearch.WordTrace tailWord_1082089 prefixEnd_1082089 555631767943122055511069 := by
  unfold tailWord_1082089
  simp only [CollatzResearch.WordTrace]
  refine ⟨39467028176783833933145321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26311352117855889288763547 39467028176783833933145321)
  ·
    refine ⟨29600271132587875449858991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39467028176783833933145321 29600271132587875449858991)
    ·
      refine ⟨44400406698881813174788487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29600271132587875449858991 44400406698881813174788487)
      ·
        refine ⟨66600610048322719762182731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44400406698881813174788487 66600610048322719762182731)
        ·
          refine ⟨99900915072484079643274097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66600610048322719762182731 99900915072484079643274097)
          ·
            refine ⟨74925686304363059732455573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99900915072484079643274097 74925686304363059732455573)
            ·
              refine ⟨3512141545517018424958855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 74925686304363059732455573 3512141545517018424958855)
              ·
                refine ⟨5268212318275527637438283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3512141545517018424958855 5268212318275527637438283)
                ·
                  refine ⟨7902318477413291456157425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5268212318275527637438283 7902318477413291456157425)
                  ·
                    refine ⟨5926738858059968592118069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7902318477413291456157425 5926738858059968592118069)
                    ·
                      refine ⟨555631767943122055511069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5926738858059968592118069 555631767943122055511069)
                      ·
                        rfl

theorem cell23_1082089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 1, 1, 2, 5].length) (baseStart_1082089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1082089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1082089 prefixEnd_1082089 := by exact prefixLift 1082089
  have htrace : WordTrace (prefixWord ++ tailWord_1082089) baseStart_1082089 baseEnd_1082089 := by
    simpa [prefixWord, tailWord_1082089, baseEnd_1082089] using wordTrace_append hprefix tailTrace_1082089
  have hstable : (prefixWord ++ tailWord_1082089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082089).length < 2 ^ (prefixWord ++ tailWord_1082089).sum := by decide
  have hdescent : baseEnd_1082089 < baseStart_1082089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082099 : List Nat := [1, 1, 1, 2, 2, 3, 1, 4, 1, 3, 4]
def baseStart_1082099 : Nat := 118140960795 + 1082099 * 2 ^ 59
def prefixEnd_1082099 : Nat := 4983230072969 + 3 ^ 40 * 1082099 * 2
def baseEnd_1082099 : Nat := 555636902749667016386023

theorem tailTrace_1082099 : CollatzResearch.WordTrace tailWord_1082099 prefixEnd_1082099 555636902749667016386023 := by
  unfold tailWord_1082099
  simp only [CollatzResearch.WordTrace]
  refine ⟨39467392906747605641009351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26311595271165070427339567 39467392906747605641009351)
  ·
    refine ⟨59201089360121408461514027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39467392906747605641009351 59201089360121408461514027)
    ·
      refine ⟨88801634040182112692271041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59201089360121408461514027 88801634040182112692271041)
      ·
        refine ⟨66601225530136584519203281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88801634040182112692271041 66601225530136584519203281)
        ·
          refine ⟨49950919147602438389402461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66601225530136584519203281 49950919147602438389402461)
          ·
            refine ⟨18731594680350914396025923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49950919147602438389402461 18731594680350914396025923)
            ·
              refine ⟨28097392020526371594038885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18731594680350914396025923 28097392020526371594038885)
              ·
                refine ⟨5268261003848694673882291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28097392020526371594038885 5268261003848694673882291)
                ·
                  refine ⟨7902391505773042010823437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5268261003848694673882291 7902391505773042010823437)
                  ·
                    refine ⟨2963396814664890754058789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7902391505773042010823437 2963396814664890754058789)
                    ·
                      refine ⟨555636902749667016386023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2963396814664890754058789 555636902749667016386023)
                      ·
                        rfl

theorem cell23_1082099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 4, 1, 3, 4].length) (baseStart_1082099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1082099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1082099 prefixEnd_1082099 := by exact prefixLift 1082099
  have htrace : WordTrace (prefixWord ++ tailWord_1082099) baseStart_1082099 baseEnd_1082099 := by
    simpa [prefixWord, tailWord_1082099, baseEnd_1082099] using wordTrace_append hprefix tailTrace_1082099
  have hstable : (prefixWord ++ tailWord_1082099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082099).length < 2 ^ (prefixWord ++ tailWord_1082099).sum := by decide
  have hdescent : baseEnd_1082099 < baseStart_1082099 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082100 : List Nat := [2, 6, 1, 1, 2, 1, 1, 2, 7]
def baseStart_1082100 : Nat := 118140960795 + 1082100 * 2 ^ 59
def prefixEnd_1082100 : Nat := 4983230072969 + 3 ^ 40 * 1082100 * 2
def baseEnd_1082100 : Nat := 61737490692257945830391

theorem tailTrace_1082100 : CollatzResearch.WordTrace tailWord_1082100 prefixEnd_1082100 61737490692257945830391 := by
  unfold tailWord_1082100
  simp only [CollatzResearch.WordTrace]
  refine ⟨19733714689871991405897877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26311619586495988541197169 19733714689871991405897877)
  ·
    refine ⟨925017876087749597151463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 19733714689871991405897877 925017876087749597151463)
    ·
      refine ⟨1387526814131624395727195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 925017876087749597151463 1387526814131624395727195)
      ·
        refine ⟨2081290221197436593590793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1387526814131624395727195 2081290221197436593590793)
        ·
          refine ⟨1560967665898077445193095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2081290221197436593590793 1560967665898077445193095)
          ·
            refine ⟨2341451498847116167789643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1560967665898077445193095 2341451498847116167789643)
            ·
              refine ⟨3512177248270674251684465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2341451498847116167789643 3512177248270674251684465)
              ·
                refine ⟨2634132936203005688763349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3512177248270674251684465 2634132936203005688763349)
                ·
                  refine ⟨61737490692257945830391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2634132936203005688763349 61737490692257945830391)
                  ·
                    rfl

theorem cell23_1082100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_1082100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1082100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1082100 prefixEnd_1082100 := by exact prefixLift 1082100
  have htrace : WordTrace (prefixWord ++ tailWord_1082100) baseStart_1082100 baseEnd_1082100 := by
    simpa [prefixWord, tailWord_1082100, baseEnd_1082100] using wordTrace_append hprefix tailTrace_1082100
  have hstable : (prefixWord ++ tailWord_1082100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082100).length < 2 ^ (prefixWord ++ tailWord_1082100).sum := by decide
  have hdescent : baseEnd_1082100 < baseStart_1082100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082116 : List Nat := [2, 3, 2, 2, 1, 1, 3, 1, 1, 3, 4]
def baseStart_1082116 : Nat := 118140960795 + 1082116 * 2 ^ 59
def prefixEnd_1082116 : Nat := 4983230072969 + 3 ^ 40 * 1082116 * 2
def baseEnd_1082116 : Nat := 555645631920793449873445

theorem tailTrace_1082116 : CollatzResearch.WordTrace tailWord_1082116 prefixEnd_1082116 555645631920793449873445 := by
  unfold tailWord_1082116
  simp only [CollatzResearch.WordTrace]
  refine ⟨19734006473843008772189101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26312008631790678362918801 19734006473843008772189101)
  ·
    refine ⟨7400252427691128289570913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19734006473843008772189101 7400252427691128289570913)
    ·
      refine ⟨5550189320768346217178185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7400252427691128289570913 5550189320768346217178185)
      ·
        refine ⟨4162641990576259662883639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5550189320768346217178185 4162641990576259662883639)
        ·
          refine ⟨6243962985864389494325459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4162641990576259662883639 6243962985864389494325459)
          ·
            refine ⟨9365944478796584241488189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6243962985864389494325459 9365944478796584241488189)
            ·
              refine ⟨3512229179548719090558071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9365944478796584241488189 3512229179548719090558071)
              ·
                refine ⟨5268343769323078635837107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3512229179548719090558071 5268343769323078635837107)
                ·
                  refine ⟨7902515653984617953755661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5268343769323078635837107 7902515653984617953755661)
                  ·
                    refine ⟨2963443370244231732658373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7902515653984617953755661 2963443370244231732658373)
                    ·
                      refine ⟨555645631920793449873445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2963443370244231732658373 555645631920793449873445)
                      ·
                        rfl

theorem cell23_1082116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_1082116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1082116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1082116 prefixEnd_1082116 := by exact prefixLift 1082116
  have htrace : WordTrace (prefixWord ++ tailWord_1082116) baseStart_1082116 baseEnd_1082116 := by
    simpa [prefixWord, tailWord_1082116, baseEnd_1082116] using wordTrace_append hprefix tailTrace_1082116
  have hstable : (prefixWord ++ tailWord_1082116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082116).length < 2 ^ (prefixWord ++ tailWord_1082116).sum := by decide
  have hdescent : baseEnd_1082116 < baseStart_1082116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082126 : List Nat := [4, 1, 1, 2, 1, 1, 1, 1, 7, 4]
def baseStart_1082126 : Nat := 118140960795 + 1082126 * 2 ^ 59
def prefixEnd_1082126 : Nat := 4983230072969 + 3 ^ 40 * 1082126 * 2
def baseEnd_1082126 : Nat := 185216922242446136916133

theorem tailTrace_1082126 : CollatzResearch.WordTrace tailWord_1082126 prefixEnd_1082126 185216922242446136916133 := by
  unfold tailWord_1082126
  simp only [CollatzResearch.WordTrace]
  refine ⟨4933547209706223656530279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26312251785099859501494821 4933547209706223656530279)
  ·
    refine ⟨7400320814559335484795419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4933547209706223656530279 7400320814559335484795419)
    ·
      refine ⟨11100481221839003227193129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7400320814559335484795419 11100481221839003227193129)
      ·
        refine ⟨8325360916379252420394847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11100481221839003227193129 8325360916379252420394847)
        ·
          refine ⟨12488041374568878630592271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8325360916379252420394847 12488041374568878630592271)
          ·
            refine ⟨18732062061853317945888407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12488041374568878630592271 18732062061853317945888407)
            ·
              refine ⟨28098093092779976918832611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18732062061853317945888407 28098093092779976918832611)
              ·
                refine ⟨42147139639169965378248917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28098093092779976918832611 42147139639169965378248917)
                ·
                  refine ⟨987823585293046063552709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 42147139639169965378248917 987823585293046063552709)
                  ·
                    refine ⟨185216922242446136916133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 987823585293046063552709 185216922242446136916133)
                    ·
                      rfl

theorem cell23_1082126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 7, 4].length) (baseStart_1082126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1082126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1082126 prefixEnd_1082126 := by exact prefixLift 1082126
  have htrace : WordTrace (prefixWord ++ tailWord_1082126) baseStart_1082126 baseEnd_1082126 := by
    simpa [prefixWord, tailWord_1082126, baseEnd_1082126] using wordTrace_append hprefix tailTrace_1082126
  have hstable : (prefixWord ++ tailWord_1082126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082126).length < 2 ^ (prefixWord ++ tailWord_1082126).sum := by decide
  have hdescent : baseEnd_1082126 < baseStart_1082126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082129 : List Nat := [1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 6]
def baseStart_1082129 : Nat := 118140960795 + 1082129 * 2 ^ 59
def prefixEnd_1082129 : Nat := 4983230072969 + 3 ^ 40 * 1082129 * 2
def baseEnd_1082129 : Nat := 555652307169301899010885

theorem tailTrace_1082129 : CollatzResearch.WordTrace tailWord_1082129 prefixEnd_1082129 555652307169301899010885 := by
  unfold tailWord_1082129
  simp only [CollatzResearch.WordTrace]
  refine ⟨39468487096638920764601441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26312324731092613843067627 39468487096638920764601441)
  ·
    refine ⟨29601365322479190573451081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39468487096638920764601441 29601365322479190573451081)
    ·
      refine ⟨22201023991859392930088311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29601365322479190573451081 22201023991859392930088311)
      ·
        refine ⟨33301535987789089395132467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22201023991859392930088311 33301535987789089395132467)
        ·
          refine ⟨49952303981683634092698701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33301535987789089395132467 49952303981683634092698701)
          ·
            refine ⟨18732113993131362784762013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49952303981683634092698701 18732113993131362784762013)
            ·
              refine ⟨7024542747424261044285755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18732113993131362784762013 7024542747424261044285755)
              ·
                refine ⟨10536814121136391566428633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7024542747424261044285755 10536814121136391566428633)
                ·
                  refine ⟨7902610590852293674821475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10536814121136391566428633 7902610590852293674821475)
                  ·
                    refine ⟨11853915886278440512232213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7902610590852293674821475 11853915886278440512232213)
                    ·
                      refine ⟨555652307169301899010885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11853915886278440512232213 555652307169301899010885)
                      ·
                        rfl

theorem cell23_1082129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 6].length) (baseStart_1082129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1082129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1082129 prefixEnd_1082129 := by exact prefixLift 1082129
  have htrace : WordTrace (prefixWord ++ tailWord_1082129) baseStart_1082129 baseEnd_1082129 := by
    simpa [prefixWord, tailWord_1082129, baseEnd_1082129] using wordTrace_append hprefix tailTrace_1082129
  have hstable : (prefixWord ++ tailWord_1082129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082129).length < 2 ^ (prefixWord ++ tailWord_1082129).sum := by decide
  have hdescent : baseEnd_1082129 < baseStart_1082129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082136 : List Nat := [2, 1, 2, 3, 1, 1, 1, 3, 4, 2, 3]
def baseStart_1082136 : Nat := 118140960795 + 1082136 * 2 ^ 59
def prefixEnd_1082136 : Nat := 4983230072969 + 3 ^ 40 * 1082136 * 2
def baseEnd_1082136 : Nat := 555655901533883371623353

theorem tailTrace_1082136 : CollatzResearch.WordTrace tailWord_1082136 prefixEnd_1082136 555655901533883371623353 := by
  unfold tailWord_1082136
  simp only [CollatzResearch.WordTrace]
  refine ⟨19734371203806780480053131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26312494938409040640070841 19734371203806780480053131)
  ·
    refine ⟨29601556805710170720079697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19734371203806780480053131 29601556805710170720079697)
    ·
      refine ⟨22201167604282628040059773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29601556805710170720079697 22201167604282628040059773)
      ·
        refine ⟨8325437851605985515022415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22201167604282628040059773 8325437851605985515022415)
        ·
          refine ⟨12488156777408978272533623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8325437851605985515022415 12488156777408978272533623)
          ·
            refine ⟨18732235166113467408800435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12488156777408978272533623 18732235166113467408800435)
            ·
              refine ⟨28098352749170201113200653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18732235166113467408800435 28098352749170201113200653)
              ·
                refine ⟨10536882280938825417450245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28098352749170201113200653 10536882280938825417450245)
                ·
                  refine ⟨1975665427676029765771921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10536882280938825417450245 1975665427676029765771921)
                  ·
                    refine ⟨1481749070757022324328941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1975665427676029765771921 1481749070757022324328941)
                    ·
                      refine ⟨555655901533883371623353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1481749070757022324328941 555655901533883371623353)
                      ·
                        rfl

theorem cell23_1082136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 4, 2, 3].length) (baseStart_1082136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1082136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1082136 prefixEnd_1082136 := by exact prefixLift 1082136
  have htrace : WordTrace (prefixWord ++ tailWord_1082136) baseStart_1082136 baseEnd_1082136 := by
    simpa [prefixWord, tailWord_1082136, baseEnd_1082136] using wordTrace_append hprefix tailTrace_1082136
  have hstable : (prefixWord ++ tailWord_1082136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082136).length < 2 ^ (prefixWord ++ tailWord_1082136).sum := by decide
  have hdescent : baseEnd_1082136 < baseStart_1082136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082143 : List Nat := [1, 1, 2, 4, 2, 3, 2, 1, 3, 4]
def baseStart_1082143 : Nat := 118140960795 + 1082143 * 2 ^ 59
def prefixEnd_1082143 : Nat := 4983230072969 + 3 ^ 40 * 1082143 * 2
def baseEnd_1082143 : Nat := 185219831966154948078607

theorem tailTrace_1082143 : CollatzResearch.WordTrace tailWord_1082143 prefixEnd_1082143 185219831966154948078607 := by
  unfold tailWord_1082143
  simp only [CollatzResearch.WordTrace]
  refine ⟨39468997718588201155611083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26312665145725467437074055 39468997718588201155611083)
  ·
    refine ⟨59203496577882301733416625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39468997718588201155611083 59203496577882301733416625)
    ·
      refine ⟨44402622433411726300062469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59203496577882301733416625 44402622433411726300062469)
      ·
        refine ⟨8325491706264698681261713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44402622433411726300062469 8325491706264698681261713)
        ·
          refine ⟨6244118779698524010946285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8325491706264698681261713 6244118779698524010946285)
          ·
            refine ⟨2341544542386946504104857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6244118779698524010946285 2341544542386946504104857)
            ·
              refine ⟨1756158406790209878078643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2341544542386946504104857 1756158406790209878078643)
              ·
                refine ⟨2634237610185314817117965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1756158406790209878078643 2634237610185314817117965)
                ·
                  refine ⟨987839103819493056419237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2634237610185314817117965 987839103819493056419237)
                  ·
                    refine ⟨185219831966154948078607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 987839103819493056419237 185219831966154948078607)
                    ·
                      rfl

theorem cell23_1082143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 1, 3, 4].length) (baseStart_1082143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1082143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1082143 prefixEnd_1082143 := by exact prefixLift 1082143
  have htrace : WordTrace (prefixWord ++ tailWord_1082143) baseStart_1082143 baseEnd_1082143 := by
    simpa [prefixWord, tailWord_1082143, baseEnd_1082143] using wordTrace_append hprefix tailTrace_1082143
  have hstable : (prefixWord ++ tailWord_1082143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082143).length < 2 ^ (prefixWord ++ tailWord_1082143).sum := by decide
  have hdescent : baseEnd_1082143 < baseStart_1082143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082200 : List Nat := [2, 1, 2, 2, 1, 1, 1, 8, 1, 1, 3]
def baseStart_1082200 : Nat := 118140960795 + 1082200 * 2 ^ 59
def prefixEnd_1082200 : Nat := 4983230072969 + 3 ^ 40 * 1082200 * 2
def baseEnd_1082200 : Nat := 555688764295771121223059

theorem tailTrace_1082200 : CollatzResearch.WordTrace tailWord_1082200 prefixEnd_1082200 555688764295771121223059 := by
  unfold tailWord_1082200
  simp only [CollatzResearch.WordTrace]
  refine ⟨19735538339690849945218027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26314051119587799926957369 19735538339690849945218027)
  ·
    refine ⟨29603307509536274917827041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19735538339690849945218027 29603307509536274917827041)
    ·
      refine ⟨22202480632152206188370281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29603307509536274917827041 22202480632152206188370281)
      ·
        refine ⟨16651860474114154641277711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22202480632152206188370281 16651860474114154641277711)
        ·
          refine ⟨24977790711171231961916567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16651860474114154641277711 24977790711171231961916567)
          ·
            refine ⟨37466686066756847942874851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24977790711171231961916567 37466686066756847942874851)
            ·
              refine ⟨56200029100135271914312277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37466686066756847942874851 56200029100135271914312277)
              ·
                refine ⟨658594091017210217745847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 56200029100135271914312277 658594091017210217745847)
                ·
                  refine ⟨987891136525815326618771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 658594091017210217745847 987891136525815326618771)
                  ·
                    refine ⟨1481836704788722989928157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 987891136525815326618771 1481836704788722989928157)
                    ·
                      refine ⟨555688764295771121223059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1481836704788722989928157 555688764295771121223059)
                      ·
                        rfl

theorem cell23_1082200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 8, 1, 1, 3].length) (baseStart_1082200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1082200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1082200 prefixEnd_1082200 := by exact prefixLift 1082200
  have htrace : WordTrace (prefixWord ++ tailWord_1082200) baseStart_1082200 baseEnd_1082200 := by
    simpa [prefixWord, tailWord_1082200, baseEnd_1082200] using wordTrace_append hprefix tailTrace_1082200
  have hstable : (prefixWord ++ tailWord_1082200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082200).length < 2 ^ (prefixWord ++ tailWord_1082200).sum := by decide
  have hdescent : baseEnd_1082200 < baseStart_1082200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082226 : List Nat := [3, 2, 1, 2, 1, 1, 2, 2, 3, 1, 5]
def baseStart_1082226 : Nat := 118140960795 + 1082226 * 2 ^ 59
def prefixEnd_1082226 : Nat := 4983230072969 + 3 ^ 40 * 1082226 * 2
def baseEnd_1082226 : Nat := 555702114792788019497939

theorem tailTrace_1082226 : CollatzResearch.WordTrace tailWord_1082226 prefixEnd_1082226 555702114792788019497939 := by
  unfold tailWord_1082226
  simp only [CollatzResearch.WordTrace]
  refine ⟨9868006244321876582720633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26314683318191670887255021 9868006244321876582720633)
  ·
    refine ⟨7401004683241407437040475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9868006244321876582720633 7401004683241407437040475)
    ·
      refine ⟨11101507024862111155560713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7401004683241407437040475 11101507024862111155560713)
      ·
        refine ⟨8326130268646583366670535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11101507024862111155560713 8326130268646583366670535)
        ·
          refine ⟨12489195402969875050005803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8326130268646583366670535 12489195402969875050005803)
          ·
            refine ⟨18733793104454812575008705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12489195402969875050005803 18733793104454812575008705)
            ·
              refine ⟨14050344828341109431256529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18733793104454812575008705 14050344828341109431256529)
              ·
                refine ⟨10537758621255832073442397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14050344828341109431256529 10537758621255832073442397)
                ·
                  refine ⟨3951659482970937027540899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10537758621255832073442397 3951659482970937027540899)
                  ·
                    refine ⟨5927489224456405541311349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3951659482970937027540899 5927489224456405541311349)
                    ·
                      refine ⟨555702114792788019497939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5927489224456405541311349 555702114792788019497939)
                      ·
                        rfl

theorem cell23_1082226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_1082226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1082226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1082226 prefixEnd_1082226 := by exact prefixLift 1082226
  have htrace : WordTrace (prefixWord ++ tailWord_1082226) baseStart_1082226 baseEnd_1082226 := by
    simpa [prefixWord, tailWord_1082226, baseEnd_1082226] using wordTrace_append hprefix tailTrace_1082226
  have hstable : (prefixWord ++ tailWord_1082226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082226).length < 2 ^ (prefixWord ++ tailWord_1082226).sum := by decide
  have hdescent : baseEnd_1082226 < baseStart_1082226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082250 : List Nat := [3, 1, 2, 4, 1, 1, 1, 4, 2, 4]
def baseStart_1082250 : Nat := 118140960795 + 1082250 * 2 ^ 59
def prefixEnd_1082250 : Nat := 4983230072969 + 3 ^ 40 * 1082250 * 2
def baseEnd_1082250 : Nat := 185238146109498641865943

theorem tailTrace_1082250 : CollatzResearch.WordTrace tailWord_1082250 prefixEnd_1082250 185238146109498641865943 := by
  unfold tailWord_1082250
  simp only [CollatzResearch.WordTrace]
  refine ⟨9868225082300139607439051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26315266886133705619837469 9868225082300139607439051)
  ·
    refine ⟨14802337623450209411158577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9868225082300139607439051 14802337623450209411158577)
    ·
      refine ⟨11101753217587657058368933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14802337623450209411158577 11101753217587657058368933)
      ·
        refine ⟨2081578728297685698444175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11101753217587657058368933 2081578728297685698444175)
        ·
          refine ⟨3122368092446528547666263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2081578728297685698444175 3122368092446528547666263)
          ·
            refine ⟨4683552138669792821499395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3122368092446528547666263 4683552138669792821499395)
            ·
              refine ⟨7025328208004689232249093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4683552138669792821499395 7025328208004689232249093)
              ·
                refine ⟨1317249039000879231046705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7025328208004689232249093 1317249039000879231046705)
                ·
                  refine ⟨987936779250659423285029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1317249039000879231046705 987936779250659423285029)
                  ·
                    refine ⟨185238146109498641865943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 987936779250659423285029 185238146109498641865943)
                    ·
                      rfl

theorem cell23_1082250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 4, 2, 4].length) (baseStart_1082250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1082250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1082250 prefixEnd_1082250 := by exact prefixLift 1082250
  have htrace : WordTrace (prefixWord ++ tailWord_1082250) baseStart_1082250 baseEnd_1082250 := by
    simpa [prefixWord, tailWord_1082250, baseEnd_1082250] using wordTrace_append hprefix tailTrace_1082250
  have hstable : (prefixWord ++ tailWord_1082250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082250).length < 2 ^ (prefixWord ++ tailWord_1082250).sum := by decide
  have hdescent : baseEnd_1082250 < baseStart_1082250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082276 : List Nat := [2, 3, 1, 2, 1, 2, 1, 2, 2, 7]
def baseStart_1082276 : Nat := 118140960795 + 1082276 * 2 ^ 59
def prefixEnd_1082276 : Nat := 4983230072969 + 3 ^ 40 * 1082276 * 2
def baseEnd_1082276 : Nat := 185242596275170941290903

theorem tailTrace_1082276 : CollatzResearch.WordTrace tailWord_1082276 prefixEnd_1082276 185242596275170941290903 := by
  unfold tailWord_1082276
  simp only [CollatzResearch.WordTrace]
  refine ⟨19736924313553182435101341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26315899084737576580135121 19736924313553182435101341)
  ·
    refine ⟨7401346617582443413163003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19736924313553182435101341 7401346617582443413163003)
    ·
      refine ⟨11102019926373665119744505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7401346617582443413163003 11102019926373665119744505)
      ·
        refine ⟨8326514944780248839808379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11102019926373665119744505 8326514944780248839808379)
        ·
          refine ⟨12489772417170373259712569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8326514944780248839808379 12489772417170373259712569)
          ·
            refine ⟨9367329312877779944784427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12489772417170373259712569 9367329312877779944784427)
            ·
              refine ⟨14050993969316669917176641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9367329312877779944784427 14050993969316669917176641)
              ·
                refine ⟨10538245476987502437882481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14050993969316669917176641 10538245476987502437882481)
                ·
                  refine ⟨7903684107740626828411861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10538245476987502437882481 7903684107740626828411861)
                  ·
                    refine ⟨185242596275170941290903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7903684107740626828411861 185242596275170941290903)
                    ·
                      rfl

theorem cell23_1082276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 2, 7].length) (baseStart_1082276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1082276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1082276 prefixEnd_1082276 := by exact prefixLift 1082276
  have htrace : WordTrace (prefixWord ++ tailWord_1082276) baseStart_1082276 baseEnd_1082276 := by
    simpa [prefixWord, tailWord_1082276, baseEnd_1082276] using wordTrace_append hprefix tailTrace_1082276
  have hstable : (prefixWord ++ tailWord_1082276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082276).length < 2 ^ (prefixWord ++ tailWord_1082276).sum := by decide
  have hdescent : baseEnd_1082276 < baseStart_1082276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082324 : List Nat := [2, 4, 1, 2, 1, 3, 3, 1, 2, 1, 3]
def baseStart_1082324 : Nat := 118140960795 + 1082324 * 2 ^ 59
def prefixEnd_1082324 : Nat := 4983230072969 + 3 ^ 40 * 1082324 * 2
def baseEnd_1082324 : Nat := 555752435896928636072489

theorem tailTrace_1082324 : CollatzResearch.WordTrace tailWord_1082324 prefixEnd_1082324 555752435896928636072489 := by
  unfold tailWord_1082324
  simp only [CollatzResearch.WordTrace]
  refine ⟨19737799665466234533975013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26317066220621646045300017 19737799665466234533975013)
  ·
    refine ⟨3700837437274918975120315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19737799665466234533975013 3700837437274918975120315)
    ·
      refine ⟨5551256155912378462680473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3700837437274918975120315 5551256155912378462680473)
      ·
        refine ⟨4163442116934283847010355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5551256155912378462680473 4163442116934283847010355)
        ·
          refine ⟨6245163175401425770515533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4163442116934283847010355 6245163175401425770515533)
          ·
            refine ⟨2341936190775534663943325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6245163175401425770515533 2341936190775534663943325)
            ·
              refine ⟨878226071540825498978747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2341936190775534663943325 878226071540825498978747)
              ·
                refine ⟨1317339107311238248468121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 878226071540825498978747 1317339107311238248468121)
                ·
                  refine ⟨988004330483428686351091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1317339107311238248468121 988004330483428686351091)
                  ·
                    refine ⟨1482006495725143029526637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 988004330483428686351091 1482006495725143029526637)
                    ·
                      refine ⟨555752435896928636072489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1482006495725143029526637 555752435896928636072489)
                      ·
                        rfl

theorem cell23_1082324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 3, 1, 2, 1, 3].length) (baseStart_1082324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1082324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1082324 prefixEnd_1082324 := by exact prefixLift 1082324
  have htrace : WordTrace (prefixWord ++ tailWord_1082324) baseStart_1082324 baseEnd_1082324 := by
    simpa [prefixWord, tailWord_1082324, baseEnd_1082324] using wordTrace_append hprefix tailTrace_1082324
  have hstable : (prefixWord ++ tailWord_1082324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082324).length < 2 ^ (prefixWord ++ tailWord_1082324).sum := by decide
  have hdescent : baseEnd_1082324 < baseStart_1082324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082350 : List Nat := [4, 1, 2, 1, 4, 1, 1, 1, 2, 1, 5]
def baseStart_1082350 : Nat := 118140960795 + 1082350 * 2 ^ 59
def prefixEnd_1082350 : Nat := 4983230072969 + 3 ^ 40 * 1082350 * 2
def baseEnd_1082350 : Nat := 555765786393945534347369

theorem tailTrace_1082350 : CollatzResearch.WordTrace tailWord_1082350 prefixEnd_1082350 555765786393945534347369 := by
  unfold tailWord_1082350
  simp only [CollatzResearch.WordTrace]
  refine ⟨4934568453604784438549563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26317698419225517005597669 4934568453604784438549563)
  ·
    refine ⟨7401852680407176657824345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4934568453604784438549563 7401852680407176657824345)
    ·
      refine ⟨5551389510305382493368259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7401852680407176657824345 5551389510305382493368259)
      ·
        refine ⟨8327084265458073740052389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5551389510305382493368259 8327084265458073740052389)
        ·
          refine ⟨1561328299773388826259823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8327084265458073740052389 1561328299773388826259823)
          ·
            refine ⟨2341992449660083239389735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1561328299773388826259823 2341992449660083239389735)
            ·
              refine ⟨3512988674490124859084603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2341992449660083239389735 3512988674490124859084603)
              ·
                refine ⟨5269483011735187288626905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3512988674490124859084603 5269483011735187288626905)
                ·
                  refine ⟨3952112258801390466470179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5269483011735187288626905 3952112258801390466470179)
                  ·
                    refine ⟨5928168388202085699705269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3952112258801390466470179 5928168388202085699705269)
                    ·
                      refine ⟨555765786393945534347369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5928168388202085699705269 555765786393945534347369)
                      ·
                        rfl

theorem cell23_1082350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 1, 2, 1, 5].length) (baseStart_1082350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1082350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1082350 prefixEnd_1082350 := by exact prefixLift 1082350
  have htrace : WordTrace (prefixWord ++ tailWord_1082350) baseStart_1082350 baseEnd_1082350 := by
    simpa [prefixWord, tailWord_1082350, baseEnd_1082350] using wordTrace_append hprefix tailTrace_1082350
  have hstable : (prefixWord ++ tailWord_1082350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082350).length < 2 ^ (prefixWord ++ tailWord_1082350).sum := by decide
  have hdescent : baseEnd_1082350 < baseStart_1082350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082423 : List Nat := [1, 1, 3, 1, 2, 2, 1, 2, 3, 4, 3]
def baseStart_1082423 : Nat := 118140960795 + 1082423 * 2 ^ 59
def prefixEnd_1082423 : Nat := 4983230072969 + 3 ^ 40 * 1082423 * 2
def baseEnd_1082423 : Nat := 555803270481723748734533

theorem tailTrace_1082423 : CollatzResearch.WordTrace tailWord_1082423 prefixEnd_1082423 555803270481723748734533 := by
  unfold tailWord_1082423
  simp only [CollatzResearch.WordTrace]
  refine ⟨39479210157573808975803923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26319473438382539317202615 39479210157573808975803923)
  ·
    refine ⟨59218815236360713463705885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39479210157573808975803923 59218815236360713463705885)
    ·
      refine ⟨22207055713635267548889707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59218815236360713463705885 22207055713635267548889707)
      ·
        refine ⟨33310583570452901323334561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22207055713635267548889707 33310583570452901323334561)
        ·
          refine ⟨24982937677839675992500921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33310583570452901323334561 24982937677839675992500921)
          ·
            refine ⟨18737203258379756994375691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24982937677839675992500921 18737203258379756994375691)
            ·
              refine ⟨28105804887569635491563537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18737203258379756994375691 28105804887569635491563537)
              ·
                refine ⟨21079353665677226618672653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28105804887569635491563537 21079353665677226618672653)
                ·
                  refine ⟨7904757624628959982002245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21079353665677226618672653 7904757624628959982002245)
                  ·
                    refine ⟨1482142054617929996625421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7904757624628959982002245 1482142054617929996625421)
                    ·
                      refine ⟨555803270481723748734533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1482142054617929996625421 555803270481723748734533)
                      ·
                        rfl

theorem cell23_1082423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 3, 4, 3].length) (baseStart_1082423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1082423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1082423 prefixEnd_1082423 := by exact prefixLift 1082423
  have htrace : WordTrace (prefixWord ++ tailWord_1082423) baseStart_1082423 baseEnd_1082423 := by
    simpa [prefixWord, tailWord_1082423, baseEnd_1082423] using wordTrace_append hprefix tailTrace_1082423
  have hstable : (prefixWord ++ tailWord_1082423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082423).length < 2 ^ (prefixWord ++ tailWord_1082423).sum := by decide
  have hdescent : baseEnd_1082423 < baseStart_1082423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082454 : List Nat := [5, 2, 2, 1, 2, 1, 1, 1, 1, 3, 4]
def baseStart_1082454 : Nat := 118140960795 + 1082454 * 2 ^ 59
def prefixEnd_1082454 : Nat := 4983230072969 + 3 ^ 40 * 1082454 * 2
def baseEnd_1082454 : Nat := 555819188382013127446891

theorem tailTrace_1082454 : CollatzResearch.WordTrace tailWord_1082454 prefixEnd_1082454 555819188382013127446891 := by
  unfold tailWord_1082454
  simp only [CollatzResearch.WordTrace]
  refine ⟨2467521301278843829386401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26320227213641000846788277 2467521301278843829386401)
  ·
    refine ⟨1850640975959132872039801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2467521301278843829386401 1850640975959132872039801)
    ·
      refine ⟨1387980731969349654029851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1850640975959132872039801 1387980731969349654029851)
      ·
        refine ⟨2081971097954024481044777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1387980731969349654029851 2081971097954024481044777)
        ·
          refine ⟨1561478323465518360783583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2081971097954024481044777 1561478323465518360783583)
          ·
            refine ⟨2342217485198277541175375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1561478323465518360783583 2342217485198277541175375)
            ·
              refine ⟨3513326227797416311763063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2342217485198277541175375 3513326227797416311763063)
              ·
                refine ⟨5269989341696124467644595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3513326227797416311763063 5269989341696124467644595)
                ·
                  refine ⟨7904984012544186701466893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5269989341696124467644595 7904984012544186701466893)
                  ·
                    refine ⟨2964369004704070013050085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7904984012544186701466893 2964369004704070013050085)
                    ·
                      refine ⟨555819188382013127446891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2964369004704070013050085 555819188382013127446891)
                      ·
                        rfl

theorem cell23_1082454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_1082454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1082454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1082454 prefixEnd_1082454 := by exact prefixLift 1082454
  have htrace : WordTrace (prefixWord ++ tailWord_1082454) baseStart_1082454 baseEnd_1082454 := by
    simpa [prefixWord, tailWord_1082454, baseEnd_1082454] using wordTrace_append hprefix tailTrace_1082454
  have hstable : (prefixWord ++ tailWord_1082454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082454).length < 2 ^ (prefixWord ++ tailWord_1082454).sum := by decide
  have hdescent : baseEnd_1082454 < baseStart_1082454 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082477 : List Nat := [1, 5, 1, 1, 2, 4, 1, 2, 6]
def baseStart_1082477 : Nat := 118140960795 + 1082477 * 2 ^ 59
def prefixEnd_1082477 : Nat := 4983230072969 + 3 ^ 40 * 1082477 * 2
def baseEnd_1082477 : Nat := 61758999826340726384365

theorem tailTrace_1082477 : CollatzResearch.WordTrace tailWord_1082477 prefixEnd_1082477 61758999826340726384365 := by
  unfold tailWord_1082477
  simp only [CollatzResearch.WordTrace]
  refine ⟨39481179699378176198269685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26320786466252117465513123 39481179699378176198269685)
  ·
    refine ⟨3701360596816704018587783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39481179699378176198269685 3701360596816704018587783)
    ·
      refine ⟨5552040895225056027881675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3701360596816704018587783 5552040895225056027881675)
      ·
        refine ⟨8328061342837584041822513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5552040895225056027881675 8328061342837584041822513)
        ·
          refine ⟨6246046007128188031366885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8328061342837584041822513 6246046007128188031366885)
          ·
            refine ⟨1171133626336535255881291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6246046007128188031366885 1171133626336535255881291)
            ·
              refine ⟨1756700439504802883821937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1171133626336535255881291 1756700439504802883821937)
              ·
                refine ⟨1317525329628602162866453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1756700439504802883821937 1317525329628602162866453)
                ·
                  refine ⟨61758999826340726384365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1317525329628602162866453 61758999826340726384365)
                  ·
                    rfl

theorem cell23_1082477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 2, 6].length) (baseStart_1082477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1082477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1082477 prefixEnd_1082477 := by exact prefixLift 1082477
  have htrace : WordTrace (prefixWord ++ tailWord_1082477) baseStart_1082477 baseEnd_1082477 := by
    simpa [prefixWord, tailWord_1082477, baseEnd_1082477] using wordTrace_append hprefix tailTrace_1082477
  have hstable : (prefixWord ++ tailWord_1082477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082477).length < 2 ^ (prefixWord ++ tailWord_1082477).sum := by decide
  have hdescent : baseEnd_1082477 < baseStart_1082477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082487 : List Nat := [1, 1, 3, 1, 1, 4, 4, 1, 3, 1, 3]
def baseStart_1082487 : Nat := 118140960795 + 1082487 * 2 ^ 59
def prefixEnd_1082487 : Nat := 4983230072969 + 3 ^ 40 * 1082487 * 2
def baseEnd_1082487 : Nat := 555836133243611498334239

theorem tailTrace_1082487 : CollatzResearch.WordTrace tailWord_1082487 prefixEnd_1082487 555836133243611498334239 := by
  unfold tailWord_1082487
  simp only [CollatzResearch.WordTrace]
  refine ⟨39481544429341947906133715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26321029619561298604089143 39481544429341947906133715)
  ·
    refine ⟨59222316644012921859200573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39481544429341947906133715 59222316644012921859200573)
    ·
      refine ⟨22208368741504845697200215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59222316644012921859200573 22208368741504845697200215)
      ·
        refine ⟨33312553112257268545800323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22208368741504845697200215 33312553112257268545800323)
        ·
          refine ⟨49968829668385902818700485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33312553112257268545800323 49968829668385902818700485)
          ·
            refine ⟨9369155562822356778506341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49968829668385902818700485 9369155562822356778506341)
            ·
              refine ⟨1756716668029191895969939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9369155562822356778506341 1756716668029191895969939)
              ·
                refine ⟨2635075002043787843954909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1756716668029191895969939 2635075002043787843954909)
                ·
                  refine ⟨988153125766420441483091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2635075002043787843954909 988153125766420441483091)
                  ·
                    refine ⟨1482229688649630662224637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 988153125766420441483091 1482229688649630662224637)
                    ·
                      refine ⟨555836133243611498334239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1482229688649630662224637 555836133243611498334239)
                      ·
                        rfl

theorem cell23_1082487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 1, 3, 1, 3].length) (baseStart_1082487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1082487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1082487 prefixEnd_1082487 := by exact prefixLift 1082487
  have htrace : WordTrace (prefixWord ++ tailWord_1082487) baseStart_1082487 baseEnd_1082487 := by
    simpa [prefixWord, tailWord_1082487, baseEnd_1082487] using wordTrace_append hprefix tailTrace_1082487
  have hstable : (prefixWord ++ tailWord_1082487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082487).length < 2 ^ (prefixWord ++ tailWord_1082487).sum := by decide
  have hdescent : baseEnd_1082487 < baseStart_1082487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082497 : List Nat := [1, 2, 4, 2, 2, 1, 1, 2, 1, 5, 2]
def baseStart_1082497 : Nat := 118140960795 + 1082497 * 2 ^ 59
def prefixEnd_1082497 : Nat := 4983230072969 + 3 ^ 40 * 1082497 * 2
def baseEnd_1082497 : Nat := 555841268050156459209193

theorem tailTrace_1082497 : CollatzResearch.WordTrace tailWord_1082497 prefixEnd_1082497 555841268050156459209193 := by
  unfold tailWord_1082497
  simp only [CollatzResearch.WordTrace]
  refine ⟨39481909159305719613997745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26321272772870479742665163 39481909159305719613997745)
  ·
    refine ⟨29611431869479289710498309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39481909159305719613997745 29611431869479289710498309)
    ·
      refine ⟨5552143475527366820718433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29611431869479289710498309 5552143475527366820718433)
      ·
        refine ⟨4164107606645525115538825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5552143475527366820718433 4164107606645525115538825)
        ·
          refine ⟨3123080704984143836654119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4164107606645525115538825 3123080704984143836654119)
          ·
            refine ⟨4684621057476215754981179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3123080704984143836654119 4684621057476215754981179)
            ·
              refine ⟨7026931586214323632471769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4684621057476215754981179 7026931586214323632471769)
              ·
                refine ⟨5270198689660742724353827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7026931586214323632471769 5270198689660742724353827)
                ·
                  refine ⟨7905298034491114086530741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5270198689660742724353827 7905298034491114086530741)
                  ·
                    refine ⟨741121690733541945612257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7905298034491114086530741 741121690733541945612257)
                    ·
                      refine ⟨555841268050156459209193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 741121690733541945612257 555841268050156459209193)
                      ·
                        rfl

theorem cell23_1082497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 2, 1, 5, 2].length) (baseStart_1082497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1082497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1082497 prefixEnd_1082497 := by exact prefixLift 1082497
  have htrace : WordTrace (prefixWord ++ tailWord_1082497) baseStart_1082497 baseEnd_1082497 := by
    simpa [prefixWord, tailWord_1082497, baseEnd_1082497] using wordTrace_append hprefix tailTrace_1082497
  have hstable : (prefixWord ++ tailWord_1082497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082497).length < 2 ^ (prefixWord ++ tailWord_1082497).sum := by decide
  have hdescent : baseEnd_1082497 < baseStart_1082497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082533 : List Nat := [1, 3, 1, 2, 1, 4, 11]
def baseStart_1082533 : Nat := 118140960795 + 1082533 * 2 ^ 59
def prefixEnd_1082533 : Nat := 4983230072969 + 3 ^ 40 * 1082533 * 2
def baseEnd_1082533 : Nat := 6862466090786645905667

theorem tailTrace_1082533 : CollatzResearch.WordTrace tailWord_1082533 prefixEnd_1082533 6862466090786645905667 := by
  unfold tailWord_1082533
  simp only [CollatzResearch.WordTrace]
  refine ⟨39483222187175297762308253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26322148124783531841538835 39483222187175297762308253)
  ·
    refine ⟨14806208320190736660865595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39483222187175297762308253 14806208320190736660865595)
    ·
      refine ⟨22209312480286104991298393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14806208320190736660865595 22209312480286104991298393)
      ·
        refine ⟨16656984360214578743473795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22209312480286104991298393 16656984360214578743473795)
        ·
          refine ⟨24985476540321868115210693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16656984360214578743473795 24985476540321868115210693)
          ·
            refine ⟨4684776851310350271602005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24985476540321868115210693 4684776851310350271602005)
            ·
              refine ⟨6862466090786645905667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 4684776851310350271602005 6862466090786645905667)
              ·
                rfl

theorem cell23_1082533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 11].length) (baseStart_1082533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1082533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1082533 prefixEnd_1082533 := by exact prefixLift 1082533
  have htrace : WordTrace (prefixWord ++ tailWord_1082533) baseStart_1082533 baseEnd_1082533 := by
    simpa [prefixWord, tailWord_1082533, baseEnd_1082533] using wordTrace_append hprefix tailTrace_1082533
  have hstable : (prefixWord ++ tailWord_1082533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082533).length < 2 ^ (prefixWord ++ tailWord_1082533).sum := by decide
  have hdescent : baseEnd_1082533 < baseStart_1082533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082561 : List Nat := [1, 2, 6, 1, 1, 3, 1, 2, 1, 1, 4]
def baseStart_1082561 : Nat := 118140960795 + 1082561 * 2 ^ 59
def prefixEnd_1082561 : Nat := 4983230072969 + 3 ^ 40 * 1082561 * 2
def baseEnd_1082561 : Nat := 555874130812044208808899

theorem tailTrace_1082561 : CollatzResearch.WordTrace tailWord_1082561 prefixEnd_1082561 555874130812044208808899 := by
  unfold tailWord_1082561
  simp only [CollatzResearch.WordTrace]
  refine ⟨39484243431073858544327537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26322828954049239029551691 39484243431073858544327537)
  ·
    refine ⟨29613182573305393908245653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39484243431073858544327537 29613182573305393908245653)
    ·
      refine ⟨1388117933123690339449015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 29613182573305393908245653 1388117933123690339449015)
      ·
        refine ⟨2082176899685535509173523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1388117933123690339449015 2082176899685535509173523)
        ·
          refine ⟨3123265349528303263760285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2082176899685535509173523 3123265349528303263760285)
          ·
            refine ⟨1171224506073113723910107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3123265349528303263760285 1171224506073113723910107)
            ·
              refine ⟨1756836759109670585865161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1171224506073113723910107 1756836759109670585865161)
              ·
                refine ⟨1317627569332252939398871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1756836759109670585865161 1317627569332252939398871)
                ·
                  refine ⟨1976441353998379409098307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1317627569332252939398871 1976441353998379409098307)
                  ·
                    refine ⟨2964662030997569113647461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1976441353998379409098307 2964662030997569113647461)
                    ·
                      refine ⟨555874130812044208808899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2964662030997569113647461 555874130812044208808899)
                      ·
                        rfl

theorem cell23_1082561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_1082561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1082561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1082561 prefixEnd_1082561 := by exact prefixLift 1082561
  have htrace : WordTrace (prefixWord ++ tailWord_1082561) baseStart_1082561 baseEnd_1082561 := by
    simpa [prefixWord, tailWord_1082561, baseEnd_1082561] using wordTrace_append hprefix tailTrace_1082561
  have hstable : (prefixWord ++ tailWord_1082561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082561).length < 2 ^ (prefixWord ++ tailWord_1082561).sum := by decide
  have hdescent : baseEnd_1082561 < baseStart_1082561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082563 : List Nat := [1, 1, 1, 3, 1, 1, 1, 3, 4, 7]
def baseStart_1082563 : Nat := 118140960795 + 1082563 * 2 ^ 59
def prefixEnd_1082563 : Nat := 4983230072969 + 3 ^ 40 * 1082563 * 2
def baseEnd_1082563 : Nat := 185291719257784400327963

theorem tailTrace_1082563 : CollatzResearch.WordTrace tailWord_1082563 prefixEnd_1082563 185291719257784400327963 := by
  unfold tailWord_1082563
  simp only [CollatzResearch.WordTrace]
  refine ⟨39484316377066612885900343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26322877584711075257266895 39484316377066612885900343)
  ·
    refine ⟨59226474565599919328850515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39484316377066612885900343 59226474565599919328850515)
    ·
      refine ⟨88839711848399878993275773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59226474565599919328850515 88839711848399878993275773)
      ·
        refine ⟨33314891943149954622478415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88839711848399878993275773 33314891943149954622478415)
        ·
          refine ⟨49972337914724931933717623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33314891943149954622478415 49972337914724931933717623)
          ·
            refine ⟨74958506872087397900576435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49972337914724931933717623 74958506872087397900576435)
            ·
              refine ⟨112437760308131096850864653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74958506872087397900576435 112437760308131096850864653)
              ·
                refine ⟨42164160115549161319074245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 112437760308131096850864653 42164160115549161319074245)
                ·
                  refine ⟨7905780021665467747326421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42164160115549161319074245 7905780021665467747326421)
                  ·
                    refine ⟨185291719257784400327963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7905780021665467747326421 185291719257784400327963)
                    ·
                      rfl

theorem cell23_1082563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 7].length) (baseStart_1082563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1082563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1082563 prefixEnd_1082563 := by exact prefixLift 1082563
  have htrace : WordTrace (prefixWord ++ tailWord_1082563) baseStart_1082563 baseEnd_1082563 := by
    simpa [prefixWord, tailWord_1082563, baseEnd_1082563] using wordTrace_append hprefix tailTrace_1082563
  have hstable : (prefixWord ++ tailWord_1082563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082563).length < 2 ^ (prefixWord ++ tailWord_1082563).sum := by decide
  have hdescent : baseEnd_1082563 < baseStart_1082563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082564 : List Nat := [2, 3, 3, 1, 3, 1, 1, 1, 3, 2, 3]
def baseStart_1082564 : Nat := 118140960795 + 1082564 * 2 ^ 59
def prefixEnd_1082564 : Nat := 4983230072969 + 3 ^ 40 * 1082564 * 2
def baseEnd_1082564 : Nat := 555875671254007697071385

theorem tailTrace_1082564 : CollatzResearch.WordTrace tailWord_1082564 prefixEnd_1082564 555875671254007697071385 := by
  unfold tailWord_1082564
  simp only [CollatzResearch.WordTrace]
  refine ⟨19742176425031495028343373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26322901900041993371124497 19742176425031495028343373)
  ·
    refine ⟨7403316159386810635628765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19742176425031495028343373 7403316159386810635628765)
    ·
      refine ⟨2776243559770053988360787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7403316159386810635628765 2776243559770053988360787)
      ·
        refine ⟨4164365339655080982541181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2776243559770053988360787 4164365339655080982541181)
        ·
          refine ⟨1561637002370655368452943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4164365339655080982541181 1561637002370655368452943)
          ·
            refine ⟨2342455503555983052679415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1561637002370655368452943 2342455503555983052679415)
            ·
              refine ⟨3513683255333974579019123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2342455503555983052679415 3513683255333974579019123)
              ·
                refine ⟨5270524883000961868528685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3513683255333974579019123 5270524883000961868528685)
                ·
                  refine ⟨1976446831125360700698257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5270524883000961868528685 1976446831125360700698257)
                  ·
                    refine ⟨1482335123344020525523693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1976446831125360700698257 1482335123344020525523693)
                    ·
                      refine ⟨555875671254007697071385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1482335123344020525523693 555875671254007697071385)
                      ·
                        rfl

theorem cell23_1082564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_1082564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1082564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1082564 prefixEnd_1082564 := by exact prefixLift 1082564
  have htrace : WordTrace (prefixWord ++ tailWord_1082564) baseStart_1082564 baseEnd_1082564 := by
    simpa [prefixWord, tailWord_1082564, baseEnd_1082564] using wordTrace_append hprefix tailTrace_1082564
  have hstable : (prefixWord ++ tailWord_1082564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082564).length < 2 ^ (prefixWord ++ tailWord_1082564).sum := by decide
  have hdescent : baseEnd_1082564 < baseStart_1082564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082581 : List Nat := [1, 3, 2, 4, 1, 2, 3, 1, 1, 2, 3]
def baseStart_1082581 : Nat := 118140960795 + 1082581 * 2 ^ 59
def prefixEnd_1082581 : Nat := 4983230072969 + 3 ^ 40 * 1082581 * 2
def baseEnd_1082581 : Nat := 555884400425134130558807

theorem tailTrace_1082581 : CollatzResearch.WordTrace tailWord_1082581 prefixEnd_1082581 555884400425134130558807 := by
  unfold tailWord_1082581
  simp only [CollatzResearch.WordTrace]
  refine ⟨39484972891001401960055597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26323315260667601306703731 39484972891001401960055597)
  ·
    refine ⟨14806864834125525735020849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39484972891001401960055597 14806864834125525735020849)
    ·
      refine ⟨11105148625594144301265637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14806864834125525735020849 11105148625594144301265637)
      ·
        refine ⟨2082215367298902056487307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11105148625594144301265637 2082215367298902056487307)
        ·
          refine ⟨3123323050948353084730961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2082215367298902056487307 3123323050948353084730961)
          ·
            refine ⟨2342492288211264813548221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3123323050948353084730961 2342492288211264813548221)
            ·
              refine ⟨878434608079224305080583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2342492288211264813548221 878434608079224305080583)
              ·
                refine ⟨1317651912118836457620875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 878434608079224305080583 1317651912118836457620875)
                ·
                  refine ⟨1976477868178254686431313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1317651912118836457620875 1976477868178254686431313)
                  ·
                    refine ⟨1482358401133691014823485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1976477868178254686431313 1482358401133691014823485)
                    ·
                      refine ⟨555884400425134130558807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1482358401133691014823485 555884400425134130558807)
                      ·
                        rfl

theorem cell23_1082581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_1082581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1082581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1082581 prefixEnd_1082581 := by exact prefixLift 1082581
  have htrace : WordTrace (prefixWord ++ tailWord_1082581) baseStart_1082581 baseEnd_1082581 := by
    simpa [prefixWord, tailWord_1082581, baseEnd_1082581] using wordTrace_append hprefix tailTrace_1082581
  have hstable : (prefixWord ++ tailWord_1082581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082581).length < 2 ^ (prefixWord ++ tailWord_1082581).sum := by decide
  have hdescent : baseEnd_1082581 < baseStart_1082581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082600 : List Nat := [2, 1, 4, 1, 2, 1, 1, 1, 1, 5, 4]
def baseStart_1082600 : Nat := 118140960795 + 1082600 * 2 ^ 59
def prefixEnd_1082600 : Nat := 4983230072969 + 3 ^ 40 * 1082600 * 2
def baseEnd_1082600 : Nat := 555894156557569556221219

theorem tailTrace_1082600 : CollatzResearch.WordTrace tailWord_1082600 prefixEnd_1082600 555894156557569556221219 := by
  unfold tailWord_1082600
  simp only [CollatzResearch.WordTrace]
  refine ⟨19742832938966284102498627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26323777251955045469998169 19742832938966284102498627)
  ·
    refine ⟨29614249408449426153747941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19742832938966284102498627 29614249408449426153747941)
    ·
      refine ⟨5552671764084267403827739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29614249408449426153747941 5552671764084267403827739)
      ·
        refine ⟨8329007646126401105741609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5552671764084267403827739 8329007646126401105741609)
        ·
          refine ⟨6246755734594800829306207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8329007646126401105741609 6246755734594800829306207)
          ·
            refine ⟨9370133601892201243959311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6246755734594800829306207 9370133601892201243959311)
            ·
              refine ⟨14055200402838301865938967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9370133601892201243959311 14055200402838301865938967)
              ·
                refine ⟨21082800604257452798908451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14055200402838301865938967 21082800604257452798908451)
                ·
                  refine ⟨31624200906386179198362677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21082800604257452798908451 31624200906386179198362677)
                  ·
                    refine ⟨2964768834973704299846501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31624200906386179198362677 2964768834973704299846501)
                    ·
                      refine ⟨555894156557569556221219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2964768834973704299846501 555894156557569556221219)
                      ·
                        rfl

theorem cell23_1082600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_1082600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1082600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1082600 prefixEnd_1082600 := by exact prefixLift 1082600
  have htrace : WordTrace (prefixWord ++ tailWord_1082600) baseStart_1082600 baseEnd_1082600 := by
    simpa [prefixWord, tailWord_1082600, baseEnd_1082600] using wordTrace_append hprefix tailTrace_1082600
  have hstable : (prefixWord ++ tailWord_1082600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082600).length < 2 ^ (prefixWord ++ tailWord_1082600).sum := by decide
  have hdescent : baseEnd_1082600 < baseStart_1082600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082634 : List Nat := [3, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2]
def baseStart_1082634 : Nat := 118140960795 + 1082634 * 2 ^ 59
def prefixEnd_1082634 : Nat := 4983230072969 + 3 ^ 40 * 1082634 * 2
def baseEnd_1082634 : Nat := 555911614899822423196063

theorem tailTrace_1082634 : CollatzResearch.WordTrace tailWord_1082634 prefixEnd_1082634 555911614899822423196063 := by
  unfold tailWord_1082634
  simp only [CollatzResearch.WordTrace]
  refine ⟨9871726489952348002933739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26324603973206261341156637 9871726489952348002933739)
  ·
    refine ⟨14807589734928522004400609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9871726489952348002933739 14807589734928522004400609)
    ·
      refine ⟨11105692301196391503300457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14807589734928522004400609 11105692301196391503300457)
      ·
        refine ⟨8329269225897293627475343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11105692301196391503300457 8329269225897293627475343)
        ·
          refine ⟨12493903838845940441213015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8329269225897293627475343 12493903838845940441213015)
          ·
            refine ⟨18740855758268910661819523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12493903838845940441213015 18740855758268910661819523)
            ·
              refine ⟨28111283637403365992729285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18740855758268910661819523 28111283637403365992729285)
              ·
                refine ⟨5270865682013131123636741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28111283637403365992729285 5270865682013131123636741)
                ·
                  refine ⟨988287315377462085681889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5270865682013131123636741 988287315377462085681889)
                  ·
                    refine ⟨741215486533096564261417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 988287315377462085681889 741215486533096564261417)
                    ·
                      refine ⟨555911614899822423196063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 741215486533096564261417 555911614899822423196063)
                      ·
                        rfl

theorem cell23_1082634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2].length) (baseStart_1082634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1082634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1082634 prefixEnd_1082634 := by exact prefixLift 1082634
  have htrace : WordTrace (prefixWord ++ tailWord_1082634) baseStart_1082634 baseEnd_1082634 := by
    simpa [prefixWord, tailWord_1082634, baseEnd_1082634] using wordTrace_append hprefix tailTrace_1082634
  have hstable : (prefixWord ++ tailWord_1082634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082634).length < 2 ^ (prefixWord ++ tailWord_1082634).sum := by decide
  have hdescent : baseEnd_1082634 < baseStart_1082634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082638 : List Nat := [4, 1, 1, 2, 1, 5, 2, 1, 1, 3, 2]
def baseStart_1082638 : Nat := 118140960795 + 1082638 * 2 ^ 59
def prefixEnd_1082638 : Nat := 4983230072969 + 3 ^ 40 * 1082638 * 2
def baseEnd_1082638 : Nat := 555913668822440407546045

theorem tailTrace_1082638 : CollatzResearch.WordTrace tailWord_1082638 prefixEnd_1082638 555913668822440407546045 := by
  unfold tailWord_1082638
  simp only [CollatzResearch.WordTrace]
  refine ⟨4935881481474362586860071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26324701234529933796587045 4935881481474362586860071)
  ·
    refine ⟨7403822222211543880290107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4935881481474362586860071 7403822222211543880290107)
    ·
      refine ⟨11105733333317315820435161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7403822222211543880290107 11105733333317315820435161)
      ·
        refine ⟨8329299999987986865326371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11105733333317315820435161 8329299999987986865326371)
        ·
          refine ⟨12493949999981980297989557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8329299999987986865326371 12493949999981980297989557)
          ·
            refine ⟨1171307812498310652936521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12493949999981980297989557 1171307812498310652936521)
            ·
              refine ⟨878480859373732989702391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1171307812498310652936521 878480859373732989702391)
              ·
                refine ⟨1317721289060599484553587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 878480859373732989702391 1317721289060599484553587)
                ·
                  refine ⟨1976581933590899226830381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1317721289060599484553587 1976581933590899226830381)
                  ·
                    refine ⟨741218225096587210061393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1976581933590899226830381 741218225096587210061393)
                    ·
                      refine ⟨555913668822440407546045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 741218225096587210061393 555913668822440407546045)
                      ·
                        rfl

theorem cell23_1082638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 2, 1, 1, 3, 2].length) (baseStart_1082638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1082638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1082638 prefixEnd_1082638 := by exact prefixLift 1082638
  have htrace : WordTrace (prefixWord ++ tailWord_1082638) baseStart_1082638 baseEnd_1082638 := by
    simpa [prefixWord, tailWord_1082638, baseEnd_1082638] using wordTrace_append hprefix tailTrace_1082638
  have hstable : (prefixWord ++ tailWord_1082638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082638).length < 2 ^ (prefixWord ++ tailWord_1082638).sum := by decide
  have hdescent : baseEnd_1082638 < baseStart_1082638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082680 : List Nat := [2, 1, 2, 1, 3, 1, 1, 2, 3, 2, 5]
def baseStart_1082680 : Nat := 118140960795 + 1082680 * 2 ^ 59
def prefixEnd_1082680 : Nat := 4983230072969 + 3 ^ 40 * 1082680 * 2
def baseEnd_1082680 : Nat := 555935235009929243220851

theorem tailTrace_1082680 : CollatzResearch.WordTrace tailWord_1082680 prefixEnd_1082680 555935235009929243220851 := by
  unfold tailWord_1082680
  simp only [CollatzResearch.WordTrace]
  refine ⟨19744291858821370933954747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26325722478428494578606329 19744291858821370933954747)
  ·
    refine ⟨29616437788232056400932121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19744291858821370933954747 29616437788232056400932121)
    ·
      refine ⟨22212328341174042300699091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29616437788232056400932121 22212328341174042300699091)
      ·
        refine ⟨33318492511761063451048637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22212328341174042300699091 33318492511761063451048637)
        ·
          refine ⟨12494434691910398794143239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33318492511761063451048637 12494434691910398794143239)
          ·
            refine ⟨18741652037865598191214859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12494434691910398794143239 18741652037865598191214859)
            ·
              refine ⟨28112478056798397286822289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18741652037865598191214859 28112478056798397286822289)
              ·
                refine ⟨21084358542598797965116717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28112478056798397286822289 21084358542598797965116717)
                ·
                  refine ⟨7906634453474549236918769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21084358542598797965116717 7906634453474549236918769)
                  ·
                    refine ⟨5929975840105911927689077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7906634453474549236918769 5929975840105911927689077)
                    ·
                      refine ⟨555935235009929243220851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5929975840105911927689077 555935235009929243220851)
                      ·
                        rfl

theorem cell23_1082680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 3, 2, 5].length) (baseStart_1082680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1082680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1082680 prefixEnd_1082680 := by exact prefixLift 1082680
  have htrace : WordTrace (prefixWord ++ tailWord_1082680) baseStart_1082680 baseEnd_1082680 := by
    simpa [prefixWord, tailWord_1082680, baseEnd_1082680] using wordTrace_append hprefix tailTrace_1082680
  have hstable : (prefixWord ++ tailWord_1082680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082680).length < 2 ^ (prefixWord ++ tailWord_1082680).sum := by decide
  have hdescent : baseEnd_1082680 < baseStart_1082680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082707 : List Nat := [1, 1, 1, 2, 1, 1, 7, 2, 2, 1, 4]
def baseStart_1082707 : Nat := 118140960795 + 1082707 * 2 ^ 59
def prefixEnd_1082707 : Nat := 4983230072969 + 3 ^ 40 * 1082707 * 2
def baseEnd_1082707 : Nat := 555949098987600637583227

theorem tailTrace_1082707 : CollatzResearch.WordTrace tailWord_1082707 prefixEnd_1082707 555949098987600637583227 := by
  unfold tailWord_1082707
  simp only [CollatzResearch.WordTrace]
  refine ⟨39489568488544925479142375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26326378992363283652761583 39489568488544925479142375)
  ·
    refine ⟨59234352732817388218713563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39489568488544925479142375 59234352732817388218713563)
    ·
      refine ⟨88851529099226082328070345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59234352732817388218713563 88851529099226082328070345)
      ·
        refine ⟨66638646824419561746052759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88851529099226082328070345 66638646824419561746052759)
        ·
          refine ⟨99957970236629342619079139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66638646824419561746052759 99957970236629342619079139)
          ·
            refine ⟨149936955354944013928618709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99957970236629342619079139 149936955354944013928618709)
            ·
              refine ⟨3514147391131500326452001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 149936955354944013928618709 3514147391131500326452001)
              ·
                refine ⟨2635610543348625244839001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3514147391131500326452001 2635610543348625244839001)
                ·
                  refine ⟨1976707907511468933629251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2635610543348625244839001 1976707907511468933629251)
                  ·
                    refine ⟨2965061861267203400443877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1976707907511468933629251 2965061861267203400443877)
                    ·
                      refine ⟨555949098987600637583227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2965061861267203400443877 555949098987600637583227)
                      ·
                        rfl

theorem cell23_1082707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 2, 2, 1, 4].length) (baseStart_1082707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1082707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1082707 prefixEnd_1082707 := by exact prefixLift 1082707
  have htrace : WordTrace (prefixWord ++ tailWord_1082707) baseStart_1082707 baseEnd_1082707 := by
    simpa [prefixWord, tailWord_1082707, baseEnd_1082707] using wordTrace_append hprefix tailTrace_1082707
  have hstable : (prefixWord ++ tailWord_1082707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082707).length < 2 ^ (prefixWord ++ tailWord_1082707).sum := by decide
  have hdescent : baseEnd_1082707 < baseStart_1082707 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082741 : List Nat := [1, 3, 4, 1, 3, 1, 2, 1, 2, 1, 4]
def baseStart_1082741 : Nat := 118140960795 + 1082741 * 2 ^ 59
def prefixEnd_1082741 : Nat := 4983230072969 + 3 ^ 40 * 1082741 * 2
def baseEnd_1082741 : Nat := 555966557329853504558071

theorem tailTrace_1082741 : CollatzResearch.WordTrace tailWord_1082741 prefixEnd_1082741 555966557329853504558071 := by
  unfold tailWord_1082741
  simp only [CollatzResearch.WordTrace]
  refine ⟨39490808570421749285880077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26327205713614499523920051 39490808570421749285880077)
  ·
    refine ⟨14809053213908155982205029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39490808570421749285880077 14809053213908155982205029)
    ·
      refine ⟨2776697477607779246663443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14809053213908155982205029 2776697477607779246663443)
      ·
        refine ⟨4165046216411668869995165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2776697477607779246663443 4165046216411668869995165)
        ·
          refine ⟨1561892331154375826248187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4165046216411668869995165 1561892331154375826248187)
          ·
            refine ⟨2342838496731563739372281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1561892331154375826248187 2342838496731563739372281)
            ·
              refine ⟨1757128872548672804529211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2342838496731563739372281 1757128872548672804529211)
              ·
                refine ⟨2635693308823009206793817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1757128872548672804529211 2635693308823009206793817)
                ·
                  refine ⟨1976769981617256905095363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2635693308823009206793817 1976769981617256905095363)
                  ·
                    refine ⟨2965154972425885357643045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1976769981617256905095363 2965154972425885357643045)
                    ·
                      refine ⟨555966557329853504558071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2965154972425885357643045 555966557329853504558071)
                      ·
                        rfl

theorem cell23_1082741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_1082741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1082741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1082741 prefixEnd_1082741 := by exact prefixLift 1082741
  have htrace : WordTrace (prefixWord ++ tailWord_1082741) baseStart_1082741 baseEnd_1082741 := by
    simpa [prefixWord, tailWord_1082741, baseEnd_1082741] using wordTrace_append hprefix tailTrace_1082741
  have hstable : (prefixWord ++ tailWord_1082741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082741).length < 2 ^ (prefixWord ++ tailWord_1082741).sum := by decide
  have hdescent : baseEnd_1082741 < baseStart_1082741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082777 : List Nat := [1, 2, 1, 2, 1, 5, 1, 2, 3, 5]
def baseStart_1082777 : Nat := 118140960795 + 1082777 * 2 ^ 59
def prefixEnd_1082777 : Nat := 4983230072969 + 3 ^ 40 * 1082777 * 2
def baseEnd_1082777 : Nat := 185328347544471787902635

theorem tailTrace_1082777 : CollatzResearch.WordTrace tailWord_1082777 prefixEnd_1082777 185328347544471787902635 := by
  unfold tailWord_1082777
  simp only [CollatzResearch.WordTrace]
  refine ⟨39492121598291327434190585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26328081065527551622793723 39492121598291327434190585)
  ·
    refine ⟨29619091198718495575642939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39492121598291327434190585 29619091198718495575642939)
    ·
      refine ⟨44428636798077743363464409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29619091198718495575642939 44428636798077743363464409)
      ·
        refine ⟨33321477598558307522598307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44428636798077743363464409 33321477598558307522598307)
        ·
          refine ⟨49982216397837461283897461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33321477598558307522598307 49982216397837461283897461)
          ·
            refine ⟨4685832787297261995365387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49982216397837461283897461 4685832787297261995365387)
            ·
              refine ⟨7028749180945892993048081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4685832787297261995365387 7028749180945892993048081)
              ·
                refine ⟨5271561885709419744786061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7028749180945892993048081 5271561885709419744786061)
                ·
                  refine ⟨1976835707141032404294773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5271561885709419744786061 1976835707141032404294773)
                  ·
                    refine ⟨185328347544471787902635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1976835707141032404294773 185328347544471787902635)
                    ·
                      rfl

theorem cell23_1082777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 2, 3, 5].length) (baseStart_1082777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1082777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1082777 prefixEnd_1082777 := by exact prefixLift 1082777
  have htrace : WordTrace (prefixWord ++ tailWord_1082777) baseStart_1082777 baseEnd_1082777 := by
    simpa [prefixWord, tailWord_1082777, baseEnd_1082777] using wordTrace_append hprefix tailTrace_1082777
  have hstable : (prefixWord ++ tailWord_1082777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082777).length < 2 ^ (prefixWord ++ tailWord_1082777).sum := by decide
  have hdescent : baseEnd_1082777 < baseStart_1082777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082784 : List Nat := [2, 1, 1, 4, 1, 2, 2, 2, 1, 5, 2]
def baseStart_1082784 : Nat := 118140960795 + 1082784 * 2 ^ 59
def prefixEnd_1082784 : Nat := 4983230072969 + 3 ^ 40 * 1082784 * 2
def baseEnd_1082784 : Nat := 555988636997996836320373

theorem tailTrace_1082784 : CollatzResearch.WordTrace tailWord_1082784 prefixEnd_1082784 555988636997996836320373 := by
  unfold tailWord_1082784
  simp only [CollatzResearch.WordTrace]
  refine ⟨19746188454632983814847703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26328251272843978419796937 19746188454632983814847703)
  ·
    refine ⟨29619282681949475722271555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19746188454632983814847703 29619282681949475722271555)
    ·
      refine ⟨44428924022924213583407333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29619282681949475722271555 44428924022924213583407333)
      ·
        refine ⟨8330423254298290046888875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44428924022924213583407333 8330423254298290046888875)
        ·
          refine ⟨12495634881447435070333313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8330423254298290046888875 12495634881447435070333313)
          ·
            refine ⟨9371726161085576302749985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12495634881447435070333313 9371726161085576302749985)
            ·
              refine ⟨7028794620814182227062489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9371726161085576302749985 7028794620814182227062489)
              ·
                refine ⟨5271595965610636670296867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7028794620814182227062489 5271595965610636670296867)
                ·
                  refine ⟨7907393948415955005445301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5271595965610636670296867 7907393948415955005445301)
                  ·
                    refine ⟨741318182663995781760497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7907393948415955005445301 741318182663995781760497)
                    ·
                      refine ⟨555988636997996836320373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 741318182663995781760497 555988636997996836320373)
                      ·
                        rfl

theorem cell23_1082784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 2, 1, 5, 2].length) (baseStart_1082784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1082784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1082784 prefixEnd_1082784 := by exact prefixLift 1082784
  have htrace : WordTrace (prefixWord ++ tailWord_1082784) baseStart_1082784 baseEnd_1082784 := by
    simpa [prefixWord, tailWord_1082784, baseEnd_1082784] using wordTrace_append hprefix tailTrace_1082784
  have hstable : (prefixWord ++ tailWord_1082784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082784).length < 2 ^ (prefixWord ++ tailWord_1082784).sum := by decide
  have hdescent : baseEnd_1082784 < baseStart_1082784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082791 : List Nat := [1, 1, 6, 1, 1, 1, 3, 2, 3, 1, 3]
def baseStart_1082791 : Nat := 118140960795 + 1082791 * 2 ^ 59
def prefixEnd_1082791 : Nat := 4983230072969 + 3 ^ 40 * 1082791 * 2
def baseEnd_1082791 : Nat := 555992231362578308932841

theorem tailTrace_1082791 : CollatzResearch.WordTrace tailWord_1082791 prefixEnd_1082791 555992231362578308932841 := by
  unfold tailWord_1082791
  simp only [CollatzResearch.WordTrace]
  refine ⟨39492632220240607825200227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26328421480160405216800151 39492632220240607825200227)
  ·
    refine ⟨59238948330360911737800341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39492632220240607825200227 59238948330360911737800341)
    ·
      refine ⟨2776825702985667737709391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 59238948330360911737800341 2776825702985667737709391)
      ·
        refine ⟨4165238554478501606564087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2776825702985667737709391 4165238554478501606564087)
        ·
          refine ⟨6247857831717752409846131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4165238554478501606564087 6247857831717752409846131)
          ·
            refine ⟨9371786747576628614769197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6247857831717752409846131 9371786747576628614769197)
            ·
              refine ⟨3514420030341235730538449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9371786747576628614769197 3514420030341235730538449)
              ·
                refine ⟨2635815022755926797903837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3514420030341235730538449 2635815022755926797903837)
                ·
                  refine ⟨988430633533472549213939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2635815022755926797903837 988430633533472549213939)
                  ·
                    refine ⟨1482645950300208823820909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 988430633533472549213939 1482645950300208823820909)
                    ·
                      refine ⟨555992231362578308932841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1482645950300208823820909 555992231362578308932841)
                      ·
                        rfl

theorem cell23_1082791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_1082791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1082791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1082791 prefixEnd_1082791 := by exact prefixLift 1082791
  have htrace : WordTrace (prefixWord ++ tailWord_1082791) baseStart_1082791 baseEnd_1082791 := by
    simpa [prefixWord, tailWord_1082791, baseEnd_1082791] using wordTrace_append hprefix tailTrace_1082791
  have hstable : (prefixWord ++ tailWord_1082791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082791).length < 2 ^ (prefixWord ++ tailWord_1082791).sum := by decide
  have hdescent : baseEnd_1082791 < baseStart_1082791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082807 : List Nat := [1, 1, 3, 1, 3, 2, 1, 4, 1, 6]
def baseStart_1082807 : Nat := 118140960795 + 1082807 * 2 ^ 59
def prefixEnd_1082807 : Nat := 4983230072969 + 3 ^ 40 * 1082807 * 2
def baseEnd_1082807 : Nat := 185333482351016748777589

theorem tailTrace_1082807 : CollatzResearch.WordTrace tailWord_1082807 prefixEnd_1082807 185333482351016748777589 := by
  unfold tailWord_1082807
  simp only [CollatzResearch.WordTrace]
  refine ⟨39493215788182642557782675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26328810525455095038521783 39493215788182642557782675)
  ·
    refine ⟨59239823682273963836674013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39493215788182642557782675 59239823682273963836674013)
    ·
      refine ⟨22214933880852736438752755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59239823682273963836674013 22214933880852736438752755)
      ·
        refine ⟨33322400821279104658129133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22214933880852736438752755 33322400821279104658129133)
        ·
          refine ⟨12495900307979664246798425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33322400821279104658129133 12495900307979664246798425)
          ·
            refine ⟨9371925230984748185098819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12495900307979664246798425 9371925230984748185098819)
            ·
              refine ⟨14057887846477122277648229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9371925230984748185098819 14057887846477122277648229)
              ·
                refine ⟨2635853971214460427059043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14057887846477122277648229 2635853971214460427059043)
                ·
                  refine ⟨3953780956821690640588565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2635853971214460427059043 3953780956821690640588565)
                  ·
                    refine ⟨185333482351016748777589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3953780956821690640588565 185333482351016748777589)
                    ·
                      rfl

theorem cell23_1082807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 4, 1, 6].length) (baseStart_1082807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1082807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1082807 prefixEnd_1082807 := by exact prefixLift 1082807
  have htrace : WordTrace (prefixWord ++ tailWord_1082807) baseStart_1082807 baseEnd_1082807 := by
    simpa [prefixWord, tailWord_1082807, baseEnd_1082807] using wordTrace_append hprefix tailTrace_1082807
  have hstable : (prefixWord ++ tailWord_1082807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082807).length < 2 ^ (prefixWord ++ tailWord_1082807).sum := by decide
  have hdescent : baseEnd_1082807 < baseStart_1082807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082824 : List Nat := [2, 1, 3, 1, 3, 1, 3, 1, 4, 4]
def baseStart_1082824 : Nat := 118140960795 + 1082824 * 2 ^ 59
def prefixEnd_1082824 : Nat := 4983230072969 + 3 ^ 40 * 1082824 * 2
def baseEnd_1082824 : Nat := 185336392074725559940063

theorem tailTrace_1082824 : CollatzResearch.WordTrace tailWord_1082824 prefixEnd_1082824 185336392074725559940063 := by
  unfold tailWord_1082824
  simp only [CollatzResearch.WordTrace]
  refine ⟨19746917914560527230575763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26329223886080702974101017 19746917914560527230575763)
  ·
    refine ⟨29620376871840790845863645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19746917914560527230575763 29620376871840790845863645)
    ·
      refine ⟨11107641326940296567198867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29620376871840790845863645 11107641326940296567198867)
      ·
        refine ⟨16661461990410444850798301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11107641326940296567198867 16661461990410444850798301)
        ·
          refine ⟨6248048246403916819049363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16661461990410444850798301 6248048246403916819049363)
          ·
            refine ⟨9372072369605875228574045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6248048246403916819049363 9372072369605875228574045)
            ·
              refine ⟨3514527138602203210715267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9372072369605875228574045 3514527138602203210715267)
              ·
                refine ⟨5271790707903304816072901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3514527138602203210715267 5271790707903304816072901)
                ·
                  refine ⟨988460757731869653013669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5271790707903304816072901 988460757731869653013669)
                  ·
                    refine ⟨185336392074725559940063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 988460757731869653013669 185336392074725559940063)
                    ·
                      rfl

theorem cell23_1082824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 1, 4, 4].length) (baseStart_1082824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1082824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1082824 prefixEnd_1082824 := by exact prefixLift 1082824
  have htrace : WordTrace (prefixWord ++ tailWord_1082824) baseStart_1082824 baseEnd_1082824 := by
    simpa [prefixWord, tailWord_1082824, baseEnd_1082824] using wordTrace_append hprefix tailTrace_1082824
  have hstable : (prefixWord ++ tailWord_1082824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082824).length < 2 ^ (prefixWord ++ tailWord_1082824).sum := by decide
  have hdescent : baseEnd_1082824 < baseStart_1082824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082827 : List Nat := [1, 1, 1, 1, 3, 3, 2, 2, 3, 2, 4]
def baseStart_1082827 : Nat := 118140960795 + 1082827 * 2 ^ 59
def prefixEnd_1082827 : Nat := 4983230072969 + 3 ^ 40 * 1082827 * 2
def baseEnd_1082827 : Nat := 556010716666140168082675

theorem tailTrace_1082827 : CollatzResearch.WordTrace tailWord_1082827 prefixEnd_1082827 556010716666140168082675 := by
  unfold tailWord_1082827
  simp only [CollatzResearch.WordTrace]
  refine ⟨39493945248110185973510735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26329296832073457315673823 39493945248110185973510735)
  ·
    refine ⟨59240917872165278960266103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39493945248110185973510735 59240917872165278960266103)
    ·
      refine ⟨88861376808247918440399155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59240917872165278960266103 88861376808247918440399155)
      ·
        refine ⟨133292065212371877660598733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88861376808247918440399155 133292065212371877660598733)
        ·
          refine ⟨49984524454639454122724525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 133292065212371877660598733 49984524454639454122724525)
          ·
            refine ⟨18744196670489795296021697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49984524454639454122724525 18744196670489795296021697)
            ·
              refine ⟨14058147502867346472016273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18744196670489795296021697 14058147502867346472016273)
              ·
                refine ⟨10543610627150509854012205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14058147502867346472016273 10543610627150509854012205)
                ·
                  refine ⟨3953853985181441195254577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10543610627150509854012205 3953853985181441195254577)
                  ·
                    refine ⟨2965390488886080896440933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3953853985181441195254577 2965390488886080896440933)
                    ·
                      refine ⟨556010716666140168082675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2965390488886080896440933 556010716666140168082675)
                      ·
                        rfl

theorem cell23_1082827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 3, 2, 4].length) (baseStart_1082827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1082827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1082827 prefixEnd_1082827 := by exact prefixLift 1082827
  have htrace : WordTrace (prefixWord ++ tailWord_1082827) baseStart_1082827 baseEnd_1082827 := by
    simpa [prefixWord, tailWord_1082827, baseEnd_1082827] using wordTrace_append hprefix tailTrace_1082827
  have hstable : (prefixWord ++ tailWord_1082827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082827).length < 2 ^ (prefixWord ++ tailWord_1082827).sum := by decide
  have hdescent : baseEnd_1082827 < baseStart_1082827 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082831 : List Nat := [1, 1, 2, 1, 1, 4, 3, 3, 3, 2, 2]
def baseStart_1082831 : Nat := 118140960795 + 1082831 * 2 ^ 59
def prefixEnd_1082831 : Nat := 4983230072969 + 3 ^ 40 * 1082831 * 2
def baseEnd_1082831 : Nat := 556012770588758152432657

theorem tailTrace_1082831 : CollatzResearch.WordTrace tailWord_1082831 prefixEnd_1082831 556012770588758152432657 := by
  unfold tailWord_1082831
  simp only [CollatzResearch.WordTrace]
  refine ⟨39494091140095694656656347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26329394093397129771104231 39494091140095694656656347)
  ·
    refine ⟨59241136710143541984984521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39494091140095694656656347 59241136710143541984984521)
    ·
      refine ⟨44430852532607656488738391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59241136710143541984984521 44430852532607656488738391)
      ·
        refine ⟨66646278798911484733107587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44430852532607656488738391 66646278798911484733107587)
        ·
          refine ⟨99969418198367227099661381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66646278798911484733107587 99969418198367227099661381)
          ·
            refine ⟨18744265912193855081186509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 99969418198367227099661381 18744265912193855081186509)
            ·
              refine ⟨7029099717072695655444941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18744265912193855081186509 7029099717072695655444941)
              ·
                refine ⟨2635912393902260870791853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7029099717072695655444941 2635912393902260870791853)
                ·
                  refine ⟨988467147713347826546945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2635912393902260870791853 988467147713347826546945)
                  ·
                    refine ⟨741350360785010869910209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 988467147713347826546945 741350360785010869910209)
                    ·
                      refine ⟨556012770588758152432657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 741350360785010869910209 556012770588758152432657)
                      ·
                        rfl

theorem cell23_1082831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 3, 3, 2, 2].length) (baseStart_1082831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1082831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1082831 prefixEnd_1082831 := by exact prefixLift 1082831
  have htrace : WordTrace (prefixWord ++ tailWord_1082831) baseStart_1082831 baseEnd_1082831 := by
    simpa [prefixWord, tailWord_1082831, baseEnd_1082831] using wordTrace_append hprefix tailTrace_1082831
  have hstable : (prefixWord ++ tailWord_1082831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082831).length < 2 ^ (prefixWord ++ tailWord_1082831).sum := by decide
  have hdescent : baseEnd_1082831 < baseStart_1082831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082837 : List Nat := [1, 3, 2, 3, 1, 1, 2, 10]
def baseStart_1082837 : Nat := 118140960795 + 1082837 * 2 ^ 59
def prefixEnd_1082837 : Nat := 4983230072969 + 3 ^ 40 * 1082837 * 2
def baseEnd_1082837 : Nat := 20593179684173523294727

theorem tailTrace_1082837 : CollatzResearch.WordTrace tailWord_1082837 prefixEnd_1082837 20593179684173523294727 := by
  unfold tailWord_1082837
  simp only [CollatzResearch.WordTrace]
  refine ⟨39494309978073957681374765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26329539985382638454249843 39494309978073957681374765)
  ·
    refine ⟨14810366241777734130515537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39494309978073957681374765 14810366241777734130515537)
    ·
      refine ⟨11107774681333300597886653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14810366241777734130515537 11107774681333300597886653)
      ·
        refine ⟨4165415505499987724207495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11107774681333300597886653 4165415505499987724207495)
        ·
          refine ⟨6248123258249981586311243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4165415505499987724207495 6248123258249981586311243)
          ·
            refine ⟨9372184887374972379466865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6248123258249981586311243 9372184887374972379466865)
            ·
              refine ⟨7029138665531229284600149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9372184887374972379466865 7029138665531229284600149)
              ·
                refine ⟨20593179684173523294727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 7029138665531229284600149 20593179684173523294727)
                ·
                  rfl

theorem cell23_1082837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 10].length) (baseStart_1082837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1082837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1082837 prefixEnd_1082837 := by exact prefixLift 1082837
  have htrace : WordTrace (prefixWord ++ tailWord_1082837) baseStart_1082837 baseEnd_1082837 := by
    simpa [prefixWord, tailWord_1082837, baseEnd_1082837] using wordTrace_append hprefix tailTrace_1082837
  have hstable : (prefixWord ++ tailWord_1082837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082837).length < 2 ^ (prefixWord ++ tailWord_1082837).sum := by decide
  have hdescent : baseEnd_1082837 < baseStart_1082837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082851 : List Nat := [1, 1, 1, 6, 2, 1, 1, 4, 1, 2, 3]
def baseStart_1082851 : Nat := 118140960795 + 1082851 * 2 ^ 59
def prefixEnd_1082851 : Nat := 4983230072969 + 3 ^ 40 * 1082851 * 2
def baseEnd_1082851 : Nat := 556023040201848074182565

theorem tailTrace_1082851 : CollatzResearch.WordTrace tailWord_1082851 prefixEnd_1082851 556023040201848074182565 := by
  unfold tailWord_1082851
  simp only [CollatzResearch.WordTrace]
  refine ⟨39494820600023238072384407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26329880400015492048256271 39494820600023238072384407)
  ·
    refine ⟨59242230900034857108576611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39494820600023238072384407 59242230900034857108576611)
    ·
      refine ⟨88863346350052285662864917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59242230900034857108576611 88863346350052285662864917)
      ·
        refine ⟨4165469360158700890446793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 88863346350052285662864917 4165469360158700890446793)
        ·
          refine ⟨3124102020119025667835095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4165469360158700890446793 3124102020119025667835095)
          ·
            refine ⟨4686153030178538501752643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3124102020119025667835095 4686153030178538501752643)
            ·
              refine ⟨7029229545267807752628965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4686153030178538501752643 7029229545267807752628965)
              ·
                refine ⟨1317980539737713953617931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7029229545267807752628965 1317980539737713953617931)
                ·
                  refine ⟨1976970809606570930426897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1317980539737713953617931 1976970809606570930426897)
                  ·
                    refine ⟨1482728107204928197820173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1976970809606570930426897 1482728107204928197820173)
                    ·
                      refine ⟨556023040201848074182565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1482728107204928197820173 556023040201848074182565)
                      ·
                        rfl

theorem cell23_1082851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_1082851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1082851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1082851 prefixEnd_1082851 := by exact prefixLift 1082851
  have htrace : WordTrace (prefixWord ++ tailWord_1082851) baseStart_1082851 baseEnd_1082851 := by
    simpa [prefixWord, tailWord_1082851, baseEnd_1082851] using wordTrace_append hprefix tailTrace_1082851
  have hstable : (prefixWord ++ tailWord_1082851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082851).length < 2 ^ (prefixWord ++ tailWord_1082851).sum := by decide
  have hdescent : baseEnd_1082851 < baseStart_1082851 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082865 : List Nat := [1, 2, 2, 2, 3, 2, 3, 3, 1, 2, 2]
def baseStart_1082865 : Nat := 118140960795 + 1082865 * 2 ^ 59
def prefixEnd_1082865 : Nat := 4983230072969 + 3 ^ 40 * 1082865 * 2
def baseEnd_1082865 : Nat := 556030228931011019407501

theorem tailTrace_1082865 : CollatzResearch.WordTrace tailWord_1082865 prefixEnd_1082865 556030228931011019407501 := by
  unfold tailWord_1082865
  simp only [CollatzResearch.WordTrace]
  refine ⟨39495331221972518463394049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26330220814648345642262699 39495331221972518463394049)
  ·
    refine ⟨29621498416479388847545537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39495331221972518463394049 29621498416479388847545537)
    ·
      refine ⟨22216123812359541635659153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29621498416479388847545537 22216123812359541635659153)
      ·
        refine ⟨16662092859269656226744365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22216123812359541635659153 16662092859269656226744365)
        ·
          refine ⟨6248284822226121085029137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16662092859269656226744365 6248284822226121085029137)
          ·
            refine ⟨4686213616669590813771853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6248284822226121085029137 4686213616669590813771853)
            ·
              refine ⟨1757330106251096555164445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4686213616669590813771853 1757330106251096555164445)
              ·
                refine ⟨658998789844161208186667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1757330106251096555164445 658998789844161208186667)
                ·
                  refine ⟨988498184766241812280001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 658998789844161208186667 988498184766241812280001)
                  ·
                    refine ⟨741373638574681359210001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 988498184766241812280001 741373638574681359210001)
                    ·
                      refine ⟨556030228931011019407501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 741373638574681359210001 556030228931011019407501)
                      ·
                        rfl

theorem cell23_1082865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 3, 1, 2, 2].length) (baseStart_1082865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1082865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1082865 prefixEnd_1082865 := by exact prefixLift 1082865
  have htrace : WordTrace (prefixWord ++ tailWord_1082865) baseStart_1082865 baseEnd_1082865 := by
    simpa [prefixWord, tailWord_1082865, baseEnd_1082865] using wordTrace_append hprefix tailTrace_1082865
  have hstable : (prefixWord ++ tailWord_1082865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082865).length < 2 ^ (prefixWord ++ tailWord_1082865).sum := by decide
  have hdescent : baseEnd_1082865 < baseStart_1082865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082882 : List Nat := [3, 4, 1, 2, 1, 3, 1, 1, 3, 2, 2]
def baseStart_1082882 : Nat := 118140960795 + 1082882 * 2 ^ 59
def prefixEnd_1082882 : Nat := 4983230072969 + 3 ^ 40 * 1082882 * 2
def baseEnd_1082882 : Nat := 556038958102137452894923

theorem tailTrace_1082882 : CollatzResearch.WordTrace tailWord_1082882 prefixEnd_1082882 556038958102137452894923 := by
  unfold tailWord_1082882
  simp only [CollatzResearch.WordTrace]
  refine ⟨9873987815727732591690725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26330634175273953577841933 9873987815727732591690725)
  ·
    refine ⟨1851372715448949860942011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9873987815727732591690725 1851372715448949860942011)
    ·
      refine ⟨2777059073173424791413017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1851372715448949860942011 2777059073173424791413017)
      ·
        refine ⟨2082794304880068593559763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2777059073173424791413017 2082794304880068593559763)
        ·
          refine ⟨3124191457320102890339645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2082794304880068593559763 3124191457320102890339645)
          ·
            refine ⟨1171571796495038583877367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3124191457320102890339645 1171571796495038583877367)
            ·
              refine ⟨1757357694742557875816051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1171571796495038583877367 1757357694742557875816051)
              ·
                refine ⟨2636036542113836813724077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1757357694742557875816051 2636036542113836813724077)
                ·
                  refine ⟨988513703292688805146529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2636036542113836813724077 988513703292688805146529)
                  ·
                    refine ⟨741385277469516603859897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 988513703292688805146529 741385277469516603859897)
                    ·
                      refine ⟨556038958102137452894923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 741385277469516603859897 556038958102137452894923)
                      ·
                        rfl

theorem cell23_1082882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_1082882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1082882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1082882 prefixEnd_1082882 := by exact prefixLift 1082882
  have htrace : WordTrace (prefixWord ++ tailWord_1082882) baseStart_1082882 baseEnd_1082882 := by
    simpa [prefixWord, tailWord_1082882, baseEnd_1082882] using wordTrace_append hprefix tailTrace_1082882
  have hstable : (prefixWord ++ tailWord_1082882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082882).length < 2 ^ (prefixWord ++ tailWord_1082882).sum := by decide
  have hdescent : baseEnd_1082882 < baseStart_1082882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082897 : List Nat := [1, 2, 2, 1, 1, 2, 4, 1, 1, 8]
def baseStart_1082897 : Nat := 118140960795 + 1082897 * 2 ^ 59
def prefixEnd_1082897 : Nat := 4983230072969 + 3 ^ 40 * 1082897 * 2
def baseEnd_1082897 : Nat := 185348886770651631402451

theorem tailTrace_1082897 : CollatzResearch.WordTrace tailWord_1082897 prefixEnd_1082897 185348886770651631402451 := by
  unfold tailWord_1082897
  simp only [CollatzResearch.WordTrace]
  refine ⟨39496498357856587928558945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26330998905237725285705963 39496498357856587928558945)
  ·
    refine ⟨29622373768392440946419209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39496498357856587928558945 29622373768392440946419209)
    ·
      refine ⟨22216780326294330709814407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29622373768392440946419209 22216780326294330709814407)
      ·
        refine ⟨33325170489441496064721611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22216780326294330709814407 33325170489441496064721611)
        ·
          refine ⟨49987755734162244097082417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33325170489441496064721611 49987755734162244097082417)
          ·
            refine ⟨37490816800621683072811813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49987755734162244097082417 37490816800621683072811813)
            ·
              refine ⟨7029528150116565576152215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37490816800621683072811813 7029528150116565576152215)
              ·
                refine ⟨10544292225174848364228323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7029528150116565576152215 10544292225174848364228323)
                ·
                  refine ⟨15816438337762272546342485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10544292225174848364228323 15816438337762272546342485)
                  ·
                    refine ⟨185348886770651631402451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 15816438337762272546342485 185348886770651631402451)
                    ·
                      rfl

theorem cell23_1082897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 8].length) (baseStart_1082897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1082897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1082897 prefixEnd_1082897 := by exact prefixLift 1082897
  have htrace : WordTrace (prefixWord ++ tailWord_1082897) baseStart_1082897 baseEnd_1082897 := by
    simpa [prefixWord, tailWord_1082897, baseEnd_1082897] using wordTrace_append hprefix tailTrace_1082897
  have hstable : (prefixWord ++ tailWord_1082897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082897).length < 2 ^ (prefixWord ++ tailWord_1082897).sum := by decide
  have hdescent : baseEnd_1082897 < baseStart_1082897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082947 : List Nat := [1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 8]
def baseStart_1082947 : Nat := 118140960795 + 1082947 * 2 ^ 59
def prefixEnd_1082947 : Nat := 4983230072969 + 3 ^ 40 * 1082947 * 2
def baseEnd_1082947 : Nat := 556072334344679698582123

theorem tailTrace_1082947 : CollatzResearch.WordTrace tailWord_1082947 prefixEnd_1082947 556072334344679698582123 := by
  unfold tailWord_1082947
  simp only [CollatzResearch.WordTrace]
  refine ⟨39498322007675446467879095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26332214671783630978586063 39498322007675446467879095)
  ·
    refine ⟨59247483011513169701818643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39498322007675446467879095 59247483011513169701818643)
    ·
      refine ⟨88871224517269754552727965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59247483011513169701818643 88871224517269754552727965)
      ·
        refine ⟨33326709193976157957272987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88871224517269754552727965 33326709193976157957272987)
        ·
          refine ⟨49990063790964236935909481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33326709193976157957272987 49990063790964236935909481)
          ·
            refine ⟨37492547843223177701932111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49990063790964236935909481 37492547843223177701932111)
            ·
              refine ⟨56238821764834766552898167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37492547843223177701932111 56238821764834766552898167)
              ·
                refine ⟨84358232647252149829347251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56238821764834766552898167 84358232647252149829347251)
                ·
                  refine ⟨126537348970878224744020877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84358232647252149829347251 126537348970878224744020877)
                  ·
                    refine ⟨47451505864079334279007829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 126537348970878224744020877 47451505864079334279007829)
                    ·
                      refine ⟨556072334344679698582123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 47451505864079334279007829 556072334344679698582123)
                      ·
                        rfl

theorem cell23_1082947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 8].length) (baseStart_1082947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1082947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1082947 prefixEnd_1082947 := by exact prefixLift 1082947
  have htrace : WordTrace (prefixWord ++ tailWord_1082947) baseStart_1082947 baseEnd_1082947 := by
    simpa [prefixWord, tailWord_1082947, baseEnd_1082947] using wordTrace_append hprefix tailTrace_1082947
  have hstable : (prefixWord ++ tailWord_1082947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082947).length < 2 ^ (prefixWord ++ tailWord_1082947).sum := by decide
  have hdescent : baseEnd_1082947 < baseStart_1082947 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082951 : List Nat := [1, 1, 4, 1, 5, 1, 1, 1, 2, 2, 4]
def baseStart_1082951 : Nat := 118140960795 + 1082951 * 2 ^ 59
def prefixEnd_1082951 : Nat := 4983230072969 + 3 ^ 40 * 1082951 * 2
def baseEnd_1082951 : Nat := 556074388267297682932105

theorem tailTrace_1082951 : CollatzResearch.WordTrace tailWord_1082951 prefixEnd_1082951 556074388267297682932105 := by
  unfold tailWord_1082951
  simp only [CollatzResearch.WordTrace]
  refine ⟨39498467899660955151024707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26332311933107303434016471 39498467899660955151024707)
  ·
    refine ⟨59247701849491432726537061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39498467899660955151024707 59247701849491432726537061)
    ·
      refine ⟨11108944096779643636225699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59247701849491432726537061 11108944096779643636225699)
      ·
        refine ⟨16663416145169465454338549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11108944096779643636225699 16663416145169465454338549)
        ·
          refine ⟨1562195263609637386344239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16663416145169465454338549 1562195263609637386344239)
          ·
            refine ⟨2343292895414456079516359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1562195263609637386344239 2343292895414456079516359)
            ·
              refine ⟨3514939343121684119274539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2343292895414456079516359 3514939343121684119274539)
              ·
                refine ⟨5272409014682526178911809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3514939343121684119274539 5272409014682526178911809)
                ·
                  refine ⟨3954306761011894634183857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5272409014682526178911809 3954306761011894634183857)
                  ·
                    refine ⟨2965730070758920975637893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3954306761011894634183857 2965730070758920975637893)
                    ·
                      refine ⟨556074388267297682932105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2965730070758920975637893 556074388267297682932105)
                      ·
                        rfl

theorem cell23_1082951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 1, 2, 2, 4].length) (baseStart_1082951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1082951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1082951 prefixEnd_1082951 := by exact prefixLift 1082951
  have htrace : WordTrace (prefixWord ++ tailWord_1082951) baseStart_1082951 baseEnd_1082951 := by
    simpa [prefixWord, tailWord_1082951, baseEnd_1082951] using wordTrace_append hprefix tailTrace_1082951
  have hstable : (prefixWord ++ tailWord_1082951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082951).length < 2 ^ (prefixWord ++ tailWord_1082951).sum := by decide
  have hdescent : baseEnd_1082951 < baseStart_1082951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082989 : List Nat := [1, 5, 1, 1, 5, 1, 1, 2, 2, 2, 2]
def baseStart_1082989 : Nat := 118140960795 + 1082989 * 2 ^ 59
def prefixEnd_1082989 : Nat := 4983230072969 + 3 ^ 40 * 1082989 * 2
def baseEnd_1082989 : Nat := 556093900532168534256931

theorem tailTrace_1082989 : CollatzResearch.WordTrace tailWord_1082989 prefixEnd_1082989 556093900532168534256931 := by
  unfold tailWord_1082989
  simp only [CollatzResearch.WordTrace]
  refine ⟨39499853873523287640908021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26333235915682191760605347 39499853873523287640908021)
  ·
    refine ⟨3703111300642808216335127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39499853873523287640908021 3703111300642808216335127)
    ·
      refine ⟨5554666950964212324502691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3703111300642808216335127 5554666950964212324502691)
      ·
        refine ⟨8332000426446318486754037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5554666950964212324502691 8332000426446318486754037)
        ·
          refine ⟨781125039979342358133191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8332000426446318486754037 781125039979342358133191)
          ·
            refine ⟨1171687559969013537199787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 781125039979342358133191 1171687559969013537199787)
            ·
              refine ⟨1757531339953520305799681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1171687559969013537199787 1757531339953520305799681)
              ·
                refine ⟨1318148504965140229349761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1757531339953520305799681 1318148504965140229349761)
                ·
                  refine ⟨988611378723855172012321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1318148504965140229349761 988611378723855172012321)
                  ·
                    refine ⟨741458534042891379009241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 988611378723855172012321 741458534042891379009241)
                    ·
                      refine ⟨556093900532168534256931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 741458534042891379009241 556093900532168534256931)
                      ·
                        rfl

theorem cell23_1082989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 2, 2, 2, 2].length) (baseStart_1082989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1082989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1082989 prefixEnd_1082989 := by exact prefixLift 1082989
  have htrace : WordTrace (prefixWord ++ tailWord_1082989) baseStart_1082989 baseEnd_1082989 := by
    simpa [prefixWord, tailWord_1082989, baseEnd_1082989] using wordTrace_append hprefix tailTrace_1082989
  have hstable : (prefixWord ++ tailWord_1082989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082989).length < 2 ^ (prefixWord ++ tailWord_1082989).sum := by decide
  have hdescent : baseEnd_1082989 < baseStart_1082989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083031 : List Nat := [1, 1, 3, 3, 2, 2, 2, 1, 1, 4, 3]
def baseStart_1083031 : Nat := 118140960795 + 1083031 * 2 ^ 59
def prefixEnd_1083031 : Nat := 4983230072969 + 3 ^ 40 * 1083031 * 2
def baseEnd_1083031 : Nat := 556115466719657369931737

theorem tailTrace_1083031 : CollatzResearch.WordTrace tailWord_1083031 prefixEnd_1083031 556115466719657369931737 := by
  unfold tailWord_1083031
  simp only [CollatzResearch.WordTrace]
  refine ⟨39501385739371128813936947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26334257159580752542624631 39501385739371128813936947)
  ·
    refine ⟨59252078609056693220905421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39501385739371128813936947 59252078609056693220905421)
    ·
      refine ⟨22219529478396259957839533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59252078609056693220905421 22219529478396259957839533)
      ·
        refine ⟨8332323554398597484189825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22219529478396259957839533 8332323554398597484189825)
        ·
          refine ⟨6249242665798948113142369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8332323554398597484189825 6249242665798948113142369)
          ·
            refine ⟨4686931999349211084856777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6249242665798948113142369 4686931999349211084856777)
            ·
              refine ⟨3515198999511908313642583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4686931999349211084856777 3515198999511908313642583)
              ·
                refine ⟨5272798499267862470463875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3515198999511908313642583 5272798499267862470463875)
                ·
                  refine ⟨7909197748901793705695813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5272798499267862470463875 7909197748901793705695813)
                  ·
                    refine ⟨1482974577919086319817965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7909197748901793705695813 1482974577919086319817965)
                    ·
                      refine ⟨556115466719657369931737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1482974577919086319817965 556115466719657369931737)
                      ·
                        rfl

theorem cell23_1083031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 1, 1, 4, 3].length) (baseStart_1083031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1083031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1083031 prefixEnd_1083031 := by exact prefixLift 1083031
  have htrace : WordTrace (prefixWord ++ tailWord_1083031) baseStart_1083031 baseEnd_1083031 := by
    simpa [prefixWord, tailWord_1083031, baseEnd_1083031] using wordTrace_append hprefix tailTrace_1083031
  have hstable : (prefixWord ++ tailWord_1083031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083031).length < 2 ^ (prefixWord ++ tailWord_1083031).sum := by decide
  have hdescent : baseEnd_1083031 < baseStart_1083031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083055 : List Nat := [1, 1, 2, 1, 2, 4, 5, 2, 1, 4]
def baseStart_1083055 : Nat := 118140960795 + 1083055 * 2 ^ 59
def prefixEnd_1083055 : Nat := 4983230072969 + 3 ^ 40 * 1083055 * 2
def baseEnd_1083055 : Nat := 185375930085121758677209

theorem tailTrace_1083055 : CollatzResearch.WordTrace tailWord_1083055 prefixEnd_1083055 185375930085121758677209 := by
  unfold tailWord_1083055
  simp only [CollatzResearch.WordTrace]
  refine ⟨39502261091284180912810619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26334840727522787275207079 39502261091284180912810619)
  ·
    refine ⟨59253391636926271369215929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39502261091284180912810619 59253391636926271369215929)
    ·
      refine ⟨44440043727694703526911947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59253391636926271369215929 44440043727694703526911947)
      ·
        refine ⟨66660065591542055290367921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44440043727694703526911947 66660065591542055290367921)
        ·
          refine ⟨49995049193656541467775941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66660065591542055290367921 49995049193656541467775941)
          ·
            refine ⟨9374071723810601525207989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49995049193656541467775941 9374071723810601525207989)
            ·
              refine ⟨878819224107243892988249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9374071723810601525207989 878819224107243892988249)
              ·
                refine ⟨659114418080432919741187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 878819224107243892988249 659114418080432919741187)
                ·
                  refine ⟨988671627120649379611781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 659114418080432919741187 988671627120649379611781)
                  ·
                    refine ⟨185375930085121758677209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 988671627120649379611781 185375930085121758677209)
                    ·
                      rfl

theorem cell23_1083055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 5, 2, 1, 4].length) (baseStart_1083055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1083055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1083055 prefixEnd_1083055 := by exact prefixLift 1083055
  have htrace : WordTrace (prefixWord ++ tailWord_1083055) baseStart_1083055 baseEnd_1083055 := by
    simpa [prefixWord, tailWord_1083055, baseEnd_1083055] using wordTrace_append hprefix tailTrace_1083055
  have hstable : (prefixWord ++ tailWord_1083055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083055).length < 2 ^ (prefixWord ++ tailWord_1083055).sum := by decide
  have hdescent : baseEnd_1083055 < baseStart_1083055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083068 : List Nat := [2, 2, 2, 3, 1, 2, 4, 1, 6]
def baseStart_1083068 : Nat := 118140960795 + 1083068 * 2 ^ 59
def prefixEnd_1083068 : Nat := 4983230072969 + 3 ^ 40 * 1083068 * 2
def baseEnd_1083068 : Nat := 61792718389319302796563

theorem tailTrace_1083068 : CollatzResearch.WordTrace tailWord_1083068 prefixEnd_1083068 61792718389319302796563 := by
  unfold tailWord_1083068
  simp only [CollatzResearch.WordTrace]
  refine ⟨19751367620118542066516929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26335156826824722755355905 19751367620118542066516929)
  ·
    refine ⟨14813525715088906549887697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19751367620118542066516929 14813525715088906549887697)
    ·
      refine ⟨11110144286316679912415773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14813525715088906549887697 11110144286316679912415773)
      ·
        refine ⟨4166304107368754967155915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11110144286316679912415773 4166304107368754967155915)
        ·
          refine ⟨6249456161053132450733873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4166304107368754967155915 6249456161053132450733873)
          ·
            refine ⟨4687092120789849338050405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6249456161053132450733873 4687092120789849338050405)
            ·
              refine ⟨878829772648096750884451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4687092120789849338050405 878829772648096750884451)
              ·
                refine ⟨1318244658972145126326677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 878829772648096750884451 1318244658972145126326677)
                ·
                  refine ⟨61792718389319302796563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1318244658972145126326677 61792718389319302796563)
                  ·
                    rfl

theorem cell23_1083068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 4, 1, 6].length) (baseStart_1083068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1083068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1083068 prefixEnd_1083068 := by exact prefixLift 1083068
  have htrace : WordTrace (prefixWord ++ tailWord_1083068) baseStart_1083068 baseEnd_1083068 := by
    simpa [prefixWord, tailWord_1083068, baseEnd_1083068] using wordTrace_append hprefix tailTrace_1083068
  have hstable : (prefixWord ++ tailWord_1083068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083068).length < 2 ^ (prefixWord ++ tailWord_1083068).sum := by decide
  have hdescent : baseEnd_1083068 < baseStart_1083068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083095 : List Nat := [1, 1, 3, 2, 1, 3, 2, 5, 1, 1, 3]
def baseStart_1083095 : Nat := 118140960795 + 1083095 * 2 ^ 59
def prefixEnd_1083095 : Nat := 4983230072969 + 3 ^ 40 * 1083095 * 2
def baseEnd_1083095 : Nat := 556148329481545119531443

theorem tailTrace_1083095 : CollatzResearch.WordTrace tailWord_1083095 prefixEnd_1083095 556148329481545119531443 := by
  unfold tailWord_1083095
  simp only [CollatzResearch.WordTrace]
  refine ⟨39503720011139267744266739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26335813340759511829511159 39503720011139267744266739)
  ·
    refine ⟨59255580016708901616400109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39503720011139267744266739 59255580016708901616400109)
    ·
      refine ⟨22220842506265838106150041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59255580016708901616400109 22220842506265838106150041)
      ·
        refine ⟨16665631879699378579612531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22220842506265838106150041 16665631879699378579612531)
        ·
          refine ⟨24998447819549067869418797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16665631879699378579612531 24998447819549067869418797)
          ·
            refine ⟨9374417932330900451032049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24998447819549067869418797 9374417932330900451032049)
            ·
              refine ⟨7030813449248175338274037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9374417932330900451032049 7030813449248175338274037)
              ·
                refine ⟨659138760867016437963191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7030813449248175338274037 659138760867016437963191)
                ·
                  refine ⟨988708141300524656944787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 659138760867016437963191 988708141300524656944787)
                  ·
                    refine ⟨1483062211950786985417181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 988708141300524656944787 1483062211950786985417181)
                    ·
                      refine ⟨556148329481545119531443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1483062211950786985417181 556148329481545119531443)
                      ·
                        rfl

theorem cell23_1083095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 5, 1, 1, 3].length) (baseStart_1083095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1083095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1083095 prefixEnd_1083095 := by exact prefixLift 1083095
  have htrace : WordTrace (prefixWord ++ tailWord_1083095) baseStart_1083095 baseEnd_1083095 := by
    simpa [prefixWord, tailWord_1083095, baseEnd_1083095] using wordTrace_append hprefix tailTrace_1083095
  have hstable : (prefixWord ++ tailWord_1083095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083095).length < 2 ^ (prefixWord ++ tailWord_1083095).sum := by decide
  have hdescent : baseEnd_1083095 < baseStart_1083095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083112 : List Nat := [2, 1, 4, 1, 3, 2, 1, 4, 1, 1, 3]
def baseStart_1083112 : Nat := 118140960795 + 1083112 * 2 ^ 59
def prefixEnd_1083112 : Nat := 4983230072969 + 3 ^ 40 * 1083112 * 2
def baseEnd_1083112 : Nat := 556157058652671553018865

theorem tailTrace_1083112 : CollatzResearch.WordTrace tailWord_1083112 prefixEnd_1083112 556157058652671553018865 := by
  unfold tailWord_1083112
  simp only [CollatzResearch.WordTrace]
  refine ⟨19752170026038839823817795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26336226701385119765090393 19752170026038839823817795)
  ·
    refine ⟨29628255039058259735726693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19752170026038839823817795 29628255039058259735726693)
    ·
      refine ⟨5555297819823423700448755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29628255039058259735726693 5555297819823423700448755)
      ·
        refine ⟨8332946729735135550673133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5555297819823423700448755 8332946729735135550673133)
        ·
          refine ⟨3124855023650675831502425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8332946729735135550673133 3124855023650675831502425)
          ·
            refine ⟨2343641267738006873626819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3124855023650675831502425 2343641267738006873626819)
            ·
              refine ⟨3515461901607010310440229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2343641267738006873626819 3515461901607010310440229)
              ·
                refine ⟨659149106551314433207543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3515461901607010310440229 659149106551314433207543)
                ·
                  refine ⟨988723659826971649811315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 659149106551314433207543 988723659826971649811315)
                  ·
                    refine ⟨1483085489740457474716973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 988723659826971649811315 1483085489740457474716973)
                    ·
                      refine ⟨556157058652671553018865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1483085489740457474716973 556157058652671553018865)
                      ·
                        rfl

theorem cell23_1083112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 4, 1, 1, 3].length) (baseStart_1083112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1083112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1083112 prefixEnd_1083112 := by exact prefixLift 1083112
  have htrace : WordTrace (prefixWord ++ tailWord_1083112) baseStart_1083112 baseEnd_1083112 := by
    simpa [prefixWord, tailWord_1083112, baseEnd_1083112] using wordTrace_append hprefix tailTrace_1083112
  have hstable : (prefixWord ++ tailWord_1083112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083112).length < 2 ^ (prefixWord ++ tailWord_1083112).sum := by decide
  have hdescent : baseEnd_1083112 < baseStart_1083112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083151 : List Nat := [1, 1, 2, 1, 1, 1, 4, 3, 3, 3, 3]
def baseStart_1083151 : Nat := 118140960795 + 1083151 * 2 ^ 59
def prefixEnd_1083151 : Nat := 4983230072969 + 3 ^ 40 * 1083151 * 2
def baseEnd_1083151 : Nat := 556177084398196900431185

theorem tailTrace_1083151 : CollatzResearch.WordTrace tailWord_1083151 prefixEnd_1083151 556177084398196900431185 := by
  unfold tailWord_1083151
  simp only [CollatzResearch.WordTrace]
  refine ⟨39505762498936389308305307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26337174999290926205536871 39505762498936389308305307)
  ·
    refine ⟨59258643748404583962457961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39505762498936389308305307 59258643748404583962457961)
    ·
      refine ⟨44443982811303437971843471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59258643748404583962457961 44443982811303437971843471)
      ·
        refine ⟨66665974216955156957765207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44443982811303437971843471 66665974216955156957765207)
        ·
          refine ⟨99998961325432735436647811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66665974216955156957765207 99998961325432735436647811)
          ·
            refine ⟨149998441988149103154971717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99998961325432735436647811 149998441988149103154971717)
            ·
              refine ⟨28124707872777956841557197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 149998441988149103154971717 28124707872777956841557197)
              ·
                refine ⟨10546765452291733815583949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28124707872777956841557197 10546765452291733815583949)
                ·
                  refine ⟨3955037044609400180843981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10546765452291733815583949 3955037044609400180843981)
                  ·
                    refine ⟨1483138891728525067816493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3955037044609400180843981 1483138891728525067816493)
                    ·
                      refine ⟨556177084398196900431185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1483138891728525067816493 556177084398196900431185)
                      ·
                        rfl

theorem cell23_1083151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 3, 3, 3].length) (baseStart_1083151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1083151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1083151 prefixEnd_1083151 := by exact prefixLift 1083151
  have htrace : WordTrace (prefixWord ++ tailWord_1083151) baseStart_1083151 baseEnd_1083151 := by
    simpa [prefixWord, tailWord_1083151, baseEnd_1083151] using wordTrace_append hprefix tailTrace_1083151
  have hstable : (prefixWord ++ tailWord_1083151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083151).length < 2 ^ (prefixWord ++ tailWord_1083151).sum := by decide
  have hdescent : baseEnd_1083151 < baseStart_1083151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083182 : List Nat := [4, 1, 3, 2, 2, 2, 1, 1, 1, 2, 4]
def baseStart_1083182 : Nat := 118140960795 + 1083182 * 2 ^ 59
def prefixEnd_1083182 : Nat := 4983230072969 + 3 ^ 40 * 1083182 * 2
def baseEnd_1083182 : Nat := 556193002298486279143543

theorem tailTrace_1083182 : CollatzResearch.WordTrace tailWord_1083182 prefixEnd_1083182 556193002298486279143543 := by
  unfold tailWord_1083182
  simp only [CollatzResearch.WordTrace]
  refine ⟨4938361645228010200335475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26337928774549387735122533 4938361645228010200335475)
  ·
    refine ⟨7407542467842015300503213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4938361645228010200335475 7407542467842015300503213)
    ·
      refine ⟨2777828425440755737688705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7407542467842015300503213 2777828425440755737688705)
      ·
        refine ⟨2083371319080566803266529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2777828425440755737688705 2083371319080566803266529)
        ·
          refine ⟨1562528489310425102449897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2083371319080566803266529 1562528489310425102449897)
          ·
            refine ⟨1171896366982818826837423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1562528489310425102449897 1171896366982818826837423)
            ·
              refine ⟨1757844550474228240256135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1171896366982818826837423 1757844550474228240256135)
              ·
                refine ⟨2636766825711342360384203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1757844550474228240256135 2636766825711342360384203)
                ·
                  refine ⟨3955150238567013540576305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2636766825711342360384203 3955150238567013540576305)
                  ·
                    refine ⟨2966362678925260155432229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3955150238567013540576305 2966362678925260155432229)
                    ·
                      refine ⟨556193002298486279143543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2966362678925260155432229 556193002298486279143543)
                      ·
                        rfl

theorem cell23_1083182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_1083182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1083182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1083182 prefixEnd_1083182 := by exact prefixLift 1083182
  have htrace : WordTrace (prefixWord ++ tailWord_1083182) baseStart_1083182 baseEnd_1083182 := by
    simpa [prefixWord, tailWord_1083182, baseEnd_1083182] using wordTrace_append hprefix tailTrace_1083182
  have hstable : (prefixWord ++ tailWord_1083182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083182).length < 2 ^ (prefixWord ++ tailWord_1083182).sum := by decide
  have hdescent : baseEnd_1083182 < baseStart_1083182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083185 : List Nat := [1, 2, 2, 3, 2, 4, 1, 1, 1, 3, 3]
def baseStart_1083185 : Nat := 118140960795 + 1083185 * 2 ^ 59
def prefixEnd_1083185 : Nat := 4983230072969 + 3 ^ 40 * 1083185 * 2
def baseEnd_1083185 : Nat := 556194542740449767406029

theorem tailTrace_1083185 : CollatzResearch.WordTrace tailWord_1083185 prefixEnd_1083185 556194542740449767406029 := by
  unfold tailWord_1083185
  simp only [CollatzResearch.WordTrace]
  refine ⟨39507002580813213115043009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26338001720542142076695339 39507002580813213115043009)
  ·
    refine ⟨29630251935609909836282257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39507002580813213115043009 29630251935609909836282257)
    ·
      refine ⟨22222688951707432377211693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29630251935609909836282257 22222688951707432377211693)
      ·
        refine ⟨8333508356890287141454385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22222688951707432377211693 8333508356890287141454385)
        ·
          refine ⟨6250131267667715356090789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8333508356890287141454385 6250131267667715356090789)
          ·
            refine ⟨1171899612687696629267023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6250131267667715356090789 1171899612687696629267023)
            ·
              refine ⟨1757849419031544943900535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1171899612687696629267023 1757849419031544943900535)
              ·
                refine ⟨2636774128547317415850803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1757849419031544943900535 2636774128547317415850803)
                ·
                  refine ⟨3955161192820976123776205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2636774128547317415850803 3955161192820976123776205)
                  ·
                    refine ⟨1483185447307866046416077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3955161192820976123776205 1483185447307866046416077)
                    ·
                      refine ⟨556194542740449767406029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1483185447307866046416077 556194542740449767406029)
                      ·
                        rfl

theorem cell23_1083185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 1, 1, 3, 3].length) (baseStart_1083185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1083185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1083185 prefixEnd_1083185 := by exact prefixLift 1083185
  have htrace : WordTrace (prefixWord ++ tailWord_1083185) baseStart_1083185 baseEnd_1083185 := by
    simpa [prefixWord, tailWord_1083185, baseEnd_1083185] using wordTrace_append hprefix tailTrace_1083185
  have hstable : (prefixWord ++ tailWord_1083185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083185).length < 2 ^ (prefixWord ++ tailWord_1083185).sum := by decide
  have hdescent : baseEnd_1083185 < baseStart_1083185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083198 : List Nat := [4, 2, 1, 2, 2, 1, 1, 1, 2, 2, 5]
def baseStart_1083198 : Nat := 118140960795 + 1083198 * 2 ^ 59
def prefixEnd_1083198 : Nat := 4983230072969 + 3 ^ 40 * 1083198 * 2
def baseEnd_1083198 : Nat := 556201217988958216543469

theorem tailTrace_1083198 : CollatzResearch.WordTrace tailWord_1083198 prefixEnd_1083198 556201217988958216543469 := by
  unfold tailWord_1083198
  simp only [CollatzResearch.WordTrace]
  refine ⟨4938434591220764541908281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26338317819844077556844165 4938434591220764541908281)
  ·
    refine ⟨3703825943415573406431211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4938434591220764541908281 3703825943415573406431211)
    ·
      refine ⟨5555738915123360109646817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3703825943415573406431211 5555738915123360109646817)
      ·
        refine ⟨4166804186342520082235113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5555738915123360109646817 4166804186342520082235113)
        ·
          refine ⟨3125103139756890061676335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4166804186342520082235113 3125103139756890061676335)
          ·
            refine ⟨4687654709635335092514503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3125103139756890061676335 4687654709635335092514503)
            ·
              refine ⟨7031482064453002638771755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4687654709635335092514503 7031482064453002638771755)
              ·
                refine ⟨10547223096679503958157633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7031482064453002638771755 10547223096679503958157633)
                ·
                  refine ⟨7910417322509627968618225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10547223096679503958157633 7910417322509627968618225)
                  ·
                    refine ⟨5932812991882220976463669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7910417322509627968618225 5932812991882220976463669)
                    ·
                      refine ⟨556201217988958216543469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5932812991882220976463669 556201217988958216543469)
                      ·
                        rfl

theorem cell23_1083198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_1083198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1083198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1083198 prefixEnd_1083198 := by exact prefixLift 1083198
  have htrace : WordTrace (prefixWord ++ tailWord_1083198) baseStart_1083198 baseEnd_1083198 := by
    simpa [prefixWord, tailWord_1083198, baseEnd_1083198] using wordTrace_append hprefix tailTrace_1083198
  have hstable : (prefixWord ++ tailWord_1083198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083198).length < 2 ^ (prefixWord ++ tailWord_1083198).sum := by decide
  have hdescent : baseEnd_1083198 < baseStart_1083198 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083225 : List Nat := [1, 2, 1, 2, 2, 3, 1, 3, 4, 2, 2]
def baseStart_1083225 : Nat := 118140960795 + 1083225 * 2 ^ 59
def prefixEnd_1083225 : Nat := 4983230072969 + 3 ^ 40 * 1083225 * 2
def baseEnd_1083225 : Nat := 556215081966629610905845

theorem tailTrace_1083225 : CollatzResearch.WordTrace tailWord_1083225 prefixEnd_1083225 556215081966629610905845 := by
  unfold tailWord_1083225
  simp only [CollatzResearch.WordTrace]
  refine ⟨39508461500668299946499129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26338974333778866630999419 39508461500668299946499129)
  ·
    refine ⟨29631346125501224959874347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39508461500668299946499129 29631346125501224959874347)
    ·
      refine ⟨44447019188251837439811521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29631346125501224959874347 44447019188251837439811521)
      ·
        refine ⟨33335264391188878079858641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44447019188251837439811521 33335264391188878079858641)
        ·
          refine ⟨25001448293391658559893981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33335264391188878079858641 25001448293391658559893981)
          ·
            refine ⟨9375543110021871959960243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25001448293391658559893981 9375543110021871959960243)
            ·
              refine ⟨14063314665032807939940365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9375543110021871959960243 14063314665032807939940365)
              ·
                refine ⟨5273742999387302977477637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14063314665032807939940365 5273742999387302977477637)
                ·
                  refine ⟨988826812385119308277057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5273742999387302977477637 988826812385119308277057)
                  ·
                    refine ⟨741620109288839481207793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 988826812385119308277057 741620109288839481207793)
                    ·
                      refine ⟨556215081966629610905845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 741620109288839481207793 556215081966629610905845)
                      ·
                        rfl

theorem cell23_1083225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3, 4, 2, 2].length) (baseStart_1083225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1083225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1083225 prefixEnd_1083225 := by exact prefixLift 1083225
  have htrace : WordTrace (prefixWord ++ tailWord_1083225) baseStart_1083225 baseEnd_1083225 := by
    simpa [prefixWord, tailWord_1083225, baseEnd_1083225] using wordTrace_append hprefix tailTrace_1083225
  have hstable : (prefixWord ++ tailWord_1083225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083225).length < 2 ^ (prefixWord ++ tailWord_1083225).sum := by decide
  have hdescent : baseEnd_1083225 < baseStart_1083225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083236 : List Nat := [2, 3, 1, 1, 6, 1, 2, 1, 2, 1, 3]
def baseStart_1083236 : Nat := 118140960795 + 1083236 * 2 ^ 59
def prefixEnd_1083236 : Nat := 4983230072969 + 3 ^ 40 * 1083236 * 2
def baseEnd_1083236 : Nat := 556220730253829067868295

theorem tailTrace_1083236 : CollatzResearch.WordTrace tailWord_1083236 prefixEnd_1083236 556220730253829067868295 := by
  unfold tailWord_1083236
  simp only [CollatzResearch.WordTrace]
  refine ⟨19754431351814224412574781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26339241802418965883433041 19754431351814224412574781)
  ·
    refine ⟨7407911756930334154715543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19754431351814224412574781 7407911756930334154715543)
    ·
      refine ⟨11111867635395501232073315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7407911756930334154715543 11111867635395501232073315)
      ·
        refine ⟨16667801453093251848109973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11111867635395501232073315 16667801453093251848109973)
        ·
          refine ⟨781303193113746180380155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 16667801453093251848109973 781303193113746180380155)
          ·
            refine ⟨1171954789670619270570233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 781303193113746180380155 1171954789670619270570233)
            ·
              refine ⟨878966092252964452927675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1171954789670619270570233 878966092252964452927675)
              ·
                refine ⟨1318449138379446679391513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 878966092252964452927675 1318449138379446679391513)
                ·
                  refine ⟨988836853784585009543635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1318449138379446679391513 988836853784585009543635)
                  ·
                    refine ⟨1483255280676877514315453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 988836853784585009543635 1483255280676877514315453)
                    ·
                      refine ⟨556220730253829067868295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1483255280676877514315453 556220730253829067868295)
                      ·
                        rfl

theorem cell23_1083236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 2, 1, 2, 1, 3].length) (baseStart_1083236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1083236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1083236 prefixEnd_1083236 := by exact prefixLift 1083236
  have htrace : WordTrace (prefixWord ++ tailWord_1083236) baseStart_1083236 baseEnd_1083236 := by
    simpa [prefixWord, tailWord_1083236, baseEnd_1083236] using wordTrace_append hprefix tailTrace_1083236
  have hstable : (prefixWord ++ tailWord_1083236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083236).length < 2 ^ (prefixWord ++ tailWord_1083236).sum := by decide
  have hdescent : baseEnd_1083236 < baseStart_1083236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083282 : List Nat := [3, 2, 3, 2, 1, 2, 1, 4, 5]
def baseStart_1083282 : Nat := 118140960795 + 1083282 * 2 ^ 59
def prefixEnd_1083282 : Nat := 4983230072969 + 3 ^ 40 * 1083282 * 2
def baseEnd_1083282 : Nat := 61804927818215098654787

theorem tailTrace_1083282 : CollatzResearch.WordTrace tailWord_1083282 prefixEnd_1083282 61804927818215098654787 := by
  unfold tailWord_1083282
  simp only [CollatzResearch.WordTrace]
  refine ⟨9877635115365449670331025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26340360307641199120882733 9877635115365449670331025)
  ·
    refine ⟨7408226336524087252748269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9877635115365449670331025 7408226336524087252748269)
    ·
      refine ⟨2778084876196532719780601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7408226336524087252748269 2778084876196532719780601)
      ·
        refine ⟨2083563657147399539835451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2778084876196532719780601 2083563657147399539835451)
        ·
          refine ⟨3125345485721099309753177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2083563657147399539835451 3125345485721099309753177)
          ·
            refine ⟨2344009114290824482314883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3125345485721099309753177 2344009114290824482314883)
            ·
              refine ⟨3516013671436236723472325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2344009114290824482314883 3516013671436236723472325)
              ·
                refine ⟨659252563394294385651061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3516013671436236723472325 659252563394294385651061)
                ·
                  refine ⟨61804927818215098654787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 659252563394294385651061 61804927818215098654787)
                  ·
                    rfl

theorem cell23_1083282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 4, 5].length) (baseStart_1083282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1083282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1083282 prefixEnd_1083282 := by exact prefixLift 1083282
  have htrace : WordTrace (prefixWord ++ tailWord_1083282) baseStart_1083282 baseEnd_1083282 := by
    simpa [prefixWord, tailWord_1083282, baseEnd_1083282] using wordTrace_append hprefix tailTrace_1083282
  have hstable : (prefixWord ++ tailWord_1083282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083282).length < 2 ^ (prefixWord ++ tailWord_1083282).sum := by decide
  have hdescent : baseEnd_1083282 < baseStart_1083282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083342 : List Nat := [4, 1, 1, 1, 2, 2, 1, 6, 1, 4]
def baseStart_1083342 : Nat := 118140960795 + 1083342 * 2 ^ 59
def prefixEnd_1083342 : Nat := 4983230072969 + 3 ^ 40 * 1083342 * 2
def baseEnd_1083342 : Nat := 185425053067735217714269

theorem tailTrace_1083342 : CollatzResearch.WordTrace tailWord_1083342 prefixEnd_1083342 185425053067735217714269 := by
  unfold tailWord_1083342
  simp only [CollatzResearch.WordTrace]
  refine ⟨4939091105155553616063535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26341819227496285952338853 4939091105155553616063535)
  ·
    refine ⟨7408636657733330424095303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4939091105155553616063535 7408636657733330424095303)
    ·
      refine ⟨11112954986599995636142955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7408636657733330424095303 11112954986599995636142955)
      ·
        refine ⟨16669432479899993454214433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11112954986599995636142955 16669432479899993454214433)
        ·
          refine ⟨12502074359924995090660825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16669432479899993454214433 12502074359924995090660825)
          ·
            refine ⟨9376555769943746317995619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12502074359924995090660825 9376555769943746317995619)
            ·
              refine ⟨14064833654915619476993429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9376555769943746317995619 14064833654915619476993429)
              ·
                refine ⟨659289077574169662984067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14064833654915619476993429 659289077574169662984067)
                ·
                  refine ⟨988933616361254494476101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 659289077574169662984067 988933616361254494476101)
                  ·
                    refine ⟨185425053067735217714269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 988933616361254494476101 185425053067735217714269)
                    ·
                      rfl

theorem cell23_1083342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 6, 1, 4].length) (baseStart_1083342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1083342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1083342 prefixEnd_1083342 := by exact prefixLift 1083342
  have htrace : WordTrace (prefixWord ++ tailWord_1083342) baseStart_1083342 baseEnd_1083342 := by
    simpa [prefixWord, tailWord_1083342, baseEnd_1083342] using wordTrace_append hprefix tailTrace_1083342
  have hstable : (prefixWord ++ tailWord_1083342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083342).length < 2 ^ (prefixWord ++ tailWord_1083342).sum := by decide
  have hdescent : baseEnd_1083342 < baseStart_1083342 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083375 : List Nat := [1, 1, 2, 1, 4, 2, 1, 3, 1, 5, 2]
def baseStart_1083375 : Nat := 118140960795 + 1083375 * 2 ^ 59
def prefixEnd_1083375 : Nat := 4983230072969 + 3 ^ 40 * 1083375 * 2
def baseEnd_1083375 : Nat := 556292104064804024030155

theorem tailTrace_1083375 : CollatzResearch.WordTrace tailWord_1083375 prefixEnd_1083375 556292104064804024030155 := by
  unfold tailWord_1083375
  simp only [CollatzResearch.WordTrace]
  refine ⟨39513932450124875564459579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26342621633416583709639719 39513932450124875564459579)
  ·
    refine ⟨59270898675187313346689369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39513932450124875564459579 59270898675187313346689369)
    ·
      refine ⟨44453174006390485010017027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59270898675187313346689369 44453174006390485010017027)
      ·
        refine ⟨66679761009585727515025541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44453174006390485010017027 66679761009585727515025541)
        ·
          refine ⟨12502455189297323909067289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66679761009585727515025541 12502455189297323909067289)
          ·
            refine ⟨9376841391972992931800467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12502455189297323909067289 9376841391972992931800467)
            ·
              refine ⟨14065262087959489397700701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9376841391972992931800467 14065262087959489397700701)
              ·
                refine ⟨5274473282984808524137763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14065262087959489397700701 5274473282984808524137763)
                ·
                  refine ⟨7911709924477212786206645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5274473282984808524137763 7911709924477212786206645)
                  ·
                    refine ⟨741722805419738698706873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7911709924477212786206645 741722805419738698706873)
                    ·
                      refine ⟨556292104064804024030155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 741722805419738698706873 556292104064804024030155)
                      ·
                        rfl

theorem cell23_1083375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 3, 1, 5, 2].length) (baseStart_1083375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1083375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1083375 prefixEnd_1083375 := by exact prefixLift 1083375
  have htrace : WordTrace (prefixWord ++ tailWord_1083375) baseStart_1083375 baseEnd_1083375 := by
    simpa [prefixWord, tailWord_1083375, baseEnd_1083375] using wordTrace_append hprefix tailTrace_1083375
  have hstable : (prefixWord ++ tailWord_1083375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083375).length < 2 ^ (prefixWord ++ tailWord_1083375).sum := by decide
  have hdescent : baseEnd_1083375 < baseStart_1083375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083385 : List Nat := [1, 2, 1, 3, 1, 4, 2, 3, 1, 5]
def baseStart_1083385 : Nat := 118140960795 + 1083385 * 2 ^ 59
def prefixEnd_1083385 : Nat := 4983230072969 + 3 ^ 40 * 1083385 * 2
def baseEnd_1083385 : Nat := 185432412957116328301703

theorem tailTrace_1083385 : CollatzResearch.WordTrace tailWord_1083385 prefixEnd_1083385 185432412957116328301703 := by
  unfold tailWord_1083385
  simp only [CollatzResearch.WordTrace]
  refine ⟨39514297180088647272323609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26342864786725764848215739 39514297180088647272323609)
  ·
    refine ⟨29635722885066485454242707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39514297180088647272323609 29635722885066485454242707)
    ·
      refine ⟨44453584327599728181364061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29635722885066485454242707 44453584327599728181364061)
      ·
        refine ⟨16670094122849898068011523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44453584327599728181364061 16670094122849898068011523)
        ·
          refine ⟨25005141184274847102017285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16670094122849898068011523 25005141184274847102017285)
          ·
            refine ⟨4688463972051533831628241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25005141184274847102017285 4688463972051533831628241)
            ·
              refine ⟨3516347979038650373721181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4688463972051533831628241 3516347979038650373721181)
              ·
                refine ⟨1318630492139493890145443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3516347979038650373721181 1318630492139493890145443)
                ·
                  refine ⟨1977945738209240835218165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1318630492139493890145443 1977945738209240835218165)
                  ·
                    refine ⟨185432412957116328301703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1977945738209240835218165 185432412957116328301703)
                    ·
                      rfl

theorem cell23_1083385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 3, 1, 5].length) (baseStart_1083385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1083385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1083385 prefixEnd_1083385 := by exact prefixLift 1083385
  have htrace : WordTrace (prefixWord ++ tailWord_1083385) baseStart_1083385 baseEnd_1083385 := by
    simpa [prefixWord, tailWord_1083385, baseEnd_1083385] using wordTrace_append hprefix tailTrace_1083385
  have hstable : (prefixWord ++ tailWord_1083385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083385).length < 2 ^ (prefixWord ++ tailWord_1083385).sum := by decide
  have hdescent : baseEnd_1083385 < baseStart_1083385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083399 : List Nat := [1, 1, 4, 3, 1, 4, 1, 1, 3, 1, 3]
def baseStart_1083399 : Nat := 118140960795 + 1083399 * 2 ^ 59
def prefixEnd_1083399 : Nat := 4983230072969 + 3 ^ 40 * 1083399 * 2
def baseEnd_1083399 : Nat := 556304427600511930130045

theorem tailTrace_1083399 : CollatzResearch.WordTrace tailWord_1083399 prefixEnd_1083399 556304427600511930130045 := by
  unfold tailWord_1083399
  simp only [CollatzResearch.WordTrace]
  refine ⟨39514807802037927663333251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26343205201358618442222167 39514807802037927663333251)
  ·
    refine ⟨59272211703056891494999877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39514807802037927663333251 59272211703056891494999877)
    ·
      refine ⟨11113539694323167155312477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59272211703056891494999877 11113539694323167155312477)
      ·
        refine ⟨4167577385371187683242179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11113539694323167155312477 4167577385371187683242179)
        ·
          refine ⟨6251366078056781524863269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4167577385371187683242179 6251366078056781524863269)
          ·
            refine ⟨1172131139635646535911863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6251366078056781524863269 1172131139635646535911863)
            ·
              refine ⟨1758196709453469803867795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1172131139635646535911863 1758196709453469803867795)
              ·
                refine ⟨2637295064180204705801693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1758196709453469803867795 2637295064180204705801693)
                ·
                  refine ⟨988985649067576764675635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2637295064180204705801693 988985649067576764675635)
                  ·
                    refine ⟨1483478473601365147013453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 988985649067576764675635 1483478473601365147013453)
                    ·
                      refine ⟨556304427600511930130045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1483478473601365147013453 556304427600511930130045)
                      ·
                        rfl

theorem cell23_1083399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_1083399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1083399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1083399 prefixEnd_1083399 := by exact prefixLift 1083399
  have htrace : WordTrace (prefixWord ++ tailWord_1083399) baseStart_1083399 baseEnd_1083399 := by
    simpa [prefixWord, tailWord_1083399, baseEnd_1083399] using wordTrace_append hprefix tailTrace_1083399
  have hstable : (prefixWord ++ tailWord_1083399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083399).length < 2 ^ (prefixWord ++ tailWord_1083399).sum := by decide
  have hdescent : baseEnd_1083399 < baseStart_1083399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083442 : List Nat := [3, 2, 1, 1, 2, 5, 1, 1, 1, 1, 5]
def baseStart_1083442 : Nat := 118140960795 + 1083442 * 2 ^ 59
def prefixEnd_1083442 : Nat := 4983230072969 + 3 ^ 40 * 1083442 * 2
def baseEnd_1083442 : Nat := 556326507268655261892347

theorem tailTrace_1083442 : CollatzResearch.WordTrace tailWord_1083442 prefixEnd_1083442 556326507268655261892347 := by
  unfold tailWord_1083442
  simp only [CollatzResearch.WordTrace]
  refine ⟨9879094035220536501787145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26344250760588097338099053 9879094035220536501787145)
  ·
    refine ⟨7409320526415402376340359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9879094035220536501787145 7409320526415402376340359)
    ·
      refine ⟨11113980789623103564510539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7409320526415402376340359 11113980789623103564510539)
      ·
        refine ⟨16670971184434655346765809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11113980789623103564510539 16670971184434655346765809)
        ·
          refine ⟨12503228388325991510074357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16670971184434655346765809 12503228388325991510074357)
          ·
            refine ⟨1172177661405561704069471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12503228388325991510074357 1172177661405561704069471)
            ·
              refine ⟨1758266492108342556104207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1172177661405561704069471 1758266492108342556104207)
              ·
                refine ⟨2637399738162513834156311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1758266492108342556104207 2637399738162513834156311)
                ·
                  refine ⟨3956099607243770751234467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2637399738162513834156311 3956099607243770751234467)
                  ·
                    refine ⟨5934149410865656126851701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3956099607243770751234467 5934149410865656126851701)
                    ·
                      refine ⟨556326507268655261892347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5934149410865656126851701 556326507268655261892347)
                      ·
                        rfl

theorem cell23_1083442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 1, 1, 1, 5].length) (baseStart_1083442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1083442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1083442 prefixEnd_1083442 := by exact prefixLift 1083442
  have htrace : WordTrace (prefixWord ++ tailWord_1083442) baseStart_1083442 baseEnd_1083442 := by
    simpa [prefixWord, tailWord_1083442, baseEnd_1083442] using wordTrace_append hprefix tailTrace_1083442
  have hstable : (prefixWord ++ tailWord_1083442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083442).length < 2 ^ (prefixWord ++ tailWord_1083442).sum := by decide
  have hdescent : baseEnd_1083442 < baseStart_1083442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083449 : List Nat := [1, 2, 1, 5, 3, 1, 2, 2, 2, 4]
def baseStart_1083449 : Nat := 118140960795 + 1083449 * 2 ^ 59
def prefixEnd_1083449 : Nat := 4983230072969 + 3 ^ 40 * 1083449 * 2
def baseEnd_1083449 : Nat := 185443367211078911501605

theorem tailTrace_1083449 : CollatzResearch.WordTrace tailWord_1083449 prefixEnd_1083449 185443367211078911501605 := by
  unfold tailWord_1083449
  simp only [CollatzResearch.WordTrace]
  refine ⟨39516631451856786202653401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26344420967904524135102267 39516631451856786202653401)
  ·
    refine ⟨29637473588892589651990051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39516631451856786202653401 29637473588892589651990051)
    ·
      refine ⟨44456210383338884477985077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29637473588892589651990051 44456210383338884477985077)
      ·
        refine ⟨4167769723438020419811101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 44456210383338884477985077 4167769723438020419811101)
        ·
          refine ⟨1562913646289257657429163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4167769723438020419811101 1562913646289257657429163)
          ·
            refine ⟨2344370469433886486143745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1562913646289257657429163 2344370469433886486143745)
            ·
              refine ⟨1758277852075414864607809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2344370469433886486143745 1758277852075414864607809)
              ·
                refine ⟨1318708389056561148455857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1758277852075414864607809 1318708389056561148455857)
                ·
                  refine ⟨989031291792420861341893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1318708389056561148455857 989031291792420861341893)
                  ·
                    refine ⟨185443367211078911501605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 989031291792420861341893 185443367211078911501605)
                    ·
                      rfl

theorem cell23_1083449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 2, 2, 4].length) (baseStart_1083449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1083449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1083449 prefixEnd_1083449 := by exact prefixLift 1083449
  have htrace : WordTrace (prefixWord ++ tailWord_1083449) baseStart_1083449 baseEnd_1083449 := by
    simpa [prefixWord, tailWord_1083449, baseEnd_1083449] using wordTrace_append hprefix tailTrace_1083449
  have hstable : (prefixWord ++ tailWord_1083449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083449).length < 2 ^ (prefixWord ++ tailWord_1083449).sum := by decide
  have hdescent : baseEnd_1083449 < baseStart_1083449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083456 : List Nat := [2, 1, 1, 2, 2, 5, 1, 4, 1, 2, 2]
def baseStart_1083456 : Nat := 118140960795 + 1083456 * 2 ^ 59
def prefixEnd_1083456 : Nat := 4983230072969 + 3 ^ 40 * 1083456 * 2
def baseEnd_1083456 : Nat := 556333695997818207117283

theorem tailTrace_1083456 : CollatzResearch.WordTrace tailWord_1083456 prefixEnd_1083456 556333695997818207117283 := by
  unfold tailWord_1083456
  simp only [CollatzResearch.WordTrace]
  refine ⟨19758443381415713199079111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26344591175220950932105481 19758443381415713199079111)
  ·
    refine ⟨29637665072123569798618667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19758443381415713199079111 29637665072123569798618667)
    ·
      refine ⟨44456497608185354697928001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29637665072123569798618667 44456497608185354697928001)
      ·
        refine ⟨33342373206139016023446001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44456497608185354697928001 33342373206139016023446001)
        ·
          refine ⟨25006779904604262017584501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33342373206139016023446001 25006779904604262017584501)
          ·
            refine ⟨2344385616056649564148547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25006779904604262017584501 2344385616056649564148547)
            ·
              refine ⟨3516578424084974346222821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2344385616056649564148547 3516578424084974346222821)
              ·
                refine ⟨659358454515932689916779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3516578424084974346222821 659358454515932689916779)
                ·
                  refine ⟨989037681773899034875169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 659358454515932689916779 989037681773899034875169)
                  ·
                    refine ⟨741778261330424276156377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 989037681773899034875169 741778261330424276156377)
                    ·
                      refine ⟨556333695997818207117283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 741778261330424276156377 556333695997818207117283)
                      ·
                        rfl

theorem cell23_1083456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 4, 1, 2, 2].length) (baseStart_1083456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1083456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1083456 prefixEnd_1083456 := by exact prefixLift 1083456
  have htrace : WordTrace (prefixWord ++ tailWord_1083456) baseStart_1083456 baseEnd_1083456 := by
    simpa [prefixWord, tailWord_1083456, baseEnd_1083456] using wordTrace_append hprefix tailTrace_1083456
  have hstable : (prefixWord ++ tailWord_1083456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083456).length < 2 ^ (prefixWord ++ tailWord_1083456).sum := by decide
  have hdescent : baseEnd_1083456 < baseStart_1083456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083482 : List Nat := [3, 1, 1, 2, 1, 1, 3, 3, 3, 3, 2]
def baseStart_1083482 : Nat := 118140960795 + 1083482 * 2 ^ 59
def prefixEnd_1083482 : Nat := 4983230072969 + 3 ^ 40 * 1083482 * 2
def baseEnd_1083482 : Nat := 556347046494835105392163

theorem tailTrace_1083482 : CollatzResearch.WordTrace tailWord_1083482 prefixEnd_1083482 556347046494835105392163 := by
  unfold tailWord_1083482
  simp only [CollatzResearch.WordTrace]
  refine ⟨9879458765184308209651175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26345223373824821892403133 9879458765184308209651175)
  ·
    refine ⟨14819188147776462314476763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9879458765184308209651175 14819188147776462314476763)
    ·
      refine ⟨22228782221664693471715145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14819188147776462314476763 22228782221664693471715145)
      ·
        refine ⟨16671586666248520103786359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22228782221664693471715145 16671586666248520103786359)
        ·
          refine ⟨25007379999372780155679539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16671586666248520103786359 25007379999372780155679539)
          ·
            refine ⟨37511069999059170233519309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25007379999372780155679539 37511069999059170233519309)
            ·
              refine ⟨14066651249647188837569741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37511069999059170233519309 14066651249647188837569741)
              ·
                refine ⟨5274994218617695814088653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14066651249647188837569741 5274994218617695814088653)
                ·
                  refine ⟨1978122831981635930283245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5274994218617695814088653 1978122831981635930283245)
                  ·
                    refine ⟨741796061993113473856217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1978122831981635930283245 741796061993113473856217)
                    ·
                      refine ⟨556347046494835105392163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 741796061993113473856217 556347046494835105392163)
                      ·
                        rfl

theorem cell23_1083482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 3, 3, 3, 2].length) (baseStart_1083482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1083482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1083482 prefixEnd_1083482 := by exact prefixLift 1083482
  have htrace : WordTrace (prefixWord ++ tailWord_1083482) baseStart_1083482 baseEnd_1083482 := by
    simpa [prefixWord, tailWord_1083482, baseEnd_1083482] using wordTrace_append hprefix tailTrace_1083482
  have hstable : (prefixWord ++ tailWord_1083482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083482).length < 2 ^ (prefixWord ++ tailWord_1083482).sum := by decide
  have hdescent : baseEnd_1083482 < baseStart_1083482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083490 : List Nat := [3, 3, 2, 2, 2, 1, 2, 3, 1, 2, 2]
def baseStart_1083490 : Nat := 118140960795 + 1083490 * 2 ^ 59
def prefixEnd_1083490 : Nat := 4983230072969 + 3 ^ 40 * 1083490 * 2
def baseEnd_1083490 : Nat := 556351154340071074092127

theorem tailTrace_1083490 : CollatzResearch.WordTrace tailWord_1083490 prefixEnd_1083490 556351154340071074092127 := by
  unfold tailWord_1083490
  simp only [CollatzResearch.WordTrace]
  refine ⟨9879531711177062551223981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26345417896472166803263949 9879531711177062551223981)
  ·
    refine ⟨3704824391691398456708993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9879531711177062551223981 3704824391691398456708993)
    ·
      refine ⟨2778618293768548842531745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3704824391691398456708993 2778618293768548842531745)
      ·
        refine ⟨2083963720326411631898809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2778618293768548842531745 2083963720326411631898809)
        ·
          refine ⟨1562972790244808723924107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2083963720326411631898809 1562972790244808723924107)
          ·
            refine ⟨2344459185367213085886161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1562972790244808723924107 2344459185367213085886161)
            ·
              refine ⟨1758344389025409814414621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2344459185367213085886161 1758344389025409814414621)
              ·
                refine ⟨659379145884528680405483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1758344389025409814414621 659379145884528680405483)
                ·
                  refine ⟨989068718826793020608225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 659379145884528680405483 989068718826793020608225)
                  ·
                    refine ⟨741801539120094765456169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 989068718826793020608225 741801539120094765456169)
                    ·
                      refine ⟨556351154340071074092127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 741801539120094765456169 556351154340071074092127)
                      ·
                        rfl

theorem cell23_1083490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_1083490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1083490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1083490 prefixEnd_1083490 := by exact prefixLift 1083490
  have htrace : WordTrace (prefixWord ++ tailWord_1083490) baseStart_1083490 baseEnd_1083490 := by
    simpa [prefixWord, tailWord_1083490, baseEnd_1083490] using wordTrace_append hprefix tailTrace_1083490
  have hstable : (prefixWord ++ tailWord_1083490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083490).length < 2 ^ (prefixWord ++ tailWord_1083490).sum := by decide
  have hdescent : baseEnd_1083490 < baseStart_1083490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083506 : List Nat := [3, 2, 1, 2, 2, 4, 1, 2, 2, 1, 3]
def baseStart_1083506 : Nat := 118140960795 + 1083506 * 2 ^ 59
def prefixEnd_1083506 : Nat := 4983230072969 + 3 ^ 40 * 1083506 * 2
def baseEnd_1083506 : Nat := 556359370030543011492053

theorem tailTrace_1083506 : CollatzResearch.WordTrace tailWord_1083506 prefixEnd_1083506 556359370030543011492053 := by
  unfold tailWord_1083506
  simp only [CollatzResearch.WordTrace]
  refine ⟨9879677603162571234369593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26345806941766856624985581 9879677603162571234369593)
  ·
    refine ⟨7409758202371928425777195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9879677603162571234369593 7409758202371928425777195)
    ·
      refine ⟨11114637303557892638665793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7409758202371928425777195 11114637303557892638665793)
      ·
        refine ⟨8335977977668419478999345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11114637303557892638665793 8335977977668419478999345)
        ·
          refine ⟨6251983483251314609249509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8335977977668419478999345 6251983483251314609249509)
          ·
            refine ⟨1172246903109621489234283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6251983483251314609249509 1172246903109621489234283)
            ·
              refine ⟨1758370354664432233851425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1172246903109621489234283 1758370354664432233851425)
              ·
                refine ⟨1318777765998324175388569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1758370354664432233851425 1318777765998324175388569)
                ·
                  refine ⟨989083324498743131541427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1318777765998324175388569 989083324498743131541427)
                  ·
                    refine ⟨1483624986748114697312141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 989083324498743131541427 1483624986748114697312141)
                    ·
                      refine ⟨556359370030543011492053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1483624986748114697312141 556359370030543011492053)
                      ·
                        rfl

theorem cell23_1083506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 2, 2, 1, 3].length) (baseStart_1083506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1083506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1083506 prefixEnd_1083506 := by exact prefixLift 1083506
  have htrace : WordTrace (prefixWord ++ tailWord_1083506) baseStart_1083506 baseEnd_1083506 := by
    simpa [prefixWord, tailWord_1083506, baseEnd_1083506] using wordTrace_append hprefix tailTrace_1083506
  have hstable : (prefixWord ++ tailWord_1083506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083506).length < 2 ^ (prefixWord ++ tailWord_1083506).sum := by decide
  have hdescent : baseEnd_1083506 < baseStart_1083506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083545 : List Nat := [1, 2, 1, 2, 1, 2, 1, 4, 1, 5, 3]
def baseStart_1083545 : Nat := 118140960795 + 1083545 * 2 ^ 59
def prefixEnd_1083545 : Nat := 4983230072969 + 3 ^ 40 * 1083545 * 2
def baseEnd_1083545 : Nat := 556379395776068358904373

theorem tailTrace_1083545 : CollatzResearch.WordTrace tailWord_1083545 prefixEnd_1083545 556379395776068358904373 := by
  unfold tailWord_1083545
  simp only [CollatzResearch.WordTrace]
  refine ⟨39520132859508994598148089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26346755239672663065432059 39520132859508994598148089)
  ·
    refine ⟨29640099644631745948611067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39520132859508994598148089 29640099644631745948611067)
    ·
      refine ⟨44460149466947618922916601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29640099644631745948611067 44460149466947618922916601)
      ·
        refine ⟨33345112100210714192187451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44460149466947618922916601 33345112100210714192187451)
        ·
          refine ⟨50017668150316071288281177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33345112100210714192187451 50017668150316071288281177)
          ·
            refine ⟨37513251112737053466210883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50017668150316071288281177 37513251112737053466210883)
            ·
              refine ⟨56269876669105580199316325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37513251112737053466210883 56269876669105580199316325)
              ·
                refine ⟨10550601875457296287371811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56269876669105580199316325 10550601875457296287371811)
                ·
                  refine ⟨15825902813185944431057717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10550601875457296287371811 15825902813185944431057717)
                  ·
                    refine ⟨1483678388736182290411661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15825902813185944431057717 1483678388736182290411661)
                    ·
                      refine ⟨556379395776068358904373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1483678388736182290411661 556379395776068358904373)
                      ·
                        rfl

theorem cell23_1083545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 5, 3].length) (baseStart_1083545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1083545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1083545 prefixEnd_1083545 := by exact prefixLift 1083545
  have htrace : WordTrace (prefixWord ++ tailWord_1083545) baseStart_1083545 baseEnd_1083545 := by
    simpa [prefixWord, tailWord_1083545, baseEnd_1083545] using wordTrace_append hprefix tailTrace_1083545
  have hstable : (prefixWord ++ tailWord_1083545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083545).length < 2 ^ (prefixWord ++ tailWord_1083545).sum := by decide
  have hdescent : baseEnd_1083545 < baseStart_1083545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083569 : List Nat := [1, 2, 2, 5, 2, 2, 1, 1, 7]
def baseStart_1083569 : Nat := 118140960795 + 1083569 * 2 ^ 59
def prefixEnd_1083569 : Nat := 4983230072969 + 3 ^ 40 * 1083569 * 2
def baseEnd_1083569 : Nat := 61821302145752918333807

theorem tailTrace_1083569 : CollatzResearch.WordTrace tailWord_1083569 prefixEnd_1083569 61821302145752918333807 := by
  unfold tailWord_1083569
  simp only [CollatzResearch.WordTrace]
  refine ⟨39521008211422046697021761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26347338807614697798014507 39521008211422046697021761)
  ·
    refine ⟨29640756158566535022766321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39521008211422046697021761 29640756158566535022766321)
    ·
      refine ⟨22230567118924901267074741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29640756158566535022766321 22230567118924901267074741)
      ·
        refine ⟨2084115667399209493788257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22230567118924901267074741 2084115667399209493788257)
        ·
          refine ⟨1563086750549407120341193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2084115667399209493788257 1563086750549407120341193)
          ·
            refine ⟨1172315062912055340255895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1563086750549407120341193 1172315062912055340255895)
            ·
              refine ⟨1758472594368083010383843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1172315062912055340255895 1758472594368083010383843)
              ·
                refine ⟨2637708891552124515575765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1758472594368083010383843 2637708891552124515575765)
                ·
                  refine ⟨61821302145752918333807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2637708891552124515575765 61821302145752918333807)
                  ·
                    rfl

theorem cell23_1083569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 1, 7].length) (baseStart_1083569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1083569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1083569 prefixEnd_1083569 := by exact prefixLift 1083569
  have htrace : WordTrace (prefixWord ++ tailWord_1083569) baseStart_1083569 baseEnd_1083569 := by
    simpa [prefixWord, tailWord_1083569, baseEnd_1083569] using wordTrace_append hprefix tailTrace_1083569
  have hstable : (prefixWord ++ tailWord_1083569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083569).length < 2 ^ (prefixWord ++ tailWord_1083569).sum := by decide
  have hdescent : baseEnd_1083569 < baseStart_1083569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083575 : List Nat := [1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 7]
def baseStart_1083575 : Nat := 118140960795 + 1083575 * 2 ^ 59
def prefixEnd_1083575 : Nat := 4983230072969 + 3 ^ 40 * 1083575 * 2
def baseEnd_1083575 : Nat := 556394800195703241529235

theorem tailTrace_1083575 : CollatzResearch.WordTrace tailWord_1083575 prefixEnd_1083575 556394800195703241529235 := by
  unfold tailWord_1083575
  simp only [CollatzResearch.WordTrace]
  refine ⟨39521227049400309721740179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26347484699600206481160119 39521227049400309721740179)
  ·
    refine ⟨59281840574100464582610269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39521227049400309721740179 59281840574100464582610269)
    ·
      refine ⟨22230690215287674218478851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59281840574100464582610269 22230690215287674218478851)
      ·
        refine ⟨33346035322931511327718277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22230690215287674218478851 33346035322931511327718277)
        ·
          refine ⟨6252381623049658373947177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33346035322931511327718277 6252381623049658373947177)
          ·
            refine ⟨4689286217287243780460383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6252381623049658373947177 4689286217287243780460383)
            ·
              refine ⟨7033929325930865670690575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4689286217287243780460383 7033929325930865670690575)
              ·
                refine ⟨10550893988896298506035863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7033929325930865670690575 10550893988896298506035863)
                ·
                  refine ⟨15826340983344447759053795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10550893988896298506035863 15826340983344447759053795)
                  ·
                    refine ⟨23739511475016671638580693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15826340983344447759053795 23739511475016671638580693)
                    ·
                      refine ⟨556394800195703241529235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 23739511475016671638580693 556394800195703241529235)
                      ·
                        rfl

theorem cell23_1083575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 7].length) (baseStart_1083575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1083575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1083575 prefixEnd_1083575 := by exact prefixLift 1083575
  have htrace : WordTrace (prefixWord ++ tailWord_1083575) baseStart_1083575 baseEnd_1083575 := by
    simpa [prefixWord, tailWord_1083575, baseEnd_1083575] using wordTrace_append hprefix tailTrace_1083575
  have hstable : (prefixWord ++ tailWord_1083575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083575).length < 2 ^ (prefixWord ++ tailWord_1083575).sum := by decide
  have hdescent : baseEnd_1083575 < baseStart_1083575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083580 : List Nat := [2, 2, 2, 3, 3, 2, 2, 1, 2, 2, 2]
def baseStart_1083580 : Nat := 118140960795 + 1083580 * 2 ^ 59
def prefixEnd_1083580 : Nat := 4983230072969 + 3 ^ 40 * 1083580 * 2
def baseEnd_1083580 : Nat := 556397367598975721966713

theorem tailTrace_1083580 : CollatzResearch.WordTrace tailWord_1083580 prefixEnd_1083580 556397367598975721966713 := by
  unfold tailWord_1083580
  simp only [CollatzResearch.WordTrace]
  refine ⟨19760704707191097787836097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26347606276254797050448129 19760704707191097787836097)
  ·
    refine ⟨14820528530393323340877073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19760704707191097787836097 14820528530393323340877073)
    ·
      refine ⟨11115396397794992505657805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14820528530393323340877073 11115396397794992505657805)
      ·
        refine ⟨4168273649173122189621677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11115396397794992505657805 4168273649173122189621677)
        ·
          refine ⟨1563102618439920821108129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4168273649173122189621677 1563102618439920821108129)
          ·
            refine ⟨1172326963829940615831097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1563102618439920821108129 1172326963829940615831097)
            ·
              refine ⟨879245222872455461873323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1172326963829940615831097 879245222872455461873323)
              ·
                refine ⟨1318867834308683192809985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 879245222872455461873323 1318867834308683192809985)
                ·
                  refine ⟨989150875731512394607489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1318867834308683192809985 989150875731512394607489)
                  ·
                    refine ⟨741863156798634295955617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 989150875731512394607489 741863156798634295955617)
                    ·
                      refine ⟨556397367598975721966713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 741863156798634295955617 556397367598975721966713)
                      ·
                        rfl

theorem cell23_1083580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 2, 1, 2, 2, 2].length) (baseStart_1083580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1083580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1083580 prefixEnd_1083580 := by exact prefixLift 1083580
  have htrace : WordTrace (prefixWord ++ tailWord_1083580) baseStart_1083580 baseEnd_1083580 := by
    simpa [prefixWord, tailWord_1083580, baseEnd_1083580] using wordTrace_append hprefix tailTrace_1083580
  have hstable : (prefixWord ++ tailWord_1083580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083580).length < 2 ^ (prefixWord ++ tailWord_1083580).sum := by decide
  have hdescent : baseEnd_1083580 < baseStart_1083580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083615 : List Nat := [1, 1, 2, 3, 2, 1, 1, 3, 2, 1, 6]
def baseStart_1083615 : Nat := 118140960795 + 1083615 * 2 ^ 59
def prefixEnd_1083615 : Nat := 4983230072969 + 3 ^ 40 * 1083615 * 2
def baseEnd_1083615 : Nat := 556415339421883085029051

theorem tailTrace_1083615 : CollatzResearch.WordTrace tailWord_1083615 prefixEnd_1083615 556415339421883085029051 := by
  unfold tailWord_1083615
  simp only [CollatzResearch.WordTrace]
  refine ⟨39522685969255396553196299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26348457312836931035464199 39522685969255396553196299)
  ·
    refine ⟨59284028953883094829794449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39522685969255396553196299 59284028953883094829794449)
    ·
      refine ⟨44463021715412321122345837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59284028953883094829794449 44463021715412321122345837)
      ·
        refine ⟨16673633143279620420879689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44463021715412321122345837 16673633143279620420879689)
        ·
          refine ⟨12505224857459715315659767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16673633143279620420879689 12505224857459715315659767)
          ·
            refine ⟨18757837286189572973489651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12505224857459715315659767 18757837286189572973489651)
            ·
              refine ⟨28136755929284359460234477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18757837286189572973489651 28136755929284359460234477)
              ·
                refine ⟨10551283473481634797587929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28136755929284359460234477 10551283473481634797587929)
                ·
                  refine ⟨7913462605111226098190947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10551283473481634797587929 7913462605111226098190947)
                  ·
                    refine ⟨11870193907666839147286421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7913462605111226098190947 11870193907666839147286421)
                    ·
                      refine ⟨556415339421883085029051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11870193907666839147286421 556415339421883085029051)
                      ·
                        rfl

theorem cell23_1083615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 2, 1, 6].length) (baseStart_1083615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1083615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1083615 prefixEnd_1083615 := by exact prefixLift 1083615
  have htrace : WordTrace (prefixWord ++ tailWord_1083615) baseStart_1083615 baseEnd_1083615 := by
    simpa [prefixWord, tailWord_1083615, baseEnd_1083615] using wordTrace_append hprefix tailTrace_1083615
  have hstable : (prefixWord ++ tailWord_1083615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083615).length < 2 ^ (prefixWord ++ tailWord_1083615).sum := by decide
  have hdescent : baseEnd_1083615 < baseStart_1083615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083642 : List Nat := [3, 1, 1, 1, 1, 5, 2, 3, 6]
def baseStart_1083642 : Nat := 118140960795 + 1083642 * 2 ^ 59
def prefixEnd_1083642 : Nat := 4983230072969 + 3 ^ 40 * 1083642 * 2
def baseEnd_1083642 : Nat := 61825467044394942154603

theorem tailTrace_1083642 : CollatzResearch.WordTrace tailWord_1083642 prefixEnd_1083642 61825467044394942154603 := by
  unfold tailWord_1083642
  simp only [CollatzResearch.WordTrace]
  refine ⟨9880917685039395041107295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26349113826771720109619453 9880917685039395041107295)
  ·
    refine ⟨14821376527559092561660943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9880917685039395041107295 14821376527559092561660943)
    ·
      refine ⟨22232064791338638842491415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14821376527559092561660943 22232064791338638842491415)
      ·
        refine ⟨33348097187007958263737123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22232064791338638842491415 33348097187007958263737123)
        ·
          refine ⟨50022145780511937395605685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33348097187007958263737123 50022145780511937395605685)
          ·
            refine ⟨4689576166922994130838033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50022145780511937395605685 4689576166922994130838033)
            ·
              refine ⟨3517182125192245598128525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4689576166922994130838033 3517182125192245598128525)
              ·
                refine ⟨1318943296947092099298197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3517182125192245598128525 1318943296947092099298197)
                ·
                  refine ⟨61825467044394942154603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1318943296947092099298197 61825467044394942154603)
                  ·
                    rfl

theorem cell23_1083642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 3, 6].length) (baseStart_1083642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1083642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1083642 prefixEnd_1083642 := by exact prefixLift 1083642
  have htrace : WordTrace (prefixWord ++ tailWord_1083642) baseStart_1083642 baseEnd_1083642 := by
    simpa [prefixWord, tailWord_1083642, baseEnd_1083642] using wordTrace_append hprefix tailTrace_1083642
  have hstable : (prefixWord ++ tailWord_1083642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083642).length < 2 ^ (prefixWord ++ tailWord_1083642).sum := by decide
  have hdescent : baseEnd_1083642 < baseStart_1083642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083656 : List Nat := [2, 1, 3, 2, 3, 3, 1, 1, 2, 2, 3]
def baseStart_1083656 : Nat := 118140960795 + 1083656 * 2 ^ 59
def prefixEnd_1083656 : Nat := 4983230072969 + 3 ^ 40 * 1083656 * 2
def baseEnd_1083656 : Nat := 556436392128717424616363

theorem tailTrace_1083656 : CollatzResearch.WordTrace tailWord_1083656 prefixEnd_1083656 556436392128717424616363 := by
  unfold tailWord_1083656
  simp only [CollatzResearch.WordTrace]
  refine ⟨19762090681053430277719411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26349454241404573703625881 19762090681053430277719411)
  ·
    refine ⟨29643136021580145416579117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19762090681053430277719411 29643136021580145416579117)
    ·
      refine ⟨11116176008092554531217169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29643136021580145416579117 11116176008092554531217169)
      ·
        refine ⟨8337132006069415898412877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11116176008092554531217169 8337132006069415898412877)
        ·
          refine ⟨3126424502276030961904829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8337132006069415898412877 3126424502276030961904829)
          ·
            refine ⟨1172409188353511610714311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3126424502276030961904829 1172409188353511610714311)
            ·
              refine ⟨1758613782530267416071467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1172409188353511610714311 1758613782530267416071467)
              ·
                refine ⟨2637920673795401124107201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1758613782530267416071467 2637920673795401124107201)
                ·
                  refine ⟨1978440505346550843080401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2637920673795401124107201 1978440505346550843080401)
                  ·
                    refine ⟨1483830379009913132310301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1978440505346550843080401 1483830379009913132310301)
                    ·
                      refine ⟨556436392128717424616363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1483830379009913132310301 556436392128717424616363)
                      ·
                        rfl

theorem cell23_1083656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 1, 2, 2, 3].length) (baseStart_1083656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1083656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1083656 prefixEnd_1083656 := by exact prefixLift 1083656
  have htrace : WordTrace (prefixWord ++ tailWord_1083656) baseStart_1083656 baseEnd_1083656 := by
    simpa [prefixWord, tailWord_1083656, baseEnd_1083656] using wordTrace_append hprefix tailTrace_1083656
  have hstable : (prefixWord ++ tailWord_1083656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083656).length < 2 ^ (prefixWord ++ tailWord_1083656).sum := by decide
  have hdescent : baseEnd_1083656 < baseStart_1083656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083692 : List Nat := [2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 4]
def baseStart_1083692 : Nat := 118140960795 + 1083692 * 2 ^ 59
def prefixEnd_1083692 : Nat := 4983230072969 + 3 ^ 40 * 1083692 * 2
def baseEnd_1083692 : Nat := 556454877432279283766197

theorem tailTrace_1083692 : CollatzResearch.WordTrace tailWord_1083692 prefixEnd_1083692 556454877432279283766197 := by
  unfold tailWord_1083692
  simp only [CollatzResearch.WordTrace]
  refine ⟨19762747194988219351874665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26350329593317625802499553 19762747194988219351874665)
  ·
    refine ⟨14822060396241164513905999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19762747194988219351874665 14822060396241164513905999)
    ·
      refine ⟨22233090594361746770858999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14822060396241164513905999 22233090594361746770858999)
      ·
        refine ⟨33349635891542620156288499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22233090594361746770858999 33349635891542620156288499)
        ·
          refine ⟨50024453837313930234432749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33349635891542620156288499 50024453837313930234432749)
          ·
            refine ⟨18759170188992723837912281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50024453837313930234432749 18759170188992723837912281)
            ·
              refine ⟨14069377641744542878434211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18759170188992723837912281 14069377641744542878434211)
              ·
                refine ⟨21104066462616814317651317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14069377641744542878434211 21104066462616814317651317)
                ·
                  refine ⟨1978506230870326342279811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21104066462616814317651317 1978506230870326342279811)
                  ·
                    refine ⟨2967759346305489513419717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1978506230870326342279811 2967759346305489513419717)
                    ·
                      refine ⟨556454877432279283766197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2967759346305489513419717 556454877432279283766197)
                      ·
                        rfl

theorem cell23_1083692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 4].length) (baseStart_1083692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1083692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1083692 prefixEnd_1083692 := by exact prefixLift 1083692
  have htrace : WordTrace (prefixWord ++ tailWord_1083692) baseStart_1083692 baseEnd_1083692 := by
    simpa [prefixWord, tailWord_1083692, baseEnd_1083692] using wordTrace_append hprefix tailTrace_1083692
  have hstable : (prefixWord ++ tailWord_1083692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083692).length < 2 ^ (prefixWord ++ tailWord_1083692).sum := by decide
  have hdescent : baseEnd_1083692 < baseStart_1083692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083693 : List Nat := [1, 5, 3, 1, 2, 1, 3, 1, 6]
def baseStart_1083693 : Nat := 118140960795 + 1083693 * 2 ^ 59
def prefixEnd_1083693 : Nat := 4983230072969 + 3 ^ 40 * 1083693 * 2
def baseEnd_1083693 : Nat := 61828376768103753317077

theorem tailTrace_1083693 : CollatzResearch.WordTrace tailWord_1083693 prefixEnd_1083693 61828376768103753317077 := by
  unfold tailWord_1083693
  simp only [CollatzResearch.WordTrace]
  refine ⟨39525530862972815874535733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26350353908648543916357155 39525530862972815874535733)
  ·
    refine ⟨3705518518403701488237725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39525530862972815874535733 3705518518403701488237725)
    ·
      refine ⟨1389569444401388058089147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3705518518403701488237725 1389569444401388058089147)
      ·
        refine ⟨2084354166602082087133721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1389569444401388058089147 2084354166602082087133721)
        ·
          refine ⟨1563265624951561565350291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2084354166602082087133721 1563265624951561565350291)
          ·
            refine ⟨2344898437427342348025437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1563265624951561565350291 2344898437427342348025437)
            ·
              refine ⟨879336914035253380509539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2344898437427342348025437 879336914035253380509539)
              ·
                refine ⟨1319005371052880070764309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 879336914035253380509539 1319005371052880070764309)
                ·
                  refine ⟨61828376768103753317077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1319005371052880070764309 61828376768103753317077)
                  ·
                    rfl

theorem cell23_1083693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 3, 1, 6].length) (baseStart_1083693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1083693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1083693 prefixEnd_1083693 := by exact prefixLift 1083693
  have htrace : WordTrace (prefixWord ++ tailWord_1083693) baseStart_1083693 baseEnd_1083693 := by
    simpa [prefixWord, tailWord_1083693, baseEnd_1083693] using wordTrace_append hprefix tailTrace_1083693
  have hstable : (prefixWord ++ tailWord_1083693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083693).length < 2 ^ (prefixWord ++ tailWord_1083693).sum := by decide
  have hdescent : baseEnd_1083693 < baseStart_1083693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083729 : List Nat := [1, 2, 2, 1, 4, 3, 2, 1, 1, 1, 5]
def baseStart_1083729 : Nat := 118140960795 + 1083729 * 2 ^ 59
def prefixEnd_1083729 : Nat := 4983230072969 + 3 ^ 40 * 1083729 * 2
def baseEnd_1083729 : Nat := 556473876216495639003527

theorem tailTrace_1083729 : CollatzResearch.WordTrace tailWord_1083729 prefixEnd_1083729 556473876216495639003527 := by
  unfold tailWord_1083729
  simp only [CollatzResearch.WordTrace]
  refine ⟨39526843890842394022846241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26351229260561596015230827 39526843890842394022846241)
  ·
    refine ⟨29645132918131795517134681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39526843890842394022846241 29645132918131795517134681)
    ·
      refine ⟨22233849688598846637851011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29645132918131795517134681 22233849688598846637851011)
      ·
        refine ⟨33350774532898269956776517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22233849688598846637851011 33350774532898269956776517)
        ·
          refine ⟨6253270224918425616895597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33350774532898269956776517 6253270224918425616895597)
          ·
            refine ⟨2344976334344409606335849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6253270224918425616895597 2344976334344409606335849)
            ·
              refine ⟨1758732250758307204751887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2344976334344409606335849 1758732250758307204751887)
              ·
                refine ⟨2638098376137460807127831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1758732250758307204751887 2638098376137460807127831)
                ·
                  refine ⟨3957147564206191210691747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2638098376137460807127831 3957147564206191210691747)
                  ·
                    refine ⟨5935721346309286816037621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3957147564206191210691747 5935721346309286816037621)
                    ·
                      refine ⟨556473876216495639003527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5935721346309286816037621 556473876216495639003527)
                      ·
                        rfl

theorem cell23_1083729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 1, 1, 1, 5].length) (baseStart_1083729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1083729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1083729 prefixEnd_1083729 := by exact prefixLift 1083729
  have htrace : WordTrace (prefixWord ++ tailWord_1083729) baseStart_1083729 baseEnd_1083729 := by
    simpa [prefixWord, tailWord_1083729, baseEnd_1083729] using wordTrace_append hprefix tailTrace_1083729
  have hstable : (prefixWord ++ tailWord_1083729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083729).length < 2 ^ (prefixWord ++ tailWord_1083729).sum := by decide
  have hdescent : baseEnd_1083729 < baseStart_1083729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
