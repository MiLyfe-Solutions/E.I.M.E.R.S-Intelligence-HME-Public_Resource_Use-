import V185TrunkScan22Chunk064

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_585570 : List Nat := [3, 3, 2, 1, 2, 1, 1, 1, 2, 6]
def baseStart_585570 : Nat := 118140960795 + 585570 * 2 ^ 59
def prefixEnd_585570 : Nat := 4983230072969 + 3 ^ 40 * 585570 * 2
def baseEnd_585570 : Nat := 200452577902252792254679

theorem tailTrace_585570 : CollatzResearch.WordTrace tailWord_585570 prefixEnd_585570 200452577902252792254679 := by
  unfold tailWord_585570
  simp only [CollatzResearch.WordTrace]
  refine ⟨5339373122146843059778541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14238328325724914826076109 5339373122146843059778541)
  ·
    refine ⟨2002264920805066147416953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5339373122146843059778541 2002264920805066147416953)
    ·
      refine ⟨1501698690603799610562715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2002264920805066147416953 1501698690603799610562715)
      ·
        refine ⟨2252548035905699415844073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1501698690603799610562715 2252548035905699415844073)
        ·
          refine ⟨1689411026929274561883055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2252548035905699415844073 1689411026929274561883055)
          ·
            refine ⟨2534116540393911842824583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1689411026929274561883055 2534116540393911842824583)
            ·
              refine ⟨3801174810590867764236875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2534116540393911842824583 3801174810590867764236875)
              ·
                refine ⟨5701762215886301646355313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3801174810590867764236875 5701762215886301646355313)
                ·
                  refine ⟨4276321661914726234766485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5701762215886301646355313 4276321661914726234766485)
                  ·
                    refine ⟨200452577902252792254679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4276321661914726234766485 200452577902252792254679)
                    ·
                      rfl

theorem cell22_585570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_585570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_585570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_585570 prefixEnd_585570 := by exact prefixLift 585570
  have htrace : WordTrace (prefixWord ++ tailWord_585570) baseStart_585570 baseEnd_585570 := by
    simpa [prefixWord, tailWord_585570, baseEnd_585570] using wordTrace_append hprefix tailTrace_585570
  have hstable : (prefixWord ++ tailWord_585570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585570).length < 2 ^ (prefixWord ++ tailWord_585570).sum := by decide
  have hdescent : baseEnd_585570 < baseStart_585570 := by decide
  rcases family_descends (prefixWord ++ tailWord_585570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585662 : List Nat := [4, 2, 1, 1, 1, 3, 1, 2, 4, 3]
def baseStart_585662 : Nat := 118140960795 + 585662 * 2 ^ 59
def prefixEnd_585662 : Nat := 4983230072969 + 3 ^ 40 * 585662 * 2
def baseEnd_585662 : Nat := 200484071382395218954397

theorem tailTrace_585662 : CollatzResearch.WordTrace tailWord_585662 prefixEnd_585662 200484071382395218954397 := by
  unfold tailWord_585662
  simp only [CollatzResearch.WordTrace]
  refine ⟨2670106000531758993932905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14240565336169381300975493 2670106000531758993932905)
  ·
    refine ⟨2002579500398819245449679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2670106000531758993932905 2002579500398819245449679)
    ·
      refine ⟨3003869250598228868174519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2002579500398819245449679 3003869250598228868174519)
      ·
        refine ⟨4505803875897343302261779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3003869250598228868174519 4505803875897343302261779)
        ·
          refine ⟨6758705813846014953392669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4505803875897343302261779 6758705813846014953392669)
          ·
            refine ⟨2534514680192255607522251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6758705813846014953392669 2534514680192255607522251)
            ·
              refine ⟨3801772020288383411283377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2534514680192255607522251 3801772020288383411283377)
              ·
                refine ⟨2851329015216287558462533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3801772020288383411283377 2851329015216287558462533)
                ·
                  refine ⟨534624190353053917211725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2851329015216287558462533 534624190353053917211725)
                  ·
                    refine ⟨200484071382395218954397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 534624190353053917211725 200484071382395218954397)
                    ·
                      rfl

theorem cell22_585662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 2, 4, 3].length) (baseStart_585662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_585662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_585662 prefixEnd_585662 := by exact prefixLift 585662
  have htrace : WordTrace (prefixWord ++ tailWord_585662) baseStart_585662 baseEnd_585662 := by
    simpa [prefixWord, tailWord_585662, baseEnd_585662] using wordTrace_append hprefix tailTrace_585662
  have hstable : (prefixWord ++ tailWord_585662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585662).length < 2 ^ (prefixWord ++ tailWord_585662).sum := by decide
  have hdescent : baseEnd_585662 < baseStart_585662 := by decide
  rcases family_descends (prefixWord ++ tailWord_585662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585673 : List Nat := [1, 2, 1, 1, 2, 1, 2, 2, 1, 9]
def baseStart_585673 : Nat := 118140960795 + 585673 * 2 ^ 59
def prefixEnd_585673 : Nat := 4983230072969 + 3 ^ 40 * 585673 * 2
def baseEnd_585673 : Nat := 200487836907194856929363

theorem tailTrace_585673 : CollatzResearch.WordTrace tailWord_585673 prefixEnd_585673 200487836907194856929363 := by
  unfold tailWord_585673
  simp only [CollatzResearch.WordTrace]
  refine ⟨21361249207214220830113673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14240832804809480553409115 21361249207214220830113673)
  ·
    refine ⟨16020936905410665622585255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21361249207214220830113673 16020936905410665622585255)
    ·
      refine ⟨24031405358115998433877883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16020936905410665622585255 24031405358115998433877883)
      ·
        refine ⟨36047108037173997650816825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24031405358115998433877883 36047108037173997650816825)
        ·
          refine ⟨27035331027880498238112619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36047108037173997650816825 27035331027880498238112619)
          ·
            refine ⟨40552996541820747357168929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27035331027880498238112619 40552996541820747357168929)
            ·
              refine ⟨30414747406365560517876697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40552996541820747357168929 30414747406365560517876697)
              ·
                refine ⟨22811060554774170388407523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30414747406365560517876697 22811060554774170388407523)
                ·
                  refine ⟨34216590832161255582611285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22811060554774170388407523 34216590832161255582611285)
                  ·
                    refine ⟨200487836907194856929363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 34216590832161255582611285 200487836907194856929363)
                    ·
                      rfl

theorem cell22_585673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 9].length) (baseStart_585673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_585673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_585673 prefixEnd_585673 := by exact prefixLift 585673
  have htrace : WordTrace (prefixWord ++ tailWord_585673) baseStart_585673 baseEnd_585673 := by
    simpa [prefixWord, tailWord_585673, baseEnd_585673] using wordTrace_append hprefix tailTrace_585673
  have hstable : (prefixWord ++ tailWord_585673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585673).length < 2 ^ (prefixWord ++ tailWord_585673).sum := by decide
  have hdescent : baseEnd_585673 < baseStart_585673 := by decide
  rcases family_descends (prefixWord ++ tailWord_585673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585724 : List Nat := [2, 2, 2, 1, 2, 2, 2, 5, 1, 3]
def baseStart_585724 : Nat := 118140960795 + 585724 * 2 ^ 59
def prefixEnd_585724 : Nat := 4983230072969 + 3 ^ 40 * 585724 * 2
def baseEnd_585724 : Nat := 200505295249447723904207

theorem tailTrace_585724 : CollatzResearch.WordTrace tailWord_585724 prefixEnd_585724 200505295249447723904207 := by
  unfold tailWord_585724
  simp only [CollatzResearch.WordTrace]
  refine ⟨10681554665014728270110113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14242072886686304360146817 10681554665014728270110113)
  ·
    refine ⟨8011165998761046202582585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10681554665014728270110113 8011165998761046202582585)
    ·
      refine ⟨6008374499070784651936939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8011165998761046202582585 6008374499070784651936939)
      ·
        refine ⟨9012561748606176977905409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6008374499070784651936939 9012561748606176977905409)
        ·
          refine ⟨6759421311454632733429057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9012561748606176977905409 6759421311454632733429057)
          ·
            refine ⟨5069565983590974550071793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6759421311454632733429057 5069565983590974550071793)
            ·
              refine ⟨3802174487693230912553845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5069565983590974550071793 3802174487693230912553845)
              ·
                refine ⟨356453858221240398051923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3802174487693230912553845 356453858221240398051923)
                ·
                  refine ⟨534680787331860597077885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 356453858221240398051923 534680787331860597077885)
                  ·
                    refine ⟨200505295249447723904207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 534680787331860597077885 200505295249447723904207)
                    ·
                      rfl

theorem cell22_585724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 5, 1, 3].length) (baseStart_585724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_585724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_585724 prefixEnd_585724 := by exact prefixLift 585724
  have htrace : WordTrace (prefixWord ++ tailWord_585724) baseStart_585724 baseEnd_585724 := by
    simpa [prefixWord, tailWord_585724, baseEnd_585724] using wordTrace_append hprefix tailTrace_585724
  have hstable : (prefixWord ++ tailWord_585724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585724).length < 2 ^ (prefixWord ++ tailWord_585724).sum := by decide
  have hdescent : baseEnd_585724 < baseStart_585724 := by decide
  rcases family_descends (prefixWord ++ tailWord_585724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585765 : List Nat := [1, 3, 1, 2, 2, 3, 1, 1, 8]
def baseStart_585765 : Nat := 118140960795 + 585765 * 2 ^ 59
def prefixEnd_585765 : Nat := 4983230072969 + 3 ^ 40 * 585765 * 2
def baseEnd_585765 : Nat := 66839776795779094543027

theorem tailTrace_585765 : CollatzResearch.WordTrace tailWord_585765 prefixEnd_585765 66839776795779094543027 := by
  unfold tailWord_585765
  simp only [CollatzResearch.WordTrace]
  refine ⟨21364604722880920542462749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14243069815253947028308499 21364604722880920542462749)
  ·
    refine ⟨8011726771080345203423531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21364604722880920542462749 8011726771080345203423531)
    ·
      refine ⟨12017590156620517805135297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8011726771080345203423531 12017590156620517805135297)
      ·
        refine ⟨9013192617465388353851473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12017590156620517805135297 9013192617465388353851473)
        ·
          refine ⟨6759894463099041265388605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9013192617465388353851473 6759894463099041265388605)
          ·
            refine ⟨2534960423662140474520727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6759894463099041265388605 2534960423662140474520727)
            ·
              refine ⟨3802440635493210711781091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2534960423662140474520727 3802440635493210711781091)
              ·
                refine ⟨5703660953239816067671637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3802440635493210711781091 5703660953239816067671637)
                ·
                  refine ⟨66839776795779094543027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5703660953239816067671637 66839776795779094543027)
                  ·
                    rfl

theorem cell22_585765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 8].length) (baseStart_585765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_585765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_585765 prefixEnd_585765 := by exact prefixLift 585765
  have htrace : WordTrace (prefixWord ++ tailWord_585765) baseStart_585765 baseEnd_585765 := by
    simpa [prefixWord, tailWord_585765, baseEnd_585765] using wordTrace_append hprefix tailTrace_585765
  have hstable : (prefixWord ++ tailWord_585765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585765).length < 2 ^ (prefixWord ++ tailWord_585765).sum := by decide
  have hdescent : baseEnd_585765 < baseStart_585765 := by decide
  rcases family_descends (prefixWord ++ tailWord_585765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585782 : List Nat := [5, 1, 2, 1, 1, 1, 1, 2, 8]
def baseStart_585782 : Nat := 118140960795 + 585782 * 2 ^ 59
def prefixEnd_585782 : Nat := 4983230072969 + 3 ^ 40 * 585782 * 2
def baseEnd_585782 : Nat := 66841716611584968651343

theorem tailTrace_585782 : CollatzResearch.WordTrace tailWord_585782 prefixEnd_585782 66841716611584968651343 := by
  unfold tailWord_585782
  simp only [CollatzResearch.WordTrace]
  refine ⟨1335326547738708277864475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14243483175879554963887733 1335326547738708277864475)
  ·
    refine ⟨2002989821608062416796713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1335326547738708277864475 2002989821608062416796713)
    ·
      refine ⟨1502242366206046812597535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2002989821608062416796713 1502242366206046812597535)
      ·
        refine ⟨2253363549309070218896303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1502242366206046812597535 2253363549309070218896303)
        ·
          refine ⟨3380045323963605328344455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2253363549309070218896303 3380045323963605328344455)
          ·
            refine ⟨5070067985945407992516683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3380045323963605328344455 5070067985945407992516683)
            ·
              refine ⟨7605101978918111988775025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5070067985945407992516683 7605101978918111988775025)
              ·
                refine ⟨5703826484188583991581269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7605101978918111988775025 5703826484188583991581269)
                ·
                  refine ⟨66841716611584968651343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5703826484188583991581269 66841716611584968651343)
                  ·
                    rfl

theorem cell22_585782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 8].length) (baseStart_585782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_585782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_585782 prefixEnd_585782 := by exact prefixLift 585782
  have htrace : WordTrace (prefixWord ++ tailWord_585782) baseStart_585782 baseEnd_585782 := by
    simpa [prefixWord, tailWord_585782, baseEnd_585782] using wordTrace_append hprefix tailTrace_585782
  have hstable : (prefixWord ++ tailWord_585782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585782).length < 2 ^ (prefixWord ++ tailWord_585782).sum := by decide
  have hdescent : baseEnd_585782 < baseStart_585782 := by decide
  rcases family_descends (prefixWord ++ tailWord_585782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585784 : List Nat := [2, 1, 2, 1, 6, 1, 1, 3, 1, 4]
def baseStart_585784 : Nat := 118140960795 + 585784 * 2 ^ 59
def prefixEnd_585784 : Nat := 4983230072969 + 3 ^ 40 * 585784 * 2
def baseEnd_585784 : Nat := 200525834475627567404023

theorem tailTrace_585784 : CollatzResearch.WordTrace tailWord_585784 prefixEnd_585784 200525834475627567404023 := by
  unfold tailWord_585784
  simp only [CollatzResearch.WordTrace]
  refine ⟨10682648854906043393702203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14243531806541391191602937 10682648854906043393702203)
  ·
    refine ⟨16023973282359065090553305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10682648854906043393702203 16023973282359065090553305)
    ·
      refine ⟨12017979961769298817914979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16023973282359065090553305 12017979961769298817914979)
      ·
        refine ⟨18026969942653948226872469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12017979961769298817914979 18026969942653948226872469)
        ·
          refine ⟨845014216061903823134647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 18026969942653948226872469 845014216061903823134647)
          ·
            refine ⟨1267521324092855734701971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 845014216061903823134647 1267521324092855734701971)
            ·
              refine ⟨1901281986139283602052957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1267521324092855734701971 1901281986139283602052957)
              ·
                refine ⟨712980744802231350769859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1901281986139283602052957 712980744802231350769859)
                ·
                  refine ⟨1069471117203347026154789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 712980744802231350769859 1069471117203347026154789)
                  ·
                    refine ⟨200525834475627567404023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1069471117203347026154789 200525834475627567404023)
                    ·
                      rfl

theorem cell22_585784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 3, 1, 4].length) (baseStart_585784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_585784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_585784 prefixEnd_585784 := by exact prefixLift 585784
  have htrace : WordTrace (prefixWord ++ tailWord_585784) baseStart_585784 baseEnd_585784 := by
    simpa [prefixWord, tailWord_585784, baseEnd_585784] using wordTrace_append hprefix tailTrace_585784
  have hstable : (prefixWord ++ tailWord_585784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585784).length < 2 ^ (prefixWord ++ tailWord_585784).sum := by decide
  have hdescent : baseEnd_585784 < baseStart_585784 := by decide
  rcases family_descends (prefixWord ++ tailWord_585784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585825 : List Nat := [1, 2, 3, 1, 1, 2, 1, 1, 1, 9]
def baseStart_585825 : Nat := 118140960795 + 585825 * 2 ^ 59
def prefixEnd_585825 : Nat := 4983230072969 + 3 ^ 40 * 585825 * 2
def baseEnd_585825 : Nat := 200539869613517127128897

theorem tailTrace_585825 : CollatzResearch.WordTrace tailWord_585825 prefixEnd_585825 200539869613517127128897 := by
  unfold tailWord_585825
  simp only [CollatzResearch.WordTrace]
  refine ⟨21366793102663550789646929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14244528735109033859764619 21366793102663550789646929)
  ·
    refine ⟨16025094826997663092235197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21366793102663550789646929 16025094826997663092235197)
    ·
      refine ⟨6009410560124123659588199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16025094826997663092235197 6009410560124123659588199)
      ·
        refine ⟨9014115840186185489382299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6009410560124123659588199 9014115840186185489382299)
        ·
          refine ⟨13521173760279278234073449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9014115840186185489382299 13521173760279278234073449)
          ·
            refine ⟨10140880320209458675555087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13521173760279278234073449 10140880320209458675555087)
            ·
              refine ⟨15211320480314188013332631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10140880320209458675555087 15211320480314188013332631)
              ·
                refine ⟨22816980720471282019998947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15211320480314188013332631 22816980720471282019998947)
                ·
                  refine ⟨34225471080706923029998421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22816980720471282019998947 34225471080706923029998421)
                  ·
                    refine ⟨200539869613517127128897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 34225471080706923029998421 200539869613517127128897)
                    ·
                      rfl

theorem cell22_585825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 9].length) (baseStart_585825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_585825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_585825 prefixEnd_585825 := by exact prefixLift 585825
  have htrace : WordTrace (prefixWord ++ tailWord_585825) baseStart_585825 baseEnd_585825 := by
    simpa [prefixWord, tailWord_585825, baseEnd_585825] using wordTrace_append hprefix tailTrace_585825
  have hstable : (prefixWord ++ tailWord_585825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585825).length < 2 ^ (prefixWord ++ tailWord_585825).sum := by decide
  have hdescent : baseEnd_585825 < baseStart_585825 := by decide
  rcases family_descends (prefixWord ++ tailWord_585825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585827 : List Nat := [1, 1, 1, 5, 1, 1, 6, 6]
def baseStart_585827 : Nat := 118140960795 + 585827 * 2 ^ 59
def prefixEnd_585827 : Nat := 4983230072969 + 3 ^ 40 * 585827 * 2
def baseEnd_585827 : Nat := 22282283806043309842099

theorem tailTrace_585827 : CollatzResearch.WordTrace tailWord_585827 prefixEnd_585827 22282283806043309842099 := by
  unfold tailWord_585827
  simp only [CollatzResearch.WordTrace]
  refine ⟨21366866048656305131219735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14244577365770870087479823 21366866048656305131219735)
  ·
    refine ⟨32050299072984457696829603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21366866048656305131219735 32050299072984457696829603)
    ·
      refine ⟨48075448609476686545244405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32050299072984457696829603 48075448609476686545244405)
      ·
        refine ⟨4507073307138439363616663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 48075448609476686545244405 4507073307138439363616663)
        ·
          refine ⟨6760609960707659045424995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4507073307138439363616663 6760609960707659045424995)
          ·
            refine ⟨10140914941061488568137493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6760609960707659045424995 10140914941061488568137493)
            ·
              refine ⟨475355387862257276631445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10140914941061488568137493 475355387862257276631445)
              ·
                refine ⟨22282283806043309842099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 475355387862257276631445 22282283806043309842099)
                ·
                  rfl

theorem cell22_585827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 6, 6].length) (baseStart_585827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_585827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_585827 prefixEnd_585827 := by exact prefixLift 585827
  have htrace : WordTrace (prefixWord ++ tailWord_585827) baseStart_585827 baseEnd_585827 := by
    simpa [prefixWord, tailWord_585827, baseEnd_585827] using wordTrace_append hprefix tailTrace_585827
  have hstable : (prefixWord ++ tailWord_585827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585827).length < 2 ^ (prefixWord ++ tailWord_585827).sum := by decide
  have hdescent : baseEnd_585827 < baseStart_585827 := by decide
  rcases family_descends (prefixWord ++ tailWord_585827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585859 : List Nat := [1, 1, 1, 3, 3, 3, 3, 1, 3, 3]
def baseStart_585859 : Nat := 118140960795 + 585859 * 2 ^ 59
def prefixEnd_585859 : Nat := 4983230072969 + 3 ^ 40 * 585859 * 2
def baseEnd_585859 : Nat := 200551508508352371778793

theorem tailTrace_585859 : CollatzResearch.WordTrace tailWord_585859 prefixEnd_585859 200551508508352371778793 := by
  unfold tailWord_585859
  simp only [CollatzResearch.WordTrace]
  refine ⟨21368033184540374596384631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14245355456360249730923087 21368033184540374596384631)
  ·
    refine ⟨32052049776810561894576947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21368033184540374596384631 32052049776810561894576947)
    ·
      refine ⟨48078074665215842841865421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32052049776810561894576947 48078074665215842841865421)
      ·
        refine ⟨18029277999455941065699533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48078074665215842841865421 18029277999455941065699533)
        ·
          refine ⟨6760979249795977899637325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18029277999455941065699533 6760979249795977899637325)
          ·
            refine ⟨2535367218673491712363997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6760979249795977899637325 2535367218673491712363997)
            ·
              refine ⟨950762707002559392136499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2535367218673491712363997 950762707002559392136499)
              ·
                refine ⟨1426144060503839088204749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 950762707002559392136499 1426144060503839088204749)
                ·
                  refine ⟨534804022688939658076781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1426144060503839088204749 534804022688939658076781)
                  ·
                    refine ⟨200551508508352371778793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 534804022688939658076781 200551508508352371778793)
                    ·
                      rfl

theorem cell22_585859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 1, 3, 3].length) (baseStart_585859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_585859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_585859 prefixEnd_585859 := by exact prefixLift 585859
  have htrace : WordTrace (prefixWord ++ tailWord_585859) baseStart_585859 baseEnd_585859 := by
    simpa [prefixWord, tailWord_585859, baseEnd_585859] using wordTrace_append hprefix tailTrace_585859
  have hstable : (prefixWord ++ tailWord_585859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585859).length < 2 ^ (prefixWord ++ tailWord_585859).sum := by decide
  have hdescent : baseEnd_585859 < baseStart_585859 := by decide
  rcases family_descends (prefixWord ++ tailWord_585859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585872 : List Nat := [2, 1, 1, 1, 1, 1, 7, 3, 5]
def baseStart_585872 : Nat := 118140960795 + 585872 * 2 ^ 59
def prefixEnd_585872 : Nat := 4983230072969 + 3 ^ 40 * 585872 * 2
def baseEnd_585872 : Nat := 66851986224674890401251

theorem tailTrace_585872 : CollatzResearch.WordTrace tailWord_585872 prefixEnd_585872 66851986224674890401251 := by
  unfold tailWord_585872
  simp only [CollatzResearch.WordTrace]
  refine ⟨10684253666746638908303935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14245671555662185211071913 10684253666746638908303935)
  ·
    refine ⟨16026380500119958362455903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10684253666746638908303935 16026380500119958362455903)
    ·
      refine ⟨24039570750179937543683855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16026380500119958362455903 24039570750179937543683855)
      ·
        refine ⟨36059356125269906315525783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24039570750179937543683855 36059356125269906315525783)
        ·
          refine ⟨54089034187904859473288675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36059356125269906315525783 54089034187904859473288675)
          ·
            refine ⟨81133551281857289209933013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54089034187904859473288675 81133551281857289209933013)
            ·
              refine ⟨1901567608168530215857805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 81133551281857289209933013 1901567608168530215857805)
              ·
                refine ⟨713087853063198830946677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1901567608168530215857805 713087853063198830946677)
                ·
                  refine ⟨66851986224674890401251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 713087853063198830946677 66851986224674890401251)
                  ·
                    rfl

theorem cell22_585872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 3, 5].length) (baseStart_585872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_585872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_585872 prefixEnd_585872 := by exact prefixLift 585872
  have htrace : WordTrace (prefixWord ++ tailWord_585872) baseStart_585872 baseEnd_585872 := by
    simpa [prefixWord, tailWord_585872, baseEnd_585872] using wordTrace_append hprefix tailTrace_585872
  have hstable : (prefixWord ++ tailWord_585872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585872).length < 2 ^ (prefixWord ++ tailWord_585872).sum := by decide
  have hdescent : baseEnd_585872 < baseStart_585872 := by decide
  rcases family_descends (prefixWord ++ tailWord_585872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585917 : List Nat := [1, 4, 1, 2, 1, 1, 1, 5, 6]
def baseStart_585917 : Nat := 118140960795 + 585917 * 2 ^ 59
def prefixEnd_585917 : Nat := 4983230072969 + 3 ^ 40 * 585917 * 2
def baseEnd_585917 : Nat := 66857121031219851276205

theorem tailTrace_585917 : CollatzResearch.WordTrace tailWord_585917 prefixEnd_585917 66857121031219851276205 := by
  unfold tailWord_585917
  simp only [CollatzResearch.WordTrace]
  refine ⟨21370148618330250501996005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14246765745553500334664003 21370148618330250501996005)
  ·
    refine ⟨4006902865936921969124251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21370148618330250501996005 4006902865936921969124251)
    ·
      refine ⟨6010354298905382953686377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4006902865936921969124251 6010354298905382953686377)
      ·
        refine ⟨4507765724179037215264783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6010354298905382953686377 4507765724179037215264783)
        ·
          refine ⟨6761648586268555822897175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4507765724179037215264783 6761648586268555822897175)
          ·
            refine ⟨10142472879402833734345763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6761648586268555822897175 10142472879402833734345763)
            ·
              refine ⟨15213709319104250601518645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10142472879402833734345763 15213709319104250601518645)
              ·
                refine ⟨1426285248666023493892373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15213709319104250601518645 1426285248666023493892373)
                ·
                  refine ⟨66857121031219851276205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1426285248666023493892373 66857121031219851276205)
                  ·
                    rfl

theorem cell22_585917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 5, 6].length) (baseStart_585917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_585917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_585917 prefixEnd_585917 := by exact prefixLift 585917
  have htrace : WordTrace (prefixWord ++ tailWord_585917) baseStart_585917 baseEnd_585917 := by
    simpa [prefixWord, tailWord_585917, baseEnd_585917] using wordTrace_append hprefix tailTrace_585917
  have hstable : (prefixWord ++ tailWord_585917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585917).length < 2 ^ (prefixWord ++ tailWord_585917).sum := by decide
  have hdescent : baseEnd_585917 < baseStart_585917 := by decide
  rcases family_descends (prefixWord ++ tailWord_585917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585921 : List Nat := [1, 2, 6, 1, 2, 1, 1, 1, 2, 5]
def baseStart_585921 : Nat := 118140960795 + 585921 * 2 ^ 59
def prefixEnd_585921 : Nat := 4983230072969 + 3 ^ 40 * 585921 * 2
def baseEnd_585921 : Nat := 200572732375404876728603

theorem tailTrace_585921 : CollatzResearch.WordTrace tailWord_585921 prefixEnd_585921 200572732375404876728603 := by
  unfold tailWord_585921
  simp only [CollatzResearch.WordTrace]
  refine ⟨21370294510315759185141617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14246863006877172790094411 21370294510315759185141617)
  ·
    refine ⟨16027720882736819388856213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21370294510315759185141617 16027720882736819388856213)
    ·
      refine ⟨751299416378288408852635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 16027720882736819388856213 751299416378288408852635)
      ·
        refine ⟨1126949124567432613278953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 751299416378288408852635 1126949124567432613278953)
        ·
          refine ⟨845211843425574459959215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1126949124567432613278953 845211843425574459959215)
          ·
            refine ⟨1267817765138361689938823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 845211843425574459959215 1267817765138361689938823)
            ·
              refine ⟨1901726647707542534908235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1267817765138361689938823 1901726647707542534908235)
              ·
                refine ⟨2852589971561313802362353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1901726647707542534908235 2852589971561313802362353)
                ·
                  refine ⟨2139442478670985351771765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2852589971561313802362353 2139442478670985351771765)
                  ·
                    refine ⟨200572732375404876728603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2139442478670985351771765 200572732375404876728603)
                    ·
                      rfl

theorem cell22_585921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_585921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_585921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_585921 prefixEnd_585921 := by exact prefixLift 585921
  have htrace : WordTrace (prefixWord ++ tailWord_585921) baseStart_585921 baseEnd_585921 := by
    simpa [prefixWord, tailWord_585921, baseEnd_585921] using wordTrace_append hprefix tailTrace_585921
  have hstable : (prefixWord ++ tailWord_585921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585921).length < 2 ^ (prefixWord ++ tailWord_585921).sum := by decide
  have hdescent : baseEnd_585921 < baseStart_585921 := by decide
  rcases family_descends (prefixWord ++ tailWord_585921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585934 : List Nat := [4, 1, 1, 1, 4, 2, 1, 2, 6]
def baseStart_585934 : Nat := 118140960795 + 585934 * 2 ^ 59
def prefixEnd_585934 : Nat := 4983230072969 + 3 ^ 40 * 585934 * 2
def baseEnd_585934 : Nat := 66859060847025725384521

theorem tailTrace_585934 : CollatzResearch.WordTrace tailWord_585934 prefixEnd_585934 66859060847025725384521 := by
  unfold tailWord_585934
  simp only [CollatzResearch.WordTrace]
  refine ⟨2671346082408582800670607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14247179106179108270243237 2671346082408582800670607)
  ·
    refine ⟨4007019123612874201005911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2671346082408582800670607 4007019123612874201005911)
    ·
      refine ⟨6010528685419311301508867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4007019123612874201005911 6010528685419311301508867)
      ·
        refine ⟨9015793028128966952263301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6010528685419311301508867 9015793028128966952263301)
        ·
          refine ⟨1690461192774181303549369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9015793028128966952263301 1690461192774181303549369)
          ·
            refine ⟨1267845894580635977662027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1690461192774181303549369 1267845894580635977662027)
            ·
              refine ⟨1901768841870953966493041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1267845894580635977662027 1901768841870953966493041)
              ·
                refine ⟨1426326631403215474869781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1901768841870953966493041 1426326631403215474869781)
                ·
                  refine ⟨66859060847025725384521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1426326631403215474869781 66859060847025725384521)
                  ·
                    rfl

theorem cell22_585934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 2, 6].length) (baseStart_585934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_585934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_585934 prefixEnd_585934 := by exact prefixLift 585934
  have htrace : WordTrace (prefixWord ++ tailWord_585934) baseStart_585934 baseEnd_585934 := by
    simpa [prefixWord, tailWord_585934, baseEnd_585934] using wordTrace_append hprefix tailTrace_585934
  have hstable : (prefixWord ++ tailWord_585934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585934).length < 2 ^ (prefixWord ++ tailWord_585934).sum := by decide
  have hdescent : baseEnd_585934 < baseStart_585934 := by decide
  rcases family_descends (prefixWord ++ tailWord_585934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585962 : List Nat := [3, 1, 3, 1, 1, 2, 11]
def baseStart_585962 : Nat := 118140960795 + 585962 * 2 ^ 59
def prefixEnd_585962 : Nat := 4983230072969 + 3 ^ 40 * 585962 * 2
def baseEnd_585962 : Nat := 7429139537529423572351

theorem tailTrace_585962 : CollatzResearch.WordTrace tailWord_585962 prefixEnd_585962 7429139537529423572351 := by
  unfold tailWord_585962
  simp only [CollatzResearch.WordTrace]
  refine ⟨5342947475791805796846035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14247859935444815458256093 5342947475791805796846035)
  ·
    refine ⟨8014421213687708695269053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5342947475791805796846035 8014421213687708695269053)
    ·
      refine ⟨3005407955132890760725895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8014421213687708695269053 3005407955132890760725895)
      ·
        refine ⟨4508111932699336141088843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3005407955132890760725895 4508111932699336141088843)
        ·
          refine ⟨6762167899049004211633265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4508111932699336141088843 6762167899049004211633265)
          ·
            refine ⟨5071625924286753158724949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6762167899049004211633265 5071625924286753158724949)
            ·
              refine ⟨7429139537529423572351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 5071625924286753158724949 7429139537529423572351)
              ·
                rfl

theorem cell22_585962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 11].length) (baseStart_585962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_585962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_585962 prefixEnd_585962 := by exact prefixLift 585962
  have htrace : WordTrace (prefixWord ++ tailWord_585962) baseStart_585962 baseEnd_585962 := by
    simpa [prefixWord, tailWord_585962, baseEnd_585962] using wordTrace_append hprefix tailTrace_585962
  have hstable : (prefixWord ++ tailWord_585962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585962).length < 2 ^ (prefixWord ++ tailWord_585962).sum := by decide
  have hdescent : baseEnd_585962 < baseStart_585962 := by decide
  rcases family_descends (prefixWord ++ tailWord_585962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586041 : List Nat := [1, 2, 1, 6, 1, 2, 1, 3, 5]
def baseStart_586041 : Nat := 118140960795 + 586041 * 2 ^ 59
def prefixEnd_586041 : Nat := 4983230072969 + 3 ^ 40 * 586041 * 2
def baseEnd_586041 : Nat := 66871270275921521242745

theorem tailTrace_586041 : CollatzResearch.WordTrace tailWord_586041 prefixEnd_586041 66871270275921521242745 := by
  unfold tailWord_586041
  simp only [CollatzResearch.WordTrace]
  refine ⟨21374671269881019679509977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14249780846587346453006651 21374671269881019679509977)
  ·
    refine ⟨16031003452410764759632483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21374671269881019679509977 16031003452410764759632483)
    ·
      refine ⟨24046505178616147139448725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16031003452410764759632483 24046505178616147139448725)
      ·
        refine ⟨1127179930247631897161659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 24046505178616147139448725 1127179930247631897161659)
        ·
          refine ⟨1690769895371447845742489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1127179930247631897161659 1690769895371447845742489)
          ·
            refine ⟨1268077421528585884306867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1690769895371447845742489 1268077421528585884306867)
            ·
              refine ⟨1902116132292878826460301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1268077421528585884306867 1902116132292878826460301)
              ·
                refine ⟨713293549609829559922613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1902116132292878826460301 713293549609829559922613)
                ·
                  refine ⟨66871270275921521242745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 713293549609829559922613 66871270275921521242745)
                  ·
                    rfl

theorem cell22_586041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 3, 5].length) (baseStart_586041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_586041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_586041 prefixEnd_586041 := by exact prefixLift 586041
  have htrace : WordTrace (prefixWord ++ tailWord_586041) baseStart_586041 baseEnd_586041 := by
    simpa [prefixWord, tailWord_586041, baseEnd_586041] using wordTrace_append hprefix tailTrace_586041
  have hstable : (prefixWord ++ tailWord_586041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586041).length < 2 ^ (prefixWord ++ tailWord_586041).sum := by decide
  have hdescent : baseEnd_586041 < baseStart_586041 := by decide
  rcases family_descends (prefixWord ++ tailWord_586041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586084 : List Nat := [2, 3, 1, 1, 3, 1, 1, 2, 3, 5]
def baseStart_586084 : Nat := 118140960795 + 586084 * 2 ^ 59
def prefixEnd_586084 : Nat := 4983230072969 + 3 ^ 40 * 586084 * 2
def baseEnd_586084 : Nat := 200628530606526784903103

theorem tailTrace_586084 : CollatzResearch.WordTrace tailWord_586084 prefixEnd_586084 200628530606526784903103 := by
  unfold tailWord_586084
  simp only [CollatzResearch.WordTrace]
  refine ⟨10688119804362619011662653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14250826405816825348883537 10688119804362619011662653)
  ·
    refine ⟨4008044926635982129373495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10688119804362619011662653 4008044926635982129373495)
    ·
      refine ⟨6012067389953973194060243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4008044926635982129373495 6012067389953973194060243)
      ·
        refine ⟨9018101084930959791090365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6012067389953973194060243 9018101084930959791090365)
        ·
          refine ⟨3381787906849109921658887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9018101084930959791090365 3381787906849109921658887)
          ·
            refine ⟨5072681860273664882488331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3381787906849109921658887 5072681860273664882488331)
            ·
              refine ⟨7609022790410497323732497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5072681860273664882488331 7609022790410497323732497)
              ·
                refine ⟨5706767092807872992799373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7609022790410497323732497 5706767092807872992799373)
                ·
                  refine ⟨2140037659802952372299765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5706767092807872992799373 2140037659802952372299765)
                  ·
                    refine ⟨200628530606526784903103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2140037659802952372299765 200628530606526784903103)
                    ·
                      rfl

theorem cell22_586084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 3, 5].length) (baseStart_586084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_586084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_586084 prefixEnd_586084 := by exact prefixLift 586084
  have htrace : WordTrace (prefixWord ++ tailWord_586084) baseStart_586084 baseEnd_586084 := by
    simpa [prefixWord, tailWord_586084, baseEnd_586084] using wordTrace_append hprefix tailTrace_586084
  have hstable : (prefixWord ++ tailWord_586084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586084).length < 2 ^ (prefixWord ++ tailWord_586084).sum := by decide
  have hdescent : baseEnd_586084 < baseStart_586084 := by decide
  rcases family_descends (prefixWord ++ tailWord_586084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586101 : List Nat := [1, 3, 4, 1, 2, 1, 1, 3, 1, 5]
def baseStart_586101 : Nat := 118140960795 + 586101 * 2 ^ 59
def prefixEnd_586101 : Nat := 4983230072969 + 3 ^ 40 * 586101 * 2
def baseEnd_586101 : Nat := 200634350053944407228051

theorem tailTrace_586101 : CollatzResearch.WordTrace tailWord_586101 prefixEnd_586101 200634350053944407228051 := by
  unfold tailWord_586101
  simp only [CollatzResearch.WordTrace]
  refine ⟨21376859649663649926694157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14251239766442433284462771 21376859649663649926694157)
  ·
    refine ⟨8016322368623868722510309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21376859649663649926694157 8016322368623868722510309)
    ·
      refine ⟨1503060444116975385470683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8016322368623868722510309 1503060444116975385470683)
      ·
        refine ⟨2254590666175463078206025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1503060444116975385470683 2254590666175463078206025)
        ·
          refine ⟨1690942999631597308654519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2254590666175463078206025 1690942999631597308654519)
          ·
            refine ⟨2536414499447395962981779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1690942999631597308654519 2536414499447395962981779)
            ·
              refine ⟨3804621749171093944472669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2536414499447395962981779 3804621749171093944472669)
              ·
                refine ⟨1426733155939160229177251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3804621749171093944472669 1426733155939160229177251)
                ·
                  refine ⟨2140099733908740343765877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1426733155939160229177251 2140099733908740343765877)
                  ·
                    refine ⟨200634350053944407228051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2140099733908740343765877 200634350053944407228051)
                    ·
                      rfl

theorem cell22_586101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_586101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_586101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_586101 prefixEnd_586101 := by exact prefixLift 586101
  have htrace : WordTrace (prefixWord ++ tailWord_586101) baseStart_586101 baseEnd_586101 := by
    simpa [prefixWord, tailWord_586101, baseEnd_586101] using wordTrace_append hprefix tailTrace_586101
  have hstable : (prefixWord ++ tailWord_586101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586101).length < 2 ^ (prefixWord ++ tailWord_586101).sum := by decide
  have hdescent : baseEnd_586101 < baseStart_586101 := by decide
  rcases family_descends (prefixWord ++ tailWord_586101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586122 : List Nat := [3, 1, 2, 5, 1, 2, 2, 1, 1, 4]
def baseStart_586122 : Nat := 118140960795 + 586122 * 2 ^ 59
def prefixEnd_586122 : Nat := 4983230072969 + 3 ^ 40 * 586122 * 2
def baseEnd_586122 : Nat := 200641538783107352452987

theorem tailTrace_586122 : CollatzResearch.WordTrace tailWord_586122 prefixEnd_586122 200641538783107352452987 := by
  unfold tailWord_586122
  simp only [CollatzResearch.WordTrace]
  refine ⟨5344406395646892628302155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14251750388391713675472413 5344406395646892628302155)
  ·
    refine ⟨8016609593470338942453233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5344406395646892628302155 8016609593470338942453233)
    ·
      refine ⟨6012457195102754206839925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8016609593470338942453233 6012457195102754206839925)
      ·
        refine ⟨563667862040883206891243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6012457195102754206839925 563667862040883206891243)
        ·
          refine ⟨845501793061324810336865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 563667862040883206891243 845501793061324810336865)
          ·
            refine ⟨634126344795993607752649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 845501793061324810336865 634126344795993607752649)
            ·
              refine ⟨475594758596995205814487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 634126344795993607752649 475594758596995205814487)
              ·
                refine ⟨713392137895492808721731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 475594758596995205814487 713392137895492808721731)
                ·
                  refine ⟨1070088206843239213082597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 713392137895492808721731 1070088206843239213082597)
                  ·
                    refine ⟨200641538783107352452987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1070088206843239213082597 200641538783107352452987)
                    ·
                      rfl

theorem cell22_586122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 2, 1, 1, 4].length) (baseStart_586122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_586122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_586122 prefixEnd_586122 := by exact prefixLift 586122
  have htrace : WordTrace (prefixWord ++ tailWord_586122) baseStart_586122 baseEnd_586122 := by
    simpa [prefixWord, tailWord_586122, baseEnd_586122] using wordTrace_append hprefix tailTrace_586122
  have hstable : (prefixWord ++ tailWord_586122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586122).length < 2 ^ (prefixWord ++ tailWord_586122).sum := by decide
  have hdescent : baseEnd_586122 < baseStart_586122 := by decide
  rcases family_descends (prefixWord ++ tailWord_586122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586152 : List Nat := [2, 1, 6, 1, 1, 2, 3, 1, 2, 3]
def baseStart_586152 : Nat := 118140960795 + 586152 * 2 ^ 59
def prefixEnd_586152 : Nat := 4983230072969 + 3 ^ 40 * 586152 * 2
def baseEnd_586152 : Nat := 200651808396197274202895

theorem tailTrace_586152 : CollatzResearch.WordTrace tailWord_586152 prefixEnd_586152 200651808396197274202895 := by
  unfold tailWord_586152
  simp only [CollatzResearch.WordTrace]
  refine ⟨10689359886239442818400355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14252479848319257091200473 10689359886239442818400355)
  ·
    refine ⟨16034039829359164227600533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10689359886239442818400355 16034039829359164227600533)
    ·
      refine ⟨751595617001210823168775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 16034039829359164227600533 751595617001210823168775)
      ·
        refine ⟨1127393425501816234753163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 751595617001210823168775 1127393425501816234753163)
        ·
          refine ⟨1691090138252724352129745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1127393425501816234753163 1691090138252724352129745)
          ·
            refine ⟨1268317603689543264097309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1691090138252724352129745 1268317603689543264097309)
            ·
              refine ⟨475619101383578724036491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1268317603689543264097309 475619101383578724036491)
              ·
                refine ⟨713428652075368086054737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 475619101383578724036491 713428652075368086054737)
                ·
                  refine ⟨535071489056526064541053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 713428652075368086054737 535071489056526064541053)
                  ·
                    refine ⟨200651808396197274202895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 535071489056526064541053 200651808396197274202895)
                    ·
                      rfl

theorem cell22_586152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_586152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_586152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_586152 prefixEnd_586152 := by exact prefixLift 586152
  have htrace : WordTrace (prefixWord ++ tailWord_586152) baseStart_586152 baseEnd_586152 := by
    simpa [prefixWord, tailWord_586152, baseEnd_586152] using wordTrace_append hprefix tailTrace_586152
  have hstable : (prefixWord ++ tailWord_586152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586152).length < 2 ^ (prefixWord ++ tailWord_586152).sum := by decide
  have hdescent : baseEnd_586152 < baseStart_586152 := by decide
  rcases family_descends (prefixWord ++ tailWord_586152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586165 : List Nat := [1, 3, 3, 2, 4, 1, 2, 6]
def baseStart_586165 : Nat := 118140960795 + 586165 * 2 ^ 59
def prefixEnd_586165 : Nat := 4983230072969 + 3 ^ 40 * 586165 * 2
def baseEnd_586165 : Nat := 22295139840207730403095

theorem tailTrace_586165 : CollatzResearch.WordTrace tailWord_586165 prefixEnd_586165 22295139840207730403095 := by
  unfold tailWord_586165
  simp only [CollatzResearch.WordTrace]
  refine ⟨21379193921431788857023949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14252795947621192571349299 21379193921431788857023949)
  ·
    refine ⟨8017197720536920821383981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21379193921431788857023949 8017197720536920821383981)
    ·
      refine ⟨3006449145201345308018993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8017197720536920821383981 3006449145201345308018993)
      ·
        refine ⟨2254836858901008981014245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3006449145201345308018993 2254836858901008981014245)
        ·
          refine ⟨422781911043939183940171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2254836858901008981014245 422781911043939183940171)
          ·
            refine ⟨634172866565908775910257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 422781911043939183940171 634172866565908775910257)
            ·
              refine ⟨475629649924431581932693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 634172866565908775910257 475629649924431581932693)
              ·
                refine ⟨22295139840207730403095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 475629649924431581932693 22295139840207730403095)
                ·
                  rfl

theorem cell22_586165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 2, 6].length) (baseStart_586165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_586165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_586165 prefixEnd_586165 := by exact prefixLift 586165
  have htrace : WordTrace (prefixWord ++ tailWord_586165) baseStart_586165 baseEnd_586165 := by
    simpa [prefixWord, tailWord_586165, baseEnd_586165] using wordTrace_append hprefix tailTrace_586165
  have hstable : (prefixWord ++ tailWord_586165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586165).length < 2 ^ (prefixWord ++ tailWord_586165).sum := by decide
  have hdescent : baseEnd_586165 < baseStart_586165 := by decide
  rcases family_descends (prefixWord ++ tailWord_586165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586197 : List Nat := [1, 3, 2, 3, 1, 3, 3, 2, 1, 3]
def baseStart_586197 : Nat := 118140960795 + 586197 * 2 ^ 59
def prefixEnd_586197 : Nat := 4983230072969 + 3 ^ 40 * 586197 * 2
def baseEnd_586197 : Nat := 200667212815832156827757

theorem tailTrace_586197 : CollatzResearch.WordTrace tailWord_586197 prefixEnd_586197 200667212815832156827757 := by
  unfold tailWord_586197
  simp only [CollatzResearch.WordTrace]
  refine ⟨21380361057315858322188845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14253574038210572214792563 21380361057315858322188845)
  ·
    refine ⟨8017635396493446870820817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21380361057315858322188845 8017635396493446870820817)
    ·
      refine ⟨6013226547370085153115613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8017635396493446870820817 6013226547370085153115613)
      ·
        refine ⟨2254959955263781932418355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6013226547370085153115613 2254959955263781932418355)
        ·
          refine ⟨3382439932895672898627533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2254959955263781932418355 3382439932895672898627533)
          ·
            refine ⟨1268414974835877336985325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3382439932895672898627533 1268414974835877336985325)
            ·
              refine ⟨475655615563454001369497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1268414974835877336985325 475655615563454001369497)
              ·
                refine ⟨356741711672590501027123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 475655615563454001369497 356741711672590501027123)
                ·
                  refine ⟨535112567508885751540685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 356741711672590501027123 535112567508885751540685)
                  ·
                    refine ⟨200667212815832156827757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 535112567508885751540685 200667212815832156827757)
                    ·
                      rfl

theorem cell22_586197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 3, 2, 1, 3].length) (baseStart_586197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_586197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_586197 prefixEnd_586197 := by exact prefixLift 586197
  have htrace : WordTrace (prefixWord ++ tailWord_586197) baseStart_586197 baseEnd_586197 := by
    simpa [prefixWord, tailWord_586197, baseEnd_586197] using wordTrace_append hprefix tailTrace_586197
  have hstable : (prefixWord ++ tailWord_586197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586197).length < 2 ^ (prefixWord ++ tailWord_586197).sum := by decide
  have hdescent : baseEnd_586197 < baseStart_586197 := by decide
  rcases family_descends (prefixWord ++ tailWord_586197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586266 : List Nat := [3, 1, 1, 3, 1, 1, 5, 7]
def baseStart_586266 : Nat := 118140960795 + 586266 * 2 ^ 59
def prefixEnd_586266 : Nat := 4983230072969 + 3 ^ 40 * 586266 * 2
def baseEnd_586266 : Nat := 22298981436215441872505

theorem tailTrace_586266 : CollatzResearch.WordTrace tailWord_586266 prefixEnd_586266 22298981436215441872505 := by
  unfold tailWord_586266
  simp only [CollatzResearch.WordTrace]
  refine ⟨5345719423516470776612663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14255251796043922070967101 5345719423516470776612663)
  ·
    refine ⟨8018579135274706164918995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5345719423516470776612663 8018579135274706164918995)
    ·
      refine ⟨12027868702912059247378493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8018579135274706164918995 12027868702912059247378493)
      ·
        refine ⟨4510450763592022217766935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12027868702912059247378493 4510450763592022217766935)
        ·
          refine ⟨6765676145388033326650403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4510450763592022217766935 6765676145388033326650403)
          ·
            refine ⟨10148514218082049989975605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6765676145388033326650403 10148514218082049989975605)
            ·
              refine ⟨951423207945192186560213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10148514218082049989975605 951423207945192186560213)
              ·
                refine ⟨22298981436215441872505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 951423207945192186560213 22298981436215441872505)
                ·
                  rfl

theorem cell22_586266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 7].length) (baseStart_586266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_586266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_586266 prefixEnd_586266 := by exact prefixLift 586266
  have htrace : WordTrace (prefixWord ++ tailWord_586266) baseStart_586266 baseEnd_586266 := by
    simpa [prefixWord, tailWord_586266, baseEnd_586266] using wordTrace_append hprefix tailTrace_586266
  have hstable : (prefixWord ++ tailWord_586266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586266).length < 2 ^ (prefixWord ++ tailWord_586266).sum := by decide
  have hdescent : baseEnd_586266 < baseStart_586266 := by decide
  rcases family_descends (prefixWord ++ tailWord_586266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586315 : List Nat := [1, 1, 1, 1, 3, 1, 6, 4, 1, 3]
def baseStart_586315 : Nat := 118140960795 + 586315 * 2 ^ 59
def prefixEnd_586315 : Nat := 4983230072969 + 3 ^ 40 * 586315 * 2
def baseEnd_586315 : Nat := 200707606627319182377395

theorem tailTrace_586315 : CollatzResearch.WordTrace tailWord_586315 prefixEnd_586315 200707606627319182377395 := by
  unfold tailWord_586315
  simp only [CollatzResearch.WordTrace]
  refine ⟨21384664870888364474984399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14256443247258909649989599 21384664870888364474984399)
  ·
    refine ⟨32076997306332546712476599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21384664870888364474984399 32076997306332546712476599)
    ·
      refine ⟨48115495959498820068714899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32076997306332546712476599 48115495959498820068714899)
      ·
        refine ⟨72173243939248230103072349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48115495959498820068714899 72173243939248230103072349)
        ·
          refine ⟨27064966477218086288652131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72173243939248230103072349 27064966477218086288652131)
          ·
            refine ⟨40597449715827129432978197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27064966477218086288652131 40597449715827129432978197)
            ·
              refine ⟨1903005455429396692170853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 40597449715827129432978197 1903005455429396692170853)
              ·
                refine ⟨356813522893011879782035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1903005455429396692170853 356813522893011879782035)
                ·
                  refine ⟨535220284339517819673053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 356813522893011879782035 535220284339517819673053)
                  ·
                    refine ⟨200707606627319182377395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 535220284339517819673053 200707606627319182377395)
                    ·
                      rfl

theorem cell22_586315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 4, 1, 3].length) (baseStart_586315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_586315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_586315 prefixEnd_586315 := by exact prefixLift 586315
  have htrace : WordTrace (prefixWord ++ tailWord_586315) baseStart_586315 baseEnd_586315 := by
    simpa [prefixWord, tailWord_586315, baseEnd_586315] using wordTrace_append hprefix tailTrace_586315
  have hstable : (prefixWord ++ tailWord_586315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586315).length < 2 ^ (prefixWord ++ tailWord_586315).sum := by decide
  have hdescent : baseEnd_586315 < baseStart_586315 := by decide
  rcases family_descends (prefixWord ++ tailWord_586315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586349 : List Nat := [1, 5, 1, 1, 3, 3, 1, 3, 1, 3]
def baseStart_586349 : Nat := 118140960795 + 586349 * 2 ^ 59
def prefixEnd_586349 : Nat := 4983230072969 + 3 ^ 40 * 586349 * 2
def baseEnd_586349 : Nat := 200719245522154427027291

theorem tailTrace_586349 : CollatzResearch.WordTrace tailWord_586349 prefixEnd_586349 200719245522154427027291 := by
  unfold tailWord_586349
  simp only [CollatzResearch.WordTrace]
  refine ⟨21385904952765188281722101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14257269968510125521148067 21385904952765188281722101)
  ·
    refine ⟨2004928589321736401411447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21385904952765188281722101 2004928589321736401411447)
    ·
      refine ⟨3007392883982604602117171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2004928589321736401411447 3007392883982604602117171)
      ·
        refine ⟨4511089325973906903175757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3007392883982604602117171 4511089325973906903175757)
        ·
          refine ⟨1691658497240215088690909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4511089325973906903175757 1691658497240215088690909)
          ·
            refine ⟨634371936465080658259091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1691658497240215088690909 634371936465080658259091)
            ·
              refine ⟨951557904697620987388637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 634371936465080658259091 951557904697620987388637)
              ·
                refine ⟨356834214261607870270739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 951557904697620987388637 356834214261607870270739)
                ·
                  refine ⟨535251321392411805406109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 356834214261607870270739 535251321392411805406109)
                  ·
                    refine ⟨200719245522154427027291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 535251321392411805406109 200719245522154427027291)
                    ·
                      rfl

theorem cell22_586349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 3, 1, 3].length) (baseStart_586349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_586349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_586349 prefixEnd_586349 := by exact prefixLift 586349
  have htrace : WordTrace (prefixWord ++ tailWord_586349) baseStart_586349 baseEnd_586349 := by
    simpa [prefixWord, tailWord_586349, baseEnd_586349] using wordTrace_append hprefix tailTrace_586349
  have hstable : (prefixWord ++ tailWord_586349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586349).length < 2 ^ (prefixWord ++ tailWord_586349).sum := by decide
  have hdescent : baseEnd_586349 < baseStart_586349 := by decide
  rcases family_descends (prefixWord ++ tailWord_586349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586373 : List Nat := [1, 3, 1, 1, 4, 2, 3, 1, 6]
def baseStart_586373 : Nat := 118140960795 + 586373 * 2 ^ 59
def prefixEnd_586373 : Nat := 4983230072969 + 3 ^ 40 * 586373 * 2
def baseEnd_586373 : Nat := 66909153737542121475739

theorem tailTrace_586373 : CollatzResearch.WordTrace tailWord_586373 prefixEnd_586373 66909153737542121475739 := by
  unfold tailWord_586373
  simp only [CollatzResearch.WordTrace]
  refine ⟨21386780304678240380595773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14257853536452160253730515 21386780304678240380595773)
  ·
    refine ⟨8020042614254340142723415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21386780304678240380595773 8020042614254340142723415)
    ·
      refine ⟨12030063921381510214085123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8020042614254340142723415 12030063921381510214085123)
      ·
        refine ⟨18045095882072265321127685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12030063921381510214085123 18045095882072265321127685)
        ·
          refine ⟨3383455477888549747711441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18045095882072265321127685 3383455477888549747711441)
          ·
            refine ⟨2537591608416412310783581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3383455477888549747711441 2537591608416412310783581)
            ·
              refine ⟨951596853156154616543843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2537591608416412310783581 951596853156154616543843)
              ·
                refine ⟨1427395279734231924815765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 951596853156154616543843 1427395279734231924815765)
                ·
                  refine ⟨66909153737542121475739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1427395279734231924815765 66909153737542121475739)
                  ·
                    rfl

theorem cell22_586373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 1, 6].length) (baseStart_586373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_586373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_586373 prefixEnd_586373 := by exact prefixLift 586373
  have htrace : WordTrace (prefixWord ++ tailWord_586373) baseStart_586373 baseEnd_586373 := by
    simpa [prefixWord, tailWord_586373, baseEnd_586373] using wordTrace_append hprefix tailTrace_586373
  have hstable : (prefixWord ++ tailWord_586373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586373).length < 2 ^ (prefixWord ++ tailWord_586373).sum := by decide
  have hdescent : baseEnd_586373 < baseStart_586373 := by decide
  rcases family_descends (prefixWord ++ tailWord_586373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586452 : List Nat := [2, 4, 1, 3, 2, 1, 3, 6]
def baseStart_586452 : Nat := 118140960795 + 586452 * 2 ^ 59
def prefixEnd_586452 : Nat := 4983230072969 + 3 ^ 40 * 586452 * 2
def baseEnd_586452 : Nat := 22306056058566276855775

theorem tailTrace_586452 : CollatzResearch.WordTrace tailWord_586452 prefixEnd_586452 22306056058566276855775 := by
  unfold tailWord_586452
  simp only [CollatzResearch.WordTrace]
  refine ⟨10694830835696018436360805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14259774447594691248481073 10694830835696018436360805)
  ·
    refine ⟨2005280781693003456817651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10694830835696018436360805 2005280781693003456817651)
    ·
      refine ⟨3007921172539505185226477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2005280781693003456817651 3007921172539505185226477)
      ·
        refine ⟨1127970439702314444459929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3007921172539505185226477 1127970439702314444459929)
        ·
          refine ⟨845977829776735833344947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1127970439702314444459929 845977829776735833344947)
          ·
            refine ⟨1268966744665103750017421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 845977829776735833344947 1268966744665103750017421)
            ·
              refine ⟨475862529249413906256533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1268966744665103750017421 475862529249413906256533)
              ·
                refine ⟨22306056058566276855775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 475862529249413906256533 22306056058566276855775)
                ·
                  rfl

theorem cell22_586452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 3, 6].length) (baseStart_586452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_586452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_586452 prefixEnd_586452 := by exact prefixLift 586452
  have htrace : WordTrace (prefixWord ++ tailWord_586452) baseStart_586452 baseEnd_586452 := by
    simpa [prefixWord, tailWord_586452, baseEnd_586452] using wordTrace_append hprefix tailTrace_586452
  have hstable : (prefixWord ++ tailWord_586452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586452).length < 2 ^ (prefixWord ++ tailWord_586452).sum := by decide
  have hdescent : baseEnd_586452 < baseStart_586452 := by decide
  rcases family_descends (prefixWord ++ tailWord_586452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586540 : List Nat := [2, 2, 1, 1, 1, 4, 1, 3, 4, 3]
def baseStart_586540 : Nat := 118140960795 + 586540 * 2 ^ 59
def prefixEnd_586540 : Nat := 4983230072969 + 3 ^ 40 * 586540 * 2
def baseEnd_586540 : Nat := 200784628725493595501705

theorem tailTrace_586540 : CollatzResearch.WordTrace tailWord_586540 prefixEnd_586540 200784628725493595501705 := by
  unfold tailWord_586540
  simp only [CollatzResearch.WordTrace]
  refine ⟨10696435647536613950962537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14261914196715485267950049 10696435647536613950962537)
  ·
    refine ⟨8022326735652460463221903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10696435647536613950962537 8022326735652460463221903)
    ·
      refine ⟨12033490103478690694832855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8022326735652460463221903 12033490103478690694832855)
      ·
        refine ⟨18050235155218036042249283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12033490103478690694832855 18050235155218036042249283)
        ·
          refine ⟨27075352732827054063373925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18050235155218036042249283 27075352732827054063373925)
          ·
            refine ⟨5076628637405072636882611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27075352732827054063373925 5076628637405072636882611)
            ·
              refine ⟨7614942956107608955323917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5076628637405072636882611 7614942956107608955323917)
              ·
                refine ⟨2855603608540353358246469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7614942956107608955323917 2855603608540353358246469)
                ·
                  refine ⟨535425676601316254671213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2855603608540353358246469 535425676601316254671213)
                  ·
                    refine ⟨200784628725493595501705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 535425676601316254671213 200784628725493595501705)
                    ·
                      rfl

theorem cell22_586540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 3].length) (baseStart_586540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_586540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_586540 prefixEnd_586540 := by exact prefixLift 586540
  have htrace : WordTrace (prefixWord ++ tailWord_586540) baseStart_586540 baseEnd_586540 := by
    simpa [prefixWord, tailWord_586540, baseEnd_586540] using wordTrace_append hprefix tailTrace_586540
  have hstable : (prefixWord ++ tailWord_586540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586540).length < 2 ^ (prefixWord ++ tailWord_586540).sum := by decide
  have hdescent : baseEnd_586540 < baseStart_586540 := by decide
  rcases family_descends (prefixWord ++ tailWord_586540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586542 : List Nat := [4, 1, 3, 2, 1, 1, 3, 1, 6]
def baseStart_586542 : Nat := 118140960795 + 586542 * 2 ^ 59
def prefixEnd_586542 : Nat := 4983230072969 + 3 ^ 40 * 586542 * 2
def baseEnd_586542 : Nat := 66928437788788752317233

theorem tailTrace_586542 : CollatzResearch.WordTrace tailWord_586542 prefixEnd_586542 66928437788788752317233 := by
  unfold tailWord_586542
  simp only [CollatzResearch.WordTrace]
  refine ⟨2674118030133247780437235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14261962827377321495665253 2674118030133247780437235)
  ·
    refine ⟨4011177045199871670655853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2674118030133247780437235 4011177045199871670655853)
    ·
      refine ⟨1504191391949951876495945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4011177045199871670655853 1504191391949951876495945)
      ·
        refine ⟨1128143543962463907371959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1504191391949951876495945 1128143543962463907371959)
        ·
          refine ⟨1692215315943695861057939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1128143543962463907371959 1692215315943695861057939)
          ·
            refine ⟨2538322973915543791586909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1692215315943695861057939 2538322973915543791586909)
            ·
              refine ⟨951871115218328921845091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2538322973915543791586909 951871115218328921845091)
              ·
                refine ⟨1427806672827493382767637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 951871115218328921845091 1427806672827493382767637)
                ·
                  refine ⟨66928437788788752317233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1427806672827493382767637 66928437788788752317233)
                  ·
                    rfl

theorem cell22_586542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 1, 6].length) (baseStart_586542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_586542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_586542 prefixEnd_586542 := by exact prefixLift 586542
  have htrace : WordTrace (prefixWord ++ tailWord_586542) baseStart_586542 baseEnd_586542 := by
    simpa [prefixWord, tailWord_586542, baseEnd_586542] using wordTrace_append hprefix tailTrace_586542
  have hstable : (prefixWord ++ tailWord_586542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586542).length < 2 ^ (prefixWord ++ tailWord_586542).sum := by decide
  have hdescent : baseEnd_586542 < baseStart_586542 := by decide
  rcases family_descends (prefixWord ++ tailWord_586542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586561 : List Nat := [1, 2, 5, 3, 1, 2, 1, 2, 1, 4]
def baseStart_586561 : Nat := 118140960795 + 586561 * 2 ^ 59
def prefixEnd_586561 : Nat := 4983230072969 + 3 ^ 40 * 586561 * 2
def baseEnd_586561 : Nat := 200791817454656540726641

theorem tailTrace_586561 : CollatzResearch.WordTrace tailWord_586561 prefixEnd_586561 200791817454656540726641 := by
  unfold tailWord_586561
  simp only [CollatzResearch.WordTrace]
  refine ⟨21393637227997148488439537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14262424818664765658959691 21393637227997148488439537)
  ·
    refine ⟨16045227920997861366329653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21393637227997148488439537 16045227920997861366329653)
    ·
      refine ⟨1504240117593549503093405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16045227920997861366329653 1504240117593549503093405)
      ·
        refine ⟨564090044097581063660027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1504240117593549503093405 564090044097581063660027)
        ·
          refine ⟨846135066146371595490041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 564090044097581063660027 846135066146371595490041)
          ·
            refine ⟨634601299609778696617531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 846135066146371595490041 634601299609778696617531)
            ·
              refine ⟨951901949414668044926297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 634601299609778696617531 951901949414668044926297)
              ·
                refine ⟨713926462061001033694723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 951901949414668044926297 713926462061001033694723)
                ·
                  refine ⟨1070889693091501550542085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 713926462061001033694723 1070889693091501550542085)
                  ·
                    refine ⟨200791817454656540726641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1070889693091501550542085 200791817454656540726641)
                    ·
                      rfl

theorem cell22_586561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_586561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_586561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_586561 prefixEnd_586561 := by exact prefixLift 586561
  have htrace : WordTrace (prefixWord ++ tailWord_586561) baseStart_586561 baseEnd_586561 := by
    simpa [prefixWord, tailWord_586561, baseEnd_586561] using wordTrace_append hprefix tailTrace_586561
  have hstable : (prefixWord ++ tailWord_586561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586561).length < 2 ^ (prefixWord ++ tailWord_586561).sum := by decide
  have hdescent : baseEnd_586561 < baseStart_586561 := by decide
  rcases family_descends (prefixWord ++ tailWord_586561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586572 : List Nat := [2, 2, 1, 3, 3, 2, 2, 1, 2, 4]
def baseStart_586572 : Nat := 118140960795 + 586572 * 2 ^ 59
def prefixEnd_586572 : Nat := 4983230072969 + 3 ^ 40 * 586572 * 2
def baseEnd_586572 : Nat := 200795582979456178701607

theorem tailTrace_586572 : CollatzResearch.WordTrace tailWord_586572 prefixEnd_586572 200795582979456178701607 := by
  unfold tailWord_586572
  simp only [CollatzResearch.WordTrace]
  refine ⟨10697019215478648683544985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14262692287304864911393313 10697019215478648683544985)
  ·
    refine ⟨8022764411608986512658739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10697019215478648683544985 8022764411608986512658739)
    ·
      refine ⟨12034146617413479768988109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8022764411608986512658739 12034146617413479768988109)
      ·
        refine ⟨4512804981530054913370541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12034146617413479768988109 4512804981530054913370541)
        ·
          refine ⟨1692301868073770592513953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4512804981530054913370541 1692301868073770592513953)
          ·
            refine ⟨1269226401055327944385465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1692301868073770592513953 1269226401055327944385465)
            ·
              refine ⟨951919800791495958289099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1269226401055327944385465 951919800791495958289099)
              ·
                refine ⟨1427879701187243937433649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 951919800791495958289099 1427879701187243937433649)
                ·
                  refine ⟨1070909775890432953075237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1427879701187243937433649 1070909775890432953075237)
                  ·
                    refine ⟨200795582979456178701607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1070909775890432953075237 200795582979456178701607)
                    ·
                      rfl

theorem cell22_586572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 1, 2, 4].length) (baseStart_586572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_586572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_586572 prefixEnd_586572 := by exact prefixLift 586572
  have htrace : WordTrace (prefixWord ++ tailWord_586572) baseStart_586572 baseEnd_586572 := by
    simpa [prefixWord, tailWord_586572, baseEnd_586572] using wordTrace_append hprefix tailTrace_586572
  have hstable : (prefixWord ++ tailWord_586572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586572).length < 2 ^ (prefixWord ++ tailWord_586572).sum := by decide
  have hdescent : baseEnd_586572 < baseStart_586572 := by decide
  rcases family_descends (prefixWord ++ tailWord_586572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586600 : List Nat := [2, 1, 4, 2, 1, 2, 1, 1, 2, 6]
def baseStart_586600 : Nat := 118140960795 + 586600 * 2 ^ 59
def prefixEnd_586600 : Nat := 4983230072969 + 3 ^ 40 * 586600 * 2
def baseEnd_586600 : Nat := 200805167951673439001521

theorem tailTrace_586600 : CollatzResearch.WordTrace tailWord_586600 prefixEnd_586600 200805167951673439001521 := by
  unfold tailWord_586600
  simp only [CollatzResearch.WordTrace]
  refine ⟨10697529837427929074554627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14263373116570572099406169 10697529837427929074554627)
  ·
    refine ⟨16046294756141893611831941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10697529837427929074554627 16046294756141893611831941)
    ·
      refine ⟨3008680266776605052218489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16046294756141893611831941 3008680266776605052218489)
      ·
        refine ⟨2256510200082453789163867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3008680266776605052218489 2256510200082453789163867)
        ·
          refine ⟨3384765300123680683745801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2256510200082453789163867 3384765300123680683745801)
          ·
            refine ⟨2538573975092760512809351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3384765300123680683745801 2538573975092760512809351)
            ·
              refine ⟨3807860962639140769214027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2538573975092760512809351 3807860962639140769214027)
              ·
                refine ⟨5711791443958711153821041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3807860962639140769214027 5711791443958711153821041)
                ·
                  refine ⟨4283843582969033365365781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5711791443958711153821041 4283843582969033365365781)
                  ·
                    refine ⟨200805167951673439001521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4283843582969033365365781 200805167951673439001521)
                    ·
                      rfl

theorem cell22_586600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_586600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_586600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_586600 prefixEnd_586600 := by exact prefixLift 586600
  have htrace : WordTrace (prefixWord ++ tailWord_586600) baseStart_586600 baseEnd_586600 := by
    simpa [prefixWord, tailWord_586600, baseEnd_586600] using wordTrace_append hprefix tailTrace_586600
  have hstable : (prefixWord ++ tailWord_586600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586600).length < 2 ^ (prefixWord ++ tailWord_586600).sum := by decide
  have hdescent : baseEnd_586600 < baseStart_586600 := by decide
  rcases family_descends (prefixWord ++ tailWord_586600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586675 : List Nat := [1, 1, 1, 2, 3, 1, 2, 5, 1, 5]
def baseStart_586675 : Nat := 118140960795 + 586675 * 2 ^ 59
def prefixEnd_586675 : Nat := 4983230072969 + 3 ^ 40 * 586675 * 2
def baseEnd_586675 : Nat := 200830841984398243376291

theorem tailTrace_586675 : CollatzResearch.WordTrace tailWord_586675 prefixEnd_586675 200830841984398243376291 := by
  unfold tailWord_586675
  simp only [CollatzResearch.WordTrace]
  refine ⟨21397795149584145958089479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14265196766389430638726319 21397795149584145958089479)
  ·
    refine ⟨32096692724376218937134219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21397795149584145958089479 32096692724376218937134219)
    ·
      refine ⟨48145039086564328405701329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32096692724376218937134219 48145039086564328405701329)
      ·
        refine ⟨36108779314923246304275997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48145039086564328405701329 36108779314923246304275997)
        ·
          refine ⟨13540792243096217364103499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36108779314923246304275997 13540792243096217364103499)
          ·
            refine ⟨20311188364644326046155249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13540792243096217364103499 20311188364644326046155249)
            ·
              refine ⟨15233391273483244534616437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20311188364644326046155249 15233391273483244534616437)
              ·
                refine ⟨1428130431889054175120291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15233391273483244534616437 1428130431889054175120291)
                ·
                  refine ⟨2142195647833581262680437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1428130431889054175120291 2142195647833581262680437)
                  ·
                    refine ⟨200830841984398243376291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2142195647833581262680437 200830841984398243376291)
                    ·
                      rfl

theorem cell22_586675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 5, 1, 5].length) (baseStart_586675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_586675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_586675 prefixEnd_586675 := by exact prefixLift 586675
  have htrace : WordTrace (prefixWord ++ tailWord_586675) baseStart_586675 baseEnd_586675 := by
    simpa [prefixWord, tailWord_586675, baseEnd_586675] using wordTrace_append hprefix tailTrace_586675
  have hstable : (prefixWord ++ tailWord_586675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586675).length < 2 ^ (prefixWord ++ tailWord_586675).sum := by decide
  have hdescent : baseEnd_586675 < baseStart_586675 := by decide
  rcases family_descends (prefixWord ++ tailWord_586675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586829 : List Nat := [1, 6, 1, 1, 1, 2, 1, 3, 6]
def baseStart_586829 : Nat := 118140960795 + 586829 * 2 ^ 59
def prefixEnd_586829 : Nat := 4983230072969 + 3 ^ 40 * 586829 * 2
def baseEnd_586829 : Nat := 66961186443864391675273

theorem tailTrace_586829 : CollatzResearch.WordTrace tailWord_586829 prefixEnd_586829 66961186443864391675273 := by
  unfold tailWord_586829
  simp only [CollatzResearch.WordTrace]
  refine ⟨21403411991026230259195541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14268941327350820172797027 21403411991026230259195541)
  ·
    refine ⟨1003284937079354543399791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 21403411991026230259195541 1003284937079354543399791)
    ·
      refine ⟨1504927405619031815099687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1003284937079354543399791 1504927405619031815099687)
      ·
        refine ⟨2257391108428547722649531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1504927405619031815099687 2257391108428547722649531)
        ·
          refine ⟨3386086662642821583974297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2257391108428547722649531 3386086662642821583974297)
          ·
            refine ⟨2539564996982116187980723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3386086662642821583974297 2539564996982116187980723)
            ·
              refine ⟨3809347495473174281971085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2539564996982116187980723 3809347495473174281971085)
              ·
                refine ⟨1428505310802440355739157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3809347495473174281971085 1428505310802440355739157)
                ·
                  refine ⟨66961186443864391675273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1428505310802440355739157 66961186443864391675273)
                  ·
                    rfl

theorem cell22_586829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_586829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_586829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_586829 prefixEnd_586829 := by exact prefixLift 586829
  have htrace : WordTrace (prefixWord ++ tailWord_586829) baseStart_586829 baseEnd_586829 := by
    simpa [prefixWord, tailWord_586829, baseEnd_586829] using wordTrace_append hprefix tailTrace_586829
  have hstable : (prefixWord ++ tailWord_586829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586829).length < 2 ^ (prefixWord ++ tailWord_586829).sum := by decide
  have hdescent : baseEnd_586829 < baseStart_586829 := by decide
  rcases family_descends (prefixWord ++ tailWord_586829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586842 : List Nat := [3, 1, 1, 2, 1, 1, 2, 1, 6, 4]
def baseStart_586842 : Nat := 118140960795 + 586842 * 2 ^ 59
def prefixEnd_586842 : Nat := 4983230072969 + 3 ^ 40 * 586842 * 2
def baseEnd_586842 : Nat := 200888009497265474450779

theorem tailTrace_586842 : CollatzResearch.WordTrace tailWord_586842 prefixEnd_586842 200888009497265474450779 := by
  unfold tailWord_586842
  simp only [CollatzResearch.WordTrace]
  refine ⟨5350971534994783369854695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14269257426652755652945853 5350971534994783369854695)
  ·
    refine ⟨8026457302492175054782043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5350971534994783369854695 8026457302492175054782043)
    ·
      refine ⟨12039685953738262582173065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8026457302492175054782043 12039685953738262582173065)
      ·
        refine ⟨9029764465303696936629799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12039685953738262582173065 9029764465303696936629799)
        ·
          refine ⟨13544646697955545404944699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9029764465303696936629799 13544646697955545404944699)
          ·
            refine ⟨20316970046933318107417049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13544646697955545404944699 20316970046933318107417049)
            ·
              refine ⟨15237727535199988580562787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20316970046933318107417049 15237727535199988580562787)
              ·
                refine ⟨22856591302799982870844181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15237727535199988580562787 22856591302799982870844181)
                ·
                  refine ⟨1071402717318749197070821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 22856591302799982870844181 1071402717318749197070821)
                  ·
                    refine ⟨200888009497265474450779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1071402717318749197070821 200888009497265474450779)
                    ·
                      rfl

theorem cell22_586842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 6, 4].length) (baseStart_586842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_586842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_586842 prefixEnd_586842 := by exact prefixLift 586842
  have htrace : WordTrace (prefixWord ++ tailWord_586842) baseStart_586842 baseEnd_586842 := by
    simpa [prefixWord, tailWord_586842, baseEnd_586842] using wordTrace_append hprefix tailTrace_586842
  have hstable : (prefixWord ++ tailWord_586842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586842).length < 2 ^ (prefixWord ++ tailWord_586842).sum := by decide
  have hdescent : baseEnd_586842 < baseStart_586842 := by decide
  rcases family_descends (prefixWord ++ tailWord_586842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586857 : List Nat := [1, 2, 1, 1, 1, 7, 1, 8]
def baseStart_586857 : Nat := 118140960795 + 586857 * 2 ^ 59
def prefixEnd_586857 : Nat := 4983230072969 + 3 ^ 40 * 586857 * 2
def baseEnd_586857 : Nat := 22321460478201159480637

theorem tailTrace_586857 : CollatzResearch.WordTrace tailWord_586857 prefixEnd_586857 22321460478201159480637 := by
  unfold tailWord_586857
  simp only [CollatzResearch.WordTrace]
  refine ⟨21404433234924791041214825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14269622156616527360809883 21404433234924791041214825)
  ·
    refine ⟨16053324926193593280911119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21404433234924791041214825 16053324926193593280911119)
    ·
      refine ⟨24079987389290389921366679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16053324926193593280911119 24079987389290389921366679)
      ·
        refine ⟨36119981083935584882050019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24079987389290389921366679 36119981083935584882050019)
        ·
          refine ⟨54179971625903377323075029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36119981083935584882050019 54179971625903377323075029)
          ·
            refine ⟨1269843084982110406009571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 54179971625903377323075029 1269843084982110406009571)
            ·
              refine ⟨1904764627473165609014357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1269843084982110406009571 1904764627473165609014357)
              ·
                refine ⟨22321460478201159480637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1904764627473165609014357 22321460478201159480637)
                ·
                  rfl

theorem cell22_586857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 8].length) (baseStart_586857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_586857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_586857 prefixEnd_586857 := by exact prefixLift 586857
  have htrace : WordTrace (prefixWord ++ tailWord_586857) baseStart_586857 baseEnd_586857 := by
    simpa [prefixWord, tailWord_586857, baseEnd_586857] using wordTrace_append hprefix tailTrace_586857
  have hstable : (prefixWord ++ tailWord_586857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586857).length < 2 ^ (prefixWord ++ tailWord_586857).sum := by decide
  have hdescent : baseEnd_586857 < baseStart_586857 := by decide
  rcases family_descends (prefixWord ++ tailWord_586857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586887 : List Nat := [1, 1, 4, 2, 1, 1, 1, 3, 2, 6]
def baseStart_586887 : Nat := 118140960795 + 586887 * 2 ^ 59
def prefixEnd_586887 : Nat := 4983230072969 + 3 ^ 40 * 586887 * 2
def baseEnd_586887 : Nat := 200903413916900357075641

theorem tailTrace_586887 : CollatzResearch.WordTrace tailWord_586887 prefixEnd_586887 200903413916900357075641 := by
  unfold tailWord_586887
  simp only [CollatzResearch.WordTrace]
  refine ⟨21405527424816106164806915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14270351616544070776537943 21405527424816106164806915)
  ·
    refine ⟨32108291137224159247210373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21405527424816106164806915 32108291137224159247210373)
    ·
      refine ⟨6020304588229529858851945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32108291137224159247210373 6020304588229529858851945)
      ·
        refine ⟨4515228441172147394138959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6020304588229529858851945 4515228441172147394138959)
        ·
          refine ⟨6772842661758221091208439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4515228441172147394138959 6772842661758221091208439)
          ·
            refine ⟨10159263992637331636812659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6772842661758221091208439 10159263992637331636812659)
            ·
              refine ⟨15238895988955997455218989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10159263992637331636812659 15238895988955997455218989)
              ·
                refine ⟨5714585995858499045707121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15238895988955997455218989 5714585995858499045707121)
                ·
                  refine ⟨4285939496893874284280341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5714585995858499045707121 4285939496893874284280341)
                  ·
                    refine ⟨200903413916900357075641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4285939496893874284280341 200903413916900357075641)
                    ·
                      rfl

theorem cell22_586887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 2, 6].length) (baseStart_586887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_586887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_586887 prefixEnd_586887 := by exact prefixLift 586887
  have htrace : WordTrace (prefixWord ++ tailWord_586887) baseStart_586887 baseEnd_586887 := by
    simpa [prefixWord, tailWord_586887, baseEnd_586887] using wordTrace_append hprefix tailTrace_586887
  have hstable : (prefixWord ++ tailWord_586887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586887).length < 2 ^ (prefixWord ++ tailWord_586887).sum := by decide
  have hdescent : baseEnd_586887 < baseStart_586887 := by decide
  rcases family_descends (prefixWord ++ tailWord_586887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586940 : List Nat := [2, 2, 2, 3, 2, 1, 4, 2, 1, 3]
def baseStart_586940 : Nat := 118140960795 + 586940 * 2 ^ 59
def prefixEnd_586940 : Nat := 4983230072969 + 3 ^ 40 * 586940 * 2
def baseEnd_586940 : Nat := 200921556900025885500479

theorem tailTrace_586940 : CollatzResearch.WordTrace tailWord_586940 prefixEnd_586940 200921556900025885500479 := by
  unfold tailWord_586940
  simp only [CollatzResearch.WordTrace]
  refine ⟨10703730246812048108243137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14271640329082730810990849 10703730246812048108243137)
  ·
    refine ⟨8027797685109036081182353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10703730246812048108243137 8027797685109036081182353)
    ·
      refine ⟨6020848263831777060886765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8027797685109036081182353 6020848263831777060886765)
      ·
        refine ⟨2257818098936916397832537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6020848263831777060886765 2257818098936916397832537)
        ·
          refine ⟨1693363574202687298374403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2257818098936916397832537 1693363574202687298374403)
          ·
            refine ⟨2540045361304030947561605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1693363574202687298374403 2540045361304030947561605)
            ·
              refine ⟨476258505244505802667801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2540045361304030947561605 476258505244505802667801)
              ·
                refine ⟨357193878933379352000851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 476258505244505802667801 357193878933379352000851)
                ·
                  refine ⟨535790818400069028001277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 357193878933379352000851 535790818400069028001277)
                  ·
                    refine ⟨200921556900025885500479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 535790818400069028001277 200921556900025885500479)
                    ·
                      rfl

theorem cell22_586940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 4, 2, 1, 3].length) (baseStart_586940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_586940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_586940 prefixEnd_586940 := by exact prefixLift 586940
  have htrace : WordTrace (prefixWord ++ tailWord_586940) baseStart_586940 baseEnd_586940 := by
    simpa [prefixWord, tailWord_586940, baseEnd_586940] using wordTrace_append hprefix tailTrace_586940
  have hstable : (prefixWord ++ tailWord_586940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586940).length < 2 ^ (prefixWord ++ tailWord_586940).sum := by decide
  have hdescent : baseEnd_586940 < baseStart_586940 := by decide
  rcases family_descends (prefixWord ++ tailWord_586940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586983 : List Nat := [1, 1, 5, 3, 2, 1, 1, 3, 1, 4]
def baseStart_586983 : Nat := 118140960795 + 586983 * 2 ^ 59
def prefixEnd_586983 : Nat := 4983230072969 + 3 ^ 40 * 586983 * 2
def baseEnd_586983 : Nat := 200936276678788106675347

theorem tailTrace_586983 : CollatzResearch.WordTrace tailWord_586983 prefixEnd_586983 200936276678788106675347 := by
  unfold tailWord_586983
  simp only [CollatzResearch.WordTrace]
  refine ⟨21409028832468314560301603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14272685888312209706867735 21409028832468314560301603)
  ·
    refine ⟨32113543248702471840452405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21409028832468314560301603 32113543248702471840452405)
    ·
      refine ⟨3010644679565856735042413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32113543248702471840452405 3010644679565856735042413)
      ·
        refine ⟨1128991754837196275640905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3010644679565856735042413 1128991754837196275640905)
        ·
          refine ⟨846743816127897206730679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1128991754837196275640905 846743816127897206730679)
          ·
            refine ⟨1270115724191845810096019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 846743816127897206730679 1270115724191845810096019)
            ·
              refine ⟨1905173586287768715144029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1270115724191845810096019 1905173586287768715144029)
              ·
                refine ⟨714440094857913268179011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1905173586287768715144029 714440094857913268179011)
                ·
                  refine ⟨1071660142286869902268517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 714440094857913268179011 1071660142286869902268517)
                  ·
                    refine ⟨200936276678788106675347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1071660142286869902268517 200936276678788106675347)
                    ·
                      rfl

theorem cell22_586983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_586983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_586983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_586983 prefixEnd_586983 := by exact prefixLift 586983
  have htrace : WordTrace (prefixWord ++ tailWord_586983) baseStart_586983 baseEnd_586983 := by
    simpa [prefixWord, tailWord_586983, baseEnd_586983] using wordTrace_append hprefix tailTrace_586983
  have hstable : (prefixWord ++ tailWord_586983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586983).length < 2 ^ (prefixWord ++ tailWord_586983).sum := by decide
  have hdescent : baseEnd_586983 < baseStart_586983 := by decide
  rcases family_descends (prefixWord ++ tailWord_586983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587013 : List Nat := [1, 3, 1, 1, 2, 1, 7, 1, 2, 3]
def baseStart_587013 : Nat := 118140960795 + 587013 * 2 ^ 59
def prefixEnd_587013 : Nat := 4983230072969 + 3 ^ 40 * 587013 * 2
def baseEnd_587013 : Nat := 200946546291878028425255

theorem tailTrace_587013 : CollatzResearch.WordTrace tailWord_587013 prefixEnd_587013 200946546291878028425255 := by
  unfold tailWord_587013
  simp only [CollatzResearch.WordTrace]
  refine ⟨21410123022359629683893693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14273415348239753122595795 21410123022359629683893693)
  ·
    refine ⟨8028796133384861131460135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21410123022359629683893693 8028796133384861131460135)
    ·
      refine ⟨12043194200077291697190203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8028796133384861131460135 12043194200077291697190203)
      ·
        refine ⟨18064791300115937545785305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12043194200077291697190203 18064791300115937545785305)
        ·
          refine ⟨13548593475086953159338979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18064791300115937545785305 13548593475086953159338979)
          ·
            refine ⟨20322890212630429739008469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13548593475086953159338979 20322890212630429739008469)
            ·
              refine ⟨476317739358525697008011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 20322890212630429739008469 476317739358525697008011)
              ·
                refine ⟨714476609037788545512017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 476317739358525697008011 714476609037788545512017)
                ·
                  refine ⟨535857456778341409134013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 714476609037788545512017 535857456778341409134013)
                  ·
                    refine ⟨200946546291878028425255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 535857456778341409134013 200946546291878028425255)
                    ·
                      rfl

theorem cell22_587013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 7, 1, 2, 3].length) (baseStart_587013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_587013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_587013 prefixEnd_587013 := by exact prefixLift 587013
  have htrace : WordTrace (prefixWord ++ tailWord_587013) baseStart_587013 baseEnd_587013 := by
    simpa [prefixWord, tailWord_587013, baseEnd_587013] using wordTrace_append hprefix tailTrace_587013
  have hstable : (prefixWord ++ tailWord_587013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587013).length < 2 ^ (prefixWord ++ tailWord_587013).sum := by decide
  have hdescent : baseEnd_587013 < baseStart_587013 := by decide
  rcases family_descends (prefixWord ++ tailWord_587013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587058 : List Nat := [3, 2, 1, 1, 4, 1, 3, 1, 3, 3]
def baseStart_587058 : Nat := 118140960795 + 587058 * 2 ^ 59
def prefixEnd_587058 : Nat := 4983230072969 + 3 ^ 40 * 587058 * 2
def baseEnd_587058 : Nat := 200961950711512911050117

theorem tailTrace_587058 : CollatzResearch.WordTrace tailWord_587058 prefixEnd_587058 200961950711512911050117 := by
  unfold tailWord_587058
  simp only [CollatzResearch.WordTrace]
  refine ⟨5352941076799150592320457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14274509538131068246187885 5352941076799150592320457)
  ·
    refine ⟨4014705807599362944240343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5352941076799150592320457 4014705807599362944240343)
    ·
      refine ⟨6022058711399044416360515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4014705807599362944240343 6022058711399044416360515)
      ·
        refine ⟨9033088067098566624540773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6022058711399044416360515 9033088067098566624540773)
        ·
          refine ⟨1693704012580981242101395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9033088067098566624540773 1693704012580981242101395)
          ·
            refine ⟨2540556018871471863152093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1693704012580981242101395 2540556018871471863152093)
            ·
              refine ⟨952708507076801948682035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2540556018871471863152093 952708507076801948682035)
              ·
                refine ⟨1429062760615202923023053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 952708507076801948682035 1429062760615202923023053)
                ·
                  refine ⟨535898535230701096133645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1429062760615202923023053 535898535230701096133645)
                  ·
                    refine ⟨200961950711512911050117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 535898535230701096133645 200961950711512911050117)
                    ·
                      rfl

theorem cell22_587058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 1, 3, 3].length) (baseStart_587058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_587058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_587058 prefixEnd_587058 := by exact prefixLift 587058
  have htrace : WordTrace (prefixWord ++ tailWord_587058) baseStart_587058 baseEnd_587058 := by
    simpa [prefixWord, tailWord_587058, baseEnd_587058] using wordTrace_append hprefix tailTrace_587058
  have hstable : (prefixWord ++ tailWord_587058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587058).length < 2 ^ (prefixWord ++ tailWord_587058).sum := by decide
  have hdescent : baseEnd_587058 < baseStart_587058 := by decide
  rcases family_descends (prefixWord ++ tailWord_587058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587071 : List Nat := [1, 1, 2, 2, 4, 3, 1, 3, 5]
def baseStart_587071 : Nat := 118140960795 + 587071 * 2 ^ 59
def prefixEnd_587071 : Nat := 4983230072969 + 3 ^ 40 * 587071 * 2
def baseEnd_587071 : Nat := 66988800292395070158359

theorem tailTrace_587071 : CollatzResearch.WordTrace tailWord_587071 prefixEnd_587071 66988800292395070158359 := by
  unfold tailWord_587071
  simp only [CollatzResearch.WordTrace]
  refine ⟨21412238456149505589505067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14274825637433003726336711 21412238456149505589505067)
  ·
    refine ⟨32118357684224258384257601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21412238456149505589505067 32118357684224258384257601)
    ·
      refine ⟨24088768263168193788193201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32118357684224258384257601 24088768263168193788193201)
      ·
        refine ⟨18066576197376145341144901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24088768263168193788193201 18066576197376145341144901)
        ·
          refine ⟨3387483037008027251464669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18066576197376145341144901 3387483037008027251464669)
          ·
            refine ⟨1270306138878010219299251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3387483037008027251464669 1270306138878010219299251)
            ·
              refine ⟨1905459208317015328948877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1270306138878010219299251 1905459208317015328948877)
              ·
                refine ⟨714547203118880748355829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1905459208317015328948877 714547203118880748355829)
                ·
                  refine ⟨66988800292395070158359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 714547203118880748355829 66988800292395070158359)
                  ·
                    rfl

theorem cell22_587071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 3, 5].length) (baseStart_587071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_587071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_587071 prefixEnd_587071 := by exact prefixLift 587071
  have htrace : WordTrace (prefixWord ++ tailWord_587071) baseStart_587071 baseEnd_587071 := by
    simpa [prefixWord, tailWord_587071, baseEnd_587071] using wordTrace_append hprefix tailTrace_587071
  have hstable : (prefixWord ++ tailWord_587071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587071).length < 2 ^ (prefixWord ++ tailWord_587071).sum := by decide
  have hdescent : baseEnd_587071 < baseStart_587071 := by decide
  rcases family_descends (prefixWord ++ tailWord_587071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587131 : List Nat := [1, 1, 1, 1, 1, 6, 4, 1, 1, 5]
def baseStart_587131 : Nat := 118140960795 + 587131 * 2 ^ 59
def prefixEnd_587131 : Nat := 4983230072969 + 3 ^ 40 * 587131 * 2
def baseEnd_587131 : Nat := 200986940103365053974893

theorem tailTrace_587131 : CollatzResearch.WordTrace tailWord_587131 prefixEnd_587131 200986940103365053974893 := by
  unfold tailWord_587131
  simp only [CollatzResearch.WordTrace]
  refine ⟨21414426835932135836689247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14276284557288090557792831 21414426835932135836689247)
  ·
    refine ⟨32121640253898203755033871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21414426835932135836689247 32121640253898203755033871)
    ·
      refine ⟨48182460380847305632550807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32121640253898203755033871 48182460380847305632550807)
      ·
        refine ⟨72273690571270958448826211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48182460380847305632550807 72273690571270958448826211)
        ·
          refine ⟨108410535856906437673239317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72273690571270958448826211 108410535856906437673239317)
          ·
            refine ⟨5081743868292489265933093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 108410535856906437673239317 5081743868292489265933093)
            ·
              refine ⟨952826975304841737362455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5081743868292489265933093 952826975304841737362455)
              ·
                refine ⟨1429240462957262606043683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 952826975304841737362455 1429240462957262606043683)
                ·
                  refine ⟨2143860694435893909065525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1429240462957262606043683 2143860694435893909065525)
                  ·
                    refine ⟨200986940103365053974893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2143860694435893909065525 200986940103365053974893)
                    ·
                      rfl

theorem cell22_587131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 1, 1, 5].length) (baseStart_587131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_587131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_587131 prefixEnd_587131 := by exact prefixLift 587131
  have htrace : WordTrace (prefixWord ++ tailWord_587131) baseStart_587131 baseEnd_587131 := by
    simpa [prefixWord, tailWord_587131, baseEnd_587131] using wordTrace_append hprefix tailTrace_587131
  have hstable : (prefixWord ++ tailWord_587131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587131).length < 2 ^ (prefixWord ++ tailWord_587131).sum := by decide
  have hdescent : baseEnd_587131 < baseStart_587131 := by decide
  rcases family_descends (prefixWord ++ tailWord_587131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587165 : List Nat := [1, 4, 2, 1, 3, 1, 3, 2, 2, 3]
def baseStart_587165 : Nat := 118140960795 + 587165 * 2 ^ 59
def prefixEnd_587165 : Nat := 4983230072969 + 3 ^ 40 * 587165 * 2
def baseEnd_587165 : Nat := 200998578998200298624789

theorem tailTrace_587165 : CollatzResearch.WordTrace tailWord_587165 prefixEnd_587165 200998578998200298624789 := by
  unfold tailWord_587165
  simp only [CollatzResearch.WordTrace]
  refine ⟨21415666917808959643426949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14277111278539306428951299 21415666917808959643426949)
  ·
    refine ⟨4015437547089179933142553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21415666917808959643426949 4015437547089179933142553)
    ·
      refine ⟨3011578160316884949856915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4015437547089179933142553 3011578160316884949856915)
      ·
        refine ⟨4517367240475327424785373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3011578160316884949856915 4517367240475327424785373)
        ·
          refine ⟨1694012715178247784294515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4517367240475327424785373 1694012715178247784294515)
          ·
            refine ⟨2541019072767371676441773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1694012715178247784294515 2541019072767371676441773)
            ·
              refine ⟨952882152287764378665665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2541019072767371676441773 952882152287764378665665)
              ·
                refine ⟨714661614215823283999249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 952882152287764378665665 714661614215823283999249)
                ·
                  refine ⟨535996210661867462999437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 714661614215823283999249 535996210661867462999437)
                  ·
                    refine ⟨200998578998200298624789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 535996210661867462999437 200998578998200298624789)
                    ·
                      rfl

theorem cell22_587165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 2, 2, 3].length) (baseStart_587165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_587165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_587165 prefixEnd_587165 := by exact prefixLift 587165
  have htrace : WordTrace (prefixWord ++ tailWord_587165) baseStart_587165 baseEnd_587165 := by
    simpa [prefixWord, tailWord_587165, baseEnd_587165] using wordTrace_append hprefix tailTrace_587165
  have hstable : (prefixWord ++ tailWord_587165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587165).length < 2 ^ (prefixWord ++ tailWord_587165).sum := by decide
  have hdescent : baseEnd_587165 < baseStart_587165 := by decide
  rcases family_descends (prefixWord ++ tailWord_587165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587285 : List Nat := [1, 3, 2, 1, 3, 3, 1, 4, 4]
def baseStart_587285 : Nat := 118140960795 + 587285 * 2 ^ 59
def prefixEnd_587285 : Nat := 4983230072969 + 3 ^ 40 * 587285 * 2
def baseEnd_587285 : Nat := 67013219150186661874807

theorem tailTrace_587285 : CollatzResearch.WordTrace tailWord_587285 prefixEnd_587285 67013219150186661874807 := by
  unfold tailWord_587285
  simp only [CollatzResearch.WordTrace]
  refine ⟨21420043677374220137795309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14280029118249480091863539 21420043677374220137795309)
  ·
    refine ⟨8032516379015332551673241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21420043677374220137795309 8032516379015332551673241)
    ·
      refine ⟨6024387284261499413754931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8032516379015332551673241 6024387284261499413754931)
      ·
        refine ⟨9036580926392249120632397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6024387284261499413754931 9036580926392249120632397)
        ·
          refine ⟨3388717847397093420237149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9036580926392249120632397 3388717847397093420237149)
          ·
            refine ⟨1270769192773910032588931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3388717847397093420237149 1270769192773910032588931)
            ·
              refine ⟨1906153789160865048883397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1270769192773910032588931 1906153789160865048883397)
              ·
                refine ⟨357403835467662196665637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1906153789160865048883397 357403835467662196665637)
                ·
                  refine ⟨67013219150186661874807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 357403835467662196665637 67013219150186661874807)
                  ·
                    rfl

theorem cell22_587285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 4, 4].length) (baseStart_587285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_587285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_587285 prefixEnd_587285 := by exact prefixLift 587285
  have htrace : WordTrace (prefixWord ++ tailWord_587285) baseStart_587285 baseEnd_587285 := by
    simpa [prefixWord, tailWord_587285, baseEnd_587285] using wordTrace_append hprefix tailTrace_587285
  have hstable : (prefixWord ++ tailWord_587285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587285).length < 2 ^ (prefixWord ++ tailWord_587285).sum := by decide
  have hdescent : baseEnd_587285 < baseStart_587285 := by decide
  rcases family_descends (prefixWord ++ tailWord_587285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587298 : List Nat := [3, 3, 1, 1, 1, 1, 2, 2, 4, 4]
def baseStart_587298 : Nat := 118140960795 + 587298 * 2 ^ 59
def prefixEnd_587298 : Nat := 4983230072969 + 3 ^ 40 * 587298 * 2
def baseEnd_587298 : Nat := 201044107616232285049381

theorem tailTrace_587298 : CollatzResearch.WordTrace tailWord_587298 prefixEnd_587298 201044107616232285049381 := by
  unfold tailWord_587298
  simp only [CollatzResearch.WordTrace]
  refine ⟨5355129456581780839504637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14280345217551415572012365 5355129456581780839504637)
  ·
    refine ⟨2008173546218167814814239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5355129456581780839504637 2008173546218167814814239)
    ·
      refine ⟨3012260319327251722221359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2008173546218167814814239 3012260319327251722221359)
      ·
        refine ⟨4518390478990877583332039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3012260319327251722221359 4518390478990877583332039)
        ·
          refine ⟨6777585718486316374998059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4518390478990877583332039 6777585718486316374998059)
          ·
            refine ⟨10166378577729474562497089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6777585718486316374998059 10166378577729474562497089)
            ·
              refine ⟨7624783933297105921872817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10166378577729474562497089 7624783933297105921872817)
              ·
                refine ⟨5718587949972829441404613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7624783933297105921872817 5718587949972829441404613)
                ·
                  refine ⟨1072235240619905520263365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5718587949972829441404613 1072235240619905520263365)
                  ·
                    refine ⟨201044107616232285049381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1072235240619905520263365 201044107616232285049381)
                    ·
                      rfl

theorem cell22_587298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_587298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_587298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_587298 prefixEnd_587298 := by exact prefixLift 587298
  have htrace : WordTrace (prefixWord ++ tailWord_587298) baseStart_587298 baseEnd_587298 := by
    simpa [prefixWord, tailWord_587298, baseEnd_587298] using wordTrace_append hprefix tailTrace_587298
  have hstable : (prefixWord ++ tailWord_587298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587298).length < 2 ^ (prefixWord ++ tailWord_587298).sum := by decide
  have hdescent : baseEnd_587298 < baseStart_587298 := by decide
  rcases family_descends (prefixWord ++ tailWord_587298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587315 : List Nat := [1, 1, 1, 2, 4, 5, 1, 1, 2, 4]
def baseStart_587315 : Nat := 118140960795 + 587315 * 2 ^ 59
def prefixEnd_587315 : Nat := 4983230072969 + 3 ^ 40 * 587315 * 2
def baseEnd_587315 : Nat := 201049927063649907374329

theorem tailTrace_587315 : CollatzResearch.WordTrace tailWord_587315 prefixEnd_587315 201049927063649907374329 := by
  unfold tailWord_587315
  simp only [CollatzResearch.WordTrace]
  refine ⟨21421137867265535261387399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14280758578177023507591599 21421137867265535261387399)
  ·
    refine ⟨32131706800898302892081099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21421137867265535261387399 32131706800898302892081099)
    ·
      refine ⟨48197560201347454338121649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32131706800898302892081099 48197560201347454338121649)
      ·
        refine ⟨36148170151010590753591237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48197560201347454338121649 36148170151010590753591237)
        ·
          refine ⟨6777781903314485766298357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36148170151010590753591237 6777781903314485766298357)
          ·
            refine ⟨635417053435733040590471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6777781903314485766298357 635417053435733040590471)
            ·
              refine ⟨953125580153599560885707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 635417053435733040590471 953125580153599560885707)
              ·
                refine ⟨1429688370230399341328561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 953125580153599560885707 1429688370230399341328561)
                ·
                  refine ⟨1072266277672799505996421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1429688370230399341328561 1072266277672799505996421)
                  ·
                    refine ⟨201049927063649907374329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1072266277672799505996421 201049927063649907374329)
                    ·
                      rfl

theorem cell22_587315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 1, 2, 4].length) (baseStart_587315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_587315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_587315 prefixEnd_587315 := by exact prefixLift 587315
  have htrace : WordTrace (prefixWord ++ tailWord_587315) baseStart_587315 baseEnd_587315 := by
    simpa [prefixWord, tailWord_587315, baseEnd_587315] using wordTrace_append hprefix tailTrace_587315
  have hstable : (prefixWord ++ tailWord_587315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587315).length < 2 ^ (prefixWord ++ tailWord_587315).sum := by decide
  have hdescent : baseEnd_587315 < baseStart_587315 := by decide
  rcases family_descends (prefixWord ++ tailWord_587315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587328 : List Nat := [2, 1, 1, 2, 2, 2, 1, 1, 7, 3]
def baseStart_587328 : Nat := 118140960795 + 587328 * 2 ^ 59
def prefixEnd_587328 : Nat := 4983230072969 + 3 ^ 40 * 587328 * 2
def baseEnd_587328 : Nat := 201054377229322206799289

theorem tailTrace_587328 : CollatzResearch.WordTrace tailWord_587328 prefixEnd_587328 201054377229322206799289 := by
  unfold tailWord_587328
  simp only [CollatzResearch.WordTrace]
  refine ⟨10710806008109219240805319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14281074677478958987740425 10710806008109219240805319)
  ·
    refine ⟨16066209012163828861207979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10710806008109219240805319 16066209012163828861207979)
    ·
      refine ⟨24099313518245743291811969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16066209012163828861207979 24099313518245743291811969)
      ·
        refine ⟨18074485138684307468858977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24099313518245743291811969 18074485138684307468858977)
        ·
          refine ⟨13555863854013230601644233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18074485138684307468858977 13555863854013230601644233)
          ·
            refine ⟨10166897890509922951233175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13555863854013230601644233 10166897890509922951233175)
            ·
              refine ⟨15250346835764884426849763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10166897890509922951233175 15250346835764884426849763)
              ·
                refine ⟨22875520253647326640274645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15250346835764884426849763 22875520253647326640274645)
                ·
                  refine ⟨536145005944859218131437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 22875520253647326640274645 536145005944859218131437)
                  ·
                    refine ⟨201054377229322206799289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 536145005944859218131437 201054377229322206799289)
                    ·
                      rfl

theorem cell22_587328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 7, 3].length) (baseStart_587328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_587328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_587328 prefixEnd_587328 := by exact prefixLift 587328
  have htrace : WordTrace (prefixWord ++ tailWord_587328) baseStart_587328 baseEnd_587328 := by
    simpa [prefixWord, tailWord_587328, baseEnd_587328] using wordTrace_append hprefix tailTrace_587328
  have hstable : (prefixWord ++ tailWord_587328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587328).length < 2 ^ (prefixWord ++ tailWord_587328).sum := by decide
  have hdescent : baseEnd_587328 < baseStart_587328 := by decide
  rcases family_descends (prefixWord ++ tailWord_587328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587334 : List Nat := [6, 1, 1, 1, 3, 1, 1, 1, 4, 3]
def baseStart_587334 : Nat := 118140960795 + 587334 * 2 ^ 59
def prefixEnd_587334 : Nat := 4983230072969 + 3 ^ 40 * 587334 * 2
def baseEnd_587334 : Nat := 201056431151940191149271

theorem tailTrace_587334 : CollatzResearch.WordTrace tailWord_587334 prefixEnd_587334 201056431151940191149271 := by
  unfold tailWord_587334
  simp only [CollatzResearch.WordTrace]
  refine ⟨669432214193646922072783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 14281220569464467670886037 669432214193646922072783)
  ·
    refine ⟨1004148321290470383109175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 669432214193646922072783 1004148321290470383109175)
    ·
      refine ⟨1506222481935705574663763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1004148321290470383109175 1506222481935705574663763)
      ·
        refine ⟨2259333722903558361995645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1506222481935705574663763 2259333722903558361995645)
        ·
          refine ⟨847250146088834385748367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2259333722903558361995645 847250146088834385748367)
          ·
            refine ⟨1270875219133251578622551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 847250146088834385748367 1270875219133251578622551)
            ·
              refine ⟨1906312828699877367933827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1270875219133251578622551 1906312828699877367933827)
              ·
                refine ⟨2859469243049816051900741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1906312828699877367933827 2859469243049816051900741)
                ·
                  refine ⟨536150483071840509731389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2859469243049816051900741 536150483071840509731389)
                  ·
                    refine ⟨201056431151940191149271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 536150483071840509731389 201056431151940191149271)
                    ·
                      rfl

theorem cell22_587334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_587334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_587334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_587334 prefixEnd_587334 := by exact prefixLift 587334
  have htrace : WordTrace (prefixWord ++ tailWord_587334) baseStart_587334 baseEnd_587334 := by
    simpa [prefixWord, tailWord_587334, baseEnd_587334] using wordTrace_append hprefix tailTrace_587334
  have hstable : (prefixWord ++ tailWord_587334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587334).length < 2 ^ (prefixWord ++ tailWord_587334).sum := by decide
  have hdescent : baseEnd_587334 < baseStart_587334 := by decide
  rcases family_descends (prefixWord ++ tailWord_587334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587345 : List Nat := [1, 2, 2, 1, 3, 2, 4, 1, 3, 3]
def baseStart_587345 : Nat := 118140960795 + 587345 * 2 ^ 59
def prefixEnd_587345 : Nat := 4983230072969 + 3 ^ 40 * 587345 * 2
def baseEnd_587345 : Nat := 201060196676739829124237

theorem tailTrace_587345 : CollatzResearch.WordTrace tailWord_587345 prefixEnd_587345 201060196676739829124237 := by
  unfold tailWord_587345
  simp only [CollatzResearch.WordTrace]
  refine ⟨21422232057156850384979489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14281488038104566923319659 21422232057156850384979489)
  ·
    refine ⟨16066674042867637788734617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21422232057156850384979489 16066674042867637788734617)
    ·
      refine ⟨12050005532150728341550963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16066674042867637788734617 12050005532150728341550963)
      ·
        refine ⟨18075008298226092512326445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12050005532150728341550963 18075008298226092512326445)
        ·
          refine ⟨6778128111834784692122417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18075008298226092512326445 6778128111834784692122417)
          ·
            refine ⟨5083596083876088519091813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6778128111834784692122417 5083596083876088519091813)
            ·
              refine ⟨953174265726766597329715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5083596083876088519091813 953174265726766597329715)
              ·
                refine ⟨1429761398590149895994573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 953174265726766597329715 1429761398590149895994573)
                ·
                  refine ⟨536160524471306210997965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1429761398590149895994573 536160524471306210997965)
                  ·
                    refine ⟨201060196676739829124237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 536160524471306210997965 201060196676739829124237)
                    ·
                      rfl

theorem cell22_587345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 1, 3, 3].length) (baseStart_587345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_587345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_587345 prefixEnd_587345 := by exact prefixLift 587345
  have htrace : WordTrace (prefixWord ++ tailWord_587345) baseStart_587345 baseEnd_587345 := by
    simpa [prefixWord, tailWord_587345, baseEnd_587345] using wordTrace_append hprefix tailTrace_587345
  have hstable : (prefixWord ++ tailWord_587345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587345).length < 2 ^ (prefixWord ++ tailWord_587345).sum := by decide
  have hdescent : baseEnd_587345 < baseStart_587345 := by decide
  rcases family_descends (prefixWord ++ tailWord_587345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587388 : List Nat := [2, 2, 2, 1, 1, 2, 1, 2, 5, 4]
def baseStart_587388 : Nat := 118140960795 + 587388 * 2 ^ 59
def prefixEnd_587388 : Nat := 4983230072969 + 3 ^ 40 * 587388 * 2
def baseEnd_587388 : Nat := 201074916455502050299105

theorem tailTrace_587388 : CollatzResearch.WordTrace tailWord_587388 prefixEnd_587388 201074916455502050299105 := by
  unfold tailWord_587388
  simp only [CollatzResearch.WordTrace]
  refine ⟨10711900198000534364397409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14282533597334045819196545 10711900198000534364397409)
  ·
    refine ⟨8033925148500400773298057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10711900198000534364397409 8033925148500400773298057)
    ·
      refine ⟨6025443861375300579973543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8033925148500400773298057 6025443861375300579973543)
      ·
        refine ⟨9038165792062950869960315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6025443861375300579973543 9038165792062950869960315)
        ·
          refine ⟨13557248688094426304940473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9038165792062950869960315 13557248688094426304940473)
          ·
            refine ⟨10167936516070819728705355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13557248688094426304940473 10167936516070819728705355)
            ·
              refine ⟨15251904774106229593058033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10167936516070819728705355 15251904774106229593058033)
              ·
                refine ⟨11438928580579672194793525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15251904774106229593058033 11438928580579672194793525)
                ·
                  refine ⟨1072399554429344268261893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11438928580579672194793525 1072399554429344268261893)
                  ·
                    refine ⟨201074916455502050299105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1072399554429344268261893 201074916455502050299105)
                    ·
                      rfl

theorem cell22_587388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 5, 4].length) (baseStart_587388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_587388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_587388 prefixEnd_587388 := by exact prefixLift 587388
  have htrace : WordTrace (prefixWord ++ tailWord_587388) baseStart_587388 baseEnd_587388 := by
    simpa [prefixWord, tailWord_587388, baseEnd_587388] using wordTrace_append hprefix tailTrace_587388
  have hstable : (prefixWord ++ tailWord_587388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587388).length < 2 ^ (prefixWord ++ tailWord_587388).sum := by decide
  have hdescent : baseEnd_587388 < baseStart_587388 := by decide
  rcases family_descends (prefixWord ++ tailWord_587388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587396 : List Nat := [2, 3, 2, 1, 4, 1, 3, 2, 1, 3]
def baseStart_587396 : Nat := 118140960795 + 587396 * 2 ^ 59
def prefixEnd_587396 : Nat := 4983230072969 + 3 ^ 40 * 587396 * 2
def baseEnd_587396 : Nat := 201077655018992696099081

theorem tailTrace_587396 : CollatzResearch.WordTrace tailWord_587396 prefixEnd_587396 201077655018992696099081 := by
  unfold tailWord_587396
  simp only [CollatzResearch.WordTrace]
  refine ⟨10712046089986043047543021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14282728119981390730057361 10712046089986043047543021)
  ·
    refine ⟨4017017283744766142828633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10712046089986043047543021 4017017283744766142828633)
    ·
      refine ⟨3012762962808574607121475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4017017283744766142828633 3012762962808574607121475)
      ·
        refine ⟨4519144444212861910682213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3012762962808574607121475 4519144444212861910682213)
        ·
          refine ⟨847339583289911608252915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4519144444212861910682213 847339583289911608252915)
          ·
            refine ⟨1271009374934867412379373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 847339583289911608252915 1271009374934867412379373)
            ·
              refine ⟨476628515600575279642265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1271009374934867412379373 476628515600575279642265)
              ·
                refine ⟨357471386700431459731699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 476628515600575279642265 357471386700431459731699)
                ·
                  refine ⟨536207080050647189597549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 357471386700431459731699 536207080050647189597549)
                  ·
                    refine ⟨201077655018992696099081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 536207080050647189597549 201077655018992696099081)
                    ·
                      rfl

theorem cell22_587396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 3, 2, 1, 3].length) (baseStart_587396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_587396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_587396 prefixEnd_587396 := by exact prefixLift 587396
  have htrace : WordTrace (prefixWord ++ tailWord_587396) baseStart_587396 baseEnd_587396 := by
    simpa [prefixWord, tailWord_587396, baseEnd_587396] using wordTrace_append hprefix tailTrace_587396
  have hstable : (prefixWord ++ tailWord_587396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587396).length < 2 ^ (prefixWord ++ tailWord_587396).sum := by decide
  have hdescent : baseEnd_587396 < baseStart_587396 := by decide
  rcases family_descends (prefixWord ++ tailWord_587396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587422 : List Nat := [4, 3, 1, 1, 1, 3, 1, 1, 3, 4]
def baseStart_587422 : Nat := 118140960795 + 587422 * 2 ^ 59
def prefixEnd_587422 : Nat := 4983230072969 + 3 ^ 40 * 587422 * 2
def baseEnd_587422 : Nat := 201086555350337294949001

theorem tailTrace_587422 : CollatzResearch.WordTrace tailWord_587422 prefixEnd_587422 201086555350337294949001 := by
  unfold tailWord_587422
  simp only [CollatzResearch.WordTrace]
  refine ⟨2678130059734736566941565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14283360318585261690355013 2678130059734736566941565)
  ·
    refine ⟨1004298772400526212603087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2678130059734736566941565 1004298772400526212603087)
    ·
      refine ⟨1506448158600789318904631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1004298772400526212603087 1506448158600789318904631)
      ·
        refine ⟨2259672237901183978356947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1506448158600789318904631 2259672237901183978356947)
        ·
          refine ⟨3389508356851775967535421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2259672237901183978356947 3389508356851775967535421)
          ·
            refine ⟨1271065633819415987825783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3389508356851775967535421 1271065633819415987825783)
            ·
              refine ⟨1906598450729123981738675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1271065633819415987825783 1906598450729123981738675)
              ·
                refine ⟨2859897676093685972608013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1906598450729123981738675 2859897676093685972608013)
                ·
                  refine ⟨1072461628535132239728005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2859897676093685972608013 1072461628535132239728005)
                  ·
                    refine ⟨201086555350337294949001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1072461628535132239728005 201086555350337294949001)
                    ·
                      rfl

theorem cell22_587422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_587422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_587422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_587422 prefixEnd_587422 := by exact prefixLift 587422
  have htrace : WordTrace (prefixWord ++ tailWord_587422) baseStart_587422 baseEnd_587422 := by
    simpa [prefixWord, tailWord_587422, baseEnd_587422] using wordTrace_append hprefix tailTrace_587422
  have hstable : (prefixWord ++ tailWord_587422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587422).length < 2 ^ (prefixWord ++ tailWord_587422).sum := by decide
  have hdescent : baseEnd_587422 < baseStart_587422 := by decide
  rcases family_descends (prefixWord ++ tailWord_587422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587437 : List Nat := [1, 5, 2, 1, 1, 1, 2, 5, 4]
def baseStart_587437 : Nat := 118140960795 + 587437 * 2 ^ 59
def prefixEnd_587437 : Nat := 4983230072969 + 3 ^ 40 * 587437 * 2
def baseEnd_587437 : Nat := 67030563385627418607985

theorem tailTrace_587437 : CollatzResearch.WordTrace tailWord_587437 prefixEnd_587437 67030563385627418607985 := by
  unfold tailWord_587437
  simp only [CollatzResearch.WordTrace]
  refine ⟨21425587572823550097328565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14283725048549033398219043 21425587572823550097328565)
  ·
    refine ⟨2008648834952207821624553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21425587572823550097328565 2008648834952207821624553)
    ·
      refine ⟨1506486626214155866218415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2008648834952207821624553 1506486626214155866218415)
      ·
        refine ⟨2259729939321233799327623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1506486626214155866218415 2259729939321233799327623)
        ·
          refine ⟨3389594908981850698991435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2259729939321233799327623 3389594908981850698991435)
          ·
            refine ⟨5084392363472776048487153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3389594908981850698991435 5084392363472776048487153)
            ·
              refine ⟨3813294272604582036365365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5084392363472776048487153 3813294272604582036365365)
              ·
                refine ⟨357496338056679565909253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3813294272604582036365365 357496338056679565909253)
                ·
                  refine ⟨67030563385627418607985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 357496338056679565909253 67030563385627418607985)
                  ·
                    rfl

theorem cell22_587437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 5, 4].length) (baseStart_587437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_587437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_587437 prefixEnd_587437 := by exact prefixLift 587437
  have htrace : WordTrace (prefixWord ++ tailWord_587437) baseStart_587437 baseEnd_587437 := by
    simpa [prefixWord, tailWord_587437, baseEnd_587437] using wordTrace_append hprefix tailTrace_587437
  have hstable : (prefixWord ++ tailWord_587437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587437).length < 2 ^ (prefixWord ++ tailWord_587437).sum := by decide
  have hdescent : baseEnd_587437 < baseStart_587437 := by decide
  rcases family_descends (prefixWord ++ tailWord_587437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587450 : List Nat := [3, 1, 1, 1, 2, 4, 2, 2, 2, 4]
def baseStart_587450 : Nat := 118140960795 + 587450 * 2 ^ 59
def prefixEnd_587450 : Nat := 4983230072969 + 3 ^ 40 * 587450 * 2
def baseEnd_587450 : Nat := 201096140322554555248915

theorem tailTrace_587450 : CollatzResearch.WordTrace tailWord_587450 prefixEnd_587450 201096140322554555248915 := by
  unfold tailWord_587450
  simp only [CollatzResearch.WordTrace]
  refine ⟨5356515430444113329387951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14284041147850968878367869 5356515430444113329387951)
  ·
    refine ⟨8034773145666169994081927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5356515430444113329387951 8034773145666169994081927)
    ·
      refine ⟨12052159718499254991122891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8034773145666169994081927 12052159718499254991122891)
      ·
        refine ⟨18078239577748882486684337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12052159718499254991122891 18078239577748882486684337)
        ·
          refine ⟨13558679683311661865013253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18078239577748882486684337 13558679683311661865013253)
          ·
            refine ⟨2542252440620936599689985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13558679683311661865013253 2542252440620936599689985)
            ·
              refine ⟨1906689330465702449767489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2542252440620936599689985 1906689330465702449767489)
              ·
                refine ⟨1430016997849276837325617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1906689330465702449767489 1430016997849276837325617)
                ·
                  refine ⟨1072512748386957627994213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1430016997849276837325617 1072512748386957627994213)
                  ·
                    refine ⟨201096140322554555248915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1072512748386957627994213 201096140322554555248915)
                    ·
                      rfl

theorem cell22_587450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 2, 2, 4].length) (baseStart_587450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_587450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_587450 prefixEnd_587450 := by exact prefixLift 587450
  have htrace : WordTrace (prefixWord ++ tailWord_587450) baseStart_587450 baseEnd_587450 := by
    simpa [prefixWord, tailWord_587450, baseEnd_587450] using wordTrace_append hprefix tailTrace_587450
  have hstable : (prefixWord ++ tailWord_587450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587450).length < 2 ^ (prefixWord ++ tailWord_587450).sum := by decide
  have hdescent : baseEnd_587450 < baseStart_587450 := by decide
  rcases family_descends (prefixWord ++ tailWord_587450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587452 : List Nat := [2, 2, 2, 3, 1, 2, 1, 4, 2, 3]
def baseStart_587452 : Nat := 118140960795 + 587452 * 2 ^ 59
def prefixEnd_587452 : Nat := 4983230072969 + 3 ^ 40 * 587452 * 2
def baseEnd_587452 : Nat := 201096824963427216698909

theorem tailTrace_587452 : CollatzResearch.WordTrace tailWord_587452 prefixEnd_587452 201096824963427216698909 := by
  unfold tailWord_587452
  simp only [CollatzResearch.WordTrace]
  refine ⟨10713067333884603829562305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14284089778512805106083073 10713067333884603829562305)
  ·
    refine ⟨8034800500413452872171729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10713067333884603829562305 8034800500413452872171729)
    ·
      refine ⟨6026100375310089654128797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8034800500413452872171729 6026100375310089654128797)
      ·
        refine ⟨2259787640741283620298299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6026100375310089654128797 2259787640741283620298299)
        ·
          refine ⟨3389681461111925430447449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2259787640741283620298299 3389681461111925430447449)
          ·
            refine ⟨2542261095833944072835587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3389681461111925430447449 2542261095833944072835587)
            ·
              refine ⟨3813391643750916109253381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2542261095833944072835587 3813391643750916109253381)
              ·
                refine ⟨715010933203296770485009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3813391643750916109253381 715010933203296770485009)
                ·
                  refine ⟨536258199902472577863757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 715010933203296770485009 536258199902472577863757)
                  ·
                    refine ⟨201096824963427216698909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 536258199902472577863757 201096824963427216698909)
                    ·
                      rfl

theorem cell22_587452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 4, 2, 3].length) (baseStart_587452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_587452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_587452 prefixEnd_587452 := by exact prefixLift 587452
  have htrace : WordTrace (prefixWord ++ tailWord_587452) baseStart_587452 baseEnd_587452 := by
    simpa [prefixWord, tailWord_587452, baseEnd_587452] using wordTrace_append hprefix tailTrace_587452
  have hstable : (prefixWord ++ tailWord_587452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587452).length < 2 ^ (prefixWord ++ tailWord_587452).sum := by decide
  have hdescent : baseEnd_587452 < baseStart_587452 := by decide
  rcases family_descends (prefixWord ++ tailWord_587452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587454 : List Nat := [4, 2, 1, 1, 2, 2, 4, 2, 4]
def baseStart_587454 : Nat := 118140960795 + 587454 * 2 ^ 59
def prefixEnd_587454 : Nat := 4983230072969 + 3 ^ 40 * 587454 * 2
def baseEnd_587454 : Nat := 67032503201433292716301

theorem tailTrace_587454 : CollatzResearch.WordTrace tailWord_587454 prefixEnd_587454 67032503201433292716301 := by
  unfold tailWord_587454
  simp only [CollatzResearch.WordTrace]
  refine ⟨2678275951720245250087177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14284138409174641333798277 2678275951720245250087177)
  ·
    refine ⟨2008706963790183937565383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2678275951720245250087177 2008706963790183937565383)
    ·
      refine ⟨3013060445685275906348075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2008706963790183937565383 3013060445685275906348075)
      ·
        refine ⟨4519590668527913859522113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3013060445685275906348075 4519590668527913859522113)
        ·
          refine ⟨3389693001395935394641585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4519590668527913859522113 3389693001395935394641585)
          ·
            refine ⟨2542269751046951545981189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3389693001395935394641585 2542269751046951545981189)
            ·
              refine ⟨476675578321303414871473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2542269751046951545981189 476675578321303414871473)
              ·
                refine ⟨357506683740977561153605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 476675578321303414871473 357506683740977561153605)
                ·
                  refine ⟨67032503201433292716301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 357506683740977561153605 67032503201433292716301)
                  ·
                    rfl

theorem cell22_587454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 4, 2, 4].length) (baseStart_587454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_587454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_587454 prefixEnd_587454 := by exact prefixLift 587454
  have htrace : WordTrace (prefixWord ++ tailWord_587454) baseStart_587454 baseEnd_587454 := by
    simpa [prefixWord, tailWord_587454, baseEnd_587454] using wordTrace_append hprefix tailTrace_587454
  have hstable : (prefixWord ++ tailWord_587454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587454).length < 2 ^ (prefixWord ++ tailWord_587454).sum := by decide
  have hdescent : baseEnd_587454 < baseStart_587454 := by decide
  rcases family_descends (prefixWord ++ tailWord_587454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587469 : List Nat := [1, 6, 2, 1, 1, 2, 2, 1, 1, 5]
def baseStart_587469 : Nat := 118140960795 + 587469 * 2 ^ 59
def prefixEnd_587469 : Nat := 4983230072969 + 3 ^ 40 * 587469 * 2
def baseEnd_587469 : Nat := 201102644410844839023857

theorem tailTrace_587469 : CollatzResearch.WordTrace tailWord_587469 prefixEnd_587469 201102644410844839023857 := by
  unfold tailWord_587469
  simp only [CollatzResearch.WordTrace]
  refine ⟨21426754708707619562493461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14284503139138413041662307 21426754708707619562493461)
  ·
    refine ⟨1004379126970669666991881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 21426754708707619562493461 1004379126970669666991881)
    ·
      refine ⟨753284345228002250243911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1004379126970669666991881 753284345228002250243911)
      ·
        refine ⟨1129926517842003375365867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 753284345228002250243911 1129926517842003375365867)
        ·
          refine ⟨1694889776763005063048801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1129926517842003375365867 1694889776763005063048801)
          ·
            refine ⟨1271167332572253797286601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1694889776763005063048801 1271167332572253797286601)
            ·
              refine ⟨953375499429190347964951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1271167332572253797286601 953375499429190347964951)
              ·
                refine ⟨1430063249143785521947427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 953375499429190347964951 1430063249143785521947427)
                ·
                  refine ⟨2145094873715678282921141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1430063249143785521947427 2145094873715678282921141)
                  ·
                    refine ⟨201102644410844839023857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2145094873715678282921141 201102644410844839023857)
                    ·
                      rfl

theorem cell22_587469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_587469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_587469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_587469 prefixEnd_587469 := by exact prefixLift 587469
  have htrace : WordTrace (prefixWord ++ tailWord_587469) baseStart_587469 baseEnd_587469 := by
    simpa [prefixWord, tailWord_587469, baseEnd_587469] using wordTrace_append hprefix tailTrace_587469
  have hstable : (prefixWord ++ tailWord_587469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587469).length < 2 ^ (prefixWord ++ tailWord_587469).sum := by decide
  have hdescent : baseEnd_587469 < baseStart_587469 := by decide
  rcases family_descends (prefixWord ++ tailWord_587469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587557 : List Nat := [1, 3, 1, 2, 3, 2, 2, 3, 1, 4]
def baseStart_587557 : Nat := 118140960795 + 587557 * 2 ^ 59
def prefixEnd_587557 : Nat := 4983230072969 + 3 ^ 40 * 587557 * 2
def baseEnd_587557 : Nat := 201132768609241942823587

theorem tailTrace_587557 : CollatzResearch.WordTrace tailWord_587557 prefixEnd_587557 201132768609241942823587 := by
  unfold tailWord_587557
  simp only [CollatzResearch.WordTrace]
  refine ⟨21429964332388810591696925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14286642888259207061131283 21429964332388810591696925)
  ·
    refine ⟨8036236624645803971886347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21429964332388810591696925 8036236624645803971886347)
    ·
      refine ⟨12054354936968705957829521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8036236624645803971886347 12054354936968705957829521)
      ·
        refine ⟨9040766202726529468372141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12054354936968705957829521 9040766202726529468372141)
        ·
          refine ⟨3390287326022448550639553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9040766202726529468372141 3390287326022448550639553)
          ·
            refine ⟨2542715494516836412979665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3390287326022448550639553 2542715494516836412979665)
            ·
              refine ⟨1907036620887627309734749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2542715494516836412979665 1907036620887627309734749)
              ·
                refine ⟨715138732832860241150531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1907036620887627309734749 715138732832860241150531)
                ·
                  refine ⟨1072708099249290361725797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 715138732832860241150531 1072708099249290361725797)
                  ·
                    refine ⟨201132768609241942823587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1072708099249290361725797 201132768609241942823587)
                    ·
                      rfl

theorem cell22_587557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 3, 1, 4].length) (baseStart_587557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_587557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_587557 prefixEnd_587557 := by exact prefixLift 587557
  have htrace : WordTrace (prefixWord ++ tailWord_587557) baseStart_587557 baseEnd_587557 := by
    simpa [prefixWord, tailWord_587557, baseEnd_587557] using wordTrace_append hprefix tailTrace_587557
  have hstable : (prefixWord ++ tailWord_587557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587557).length < 2 ^ (prefixWord ++ tailWord_587557).sum := by decide
  have hdescent : baseEnd_587557 < baseStart_587557 := by decide
  rcases family_descends (prefixWord ++ tailWord_587557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587602 : List Nat := [3, 2, 2, 1, 1, 3, 1, 3, 2, 4]
def baseStart_587602 : Nat := 118140960795 + 587602 * 2 ^ 59
def prefixEnd_587602 : Nat := 4983230072969 + 3 ^ 40 * 587602 * 2
def baseEnd_587602 : Nat := 201148173028876825448449

theorem tailTrace_587602 : CollatzResearch.WordTrace tailWord_587602 prefixEnd_587602 201148173028876825448449 := by
  unfold tailWord_587602
  simp only [CollatzResearch.WordTrace]
  refine ⟨5357901404306445819271265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14287737078150522184723373 5357901404306445819271265)
  ·
    refine ⟨4018426053229834364453449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5357901404306445819271265 4018426053229834364453449)
    ·
      refine ⟨3013819539922375773340087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4018426053229834364453449 3013819539922375773340087)
      ·
        refine ⟨4520729309883563660010131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3013819539922375773340087 4520729309883563660010131)
        ·
          refine ⟨6781093964825345490015197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4520729309883563660010131 6781093964825345490015197)
          ·
            refine ⟨2542910236809504558755699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6781093964825345490015197 2542910236809504558755699)
            ·
              refine ⟨3814365355214256838133549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2542910236809504558755699 3814365355214256838133549)
              ·
                refine ⟨1430387008205346314300081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3814365355214256838133549 1430387008205346314300081)
                ·
                  refine ⟨1072790256154009735725061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1430387008205346314300081 1072790256154009735725061)
                  ·
                    refine ⟨201148173028876825448449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1072790256154009735725061 201148173028876825448449)
                    ·
                      rfl

theorem cell22_587602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_587602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_587602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_587602 prefixEnd_587602 := by exact prefixLift 587602
  have htrace : WordTrace (prefixWord ++ tailWord_587602) baseStart_587602 baseEnd_587602 := by
    simpa [prefixWord, tailWord_587602, baseEnd_587602] using wordTrace_append hprefix tailTrace_587602
  have hstable : (prefixWord ++ tailWord_587602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587602).length < 2 ^ (prefixWord ++ tailWord_587602).sum := by decide
  have hdescent : baseEnd_587602 < baseStart_587602 := by decide
  rcases family_descends (prefixWord ++ tailWord_587602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587632 : List Nat := [2, 1, 1, 1, 4, 1, 1, 5, 3, 3]
def baseStart_587632 : Nat := 118140960795 + 587632 * 2 ^ 59
def prefixEnd_587632 : Nat := 4983230072969 + 3 ^ 40 * 587632 * 2
def baseEnd_587632 : Nat := 201158442641966747198357

theorem tailTrace_587632 : CollatzResearch.WordTrace tailWord_587632 prefixEnd_587632 201158442641966747198357 := by
  unfold tailWord_587632
  simp only [CollatzResearch.WordTrace]
  refine ⟨10716349903558549200338575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14288466538078065600451433 10716349903558549200338575)
  ·
    refine ⟨16074524855337823800507863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10716349903558549200338575 16074524855337823800507863)
    ·
      refine ⟨24111787283006735700761795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16074524855337823800507863 24111787283006735700761795)
      ·
        refine ⟨36167680924510103551142693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24111787283006735700761795 36167680924510103551142693)
        ·
          refine ⟨6781440173345644415839255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36167680924510103551142693 6781440173345644415839255)
          ·
            refine ⟨10172160260018466623758883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6781440173345644415839255 10172160260018466623758883)
            ·
              refine ⟨15258240390027699935638325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10172160260018466623758883 15258240390027699935638325)
              ·
                refine ⟨1430460036565096868966093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15258240390027699935638325 1430460036565096868966093)
                ·
                  refine ⟨536422513711911325862285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1430460036565096868966093 536422513711911325862285)
                  ·
                    refine ⟨201158442641966747198357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 536422513711911325862285 201158442641966747198357)
                    ·
                      rfl

theorem cell22_587632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 5, 3, 3].length) (baseStart_587632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_587632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_587632 prefixEnd_587632 := by exact prefixLift 587632
  have htrace : WordTrace (prefixWord ++ tailWord_587632) baseStart_587632 baseEnd_587632 := by
    simpa [prefixWord, tailWord_587632, baseEnd_587632] using wordTrace_append hprefix tailTrace_587632
  have hstable : (prefixWord ++ tailWord_587632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587632).length < 2 ^ (prefixWord ++ tailWord_587632).sum := by decide
  have hdescent : baseEnd_587632 < baseStart_587632 := by decide
  rcases family_descends (prefixWord ++ tailWord_587632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587645 : List Nat := [1, 4, 1, 1, 2, 1, 1, 2, 9]
def baseStart_587645 : Nat := 118140960795 + 587645 * 2 ^ 59
def prefixEnd_587645 : Nat := 4983230072969 + 3 ^ 40 * 587645 * 2
def baseEnd_587645 : Nat := 67054297602546348874439

theorem tailTrace_587645 : CollatzResearch.WordTrace tailWord_587645 prefixEnd_587645 67054297602546348874439 := by
  unfold tailWord_587645
  simp only [CollatzResearch.WordTrace]
  refine ⟨21433173956070001620900389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14288782637380001080600259 21433173956070001620900389)
  ·
    refine ⟨4018720116763125303918823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21433173956070001620900389 4018720116763125303918823)
    ·
      refine ⟨6028080175144687955878235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4018720116763125303918823 6028080175144687955878235)
      ·
        refine ⟨9042120262717031933817353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6028080175144687955878235 9042120262717031933817353)
        ·
          refine ⟨6781590197037773950363015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9042120262717031933817353 6781590197037773950363015)
          ·
            refine ⟨10172385295556660925544523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6781590197037773950363015 10172385295556660925544523)
            ·
              refine ⟨15258577943334991388316785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10172385295556660925544523 15258577943334991388316785)
              ·
                refine ⟨11443933457501243541237589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15258577943334991388316785 11443933457501243541237589)
                ·
                  refine ⟨67054297602546348874439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 11443933457501243541237589 67054297602546348874439)
                  ·
                    rfl

theorem cell22_587645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 9].length) (baseStart_587645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_587645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_587645 prefixEnd_587645 := by exact prefixLift 587645
  have htrace : WordTrace (prefixWord ++ tailWord_587645) baseStart_587645 baseEnd_587645 := by
    simpa [prefixWord, tailWord_587645, baseEnd_587645] using wordTrace_append hprefix tailTrace_587645
  have hstable : (prefixWord ++ tailWord_587645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587645).length < 2 ^ (prefixWord ++ tailWord_587645).sum := by decide
  have hdescent : baseEnd_587645 < baseStart_587645 := by decide
  rcases family_descends (prefixWord ++ tailWord_587645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587660 : List Nat := [2, 2, 1, 2, 1, 2, 1, 1, 3, 7]
def baseStart_587660 : Nat := 118140960795 + 587660 * 2 ^ 59
def prefixEnd_587660 : Nat := 4983230072969 + 3 ^ 40 * 587660 * 2
def baseEnd_587660 : Nat := 201168027614184007498271

theorem tailTrace_587660 : CollatzResearch.WordTrace tailWord_587660 prefixEnd_587660 201168027614184007498271 := by
  unfold tailWord_587660
  simp only [CollatzResearch.WordTrace]
  refine ⟨10716860525507829591348217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14289147367343772788464289 10716860525507829591348217)
  ·
    refine ⟨8037645394130872193511163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10716860525507829591348217 8037645394130872193511163)
    ·
      refine ⟨12056468091196308290266745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8037645394130872193511163 12056468091196308290266745)
      ·
        refine ⟨9042351068397231217700059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12056468091196308290266745 9042351068397231217700059)
        ·
          refine ⟨13563526602595846826550089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9042351068397231217700059 13563526602595846826550089)
          ·
            refine ⟨10172644951946885119912567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13563526602595846826550089 10172644951946885119912567)
            ·
              refine ⟨15258967427920327679868851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10172644951946885119912567 15258967427920327679868851)
              ·
                refine ⟨22888451141880491519803277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15258967427920327679868851 22888451141880491519803277)
                ·
                  refine ⟨8583169178205184319926229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22888451141880491519803277 8583169178205184319926229)
                  ·
                    refine ⟨201168027614184007498271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8583169178205184319926229 201168027614184007498271)
                    ·
                      rfl

theorem cell22_587660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 3, 7].length) (baseStart_587660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_587660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_587660 prefixEnd_587660 := by exact prefixLift 587660
  have htrace : WordTrace (prefixWord ++ tailWord_587660) baseStart_587660 baseEnd_587660 := by
    simpa [prefixWord, tailWord_587660, baseEnd_587660] using wordTrace_append hprefix tailTrace_587660
  have hstable : (prefixWord ++ tailWord_587660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587660).length < 2 ^ (prefixWord ++ tailWord_587660).sum := by decide
  have hdescent : baseEnd_587660 < baseStart_587660 := by decide
  rcases family_descends (prefixWord ++ tailWord_587660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587677 : List Nat := [1, 4, 2, 1, 2, 2, 1, 2, 2, 5]
def baseStart_587677 : Nat := 118140960795 + 587677 * 2 ^ 59
def prefixEnd_587677 : Nat := 4983230072969 + 3 ^ 40 * 587677 * 2
def baseEnd_587677 : Nat := 201173847061601629823219

theorem tailTrace_587677 : CollatzResearch.WordTrace tailWord_587677 prefixEnd_587677 201173847061601629823219 := by
  unfold tailWord_587677
  simp only [CollatzResearch.WordTrace]
  refine ⟨21434341091954071086065285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14289560727969380724043523 21434341091954071086065285)
  ·
    refine ⟨4018938954741388328637241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21434341091954071086065285 4018938954741388328637241)
    ·
      refine ⟨3014204216056041246477931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4018938954741388328637241 3014204216056041246477931)
      ·
        refine ⟨4521306324084061869716897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3014204216056041246477931 4521306324084061869716897)
        ·
          refine ⟨3390979743063046402287673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4521306324084061869716897 3390979743063046402287673)
          ·
            refine ⟨2543234807297284801715755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3390979743063046402287673 2543234807297284801715755)
            ·
              refine ⟨3814852210945927202573633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2543234807297284801715755 3814852210945927202573633)
              ·
                refine ⟨2861139158209445401930225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3814852210945927202573633 2861139158209445401930225)
                ·
                  refine ⟨2145854368657084051447669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2861139158209445401930225 2145854368657084051447669)
                  ·
                    refine ⟨201173847061601629823219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2145854368657084051447669 201173847061601629823219)
                    ·
                      rfl

theorem cell22_587677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_587677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_587677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_587677 prefixEnd_587677 := by exact prefixLift 587677
  have htrace : WordTrace (prefixWord ++ tailWord_587677) baseStart_587677 baseEnd_587677 := by
    simpa [prefixWord, tailWord_587677, baseEnd_587677] using wordTrace_append hprefix tailTrace_587677
  have hstable : (prefixWord ++ tailWord_587677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587677).length < 2 ^ (prefixWord ++ tailWord_587677).sum := by decide
  have hdescent : baseEnd_587677 < baseStart_587677 := by decide
  rcases family_descends (prefixWord ++ tailWord_587677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587709 : List Nat := [1, 4, 1, 2, 3, 1, 1, 4, 1, 4]
def baseStart_587709 : Nat := 118140960795 + 587709 * 2 ^ 59
def prefixEnd_587709 : Nat := 4983230072969 + 3 ^ 40 * 587709 * 2
def baseEnd_587709 : Nat := 201184801315564213023121

theorem tailTrace_587709 : CollatzResearch.WordTrace tailWord_587709 prefixEnd_587709 201184801315564213023121 := by
  unfold tailWord_587709
  simp only [CollatzResearch.WordTrace]
  refine ⟨21435508227838140551230181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14290338818558760367486787 21435508227838140551230181)
  ·
    refine ⟨4019157792719651353355659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21435508227838140551230181 4019157792719651353355659)
    ·
      refine ⟨6028736689079477030033489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4019157792719651353355659 6028736689079477030033489)
      ·
        refine ⟨4521552516809607772525117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6028736689079477030033489 4521552516809607772525117)
        ·
          refine ⟨1695582193803602914696919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4521552516809607772525117 1695582193803602914696919)
          ·
            refine ⟨2543373290705404372045379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1695582193803602914696919 2543373290705404372045379)
            ·
              refine ⟨3815059936058106558068069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2543373290705404372045379 3815059936058106558068069)
              ·
                refine ⟨715323738010894979637763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3815059936058106558068069 715323738010894979637763)
                ·
                  refine ⟨1072985607016342469456645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 715323738010894979637763 1072985607016342469456645)
                  ·
                    refine ⟨201184801315564213023121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1072985607016342469456645 201184801315564213023121)
                    ·
                      rfl

theorem cell22_587709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 4, 1, 4].length) (baseStart_587709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_587709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_587709 prefixEnd_587709 := by exact prefixLift 587709
  have htrace : WordTrace (prefixWord ++ tailWord_587709) baseStart_587709 baseEnd_587709 := by
    simpa [prefixWord, tailWord_587709, baseEnd_587709] using wordTrace_append hprefix tailTrace_587709
  have hstable : (prefixWord ++ tailWord_587709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587709).length < 2 ^ (prefixWord ++ tailWord_587709).sum := by decide
  have hdescent : baseEnd_587709 < baseStart_587709 := by decide
  rcases family_descends (prefixWord ++ tailWord_587709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587722 : List Nat := [3, 1, 2, 1, 2, 1, 2, 4, 1, 5]
def baseStart_587722 : Nat := 118140960795 + 587722 * 2 ^ 59
def prefixEnd_587722 : Nat := 4983230072969 + 3 ^ 40 * 587722 * 2
def baseEnd_587722 : Nat := 201189251481236512448081

theorem tailTrace_587722 : CollatzResearch.WordTrace tailWord_587722 prefixEnd_587722 201189251481236512448081 := by
  unfold tailWord_587722
  simp only [CollatzResearch.WordTrace]
  refine ⟨5358995594197760942863355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14290654917860695847635613 5358995594197760942863355)
  ·
    refine ⟨8038493391296641414295033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5358995594197760942863355 8038493391296641414295033)
    ·
      refine ⟨6028870043472481060721275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8038493391296641414295033 6028870043472481060721275)
      ·
        refine ⟨9043305065208721591081913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6028870043472481060721275 9043305065208721591081913)
        ·
          refine ⟨6782478798906541193311435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9043305065208721591081913 6782478798906541193311435)
          ·
            refine ⟨10173718198359811789967153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6782478798906541193311435 10173718198359811789967153)
            ·
              refine ⟨7630288648769858842475365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10173718198359811789967153 7630288648769858842475365)
              ·
                refine ⟨1430679121644348532964131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7630288648769858842475365 1430679121644348532964131)
                ·
                  refine ⟨2146018682466522799446197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1430679121644348532964131 2146018682466522799446197)
                  ·
                    refine ⟨201189251481236512448081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2146018682466522799446197 201189251481236512448081)
                    ·
                      rfl

theorem cell22_587722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 4, 1, 5].length) (baseStart_587722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_587722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_587722 prefixEnd_587722 := by exact prefixLift 587722
  have htrace : WordTrace (prefixWord ++ tailWord_587722) baseStart_587722 baseEnd_587722 := by
    simpa [prefixWord, tailWord_587722, baseEnd_587722] using wordTrace_append hprefix tailTrace_587722
  have hstable : (prefixWord ++ tailWord_587722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587722).length < 2 ^ (prefixWord ++ tailWord_587722).sum := by decide
  have hdescent : baseEnd_587722 < baseStart_587722 := by decide
  rcases family_descends (prefixWord ++ tailWord_587722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587741 : List Nat := [1, 4, 3, 1, 3, 2, 1, 1, 6]
def baseStart_587741 : Nat := 118140960795 + 587741 * 2 ^ 59
def prefixEnd_587741 : Nat := 4983230072969 + 3 ^ 40 * 587741 * 2
def baseEnd_587741 : Nat := 67065251856508932074341

theorem tailTrace_587741 : CollatzResearch.WordTrace tailWord_587741 prefixEnd_587741 67065251856508932074341 := by
  unfold tailWord_587741
  simp only [CollatzResearch.WordTrace]
  refine ⟨21436675363722210016395077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14291116909148140010930051 21436675363722210016395077)
  ·
    refine ⟨4019376630697914378074077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21436675363722210016395077 4019376630697914378074077)
    ·
      refine ⟨1507266236511717891777779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4019376630697914378074077 1507266236511717891777779)
      ·
        refine ⟨2260899354767576837666669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1507266236511717891777779 2260899354767576837666669)
        ·
          refine ⟨847837258037841314125001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2260899354767576837666669 847837258037841314125001)
          ·
            refine ⟨635877943528380985593751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 847837258037841314125001 635877943528380985593751)
            ·
              refine ⟨953816915292571478390627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 635877943528380985593751 953816915292571478390627)
              ·
                refine ⟨1430725372938857217585941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 953816915292571478390627 1430725372938857217585941)
                ·
                  refine ⟨67065251856508932074341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1430725372938857217585941 67065251856508932074341)
                  ·
                    rfl

theorem cell22_587741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 1, 6].length) (baseStart_587741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_587741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_587741 prefixEnd_587741 := by exact prefixLift 587741
  have htrace : WordTrace (prefixWord ++ tailWord_587741) baseStart_587741 baseEnd_587741 := by
    simpa [prefixWord, tailWord_587741, baseEnd_587741] using wordTrace_append hprefix tailTrace_587741
  have hstable : (prefixWord ++ tailWord_587741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587741).length < 2 ^ (prefixWord ++ tailWord_587741).sum := by decide
  have hdescent : baseEnd_587741 < baseStart_587741 := by decide
  rcases family_descends (prefixWord ++ tailWord_587741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587846 : List Nat := [6, 1, 1, 1, 1, 1, 1, 1, 4, 5]
def baseStart_587846 : Nat := 118140960795 + 587846 * 2 ^ 59
def prefixEnd_587846 : Nat := 4983230072969 + 3 ^ 40 * 587846 * 2
def baseEnd_587846 : Nat := 201231699215341522347701

theorem tailTrace_587846 : CollatzResearch.WordTrace tailWord_587846 prefixEnd_587846 201231699215341522347701 := by
  unfold tailWord_587846
  simp only [CollatzResearch.WordTrace]
  refine ⟨670015782135681654655231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 14293670018894541965978261 670015782135681654655231)
  ·
    refine ⟨1005023673203522481982847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 670015782135681654655231 1005023673203522481982847)
    ·
      refine ⟨1507535509805283722974271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1005023673203522481982847 1507535509805283722974271)
      ·
        refine ⟨2261303264707925584461407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1507535509805283722974271 2261303264707925584461407)
        ·
          refine ⟨3391954897061888376692111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2261303264707925584461407 3391954897061888376692111)
          ·
            refine ⟨5087932345592832565038167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3391954897061888376692111 5087932345592832565038167)
            ·
              refine ⟨7631898518389248847557251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5087932345592832565038167 7631898518389248847557251)
              ·
                refine ⟨11447847777583873271335877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7631898518389248847557251 11447847777583873271335877)
                ·
                  refine ⟨2146471458296976238375477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11447847777583873271335877 2146471458296976238375477)
                  ·
                    refine ⟨201231699215341522347701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2146471458296976238375477 201231699215341522347701)
                    ·
                      rfl

theorem cell22_587846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_587846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_587846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_587846 prefixEnd_587846 := by exact prefixLift 587846
  have htrace : WordTrace (prefixWord ++ tailWord_587846) baseStart_587846 baseEnd_587846 := by
    simpa [prefixWord, tailWord_587846, baseEnd_587846] using wordTrace_append hprefix tailTrace_587846
  have hstable : (prefixWord ++ tailWord_587846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587846).length < 2 ^ (prefixWord ++ tailWord_587846).sum := by decide
  have hdescent : baseEnd_587846 < baseStart_587846 := by decide
  rcases family_descends (prefixWord ++ tailWord_587846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587889 : List Nat := [1, 2, 2, 2, 1, 1, 4, 3, 2, 4]
def baseStart_587889 : Nat := 118140960795 + 587889 * 2 ^ 59
def prefixEnd_587889 : Nat := 4983230072969 + 3 ^ 40 * 587889 * 2
def baseEnd_587889 : Nat := 201246418994103743522569

theorem tailTrace_587889 : CollatzResearch.WordTrace tailWord_587889 prefixEnd_587889 201246418994103743522569 := by
  unfold tailWord_587889
  simp only [CollatzResearch.WordTrace]
  refine ⟨21442073367186031292782721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14294715578124020861855147 21442073367186031292782721)
  ·
    refine ⟨16081555025389523469587041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21442073367186031292782721 16081555025389523469587041)
    ·
      refine ⟨12061166269042142602190281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16081555025389523469587041 12061166269042142602190281)
      ·
        refine ⟨9045874701781606951642711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12061166269042142602190281 9045874701781606951642711)
        ·
          refine ⟨13568812052672410427464067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9045874701781606951642711 13568812052672410427464067)
          ·
            refine ⟨20353218079008615641196101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13568812052672410427464067 20353218079008615641196101)
            ·
              refine ⟨3816228389814115432724269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20353218079008615641196101 3816228389814115432724269)
              ·
                refine ⟨1431085646180293287271601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3816228389814115432724269 1431085646180293287271601)
                ·
                  refine ⟨1073314234635219965453701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1431085646180293287271601 1073314234635219965453701)
                  ·
                    refine ⟨201246418994103743522569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1073314234635219965453701 201246418994103743522569)
                    ·
                      rfl

theorem cell22_587889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 3, 2, 4].length) (baseStart_587889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_587889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_587889 prefixEnd_587889 := by exact prefixLift 587889
  have htrace : WordTrace (prefixWord ++ tailWord_587889) baseStart_587889 baseEnd_587889 := by
    simpa [prefixWord, tailWord_587889, baseEnd_587889] using wordTrace_append hprefix tailTrace_587889
  have hstable : (prefixWord ++ tailWord_587889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587889).length < 2 ^ (prefixWord ++ tailWord_587889).sum := by decide
  have hdescent : baseEnd_587889 < baseStart_587889 := by decide
  rcases family_descends (prefixWord ++ tailWord_587889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587979 : List Nat := [1, 1, 1, 1, 3, 2, 3, 1, 5, 4]
def baseStart_587979 : Nat := 118140960795 + 587979 * 2 ^ 59
def prefixEnd_587979 : Nat := 4983230072969 + 3 ^ 40 * 587979 * 2
def baseEnd_587979 : Nat := 201277227833373508772293

theorem tailTrace_587979 : CollatzResearch.WordTrace tailWord_587979 prefixEnd_587979 201277227833373508772293 := by
  unfold tailWord_587979
  simp only [CollatzResearch.WordTrace]
  refine ⟨21445355936859976663558991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14296903957906651109039327 21445355936859976663558991)
  ·
    refine ⟨32168033905289964995338487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21445355936859976663558991 32168033905289964995338487)
    ·
      refine ⟨48252050857934947493007731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32168033905289964995338487 48252050857934947493007731)
      ·
        refine ⟨72378076286902421239511597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48252050857934947493007731 72378076286902421239511597)
        ·
          refine ⟨27141778607588407964816849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72378076286902421239511597 27141778607588407964816849)
          ·
            refine ⟨20356333955691305973612637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27141778607588407964816849 20356333955691305973612637)
            ·
              refine ⟨7633625233384239740104739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20356333955691305973612637 7633625233384239740104739)
              ·
                refine ⟨11450437850076359610157109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7633625233384239740104739 11450437850076359610157109)
                ·
                  refine ⟨1073478548444658713452229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11450437850076359610157109 1073478548444658713452229)
                  ·
                    refine ⟨201277227833373508772293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1073478548444658713452229 201277227833373508772293)
                    ·
                      rfl

theorem cell22_587979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 5, 4].length) (baseStart_587979 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_587979 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_587979 prefixEnd_587979 := by exact prefixLift 587979
  have htrace : WordTrace (prefixWord ++ tailWord_587979) baseStart_587979 baseEnd_587979 := by
    simpa [prefixWord, tailWord_587979, baseEnd_587979] using wordTrace_append hprefix tailTrace_587979
  have hstable : (prefixWord ++ tailWord_587979).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587979).length < 2 ^ (prefixWord ++ tailWord_587979).sum := by decide
  have hdescent : baseEnd_587979 < baseStart_587979 := by decide
  rcases family_descends (prefixWord ++ tailWord_587979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587994 : List Nat := [3, 1, 1, 2, 2, 1, 3, 1, 8]
def baseStart_587994 : Nat := 118140960795 + 587994 * 2 ^ 59
def prefixEnd_587994 : Nat := 4983230072969 + 3 ^ 40 * 587994 * 2
def baseEnd_587994 : Nat := 67094120879972823215749

theorem tailTrace_587994 : CollatzResearch.WordTrace tailWord_587994 prefixEnd_587994 67094120879972823215749 := by
  unfold tailWord_587994
  simp only [CollatzResearch.WordTrace]
  refine ⟨5361475757951408556338759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14297268687870422816903357 5361475757951408556338759)
  ·
    refine ⟨8042213636927112834508139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5361475757951408556338759 8042213636927112834508139)
    ·
      refine ⟨12063320455390669251762209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8042213636927112834508139 12063320455390669251762209)
      ·
        refine ⟨9047490341543001938821657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12063320455390669251762209 9047490341543001938821657)
        ·
          refine ⟨6785617756157251454116243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9047490341543001938821657 6785617756157251454116243)
          ·
            refine ⟨10178426634235877181174365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6785617756157251454116243 10178426634235877181174365)
            ·
              refine ⟨3816909987838453942940387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10178426634235877181174365 3816909987838453942940387)
              ·
                refine ⟨5725364981757680914410581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3816909987838453942940387 5725364981757680914410581)
                ·
                  refine ⟨67094120879972823215749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5725364981757680914410581 67094120879972823215749)
                  ·
                    rfl

theorem cell22_587994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 8].length) (baseStart_587994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_587994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_587994 prefixEnd_587994 := by exact prefixLift 587994
  have htrace : WordTrace (prefixWord ++ tailWord_587994) baseStart_587994 baseEnd_587994 := by
    simpa [prefixWord, tailWord_587994, baseEnd_587994] using wordTrace_append hprefix tailTrace_587994
  have hstable : (prefixWord ++ tailWord_587994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587994).length < 2 ^ (prefixWord ++ tailWord_587994).sum := by decide
  have hdescent : baseEnd_587994 < baseStart_587994 := by decide
  rcases family_descends (prefixWord ++ tailWord_587994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588028 : List Nat := [2, 2, 2, 1, 4, 1, 2, 4, 4]
def baseStart_588028 : Nat := 118140960795 + 588028 * 2 ^ 59
def prefixEnd_588028 : Nat := 4983230072969 + 3 ^ 40 * 588028 * 2
def baseEnd_588028 : Nat := 67098000511584571432381

theorem tailTrace_588028 : CollatzResearch.WordTrace tailWord_588028 prefixEnd_588028 67098000511584571432381 := by
  unfold tailWord_588028
  simp only [CollatzResearch.WordTrace]
  refine ⟨10723571556841229016046369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14298095409121638688061825 10723571556841229016046369)
  ·
    refine ⟨8042678667630921762034777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10723571556841229016046369 8042678667630921762034777)
    ·
      refine ⟨6032009000723191321526083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8042678667630921762034777 6032009000723191321526083)
      ·
        refine ⟨9048013501084786982289125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6032009000723191321526083 9048013501084786982289125)
        ·
          refine ⟨1696502531453397559179211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9048013501084786982289125 1696502531453397559179211)
          ·
            refine ⟨2544753797180096338768817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1696502531453397559179211 2544753797180096338768817)
            ·
              refine ⟨1908565347885072254076613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2544753797180096338768817 1908565347885072254076613)
              ·
                refine ⟨357856002728451047639365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1908565347885072254076613 357856002728451047639365)
                ·
                  refine ⟨67098000511584571432381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 357856002728451047639365 67098000511584571432381)
                  ·
                    rfl

theorem cell22_588028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 4, 4].length) (baseStart_588028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_588028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_588028 prefixEnd_588028 := by exact prefixLift 588028
  have htrace : WordTrace (prefixWord ++ tailWord_588028) baseStart_588028 baseEnd_588028 := by
    simpa [prefixWord, tailWord_588028, baseEnd_588028] using wordTrace_append hprefix tailTrace_588028
  have hstable : (prefixWord ++ tailWord_588028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588028).length < 2 ^ (prefixWord ++ tailWord_588028).sum := by decide
  have hdescent : baseEnd_588028 < baseStart_588028 := by decide
  rcases family_descends (prefixWord ++ tailWord_588028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588062 : List Nat := [4, 3, 2, 1, 1, 1, 3, 3, 4]
def baseStart_588062 : Nat := 118140960795 + 588062 * 2 ^ 59
def prefixEnd_588062 : Nat := 4983230072969 + 3 ^ 40 * 588062 * 2
def baseEnd_588062 : Nat := 67101880143196319649013

theorem tailTrace_588062 : CollatzResearch.WordTrace tailWord_588062 prefixEnd_588062 67101880143196319649013 := by
  unfold tailWord_588062
  simp only [CollatzResearch.WordTrace]
  refine ⟨2681047899444910229853805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14298922130372854559220293 2681047899444910229853805)
  ·
    refine ⟨1005392962291841336195177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2681047899444910229853805 1005392962291841336195177)
    ·
      refine ⟨754044721718881002146383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1005392962291841336195177 754044721718881002146383)
      ·
        refine ⟨1131067082578321503219575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 754044721718881002146383 1131067082578321503219575)
        ·
          refine ⟨1696600623867482254829363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1131067082578321503219575 1696600623867482254829363)
          ·
            refine ⟨2544900935801223382244045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1696600623867482254829363 2544900935801223382244045)
            ·
              refine ⟨954337850925458768341517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2544900935801223382244045 954337850925458768341517)
              ·
                refine ⟨357876694097047038128069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 954337850925458768341517 357876694097047038128069)
                ·
                  refine ⟨67101880143196319649013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 357876694097047038128069 67101880143196319649013)
                  ·
                    rfl

theorem cell22_588062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_588062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_588062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_588062 prefixEnd_588062 := by exact prefixLift 588062
  have htrace : WordTrace (prefixWord ++ tailWord_588062) baseStart_588062 baseEnd_588062 := by
    simpa [prefixWord, tailWord_588062, baseEnd_588062] using wordTrace_append hprefix tailTrace_588062
  have hstable : (prefixWord ++ tailWord_588062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588062).length < 2 ^ (prefixWord ++ tailWord_588062).sum := by decide
  have hdescent : baseEnd_588062 < baseStart_588062 := by decide
  rcases family_descends (prefixWord ++ tailWord_588062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588088 : List Nat := [2, 1, 2, 1, 3, 1, 5, 1, 3, 3]
def baseStart_588088 : Nat := 118140960795 + 588088 * 2 ^ 59
def prefixEnd_588088 : Nat := 4983230072969 + 3 ^ 40 * 588088 * 2
def baseEnd_588088 : Nat := 201314540760933557796959

theorem tailTrace_588088 : CollatzResearch.WordTrace tailWord_588088 prefixEnd_588088 201314540760933557796959 := by
  unfold tailWord_588088
  simp only [CollatzResearch.WordTrace]
  refine ⟨10724665746732544139638459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14299554328976725519517945 10724665746732544139638459)
  ·
    refine ⟨16086998620098816209457689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10724665746732544139638459 16086998620098816209457689)
    ·
      refine ⟨12065248965074112157093267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16086998620098816209457689 12065248965074112157093267)
      ·
        refine ⟨18097873447611168235639901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12065248965074112157093267 18097873447611168235639901)
        ·
          refine ⟨6786702542854188088364963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18097873447611168235639901 6786702542854188088364963)
          ·
            refine ⟨10180053814281282132547445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6786702542854188088364963 10180053814281282132547445)
            ·
              refine ⟨954380045088870199926323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10180053814281282132547445 954380045088870199926323)
              ·
                refine ⟨1431570067633305299889485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 954380045088870199926323 1431570067633305299889485)
                ·
                  refine ⟨536838775362489487458557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1431570067633305299889485 536838775362489487458557)
                  ·
                    refine ⟨201314540760933557796959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 536838775362489487458557 201314540760933557796959)
                    ·
                      rfl

theorem cell22_588088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 1, 3, 3].length) (baseStart_588088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_588088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_588088 prefixEnd_588088 := by exact prefixLift 588088
  have htrace : WordTrace (prefixWord ++ tailWord_588088) baseStart_588088 baseEnd_588088 := by
    simpa [prefixWord, tailWord_588088, baseEnd_588088] using wordTrace_append hprefix tailTrace_588088
  have hstable : (prefixWord ++ tailWord_588088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588088).length < 2 ^ (prefixWord ++ tailWord_588088).sum := by decide
  have hdescent : baseEnd_588088 < baseStart_588088 := by decide
  rcases family_descends (prefixWord ++ tailWord_588088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588163 : List Nat := [1, 1, 1, 3, 6, 1, 1, 2, 6]
def baseStart_588163 : Nat := 118140960795 + 588163 * 2 ^ 59
def prefixEnd_588163 : Nat := 4983230072969 + 3 ^ 40 * 588163 * 2
def baseEnd_588163 : Nat := 67113404931219454057243

theorem tailTrace_588163 : CollatzResearch.WordTrace tailWord_588163 prefixEnd_588163 67113404931219454057243 := by
  unfold tailWord_588163
  simp only [CollatzResearch.WordTrace]
  refine ⟨21452066968193376088257143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14301377978795584058838095 21452066968193376088257143)
  ·
    refine ⟨32178100452290064132385715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21452066968193376088257143 32178100452290064132385715)
    ·
      refine ⟨48267150678435096198578573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32178100452290064132385715 48267150678435096198578573)
      ·
        refine ⟨18100181504413161074466965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48267150678435096198578573 18100181504413161074466965)
        ·
          refine ⟨848446008019366925365639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 18100181504413161074466965 848446008019366925365639)
          ·
            refine ⟨1272669012029050388048459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 848446008019366925365639 1272669012029050388048459)
            ·
              refine ⟨1909003518043575582072689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1272669012029050388048459 1909003518043575582072689)
              ·
                refine ⟨1431752638532681686554517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1909003518043575582072689 1431752638532681686554517)
                ·
                  refine ⟨67113404931219454057243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1431752638532681686554517 67113404931219454057243)
                  ·
                    rfl

theorem cell22_588163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 2, 6].length) (baseStart_588163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_588163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_588163 prefixEnd_588163 := by exact prefixLift 588163
  have htrace : WordTrace (prefixWord ++ tailWord_588163) baseStart_588163 baseEnd_588163 := by
    simpa [prefixWord, tailWord_588163, baseEnd_588163] using wordTrace_append hprefix tailTrace_588163
  have hstable : (prefixWord ++ tailWord_588163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588163).length < 2 ^ (prefixWord ++ tailWord_588163).sum := by decide
  have hdescent : baseEnd_588163 < baseStart_588163 := by decide
  rcases family_descends (prefixWord ++ tailWord_588163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588176 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 8, 4]
def baseStart_588176 : Nat := 118140960795 + 588176 * 2 ^ 59
def prefixEnd_588176 : Nat := 4983230072969 + 3 ^ 40 * 588176 * 2
def baseEnd_588176 : Nat := 201344664959330661596689

theorem tailTrace_588176 : CollatzResearch.WordTrace tailWord_588176 prefixEnd_588176 201344664959330661596689 := by
  unfold tailWord_588176
  simp only [CollatzResearch.WordTrace]
  refine ⟨10726270558573139654240191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14301694078097519538986921 10726270558573139654240191)
  ·
    refine ⟨16089405837859709481360287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10726270558573139654240191 16089405837859709481360287)
    ·
      refine ⟨24134108756789564222040431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16089405837859709481360287 24134108756789564222040431)
      ·
        refine ⟨36201163135184346333060647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24134108756789564222040431 36201163135184346333060647)
        ·
          refine ⟨54301744702776519499590971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36201163135184346333060647 54301744702776519499590971)
          ·
            refine ⟨81452617054164779249386457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54301744702776519499590971 81452617054164779249386457)
            ·
              refine ⟨61089462790623584437039843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81452617054164779249386457 61089462790623584437039843)
              ·
                refine ⟨91634194185935376655559765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61089462790623584437039843 91634194185935376655559765)
                ·
                  refine ⟨1073838213116430195182341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 91634194185935376655559765 1073838213116430195182341)
                  ·
                    refine ⟨201344664959330661596689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1073838213116430195182341 201344664959330661596689)
                    ·
                      rfl

theorem cell22_588176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 8, 4].length) (baseStart_588176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_588176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_588176 prefixEnd_588176 := by exact prefixLift 588176
  have htrace : WordTrace (prefixWord ++ tailWord_588176) baseStart_588176 baseEnd_588176 := by
    simpa [prefixWord, tailWord_588176, baseEnd_588176] using wordTrace_append hprefix tailTrace_588176
  have hstable : (prefixWord ++ tailWord_588176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588176).length < 2 ^ (prefixWord ++ tailWord_588176).sum := by decide
  have hdescent : baseEnd_588176 < baseStart_588176 := by decide
  rcases family_descends (prefixWord ++ tailWord_588176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588191 : List Nat := [1, 1, 2, 5, 1, 1, 11]
def baseStart_588191 : Nat := 118140960795 + 588191 * 2 ^ 59
def prefixEnd_588191 : Nat := 4983230072969 + 3 ^ 40 * 588191 * 2
def baseEnd_588191 : Nat := 7457399991328726758209

theorem tailTrace_588191 : CollatzResearch.WordTrace tailWord_588191 prefixEnd_588191 7457399991328726758209 := by
  unfold tailWord_588191
  simp only [CollatzResearch.WordTrace]
  refine ⟨21453088212091936870276427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14302058808061291246850951 21453088212091936870276427)
  ·
    refine ⟨32179632318137905305414641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21453088212091936870276427 32179632318137905305414641)
    ·
      refine ⟨24134724238603428979060981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32179632318137905305414641 24134724238603428979060981)
      ·
        refine ⟨2262630397369071466786967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24134724238603428979060981 2262630397369071466786967)
        ·
          refine ⟨3393945596053607200180451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2262630397369071466786967 3393945596053607200180451)
          ·
            refine ⟨5090918394080410800270677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3393945596053607200180451 5090918394080410800270677)
            ·
              refine ⟨7457399991328726758209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 5090918394080410800270677 7457399991328726758209)
              ·
                rfl

theorem cell22_588191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 11].length) (baseStart_588191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_588191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_588191 prefixEnd_588191 := by exact prefixLift 588191
  have htrace : WordTrace (prefixWord ++ tailWord_588191) baseStart_588191 baseEnd_588191 := by
    simpa [prefixWord, tailWord_588191, baseEnd_588191] using wordTrace_append hprefix tailTrace_588191
  have hstable : (prefixWord ++ tailWord_588191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588191).length < 2 ^ (prefixWord ++ tailWord_588191).sum := by decide
  have hdescent : baseEnd_588191 < baseStart_588191 := by decide
  rcases family_descends (prefixWord ++ tailWord_588191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588195 : List Nat := [1, 1, 1, 4, 1, 4, 3, 2, 2, 3]
def baseStart_588195 : Nat := 118140960795 + 588195 * 2 ^ 59
def prefixEnd_588195 : Nat := 4983230072969 + 3 ^ 40 * 588195 * 2
def baseEnd_588195 : Nat := 201351169047620945371631

theorem tailTrace_588195 : CollatzResearch.WordTrace tailWord_588195 prefixEnd_588195 201351169047620945371631 := by
  unfold tailWord_588195
  simp only [CollatzResearch.WordTrace]
  refine ⟨21453234104077445553422039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14302156069384963702281359 21453234104077445553422039)
  ·
    refine ⟨32179851156116168330133059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21453234104077445553422039 32179851156116168330133059)
    ·
      refine ⟨48269776734174252495199589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32179851156116168330133059 48269776734174252495199589)
      ·
        refine ⟨9050583137657672342849923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48269776734174252495199589 9050583137657672342849923)
        ·
          refine ⟨13575874706486508514274885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9050583137657672342849923 13575874706486508514274885)
          ·
            refine ⟨2545476507466220346426541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13575874706486508514274885 2545476507466220346426541)
            ·
              refine ⟨954553690299832629909953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2545476507466220346426541 954553690299832629909953)
              ·
                refine ⟨715915267724874472432465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 954553690299832629909953 715915267724874472432465)
                ·
                  refine ⟨536936450793655854324349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 715915267724874472432465 536936450793655854324349)
                  ·
                    refine ⟨201351169047620945371631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 536936450793655854324349 201351169047620945371631)
                    ·
                      rfl

theorem cell22_588195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 2, 2, 3].length) (baseStart_588195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_588195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_588195 prefixEnd_588195 := by exact prefixLift 588195
  have htrace : WordTrace (prefixWord ++ tailWord_588195) baseStart_588195 baseEnd_588195 := by
    simpa [prefixWord, tailWord_588195, baseEnd_588195] using wordTrace_append hprefix tailTrace_588195
  have hstable : (prefixWord ++ tailWord_588195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588195).length < 2 ^ (prefixWord ++ tailWord_588195).sum := by decide
  have hdescent : baseEnd_588195 < baseStart_588195 := by decide
  rcases family_descends (prefixWord ++ tailWord_588195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588242 : List Nat := [3, 2, 2, 4, 2, 1, 8]
def baseStart_588242 : Nat := 118140960795 + 588242 * 2 ^ 59
def prefixEnd_588242 : Nat := 4983230072969 + 3 ^ 40 * 588242 * 2
def baseEnd_588242 : Nat := 7458046596597351460981

theorem tailTrace_588242 : CollatzResearch.WordTrace tailWord_588242 prefixEnd_588242 7458046596597351460981 := by
  unfold tailWord_588242
  simp only [CollatzResearch.WordTrace]
  refine ⟨5363737083726793145095745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14303298889938115053588653 5363737083726793145095745)
  ·
    refine ⟨4022802812795094858821809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5363737083726793145095745 4022802812795094858821809)
    ·
      refine ⟨3017102109596321144116357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4022802812795094858821809 3017102109596321144116357)
      ·
        refine ⟨565706645549310214521817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3017102109596321144116357 565706645549310214521817)
        ·
          refine ⟨424279984161982660891363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 565706645549310214521817 424279984161982660891363)
          ·
            refine ⟨636419976242973991337045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 424279984161982660891363 636419976242973991337045)
            ·
              refine ⟨7458046596597351460981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 636419976242973991337045 7458046596597351460981)
              ·
                rfl

theorem cell22_588242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 8].length) (baseStart_588242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_588242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_588242 prefixEnd_588242 := by exact prefixLift 588242
  have htrace : WordTrace (prefixWord ++ tailWord_588242) baseStart_588242 baseEnd_588242 := by
    simpa [prefixWord, tailWord_588242, baseEnd_588242] using wordTrace_append hprefix tailTrace_588242
  have hstable : (prefixWord ++ tailWord_588242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588242).length < 2 ^ (prefixWord ++ tailWord_588242).sum := by decide
  have hdescent : baseEnd_588242 < baseStart_588242 := by decide
  rcases family_descends (prefixWord ++ tailWord_588242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588253 : List Nat := [1, 4, 3, 1, 1, 1, 1, 3, 7]
def baseStart_588253 : Nat := 118140960795 + 588253 * 2 ^ 59
def prefixEnd_588253 : Nat := 4983230072969 + 3 ^ 40 * 588253 * 2
def baseEnd_588253 : Nat := 67123674544309375807151

theorem tailTrace_588253 : CollatzResearch.WordTrace tailWord_588253 prefixEnd_588253 67123674544309375807151 := by
  unfold tailWord_588253
  simp only [CollatzResearch.WordTrace]
  refine ⟨21455349537867321459033413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14303566358578214306022275 21455349537867321459033413)
  ·
    refine ⟨4022878038350122773568765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21455349537867321459033413 4022878038350122773568765)
    ·
      refine ⟨1508579264381296040088287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4022878038350122773568765 1508579264381296040088287)
      ·
        refine ⟨2262868896571944060132431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1508579264381296040088287 2262868896571944060132431)
        ·
          refine ⟨3394303344857916090198647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2262868896571944060132431 3394303344857916090198647)
          ·
            refine ⟨5091455017286874135297971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3394303344857916090198647 5091455017286874135297971)
            ·
              refine ⟨7637182525930311202946957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5091455017286874135297971 7637182525930311202946957)
              ·
                refine ⟨2863943447223866701105109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7637182525930311202946957 2863943447223866701105109)
                ·
                  refine ⟨67123674544309375807151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2863943447223866701105109 67123674544309375807151)
                  ·
                    rfl

theorem cell22_588253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 3, 7].length) (baseStart_588253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_588253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_588253 prefixEnd_588253 := by exact prefixLift 588253
  have htrace : WordTrace (prefixWord ++ tailWord_588253) baseStart_588253 baseEnd_588253 := by
    simpa [prefixWord, tailWord_588253, baseEnd_588253] using wordTrace_append hprefix tailTrace_588253
  have hstable : (prefixWord ++ tailWord_588253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588253).length < 2 ^ (prefixWord ++ tailWord_588253).sum := by decide
  have hdescent : baseEnd_588253 < baseStart_588253 := by decide
  rcases family_descends (prefixWord ++ tailWord_588253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588270 : List Nat := [4, 1, 2, 1, 2, 3, 1, 3, 5]
def baseStart_588270 : Nat := 118140960795 + 588270 * 2 ^ 59
def prefixEnd_588270 : Nat := 4983230072969 + 3 ^ 40 * 588270 * 2
def baseEnd_588270 : Nat := 67125614360115249915467

theorem tailTrace_588270 : CollatzResearch.WordTrace tailWord_588270 prefixEnd_588270 67125614360115249915467 := by
  unfold tailWord_588270
  simp only [CollatzResearch.WordTrace]
  refine ⟨2681996197350716670300283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14303979719203822241601509 2681996197350716670300283)
  ·
    refine ⟨4022994296026075005450425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2681996197350716670300283 4022994296026075005450425)
    ·
      refine ⟨3017245722019556254087819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4022994296026075005450425 3017245722019556254087819)
      ·
        refine ⟨4525868583029334381131729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3017245722019556254087819 4525868583029334381131729)
        ·
          refine ⟨3394401437272000785848797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4525868583029334381131729 3394401437272000785848797)
          ·
            refine ⟨1272900538977000294693299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3394401437272000785848797 1272900538977000294693299)
            ·
              refine ⟨1909350808465500442039949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1272900538977000294693299 1909350808465500442039949)
              ·
                refine ⟨716006553174562665764981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1909350808465500442039949 716006553174562665764981)
                ·
                  refine ⟨67125614360115249915467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 716006553174562665764981 67125614360115249915467)
                  ·
                    rfl

theorem cell22_588270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 3, 5].length) (baseStart_588270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_588270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_588270 prefixEnd_588270 := by exact prefixLift 588270
  have htrace : WordTrace (prefixWord ++ tailWord_588270) baseStart_588270 baseEnd_588270 := by
    simpa [prefixWord, tailWord_588270, baseEnd_588270] using wordTrace_append hprefix tailTrace_588270
  have hstable : (prefixWord ++ tailWord_588270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588270).length < 2 ^ (prefixWord ++ tailWord_588270).sum := by decide
  have hdescent : baseEnd_588270 < baseStart_588270 := by decide
  rcases family_descends (prefixWord ++ tailWord_588270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588308 : List Nat := [2, 4, 3, 1, 1, 3, 2, 2, 1, 3]
def baseStart_588308 : Nat := 118140960795 + 588308 * 2 ^ 59
def prefixEnd_588308 : Nat := 4983230072969 + 3 ^ 40 * 588308 * 2
def baseEnd_588308 : Nat := 201389851256926317296285

theorem tailTrace_588308 : CollatzResearch.WordTrace tailWord_588308 prefixEnd_588308 201389851256926317296285 := by
  unfold tailWord_588308
  simp only [CollatzResearch.WordTrace]
  refine ⟨10728677776334032926142789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14304903701778710568190385 10728677776334032926142789)
  ·
    refine ⟨2011627083062631173651773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10728677776334032926142789 2011627083062631173651773)
    ·
      refine ⟨754360156148486690119415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2011627083062631173651773 754360156148486690119415)
      ·
        refine ⟨1131540234222730035179123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 754360156148486690119415 1131540234222730035179123)
        ·
          refine ⟨1697310351334095052768685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1131540234222730035179123 1697310351334095052768685)
          ·
            refine ⟨636491381750285644788257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1697310351334095052768685 636491381750285644788257)
            ·
              refine ⟨477368536312714233591193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 636491381750285644788257 477368536312714233591193)
              ·
                refine ⟨358026402234535675193395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 477368536312714233591193 358026402234535675193395)
                ·
                  refine ⟨537039603351803512790093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 358026402234535675193395 537039603351803512790093)
                  ·
                    refine ⟨201389851256926317296285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 537039603351803512790093 201389851256926317296285)
                    ·
                      rfl

theorem cell22_588308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_588308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_588308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_588308 prefixEnd_588308 := by exact prefixLift 588308
  have htrace : WordTrace (prefixWord ++ tailWord_588308) baseStart_588308 baseEnd_588308 := by
    simpa [prefixWord, tailWord_588308, baseEnd_588308] using wordTrace_append hprefix tailTrace_588308
  have hstable : (prefixWord ++ tailWord_588308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588308).length < 2 ^ (prefixWord ++ tailWord_588308).sum := by decide
  have hdescent : baseEnd_588308 < baseStart_588308 := by decide
  rcases family_descends (prefixWord ++ tailWord_588308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588330 : List Nat := [3, 1, 4, 1, 1, 2, 1, 3, 1, 5]
def baseStart_588330 : Nat := 118140960795 + 588330 * 2 ^ 59
def prefixEnd_588330 : Nat := 4983230072969 + 3 ^ 40 * 588330 * 2
def baseEnd_588330 : Nat := 201397382306525593246217

theorem tailTrace_588330 : CollatzResearch.WordTrace tailWord_588330 prefixEnd_588330 201397382306525593246217 := by
  unfold tailWord_588330
  simp only [CollatzResearch.WordTrace]
  refine ⟨5364539489647090902396611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14305438639058909073057629 5364539489647090902396611)
  ·
    refine ⟨8046809234470636353594917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5364539489647090902396611 8046809234470636353594917)
    ·
      refine ⟨1508776731463244316299047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8046809234470636353594917 1508776731463244316299047)
      ·
        refine ⟨2263165097194866474448571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1508776731463244316299047 2263165097194866474448571)
        ·
          refine ⟨3394747645792299711672857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2263165097194866474448571 3394747645792299711672857)
          ·
            refine ⟨2546060734344224783754643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3394747645792299711672857 2546060734344224783754643)
            ·
              refine ⟨3819091101516337175631965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2546060734344224783754643 3819091101516337175631965)
              ·
                refine ⟨1432159163068626440861987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3819091101516337175631965 1432159163068626440861987)
                ·
                  refine ⟨2148238744602939661292981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1432159163068626440861987 2148238744602939661292981)
                  ·
                    refine ⟨201397382306525593246217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2148238744602939661292981 201397382306525593246217)
                    ·
                      rfl

theorem cell22_588330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_588330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_588330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_588330 prefixEnd_588330 := by exact prefixLift 588330
  have htrace : WordTrace (prefixWord ++ tailWord_588330) baseStart_588330 baseEnd_588330 := by
    simpa [prefixWord, tailWord_588330, baseEnd_588330] using wordTrace_append hprefix tailTrace_588330
  have hstable : (prefixWord ++ tailWord_588330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588330).length < 2 ^ (prefixWord ++ tailWord_588330).sum := by decide
  have hdescent : baseEnd_588330 < baseStart_588330 := by decide
  rcases family_descends (prefixWord ++ tailWord_588330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588373 : List Nat := [1, 3, 2, 2, 1, 1, 2, 1, 1, 8]
def baseStart_588373 : Nat := 118140960795 + 588373 * 2 ^ 59
def prefixEnd_588373 : Nat := 4983230072969 + 3 ^ 40 * 588373 * 2
def baseEnd_588373 : Nat := 201412102085287814421085

theorem tailTrace_588373 : CollatzResearch.WordTrace tailWord_588373 prefixEnd_588373 201412102085287814421085 := by
  unfold tailWord_588373
  simp only [CollatzResearch.WordTrace]
  refine ⟨21459726297432581953401773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14306484198288387968934515 21459726297432581953401773)
  ·
    refine ⟨8047397361537218232525665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21459726297432581953401773 8047397361537218232525665)
    ·
      refine ⟨6035548021152913674394249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8047397361537218232525665 6035548021152913674394249)
      ·
        refine ⟨4526661015864685255795687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6035548021152913674394249 4526661015864685255795687)
        ·
          refine ⟨6789991523797027883693531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4526661015864685255795687 6789991523797027883693531)
          ·
            refine ⟨10184987285695541825540297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6789991523797027883693531 10184987285695541825540297)
            ·
              refine ⟨7638740464271656369155223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10184987285695541825540297 7638740464271656369155223)
              ·
                refine ⟨11458110696407484553732835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7638740464271656369155223 11458110696407484553732835)
                ·
                  refine ⟨17187166044611226830599253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11458110696407484553732835 17187166044611226830599253)
                  ·
                    refine ⟨201412102085287814421085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 17187166044611226830599253 201412102085287814421085)
                    ·
                      rfl

theorem cell22_588373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 8].length) (baseStart_588373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_588373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_588373 prefixEnd_588373 := by exact prefixLift 588373
  have htrace : WordTrace (prefixWord ++ tailWord_588373) baseStart_588373 baseEnd_588373 := by
    simpa [prefixWord, tailWord_588373, baseEnd_588373] using wordTrace_append hprefix tailTrace_588373
  have hstable : (prefixWord ++ tailWord_588373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588373).length < 2 ^ (prefixWord ++ tailWord_588373).sum := by decide
  have hdescent : baseEnd_588373 < baseStart_588373 := by decide
  rcases family_descends (prefixWord ++ tailWord_588373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588403 : List Nat := [1, 1, 1, 2, 2, 1, 1, 4, 4, 5]
def baseStart_588403 : Nat := 118140960795 + 588403 * 2 ^ 59
def prefixEnd_588403 : Nat := 4983230072969 + 3 ^ 40 * 588403 * 2
def baseEnd_588403 : Nat := 201422371698377736170993

theorem tailTrace_588403 : CollatzResearch.WordTrace tailWord_588403 prefixEnd_588403 201422371698377736170993 := by
  unfold tailWord_588403
  simp only [CollatzResearch.WordTrace]
  refine ⟨21460820487323897076993863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14307213658215931384662575 21460820487323897076993863)
  ·
    refine ⟨32191230730985845615490795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21460820487323897076993863 32191230730985845615490795)
    ·
      refine ⟨48286846096478768423236193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32191230730985845615490795 48286846096478768423236193)
      ·
        refine ⟨36215134572359076317427145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48286846096478768423236193 36215134572359076317427145)
        ·
          refine ⟨27161350929269307238070359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36215134572359076317427145 27161350929269307238070359)
          ·
            refine ⟨40742026393903960857105539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27161350929269307238070359 40742026393903960857105539)
            ·
              refine ⟨61113039590855941285658309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40742026393903960857105539 61113039590855941285658309)
              ·
                refine ⟨11458694923285488991060933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61113039590855941285658309 11458694923285488991060933)
                ·
                  refine ⟨2148505298116029185823925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11458694923285488991060933 2148505298116029185823925)
                  ·
                    refine ⟨201422371698377736170993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2148505298116029185823925 201422371698377736170993)
                    ·
                      rfl

theorem cell22_588403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 4, 5].length) (baseStart_588403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_588403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_588403 prefixEnd_588403 := by exact prefixLift 588403
  have htrace : WordTrace (prefixWord ++ tailWord_588403) baseStart_588403 baseEnd_588403 := by
    simpa [prefixWord, tailWord_588403, baseEnd_588403] using wordTrace_append hprefix tailTrace_588403
  have hstable : (prefixWord ++ tailWord_588403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588403).length < 2 ^ (prefixWord ++ tailWord_588403).sum := by decide
  have hdescent : baseEnd_588403 < baseStart_588403 := by decide
  rcases family_descends (prefixWord ++ tailWord_588403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588409 : List Nat := [1, 2, 1, 3, 3, 2, 3, 3, 1, 3]
def baseStart_588409 : Nat := 118140960795 + 588409 * 2 ^ 59
def prefixEnd_588409 : Nat := 4983230072969 + 3 ^ 40 * 588409 * 2
def baseEnd_588409 : Nat := 201424425620995720520975

theorem tailTrace_588409 : CollatzResearch.WordTrace tailWord_588409 prefixEnd_588409 201424425620995720520975 := by
  unfold tailWord_588409
  simp only [CollatzResearch.WordTrace]
  refine ⟨21461039325302160101712281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14307359550201440067808187 21461039325302160101712281)
  ·
    refine ⟨16095779493976620076284211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21461039325302160101712281 16095779493976620076284211)
    ·
      refine ⟨24143669240964930114426317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16095779493976620076284211 24143669240964930114426317)
      ·
        refine ⟨9053875965361848792909869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24143669240964930114426317 9053875965361848792909869)
        ·
          refine ⟨3395203487010693297341201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9053875965361848792909869 3395203487010693297341201)
          ·
            refine ⟨2546402615258019973005901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3395203487010693297341201 2546402615258019973005901)
            ·
              refine ⟨954900980721757489877213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2546402615258019973005901 954900980721757489877213)
              ·
                refine ⟨358087867770659058703955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 954900980721757489877213 358087867770659058703955)
                ·
                  refine ⟨537131801655988588055933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 358087867770659058703955 537131801655988588055933)
                  ·
                    refine ⟨201424425620995720520975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 537131801655988588055933 201424425620995720520975)
                    ·
                      rfl

theorem cell22_588409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 3, 1, 3].length) (baseStart_588409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_588409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_588409 prefixEnd_588409 := by exact prefixLift 588409
  have htrace : WordTrace (prefixWord ++ tailWord_588409) baseStart_588409 baseEnd_588409 := by
    simpa [prefixWord, tailWord_588409, baseEnd_588409] using wordTrace_append hprefix tailTrace_588409
  have hstable : (prefixWord ++ tailWord_588409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588409).length < 2 ^ (prefixWord ++ tailWord_588409).sum := by decide
  have hdescent : baseEnd_588409 < baseStart_588409 := by decide
  rcases family_descends (prefixWord ++ tailWord_588409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588426 : List Nat := [3, 1, 2, 3, 4, 1, 1, 1, 3, 3]
def baseStart_588426 : Nat := 118140960795 + 588426 * 2 ^ 59
def prefixEnd_588426 : Nat := 4983230072969 + 3 ^ 40 * 588426 * 2
def baseEnd_588426 : Nat := 201430245068413342845923

theorem tailTrace_588426 : CollatzResearch.WordTrace tailWord_588426 prefixEnd_588426 201430245068413342845923 := by
  unfold tailWord_588426
  simp only [CollatzResearch.WordTrace]
  refine ⟨5365414841560143001270283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14307772910827048003387421 5365414841560143001270283)
  ·
    refine ⟨8048122262340214501905425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5365414841560143001270283 8048122262340214501905425)
    ·
      refine ⟨6036091696755160876429069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8048122262340214501905425 6036091696755160876429069)
      ·
        refine ⟨2263534386283185328660901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6036091696755160876429069 2263534386283185328660901)
        ·
          refine ⟨424412697428097249123919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2263534386283185328660901 424412697428097249123919)
          ·
            refine ⟨636619046142145873685879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 424412697428097249123919 636619046142145873685879)
            ·
              refine ⟨954928569213218810528819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 636619046142145873685879 954928569213218810528819)
              ·
                refine ⟨1432392853819828215793229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 954928569213218810528819 1432392853819828215793229)
                ·
                  refine ⟨537147320182435580922461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1432392853819828215793229 537147320182435580922461)
                  ·
                    refine ⟨201430245068413342845923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 537147320182435580922461 201430245068413342845923)
                    ·
                      rfl

theorem cell22_588426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 1, 3, 3].length) (baseStart_588426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_588426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_588426 prefixEnd_588426 := by exact prefixLift 588426
  have htrace : WordTrace (prefixWord ++ tailWord_588426) baseStart_588426 baseEnd_588426 := by
    simpa [prefixWord, tailWord_588426, baseEnd_588426] using wordTrace_append hprefix tailTrace_588426
  have hstable : (prefixWord ++ tailWord_588426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588426).length < 2 ^ (prefixWord ++ tailWord_588426).sum := by decide
  have hdescent : baseEnd_588426 < baseStart_588426 := by decide
  rcases family_descends (prefixWord ++ tailWord_588426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588484 : List Nat := [2, 3, 3, 1, 1, 3, 1, 4, 4]
def baseStart_588484 : Nat := 118140960795 + 588484 * 2 ^ 59
def prefixEnd_588484 : Nat := 4983230072969 + 3 ^ 40 * 588484 * 2
def baseEnd_588484 : Nat := 67150033217906841631915

theorem tailTrace_588484 : CollatzResearch.WordTrace tailWord_588484 prefixEnd_588484 67150033217906841631915 := by
  unfold tailWord_588484
  simp only [CollatzResearch.WordTrace]
  refine ⟨10731887400015223955346253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14309183200020298607128337 10731887400015223955346253)
  ·
    refine ⟨4024457775005708983254845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10731887400015223955346253 4024457775005708983254845)
    ·
      refine ⟨1509171665627140868720567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4024457775005708983254845 1509171665627140868720567)
      ·
        refine ⟨2263757498440711303080851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1509171665627140868720567 2263757498440711303080851)
        ·
          refine ⟨3395636247661066954621277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2263757498440711303080851 3395636247661066954621277)
          ·
            refine ⟨1273363592872900107982979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3395636247661066954621277 1273363592872900107982979)
            ·
              refine ⟨1910045389309350161974469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1273363592872900107982979 1910045389309350161974469)
              ·
                refine ⟨358133510495503155370213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1910045389309350161974469 358133510495503155370213)
                ·
                  refine ⟨67150033217906841631915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 358133510495503155370213 67150033217906841631915)
                  ·
                    rfl

theorem cell22_588484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 4, 4].length) (baseStart_588484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_588484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_588484 prefixEnd_588484 := by exact prefixLift 588484
  have htrace : WordTrace (prefixWord ++ tailWord_588484) baseStart_588484 baseEnd_588484 := by
    simpa [prefixWord, tailWord_588484, baseEnd_588484] using wordTrace_append hprefix tailTrace_588484
  have hstable : (prefixWord ++ tailWord_588484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588484).length < 2 ^ (prefixWord ++ tailWord_588484).sum := by decide
  have hdescent : baseEnd_588484 < baseStart_588484 := by decide
  rcases family_descends (prefixWord ++ tailWord_588484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588533 : List Nat := [1, 3, 6, 1, 1, 1, 1, 1, 4, 3]
def baseStart_588533 : Nat := 118140960795 + 588533 * 2 ^ 59
def prefixEnd_588533 : Nat := 4983230072969 + 3 ^ 40 * 588533 * 2
def baseEnd_588533 : Nat := 201466873355100730420595

theorem tailTrace_588533 : CollatzResearch.WordTrace tailWord_588533 prefixEnd_588533 201466873355100730420595 := by
  unfold tailWord_588533
  simp only [CollatzResearch.WordTrace]
  refine ⟨21465561976852929279226253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14310374651235286186150835 21465561976852929279226253)
  ·
    refine ⟨8049585741319848479709845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21465561976852929279226253 8049585741319848479709845)
    ·
      refine ⟨377324331624367897486399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 8049585741319848479709845 377324331624367897486399)
      ·
        refine ⟨565986497436551846229599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 377324331624367897486399 565986497436551846229599)
        ·
          refine ⟨848979746154827769344399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 565986497436551846229599 848979746154827769344399)
          ·
            refine ⟨1273469619232241654016599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 848979746154827769344399 1273469619232241654016599)
            ·
              refine ⟨1910204428848362481024899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1273469619232241654016599 1910204428848362481024899)
              ·
                refine ⟨2865306643272543721537349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1910204428848362481024899 2865306643272543721537349)
                ·
                  refine ⟨537244995613601947788253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2865306643272543721537349 537244995613601947788253)
                  ·
                    refine ⟨201466873355100730420595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 537244995613601947788253 201466873355100730420595)
                    ·
                      rfl

theorem cell22_588533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_588533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_588533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_588533 prefixEnd_588533 := by exact prefixLift 588533
  have htrace : WordTrace (prefixWord ++ tailWord_588533) baseStart_588533 baseEnd_588533 := by
    simpa [prefixWord, tailWord_588533, baseEnd_588533] using wordTrace_append hprefix tailTrace_588533
  have hstable : (prefixWord ++ tailWord_588533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588533).length < 2 ^ (prefixWord ++ tailWord_588533).sum := by decide
  have hdescent : baseEnd_588533 < baseStart_588533 := by decide
  rcases family_descends (prefixWord ++ tailWord_588533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588578 : List Nat := [3, 3, 1, 1, 2, 4, 1, 3, 1, 3]
def baseStart_588578 : Nat := 118140960795 + 588578 * 2 ^ 59
def prefixEnd_588578 : Nat := 4983230072969 + 3 ^ 40 * 588578 * 2
def baseEnd_588578 : Nat := 201482277774735613045457

theorem tailTrace_588578 : CollatzResearch.WordTrace tailWord_588578 prefixEnd_588578 201482277774735613045457 := by
  unfold tailWord_588578
  simp only [CollatzResearch.WordTrace]
  refine ⟨5366800815422475491153597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14311468841126601309742925 5366800815422475491153597)
  ·
    refine ⟨2012550305783428309182599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5366800815422475491153597 2012550305783428309182599)
    ·
      refine ⟨3018825458675142463773899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2012550305783428309182599 3018825458675142463773899)
      ·
        refine ⟨4528238188012713695660849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3018825458675142463773899 4528238188012713695660849)
        ·
          refine ⟨3396178641009535271745637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4528238188012713695660849 3396178641009535271745637)
          ·
            refine ⟨636783495189287863452307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3396178641009535271745637 636783495189287863452307)
            ·
              refine ⟨955175242783931795178461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 636783495189287863452307 955175242783931795178461)
              ·
                refine ⟨358190716043974423191923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 955175242783931795178461 358190716043974423191923)
                ·
                  refine ⟨537286074065961634787885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 358190716043974423191923 537286074065961634787885)
                  ·
                    refine ⟨201482277774735613045457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 537286074065961634787885 201482277774735613045457)
                    ·
                      rfl

theorem cell22_588578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 3, 1, 3].length) (baseStart_588578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_588578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_588578 prefixEnd_588578 := by exact prefixLift 588578
  have htrace : WordTrace (prefixWord ++ tailWord_588578) baseStart_588578 baseEnd_588578 := by
    simpa [prefixWord, tailWord_588578, baseEnd_588578] using wordTrace_append hprefix tailTrace_588578
  have hstable : (prefixWord ++ tailWord_588578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588578).length < 2 ^ (prefixWord ++ tailWord_588578).sum := by decide
  have hdescent : baseEnd_588578 < baseStart_588578 := by decide
  rcases family_descends (prefixWord ++ tailWord_588578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588621 : List Nat := [1, 6, 1, 2, 2, 1, 1, 1, 3, 4]
def baseStart_588621 : Nat := 118140960795 + 588621 * 2 ^ 59
def prefixEnd_588621 : Nat := 4983230072969 + 3 ^ 40 * 588621 * 2
def baseEnd_588621 : Nat := 201496997553497834220325

theorem tailTrace_588621 : CollatzResearch.WordTrace tailWord_588621 prefixEnd_588621 201496997553497834220325 := by
  unfold tailWord_588621
  simp only [CollatzResearch.WordTrace]
  refine ⟨21468771600534120308429717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14312514400356080205619811 21468771600534120308429717)
  ·
    refine ⟨1006348668775036889457643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 21468771600534120308429717 1006348668775036889457643)
    ·
      refine ⟨1509523003162555334186465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1006348668775036889457643 1509523003162555334186465)
      ·
        refine ⟨1132142252371916500639849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1509523003162555334186465 1132142252371916500639849)
        ·
          refine ⟨849106689278937375479887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1132142252371916500639849 849106689278937375479887)
          ·
            refine ⟨1273660033918406063219831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 849106689278937375479887 1273660033918406063219831)
            ·
              refine ⟨1910490050877609094829747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1273660033918406063219831 1910490050877609094829747)
              ·
                refine ⟨2865735076316413642244621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1910490050877609094829747 2865735076316413642244621)
                ·
                  refine ⟨1074650653618655115841733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2865735076316413642244621 1074650653618655115841733)
                  ·
                    refine ⟨201496997553497834220325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1074650653618655115841733 201496997553497834220325)
                    ·
                      rfl

theorem cell22_588621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_588621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_588621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_588621 prefixEnd_588621 := by exact prefixLift 588621
  have htrace : WordTrace (prefixWord ++ tailWord_588621) baseStart_588621 baseEnd_588621 := by
    simpa [prefixWord, tailWord_588621, baseEnd_588621] using wordTrace_append hprefix tailTrace_588621
  have hstable : (prefixWord ++ tailWord_588621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588621).length < 2 ^ (prefixWord ++ tailWord_588621).sum := by decide
  have hdescent : baseEnd_588621 < baseStart_588621 := by decide
  rcases family_descends (prefixWord ++ tailWord_588621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588679 : List Nat := [1, 1, 4, 2, 3, 1, 1, 1, 5, 3]
def baseStart_588679 : Nat := 118140960795 + 588679 * 2 ^ 59
def prefixEnd_588679 : Nat := 4983230072969 + 3 ^ 40 * 588679 * 2
def baseEnd_588679 : Nat := 201516852138805016270147

theorem tailTrace_588679 : CollatzResearch.WordTrace tailWord_588679 prefixEnd_588679 201516852138805016270147 := by
  unfold tailWord_588679
  simp only [CollatzResearch.WordTrace]
  refine ⟨21470887034323996214041091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14313924689549330809360727 21470887034323996214041091)
  ·
    refine ⟨32206330551485994321061637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21470887034323996214041091 32206330551485994321061637)
    ·
      refine ⟨6038686978403623935199057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32206330551485994321061637 6038686978403623935199057)
      ·
        refine ⟨4529015233802717951399293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6038686978403623935199057 4529015233802717951399293)
        ·
          refine ⟨1698380712676019231774735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4529015233802717951399293 1698380712676019231774735)
          ·
            refine ⟨2547571069014028847662103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1698380712676019231774735 2547571069014028847662103)
            ·
              refine ⟨3821356603521043271493155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2547571069014028847662103 3821356603521043271493155)
              ·
                refine ⟨5732034905281564907239733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3821356603521043271493155 5732034905281564907239733)
                ·
                  refine ⟨537378272370146710053725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5732034905281564907239733 537378272370146710053725)
                  ·
                    refine ⟨201516852138805016270147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 537378272370146710053725 201516852138805016270147)
                    ·
                      rfl

theorem cell22_588679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 5, 3].length) (baseStart_588679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_588679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_588679 prefixEnd_588679 := by exact prefixLift 588679
  have htrace : WordTrace (prefixWord ++ tailWord_588679) baseStart_588679 baseEnd_588679 := by
    simpa [prefixWord, tailWord_588679, baseEnd_588679] using wordTrace_append hprefix tailTrace_588679
  have hstable : (prefixWord ++ tailWord_588679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588679).length < 2 ^ (prefixWord ++ tailWord_588679).sum := by decide
  have hdescent : baseEnd_588679 < baseStart_588679 := by decide
  rcases family_descends (prefixWord ++ tailWord_588679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588707 : List Nat := [1, 1, 1, 4, 1, 2, 3, 2, 2, 5]
def baseStart_588707 : Nat := 118140960795 + 588707 * 2 ^ 59
def prefixEnd_588707 : Nat := 4983230072969 + 3 ^ 40 * 588707 * 2
def baseEnd_588707 : Nat := 201526437111022276570061

theorem tailTrace_588707 : CollatzResearch.WordTrace tailWord_588707 prefixEnd_588707 201526437111022276570061 := by
  unfold tailWord_588707
  simp only [CollatzResearch.WordTrace]
  refine ⟨21471908278222556996060375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14314605518815037997373583 21471908278222556996060375)
  ·
    refine ⟨32207862417333835494090563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21471908278222556996060375 32207862417333835494090563)
    ·
      refine ⟨48311793626000753241135845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32207862417333835494090563 48311793626000753241135845)
      ·
        refine ⟨9058461304875141232712971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48311793626000753241135845 9058461304875141232712971)
        ·
          refine ⟨13587691957312711849069457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9058461304875141232712971 13587691957312711849069457)
          ·
            refine ⟨10190768967984533886802093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13587691957312711849069457 10190768967984533886802093)
            ·
              refine ⟨3821538362994200207550785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10190768967984533886802093 3821538362994200207550785)
              ·
                refine ⟨2866153772245650155663089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3821538362994200207550785 2866153772245650155663089)
                ·
                  refine ⟨2149615329184237616747317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2866153772245650155663089 2149615329184237616747317)
                  ·
                    refine ⟨201526437111022276570061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2149615329184237616747317 201526437111022276570061)
                    ·
                      rfl

theorem cell22_588707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 2, 2, 5].length) (baseStart_588707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_588707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_588707 prefixEnd_588707 := by exact prefixLift 588707
  have htrace : WordTrace (prefixWord ++ tailWord_588707) baseStart_588707 baseEnd_588707 := by
    simpa [prefixWord, tailWord_588707, baseEnd_588707] using wordTrace_append hprefix tailTrace_588707
  have hstable : (prefixWord ++ tailWord_588707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588707).length < 2 ^ (prefixWord ++ tailWord_588707).sum := by decide
  have hdescent : baseEnd_588707 < baseStart_588707 := by decide
  rcases family_descends (prefixWord ++ tailWord_588707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588752 : List Nat := [2, 1, 1, 1, 1, 2, 3, 3, 3, 5]
def baseStart_588752 : Nat := 118140960795 + 588752 * 2 ^ 59
def prefixEnd_588752 : Nat := 4983230072969 + 3 ^ 40 * 588752 * 2
def baseEnd_588752 : Nat := 201541841530657159194923

theorem tailTrace_588752 : CollatzResearch.WordTrace tailWord_588752 prefixEnd_588752 201541841530657159194923 := by
  unfold tailWord_588752
  simp only [CollatzResearch.WordTrace]
  refine ⟨10736774781529764840724255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14315699708706353120965673 10736774781529764840724255)
  ·
    refine ⟨16105162172294647261086383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10736774781529764840724255 16105162172294647261086383)
    ·
      refine ⟨24157743258441970891629575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16105162172294647261086383 24157743258441970891629575)
      ·
        refine ⟨36236614887662956337444363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24157743258441970891629575 36236614887662956337444363)
        ·
          refine ⟨54354922331494434506166545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36236614887662956337444363 54354922331494434506166545)
          ·
            refine ⟨40766191748620825879624909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54354922331494434506166545 40766191748620825879624909)
            ·
              refine ⟨15287321905732809704859341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40766191748620825879624909 15287321905732809704859341)
              ·
                refine ⟨5732745714649803639322253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15287321905732809704859341 5732745714649803639322253)
                ·
                  refine ⟨2149779642993676364745845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5732745714649803639322253 2149779642993676364745845)
                  ·
                    refine ⟨201541841530657159194923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2149779642993676364745845 201541841530657159194923)
                    ·
                      rfl

theorem cell22_588752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 3, 5].length) (baseStart_588752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_588752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_588752 prefixEnd_588752 := by exact prefixLift 588752
  have htrace : WordTrace (prefixWord ++ tailWord_588752) baseStart_588752 baseEnd_588752 := by
    simpa [prefixWord, tailWord_588752, baseEnd_588752] using wordTrace_append hprefix tailTrace_588752
  have hstable : (prefixWord ++ tailWord_588752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588752).length < 2 ^ (prefixWord ++ tailWord_588752).sum := by decide
  have hdescent : baseEnd_588752 < baseStart_588752 := by decide
  rcases family_descends (prefixWord ++ tailWord_588752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588756 : List Nat := [2, 4, 1, 2, 1, 2, 2, 3, 1, 4]
def baseStart_588756 : Nat := 118140960795 + 588756 * 2 ^ 59
def prefixEnd_588756 : Nat := 4983230072969 + 3 ^ 40 * 588756 * 2
def baseEnd_588756 : Nat := 201543210812402482094911

theorem tailTrace_588756 : CollatzResearch.WordTrace tailWord_588756 prefixEnd_588756 201543210812402482094911 := by
  unfold tailWord_588756
  simp only [CollatzResearch.WordTrace]
  refine ⟨10736847727522519182297061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14315796970030025576396081 10736847727522519182297061)
  ·
    refine ⟨2013158948910472346680699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10736847727522519182297061 2013158948910472346680699)
    ·
      refine ⟨3019738423365708520021049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2013158948910472346680699 3019738423365708520021049)
      ·
        refine ⟨2264803817524281390015787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3019738423365708520021049 2264803817524281390015787)
        ·
          refine ⟨3397205726286422085023681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2264803817524281390015787 3397205726286422085023681)
          ·
            refine ⟨2547904294714816563767761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3397205726286422085023681 2547904294714816563767761)
            ·
              refine ⟨1910928221036112422825821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2547904294714816563767761 1910928221036112422825821)
              ·
                refine ⟨716598082888542158559683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1910928221036112422825821 716598082888542158559683)
                ·
                  refine ⟨1074897124332813237839525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 716598082888542158559683 1074897124332813237839525)
                  ·
                    refine ⟨201543210812402482094911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1074897124332813237839525 201543210812402482094911)
                    ·
                      rfl

theorem cell22_588756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_588756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_588756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_588756 prefixEnd_588756 := by exact prefixLift 588756
  have htrace : WordTrace (prefixWord ++ tailWord_588756) baseStart_588756 baseEnd_588756 := by
    simpa [prefixWord, tailWord_588756, baseEnd_588756] using wordTrace_append hprefix tailTrace_588756
  have hstable : (prefixWord ++ tailWord_588756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588756).length < 2 ^ (prefixWord ++ tailWord_588756).sum := by decide
  have hdescent : baseEnd_588756 < baseStart_588756 := by decide
  rcases family_descends (prefixWord ++ tailWord_588756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588801 : List Nat := [1, 2, 4, 1, 2, 3, 2, 1, 2, 4]
def baseStart_588801 : Nat := 118140960795 + 588801 * 2 ^ 59
def prefixEnd_588801 : Nat := 4983230072969 + 3 ^ 40 * 588801 * 2
def baseEnd_588801 : Nat := 201558615232037364719773

theorem tailTrace_588801 : CollatzResearch.WordTrace tailWord_588801 prefixEnd_588801 201558615232037364719773 := by
  unfold tailWord_588801
  simp only [CollatzResearch.WordTrace]
  refine ⟨21475336739882011049982257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14316891159921340699988171 21475336739882011049982257)
  ·
    refine ⟨16106502554911508287486693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21475336739882011049982257 16106502554911508287486693)
    ·
      refine ⟨3019969229045907803903755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16106502554911508287486693 3019969229045907803903755)
      ·
        refine ⟨4529953843568861705855633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3019969229045907803903755 4529953843568861705855633)
        ·
          refine ⟨3397465382676646279391725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4529953843568861705855633 3397465382676646279391725)
          ·
            refine ⟨1274049518503742354771897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3397465382676646279391725 1274049518503742354771897)
            ·
              refine ⟨955537138877806766078923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1274049518503742354771897 955537138877806766078923)
              ·
                refine ⟨1433305708316710149118385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 955537138877806766078923 1433305708316710149118385)
                ·
                  refine ⟨1074979281237532611838789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1433305708316710149118385 1074979281237532611838789)
                  ·
                    refine ⟨201558615232037364719773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1074979281237532611838789 201558615232037364719773)
                    ·
                      rfl

theorem cell22_588801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_588801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_588801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_588801 prefixEnd_588801 := by exact prefixLift 588801
  have htrace : WordTrace (prefixWord ++ tailWord_588801) baseStart_588801 baseEnd_588801 := by
    simpa [prefixWord, tailWord_588801, baseEnd_588801] using wordTrace_append hprefix tailTrace_588801
  have hstable : (prefixWord ++ tailWord_588801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588801).length < 2 ^ (prefixWord ++ tailWord_588801).sum := by decide
  have hdescent : baseEnd_588801 < baseStart_588801 := by decide
  rcases family_descends (prefixWord ++ tailWord_588801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588827 : List Nat := [1, 1, 1, 1, 1, 1, 3, 2, 11]
def baseStart_588827 : Nat := 118140960795 + 588827 * 2 ^ 59
def prefixEnd_588827 : Nat := 4983230072969 + 3 ^ 40 * 588827 * 2
def baseEnd_588827 : Nat := 67189171854460654523231

theorem tailTrace_588827 : CollatzResearch.WordTrace tailWord_588827 prefixEnd_588827 67189171854460654523231 := by
  unfold tailWord_588827
  simp only [CollatzResearch.WordTrace]
  refine ⟨21476285037787817490428735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14317523358525211660285823 21476285037787817490428735)
  ·
    refine ⟨32214427556681726235643103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21476285037787817490428735 32214427556681726235643103)
    ·
      refine ⟨48321641335022589353464655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32214427556681726235643103 48321641335022589353464655)
      ·
        refine ⟨72482462002533884030196983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48321641335022589353464655 72482462002533884030196983)
        ·
          refine ⟨108723693003800826045295475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72482462002533884030196983 108723693003800826045295475)
          ·
            refine ⟨163085539505701239067943213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108723693003800826045295475 163085539505701239067943213)
            ·
              refine ⟨61157077314637964650478705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 163085539505701239067943213 61157077314637964650478705)
              ·
                refine ⟨45867807985978473487859029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61157077314637964650478705 45867807985978473487859029)
                ·
                  refine ⟨67189171854460654523231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 45867807985978473487859029 67189171854460654523231)
                  ·
                    rfl

theorem cell22_588827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 11].length) (baseStart_588827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_588827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_588827 prefixEnd_588827 := by exact prefixLift 588827
  have htrace : WordTrace (prefixWord ++ tailWord_588827) baseStart_588827 baseEnd_588827 := by
    simpa [prefixWord, tailWord_588827, baseEnd_588827] using wordTrace_append hprefix tailTrace_588827
  have hstable : (prefixWord ++ tailWord_588827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588827).length < 2 ^ (prefixWord ++ tailWord_588827).sum := by decide
  have hdescent : baseEnd_588827 < baseStart_588827 := by decide
  rcases family_descends (prefixWord ++ tailWord_588827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588844 : List Nat := [2, 2, 1, 1, 1, 2, 3, 5, 5]
def baseStart_588844 : Nat := 118140960795 + 588844 * 2 ^ 59
def prefixEnd_588844 : Nat := 4983230072969 + 3 ^ 40 * 588844 * 2
def baseEnd_588844 : Nat := 67191111670266528631547

theorem tailTrace_588844 : CollatzResearch.WordTrace tailWord_588844 prefixEnd_588844 67191111670266528631547 := by
  unfold tailWord_588844
  simp only [CollatzResearch.WordTrace]
  refine ⟨10738452539363114696898793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14317936719150819595865057 10738452539363114696898793)
  ·
    refine ⟨8053839404522336022674095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10738452539363114696898793 8053839404522336022674095)
    ·
      refine ⟨12080759106783504034011143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8053839404522336022674095 12080759106783504034011143)
      ·
        refine ⟨18121138660175256051016715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12080759106783504034011143 18121138660175256051016715)
        ·
          refine ⟨27181707990262884076525073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18121138660175256051016715 27181707990262884076525073)
          ·
            refine ⟨20386280992697163057393805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27181707990262884076525073 20386280992697163057393805)
            ·
              refine ⟨7644855372261436146522677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20386280992697163057393805 7644855372261436146522677)
              ·
                refine ⟨716705191149509638736501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7644855372261436146522677 716705191149509638736501)
                ·
                  refine ⟨67191111670266528631547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 716705191149509638736501 67191111670266528631547)
                  ·
                    rfl

theorem cell22_588844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 5].length) (baseStart_588844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_588844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_588844 prefixEnd_588844 := by exact prefixLift 588844
  have htrace : WordTrace (prefixWord ++ tailWord_588844) baseStart_588844 baseEnd_588844 := by
    simpa [prefixWord, tailWord_588844, baseEnd_588844] using wordTrace_append hprefix tailTrace_588844
  have hstable : (prefixWord ++ tailWord_588844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588844).length < 2 ^ (prefixWord ++ tailWord_588844).sum := by decide
  have hdescent : baseEnd_588844 < baseStart_588844 := by decide
  rcases family_descends (prefixWord ++ tailWord_588844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588906 : List Nat := [3, 1, 3, 2, 2, 1, 2, 2, 6]
def baseStart_588906 : Nat := 118140960795 + 588906 * 2 ^ 59
def prefixEnd_588906 : Nat := 4983230072969 + 3 ^ 40 * 588906 * 2
def baseEnd_588906 : Nat := 67198186292617363614817

theorem tailTrace_588906 : CollatzResearch.WordTrace tailWord_588906 prefixEnd_588906 67198186292617363614817 := by
  unfold tailWord_588906
  simp only [CollatzResearch.WordTrace]
  refine ⟨5369791601125403495638643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14319444269667742655036381 5369791601125403495638643)
  ·
    refine ⟨8054687401688105243457965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5369791601125403495638643 8054687401688105243457965)
    ·
      refine ⟨3020507775633039466296737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8054687401688105243457965 3020507775633039466296737)
      ·
        refine ⟨2265380831724779599722553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3020507775633039466296737 2265380831724779599722553)
        ·
          refine ⟨1699035623793584699791915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2265380831724779599722553 1699035623793584699791915)
          ·
            refine ⟨2548553435690377049687873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1699035623793584699791915 2548553435690377049687873)
            ·
              refine ⟨1911415076767782787265905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2548553435690377049687873 1911415076767782787265905)
              ·
                refine ⟨1433561307575837090449429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1911415076767782787265905 1433561307575837090449429)
                ·
                  refine ⟨67198186292617363614817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1433561307575837090449429 67198186292617363614817)
                  ·
                    rfl

theorem cell22_588906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 2, 6].length) (baseStart_588906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_588906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_588906 prefixEnd_588906 := by exact prefixLift 588906
  have htrace : WordTrace (prefixWord ++ tailWord_588906) baseStart_588906 baseEnd_588906 := by
    simpa [prefixWord, tailWord_588906, baseEnd_588906] using wordTrace_append hprefix tailTrace_588906
  have hstable : (prefixWord ++ tailWord_588906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588906).length < 2 ^ (prefixWord ++ tailWord_588906).sum := by decide
  have hdescent : baseEnd_588906 < baseStart_588906 := by decide
  rcases family_descends (prefixWord ++ tailWord_588906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588919 : List Nat := [1, 1, 3, 1, 1, 4, 1, 3, 1, 6]
def baseStart_588919 : Nat := 118140960795 + 588919 * 2 ^ 59
def prefixEnd_588919 : Nat := 4983230072969 + 3 ^ 40 * 588919 * 2
def baseEnd_588919 : Nat := 201599009043524390269411

theorem tailTrace_588919 : CollatzResearch.WordTrace tailWord_588919 prefixEnd_588919 201599009043524390269411 := by
  unfold tailWord_588919
  simp only [CollatzResearch.WordTrace]
  refine ⟨21479640553454517202777811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14319760368969678135185207 21479640553454517202777811)
  ·
    refine ⟨32219460830181775804166717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21479640553454517202777811 32219460830181775804166717)
    ·
      refine ⟨12082297811318165926562519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32219460830181775804166717 12082297811318165926562519)
      ·
        refine ⟨18123446716977248889843779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12082297811318165926562519 18123446716977248889843779)
        ·
          refine ⟨27185170075465873334765669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18123446716977248889843779 27185170075465873334765669)
          ·
            refine ⟨5097219389149851250268563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27185170075465873334765669 5097219389149851250268563)
            ·
              refine ⟨7645829083724776875402845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5097219389149851250268563 7645829083724776875402845)
              ·
                refine ⟨2867185906396791328276067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7645829083724776875402845 2867185906396791328276067)
                ·
                  refine ⟨4300778859595186992414101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2867185906396791328276067 4300778859595186992414101)
                  ·
                    refine ⟨201599009043524390269411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4300778859595186992414101 201599009043524390269411)
                    ·
                      rfl

theorem cell22_588919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 3, 1, 6].length) (baseStart_588919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_588919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_588919 prefixEnd_588919 := by exact prefixLift 588919
  have htrace : WordTrace (prefixWord ++ tailWord_588919) baseStart_588919 baseEnd_588919 := by
    simpa [prefixWord, tailWord_588919, baseEnd_588919] using wordTrace_append hprefix tailTrace_588919
  have hstable : (prefixWord ++ tailWord_588919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588919).length < 2 ^ (prefixWord ++ tailWord_588919).sum := by decide
  have hdescent : baseEnd_588919 < baseStart_588919 := by decide
  rcases family_descends (prefixWord ++ tailWord_588919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588938 : List Nat := [3, 1, 2, 3, 1, 1, 2, 4, 2, 3]
def baseStart_588938 : Nat := 118140960795 + 588938 * 2 ^ 59
def prefixEnd_588938 : Nat := 4983230072969 + 3 ^ 40 * 588938 * 2
def baseEnd_588938 : Nat := 201605513131814674044353

theorem tailTrace_588938 : CollatzResearch.WordTrace tailWord_588938 prefixEnd_588938 201605513131814674044353 := by
  unfold tailWord_588938
  simp only [CollatzResearch.WordTrace]
  refine ⟨5370083385096420861929867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14320222360257122298479645 5370083385096420861929867)
  ·
    refine ⟨8055125077644631292894801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5370083385096420861929867 8055125077644631292894801)
    ·
      refine ⟨6041343808233473469671101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8055125077644631292894801 6041343808233473469671101)
      ·
        refine ⟨2265503928087552551126663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6041343808233473469671101 2265503928087552551126663)
        ·
          refine ⟨3398255892131328826689995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2265503928087552551126663 3398255892131328826689995)
          ·
            refine ⟨5097383838196993240034993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3398255892131328826689995 5097383838196993240034993)
            ·
              refine ⟨3823037878647744930026245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5097383838196993240034993 3823037878647744930026245)
              ·
                refine ⟨716819602246452174379921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3823037878647744930026245 716819602246452174379921)
                ·
                  refine ⟨537614701684839130784941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 716819602246452174379921 537614701684839130784941)
                  ·
                    refine ⟨201605513131814674044353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 537614701684839130784941 201605513131814674044353)
                    ·
                      rfl

theorem cell22_588938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 4, 2, 3].length) (baseStart_588938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_588938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_588938 prefixEnd_588938 := by exact prefixLift 588938
  have htrace : WordTrace (prefixWord ++ tailWord_588938) baseStart_588938 baseEnd_588938 := by
    simpa [prefixWord, tailWord_588938, baseEnd_588938] using wordTrace_append hprefix tailTrace_588938
  have hstable : (prefixWord ++ tailWord_588938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588938).length < 2 ^ (prefixWord ++ tailWord_588938).sum := by decide
  have hdescent : baseEnd_588938 < baseStart_588938 := by decide
  rcases family_descends (prefixWord ++ tailWord_588938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588949 : List Nat := [1, 3, 2, 1, 1, 1, 2, 2, 2, 7]
def baseStart_588949 : Nat := 118140960795 + 588949 * 2 ^ 59
def prefixEnd_588949 : Nat := 4983230072969 + 3 ^ 40 * 588949 * 2
def baseEnd_588949 : Nat := 201609278656614312019319

theorem tailTrace_588949 : CollatzResearch.WordTrace tailWord_588949 prefixEnd_588949 201609278656614312019319 := by
  unfold tailWord_588949
  simp only [CollatzResearch.WordTrace]
  refine ⟨21480734743345832326369901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14320489828897221550913267 21480734743345832326369901)
  ·
    refine ⟨8055275528754687122388713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21480734743345832326369901 8055275528754687122388713)
    ·
      refine ⟨6041456646566015341791535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8055275528754687122388713 6041456646566015341791535)
      ·
        refine ⟨9062184969849023012687303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6041456646566015341791535 9062184969849023012687303)
        ·
          refine ⟨13593277454773534519030955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9062184969849023012687303 13593277454773534519030955)
          ·
            refine ⟨20389916182160301778546433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13593277454773534519030955 20389916182160301778546433)
            ·
              refine ⟨15292437136620226333909825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20389916182160301778546433 15292437136620226333909825)
              ·
                refine ⟨11469327852465169750432369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15292437136620226333909825 11469327852465169750432369)
                ·
                  refine ⟨8601995889348877312824277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11469327852465169750432369 8601995889348877312824277)
                  ·
                    refine ⟨201609278656614312019319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8601995889348877312824277 201609278656614312019319)
                    ·
                      rfl

theorem cell22_588949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 7].length) (baseStart_588949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_588949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_588949 prefixEnd_588949 := by exact prefixLift 588949
  have htrace : WordTrace (prefixWord ++ tailWord_588949) baseStart_588949 baseEnd_588949 := by
    simpa [prefixWord, tailWord_588949, baseEnd_588949] using wordTrace_append hprefix tailTrace_588949
  have hstable : (prefixWord ++ tailWord_588949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588949).length < 2 ^ (prefixWord ++ tailWord_588949).sum := by decide
  have hdescent : baseEnd_588949 < baseStart_588949 := by decide
  rcases family_descends (prefixWord ++ tailWord_588949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588951 : List Nat := [1, 1, 3, 3, 3, 2, 2, 7]
def baseStart_588951 : Nat := 118140960795 + 588951 * 2 ^ 59
def prefixEnd_588951 : Nat := 4983230072969 + 3 ^ 40 * 588951 * 2
def baseEnd_588951 : Nat := 22401107033054108163257

theorem tailTrace_588951 : CollatzResearch.WordTrace tailWord_588951 prefixEnd_588951 22401107033054108163257 := by
  unfold tailWord_588951
  simp only [CollatzResearch.WordTrace]
  refine ⟨21480807689338586667942707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14320538459559057778628471 21480807689338586667942707)
  ·
    refine ⟨32221211534007880001914061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21480807689338586667942707 32221211534007880001914061)
    ·
      refine ⟨12082954325252955000717773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32221211534007880001914061 12082954325252955000717773)
      ·
        refine ⟨4531107871969858125269165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12082954325252955000717773 4531107871969858125269165)
        ·
          refine ⟨1699165451988696796975937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4531107871969858125269165 1699165451988696796975937)
          ·
            refine ⟨1274374088991522597731953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1699165451988696796975937 1274374088991522597731953)
            ·
              refine ⟨955780566743641948298965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1274374088991522597731953 955780566743641948298965)
              ·
                refine ⟨22401107033054108163257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 955780566743641948298965 22401107033054108163257)
                ·
                  rfl

theorem cell22_588951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 7].length) (baseStart_588951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_588951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_588951 prefixEnd_588951 := by exact prefixLift 588951
  have htrace : WordTrace (prefixWord ++ tailWord_588951) baseStart_588951 baseEnd_588951 := by
    simpa [prefixWord, tailWord_588951, baseEnd_588951] using wordTrace_append hprefix tailTrace_588951
  have hstable : (prefixWord ++ tailWord_588951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588951).length < 2 ^ (prefixWord ++ tailWord_588951).sum := by decide
  have hdescent : baseEnd_588951 < baseStart_588951 := by decide
  rcases family_descends (prefixWord ++ tailWord_588951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588970 : List Nat := [3, 1, 5, 1, 1, 2, 2, 1, 2, 4]
def baseStart_588970 : Nat := 118140960795 + 588970 * 2 ^ 59
def prefixEnd_588970 : Nat := 4983230072969 + 3 ^ 40 * 588970 * 2
def baseEnd_588970 : Nat := 201616467385777257244255

theorem tailTrace_588970 : CollatzResearch.WordTrace tailWord_588970 prefixEnd_588970 201616467385777257244255 := by
  unfold tailWord_588970
  simp only [CollatzResearch.WordTrace]
  refine ⟨5370375169067438228221091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14321000450846501941922909 5370375169067438228221091)
  ·
    refine ⟨8055562753601157342331637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5370375169067438228221091 8055562753601157342331637)
    ·
      refine ⟨755209008150108500843591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8055562753601157342331637 755209008150108500843591)
      ·
        refine ⟨1132813512225162751265387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 755209008150108500843591 1132813512225162751265387)
        ·
          refine ⟨1699220268337744126898081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1132813512225162751265387 1699220268337744126898081)
          ·
            refine ⟨1274415201253308095173561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1699220268337744126898081 1274415201253308095173561)
            ·
              refine ⟨955811400939981071380171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1274415201253308095173561 955811400939981071380171)
              ·
                refine ⟨1433717101409971607070257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 955811400939981071380171 1433717101409971607070257)
                ·
                  refine ⟨1075287826057478705302693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1433717101409971607070257 1075287826057478705302693)
                  ·
                    refine ⟨201616467385777257244255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1075287826057478705302693 201616467385777257244255)
                    ·
                      rfl

theorem cell22_588970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_588970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_588970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_588970 prefixEnd_588970 := by exact prefixLift 588970
  have htrace : WordTrace (prefixWord ++ tailWord_588970) baseStart_588970 baseEnd_588970 := by
    simpa [prefixWord, tailWord_588970, baseEnd_588970] using wordTrace_append hprefix tailTrace_588970
  have hstable : (prefixWord ++ tailWord_588970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588970).length < 2 ^ (prefixWord ++ tailWord_588970).sum := by decide
  have hdescent : baseEnd_588970 < baseStart_588970 := by decide
  rcases family_descends (prefixWord ++ tailWord_588970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588979 : List Nat := [1, 1, 1, 2, 3, 2, 2, 1, 9]
def baseStart_588979 : Nat := 118140960795 + 588979 * 2 ^ 59
def prefixEnd_588979 : Nat := 4983230072969 + 3 ^ 40 * 588979 * 2
def baseEnd_588979 : Nat := 67206516089901411256409

theorem tailTrace_588979 : CollatzResearch.WordTrace tailWord_588979 prefixEnd_588979 67206516089901411256409 := by
  unfold tailWord_588979
  simp only [CollatzResearch.WordTrace]
  refine ⟨21481828933237147449961991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14321219288824764966641327 21481828933237147449961991)
  ·
    refine ⟨32222743399855721174942987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21481828933237147449961991 32222743399855721174942987)
    ·
      refine ⟨48334115099783581762414481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32222743399855721174942987 48334115099783581762414481)
      ·
        refine ⟨36250586324837686321810861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48334115099783581762414481 36250586324837686321810861)
        ·
          refine ⟨13593969871814132370679073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36250586324837686321810861 13593969871814132370679073)
          ·
            refine ⟨10195477403860599278009305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13593969871814132370679073 10195477403860599278009305)
            ·
              refine ⟨7646608052895449458506979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10195477403860599278009305 7646608052895449458506979)
              ·
                refine ⟨11469912079343174187760469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7646608052895449458506979 11469912079343174187760469)
                ·
                  refine ⟨67206516089901411256409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 11469912079343174187760469 67206516089901411256409)
                  ·
                    rfl

theorem cell22_588979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 9].length) (baseStart_588979 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_588979 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_588979 prefixEnd_588979 := by exact prefixLift 588979
  have htrace : WordTrace (prefixWord ++ tailWord_588979) baseStart_588979 baseEnd_588979 := by
    simpa [prefixWord, tailWord_588979, baseEnd_588979] using wordTrace_append hprefix tailTrace_588979
  have hstable : (prefixWord ++ tailWord_588979).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588979).length < 2 ^ (prefixWord ++ tailWord_588979).sum := by decide
  have hdescent : baseEnd_588979 < baseStart_588979 := by decide
  rcases family_descends (prefixWord ++ tailWord_588979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589013 : List Nat := [1, 3, 2, 4, 1, 1, 2, 3, 5]
def baseStart_589013 : Nat := 118140960795 + 589013 * 2 ^ 59
def prefixEnd_589013 : Nat := 4983230072969 + 3 ^ 40 * 589013 * 2
def baseEnd_589013 : Nat := 67210395721513159473041

theorem tailTrace_589013 : CollatzResearch.WordTrace tailWord_589013 prefixEnd_589013 67210395721513159473041 := by
  unfold tailWord_589013
  simp only [CollatzResearch.WordTrace]
  refine ⟨21483069015113971256699693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14322046010075980837799795 21483069015113971256699693)
  ·
    refine ⟨8056150880667739221262385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21483069015113971256699693 8056150880667739221262385)
    ·
      refine ⟨6042113160500804415946789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8056150880667739221262385 6042113160500804415946789)
      ·
        refine ⟨1132896217593900827990023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6042113160500804415946789 1132896217593900827990023)
        ·
          refine ⟨1699344326390851241985035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1132896217593900827990023 1699344326390851241985035)
          ·
            refine ⟨2549016489586276862977553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1699344326390851241985035 2549016489586276862977553)
            ·
              refine ⟨1911762367189707647233165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2549016489586276862977553 1911762367189707647233165)
              ·
                refine ⟨716910887696140367712437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1911762367189707647233165 716910887696140367712437)
                ·
                  refine ⟨67210395721513159473041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 716910887696140367712437 67210395721513159473041)
                  ·
                    rfl

theorem cell22_589013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 3, 5].length) (baseStart_589013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_589013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_589013 prefixEnd_589013 := by exact prefixLift 589013
  have htrace : WordTrace (prefixWord ++ tailWord_589013) baseStart_589013 baseEnd_589013 := by
    simpa [prefixWord, tailWord_589013, baseEnd_589013] using wordTrace_append hprefix tailTrace_589013
  have hstable : (prefixWord ++ tailWord_589013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589013).length < 2 ^ (prefixWord ++ tailWord_589013).sum := by decide
  have hdescent : baseEnd_589013 < baseStart_589013 := by decide
  rcases family_descends (prefixWord ++ tailWord_589013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589043 : List Nat := [1, 1, 1, 2, 2, 6, 1, 3, 1, 4]
def baseStart_589043 : Nat := 118140960795 + 589043 * 2 ^ 59
def prefixEnd_589043 : Nat := 4983230072969 + 3 ^ 40 * 589043 * 2
def baseEnd_589043 : Nat := 201641456777629400169031

theorem tailTrace_589043 : CollatzResearch.WordTrace tailWord_589043 prefixEnd_589043 201641456777629400169031 := by
  unfold tailWord_589043
  simp only [CollatzResearch.WordTrace]
  refine ⟨21484163205005286380291783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14322775470003524253527855 21484163205005286380291783)
  ·
    refine ⟨32226244807507929570437675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21484163205005286380291783 32226244807507929570437675)
    ·
      refine ⟨48339367211261894355656513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32226244807507929570437675 48339367211261894355656513)
      ·
        refine ⟨36254525408446420766742385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48339367211261894355656513 36254525408446420766742385)
        ·
          refine ⟨27190894056334815575056789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36254525408446420766742385 27190894056334815575056789)
          ·
            refine ⟨1274573158890694480080787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 27190894056334815575056789 1274573158890694480080787)
            ·
              refine ⟨1911859738336041720121181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1274573158890694480080787 1911859738336041720121181)
              ·
                refine ⟨716947401876015645045443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1911859738336041720121181 716947401876015645045443)
                ·
                  refine ⟨1075421102814023467568165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 716947401876015645045443 1075421102814023467568165)
                  ·
                    refine ⟨201641456777629400169031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1075421102814023467568165 201641456777629400169031)
                    ·
                      rfl

theorem cell22_589043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 3, 1, 4].length) (baseStart_589043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_589043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_589043 prefixEnd_589043 := by exact prefixLift 589043
  have htrace : WordTrace (prefixWord ++ tailWord_589043) baseStart_589043 baseEnd_589043 := by
    simpa [prefixWord, tailWord_589043, baseEnd_589043] using wordTrace_append hprefix tailTrace_589043
  have hstable : (prefixWord ++ tailWord_589043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589043).length < 2 ^ (prefixWord ++ tailWord_589043).sum := by decide
  have hdescent : baseEnd_589043 < baseStart_589043 := by decide
  rcases family_descends (prefixWord ++ tailWord_589043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589124 : List Nat := [2, 3, 4, 1, 1, 1, 4, 1, 2, 3]
def baseStart_589124 : Nat := 118140960795 + 589124 * 2 ^ 59
def prefixEnd_589124 : Nat := 4983230072969 + 3 ^ 40 * 589124 * 2
def baseEnd_589124 : Nat := 201669184732972188893783

theorem tailTrace_589124 : CollatzResearch.WordTrace tailWord_589124 prefixEnd_589124 201669184732972188893783 := by
  unfold tailWord_589124
  simp only [CollatzResearch.WordTrace]
  refine ⟨10743558758855918606995213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14324745011807891475993617 10743558758855918606995213)
  ·
    refine ⟨4028834534570969477623205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10743558758855918606995213 4028834534570969477623205)
    ·
      refine ⟨755406475232056777054351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4028834534570969477623205 755406475232056777054351)
      ·
        refine ⟨1133109712848085165581527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 755406475232056777054351 1133109712848085165581527)
        ·
          refine ⟨1699664569272127748372291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1133109712848085165581527 1699664569272127748372291)
          ·
            refine ⟨2549496853908191622558437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1699664569272127748372291 2549496853908191622558437)
            ·
              refine ⟨478030660107785929229707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2549496853908191622558437 478030660107785929229707)
              ·
                refine ⟨717045990161678893844561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 478030660107785929229707 717045990161678893844561)
                ·
                  refine ⟨537784492621259170383421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 717045990161678893844561 537784492621259170383421)
                  ·
                    refine ⟨201669184732972188893783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 537784492621259170383421 201669184732972188893783)
                    ·
                      rfl

theorem cell22_589124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_589124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_589124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_589124 prefixEnd_589124 := by exact prefixLift 589124
  have htrace : WordTrace (prefixWord ++ tailWord_589124) baseStart_589124 baseEnd_589124 := by
    simpa [prefixWord, tailWord_589124, baseEnd_589124] using wordTrace_append hprefix tailTrace_589124
  have hstable : (prefixWord ++ tailWord_589124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589124).length < 2 ^ (prefixWord ++ tailWord_589124).sum := by decide
  have hdescent : baseEnd_589124 < baseStart_589124 := by decide
  rcases family_descends (prefixWord ++ tailWord_589124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589165 : List Nat := [1, 5, 1, 1, 1, 4, 2, 2, 5]
def baseStart_589165 : Nat := 118140960795 + 589165 * 2 ^ 59
def prefixEnd_589165 : Nat := 4983230072969 + 3 ^ 40 * 589165 * 2
def baseEnd_589165 : Nat := 67227739956953916206219

theorem tailTrace_589165 : CollatzResearch.WordTrace tailWord_589165 prefixEnd_589165 67227739956953916206219 := by
  unfold tailWord_589165
  simp only [CollatzResearch.WordTrace]
  refine ⟨21488612910563301216232949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14325741940375534144155299 21488612910563301216232949)
  ·
    refine ⟨2014557460365309489021839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21488612910563301216232949 2014557460365309489021839)
    ·
      refine ⟨3021836190547964233532759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2014557460365309489021839 3021836190547964233532759)
      ·
        refine ⟨4532754285821946350299139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3021836190547964233532759 4532754285821946350299139)
        ·
          refine ⟨6799131428732919525448709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4532754285821946350299139 6799131428732919525448709)
          ·
            refine ⟨1274837142887422411021633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6799131428732919525448709 1274837142887422411021633)
            ·
              refine ⟨956127857165566808266225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1274837142887422411021633 956127857165566808266225)
              ·
                refine ⟨717095892874175106199669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 956127857165566808266225 717095892874175106199669)
                ·
                  refine ⟨67227739956953916206219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 717095892874175106199669 67227739956953916206219)
                  ·
                    rfl

theorem cell22_589165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 2, 5].length) (baseStart_589165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_589165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_589165 prefixEnd_589165 := by exact prefixLift 589165
  have htrace : WordTrace (prefixWord ++ tailWord_589165) baseStart_589165 baseEnd_589165 := by
    simpa [prefixWord, tailWord_589165, baseEnd_589165] using wordTrace_append hprefix tailTrace_589165
  have hstable : (prefixWord ++ tailWord_589165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589165).length < 2 ^ (prefixWord ++ tailWord_589165).sum := by decide
  have hdescent : baseEnd_589165 < baseStart_589165 := by decide
  rcases family_descends (prefixWord ++ tailWord_589165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589176 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 12]
def baseStart_589176 : Nat := 118140960795 + 589176 * 2 ^ 59
def prefixEnd_589176 : Nat := 4983230072969 + 3 ^ 40 * 589176 * 2
def baseEnd_589176 : Nat := 67228995131887128864541

theorem tailTrace_589176 : CollatzResearch.WordTrace tailWord_589176 prefixEnd_589176 67228995131887128864541 := by
  unfold tailWord_589176
  simp only [CollatzResearch.WordTrace]
  refine ⟨10744507056761725047441691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14326009409015633396588921 10744507056761725047441691)
  ·
    refine ⟨16116760585142587571162537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10744507056761725047441691 16116760585142587571162537)
    ·
      refine ⟨12087570438856940678371903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16116760585142587571162537 12087570438856940678371903)
      ·
        refine ⟨18131355658285411017557855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12087570438856940678371903 18131355658285411017557855)
        ·
          refine ⟨27197033487428116526336783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18131355658285411017557855 27197033487428116526336783)
          ·
            refine ⟨40795550231142174789505175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27197033487428116526336783 40795550231142174789505175)
            ·
              refine ⟨61193325346713262184257763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40795550231142174789505175 61193325346713262184257763)
              ·
                refine ⟨91789988020069893276386645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61193325346713262184257763 91789988020069893276386645)
                ·
                  refine ⟨67228995131887128864541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 91789988020069893276386645 67228995131887128864541)
                  ·
                    rfl

theorem cell22_589176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 12].length) (baseStart_589176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_589176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_589176 prefixEnd_589176 := by exact prefixLift 589176
  have htrace : WordTrace (prefixWord ++ tailWord_589176) baseStart_589176 baseEnd_589176 := by
    simpa [prefixWord, tailWord_589176, baseEnd_589176] using wordTrace_append hprefix tailTrace_589176
  have hstable : (prefixWord ++ tailWord_589176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589176).length < 2 ^ (prefixWord ++ tailWord_589176).sum := by decide
  have hdescent : baseEnd_589176 < baseStart_589176 := by decide
  rcases family_descends (prefixWord ++ tailWord_589176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589287 : List Nat := [1, 1, 5, 2, 1, 2, 3, 1, 3, 3]
def baseStart_589287 : Nat := 118140960795 + 589287 * 2 ^ 59
def prefixEnd_589287 : Nat := 4983230072969 + 3 ^ 40 * 589287 * 2
def baseEnd_589287 : Nat := 201724982964094097068283

theorem tailTrace_589287 : CollatzResearch.WordTrace tailWord_589287 prefixEnd_589287 201724982964094097068283 := by
  unfold tailWord_589287
  simp only [CollatzResearch.WordTrace]
  refine ⟨21493062616121316052174115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14328708410747544034782743 21493062616121316052174115)
  ·
    refine ⟨32239593924181974078261173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21493062616121316052174115 32239593924181974078261173)
    ·
      refine ⟨3022461930392060069836985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32239593924181974078261173 3022461930392060069836985)
      ·
        refine ⟨2266846447794045052377739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3022461930392060069836985 2266846447794045052377739)
        ·
          refine ⟨3400269671691067578566609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2266846447794045052377739 3400269671691067578566609)
          ·
            refine ⟨2550202253768300683924957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3400269671691067578566609 2550202253768300683924957)
            ·
              refine ⟨956325845163112756471859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2550202253768300683924957 956325845163112756471859)
              ·
                refine ⟨1434488767744669134707789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 956325845163112756471859 1434488767744669134707789)
                ·
                  refine ⟨537933287904250925515421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1434488767744669134707789 537933287904250925515421)
                  ·
                    refine ⟨201724982964094097068283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 537933287904250925515421 201724982964094097068283)
                    ·
                      rfl

theorem cell22_589287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 1, 3, 3].length) (baseStart_589287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_589287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_589287 prefixEnd_589287 := by exact prefixLift 589287
  have htrace : WordTrace (prefixWord ++ tailWord_589287) baseStart_589287 baseEnd_589287 := by
    simpa [prefixWord, tailWord_589287, baseEnd_589287] using wordTrace_append hprefix tailTrace_589287
  have hstable : (prefixWord ++ tailWord_589287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589287).length < 2 ^ (prefixWord ++ tailWord_589287).sum := by decide
  have hdescent : baseEnd_589287 < baseStart_589287 := by decide
  rcases family_descends (prefixWord ++ tailWord_589287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589293 : List Nat := [1, 5, 1, 3, 3, 1, 2, 1, 2, 3]
def baseStart_589293 : Nat := 118140960795 + 589293 * 2 ^ 59
def prefixEnd_589293 : Nat := 4983230072969 + 3 ^ 40 * 589293 * 2
def baseEnd_589293 : Nat := 201727036886712081418265

theorem tailTrace_589293 : CollatzResearch.WordTrace tailWord_589293 prefixEnd_589293 201727036886712081418265 := by
  unfold tailWord_589293
  simp only [CollatzResearch.WordTrace]
  refine ⟨21493281454099579076892533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14328854302733052717928355 21493281454099579076892533)
  ·
    refine ⟨2014995136321835538458675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21493281454099579076892533 2014995136321835538458675)
    ·
      refine ⟨3022492704482753307688013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2014995136321835538458675 3022492704482753307688013)
      ·
        refine ⟨1133434764181032490383005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3022492704482753307688013 1133434764181032490383005)
        ·
          refine ⟨425038036567887183893627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1133434764181032490383005 425038036567887183893627)
          ·
            refine ⟨637557054851830775840441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 425038036567887183893627 637557054851830775840441)
            ·
              refine ⟨478167791138873081880331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 637557054851830775840441 478167791138873081880331)
              ·
                refine ⟨717251686708309622820497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 478167791138873081880331 717251686708309622820497)
                ·
                  refine ⟨537938765031232217115373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 717251686708309622820497 537938765031232217115373)
                  ·
                    refine ⟨201727036886712081418265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 537938765031232217115373 201727036886712081418265)
                    ·
                      rfl

theorem cell22_589293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 2, 1, 2, 3].length) (baseStart_589293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_589293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_589293 prefixEnd_589293 := by exact prefixLift 589293
  have htrace : WordTrace (prefixWord ++ tailWord_589293) baseStart_589293 baseEnd_589293 := by
    simpa [prefixWord, tailWord_589293, baseEnd_589293] using wordTrace_append hprefix tailTrace_589293
  have hstable : (prefixWord ++ tailWord_589293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589293).length < 2 ^ (prefixWord ++ tailWord_589293).sum := by decide
  have hdescent : baseEnd_589293 < baseStart_589293 := by decide
  rcases family_descends (prefixWord ++ tailWord_589293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589360 : List Nat := [2, 1, 1, 1, 2, 3, 1, 2, 6, 3]
def baseStart_589360 : Nat := 118140960795 + 589360 * 2 ^ 59
def prefixEnd_589360 : Nat := 4983230072969 + 3 ^ 40 * 589360 * 2
def baseEnd_589360 : Nat := 201749972355946239993059

theorem tailTrace_589360 : CollatzResearch.WordTrace tailWord_589360 prefixEnd_589360 201749972355946239993059 := by
  unfold tailWord_589360
  simp only [CollatzResearch.WordTrace]
  refine ⟨10747862572428424759790767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14330483429904566346387689 10747862572428424759790767)
  ·
    refine ⟨16121793858642637139686151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10747862572428424759790767 16121793858642637139686151)
    ·
      refine ⟨24182690787963955709529227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16121793858642637139686151 24182690787963955709529227)
      ·
        refine ⟨36274036181945933564293841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24182690787963955709529227 36274036181945933564293841)
        ·
          refine ⟨27205527136459450173220381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36274036181945933564293841 27205527136459450173220381)
          ·
            refine ⟨10202072676172293814957643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27205527136459450173220381 10202072676172293814957643)
            ·
              refine ⟨15303109014258440722436465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10202072676172293814957643 15303109014258440722436465)
              ·
                refine ⟨11477331760693830541827349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15303109014258440722436465 11477331760693830541827349)
                ·
                  refine ⟨537999926282523306648157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 11477331760693830541827349 537999926282523306648157)
                  ·
                    refine ⟨201749972355946239993059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 537999926282523306648157 201749972355946239993059)
                    ·
                      rfl

theorem cell22_589360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 6, 3].length) (baseStart_589360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_589360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_589360 prefixEnd_589360 := by exact prefixLift 589360
  have htrace : WordTrace (prefixWord ++ tailWord_589360) baseStart_589360 baseEnd_589360 := by
    simpa [prefixWord, tailWord_589360, baseEnd_589360] using wordTrace_append hprefix tailTrace_589360
  have hstable : (prefixWord ++ tailWord_589360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589360).length < 2 ^ (prefixWord ++ tailWord_589360).sum := by decide
  have hdescent : baseEnd_589360 < baseStart_589360 := by decide
  rcases family_descends (prefixWord ++ tailWord_589360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589375 : List Nat := [1, 1, 2, 2, 3, 4, 1, 1, 1, 6]
def baseStart_589375 : Nat := 118140960795 + 589375 * 2 ^ 59
def prefixEnd_589375 : Nat := 4983230072969 + 3 ^ 40 * 589375 * 2
def baseEnd_589375 : Nat := 201755107162491200868013

theorem tailTrace_589375 : CollatzResearch.WordTrace tailWord_589375 prefixEnd_589375 201755107162491200868013 := by
  unfold tailWord_589375
  simp only [CollatzResearch.WordTrace]
  refine ⟨21496272239802507081377579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14330848159868338054251719 21496272239802507081377579)
  ·
    refine ⟨32244408359703760622066369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21496272239802507081377579 32244408359703760622066369)
    ·
      refine ⟨24183306269777820466549777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32244408359703760622066369 24183306269777820466549777)
      ·
        refine ⟨18137479702333365349912333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24183306269777820466549777 18137479702333365349912333)
        ·
          refine ⟨6801554888375012006217125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18137479702333365349912333 6801554888375012006217125)
          ·
            refine ⟨1275291541570314751165711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6801554888375012006217125 1275291541570314751165711)
            ·
              refine ⟨1912937312355472126748567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1275291541570314751165711 1912937312355472126748567)
              ·
                refine ⟨2869405968533208190122851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1912937312355472126748567 2869405968533208190122851)
                ·
                  refine ⟨4304108952799812285184277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2869405968533208190122851 4304108952799812285184277)
                  ·
                    refine ⟨201755107162491200868013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4304108952799812285184277 201755107162491200868013)
                    ·
                      rfl

theorem cell22_589375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 1, 1, 6].length) (baseStart_589375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_589375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_589375 prefixEnd_589375 := by exact prefixLift 589375
  have htrace : WordTrace (prefixWord ++ tailWord_589375) baseStart_589375 baseEnd_589375 := by
    simpa [prefixWord, tailWord_589375, baseEnd_589375] using wordTrace_append hprefix tailTrace_589375
  have hstable : (prefixWord ++ tailWord_589375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589375).length < 2 ^ (prefixWord ++ tailWord_589375).sum := by decide
  have hdescent : baseEnd_589375 < baseStart_589375 := by decide
  rcases family_descends (prefixWord ++ tailWord_589375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589377 : List Nat := [1, 2, 5, 1, 1, 1, 2, 2, 4, 3]
def baseStart_589377 : Nat := 118140960795 + 589377 * 2 ^ 59
def prefixEnd_589377 : Nat := 4983230072969 + 3 ^ 40 * 589377 * 2
def baseEnd_589377 : Nat := 201755791803363862318007

theorem tailTrace_589377 : CollatzResearch.WordTrace tailWord_589377 prefixEnd_589377 201755791803363862318007 := by
  unfold tailWord_589377
  simp only [CollatzResearch.WordTrace]
  refine ⟨21496345185795261422950385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14330896790530174281966923 21496345185795261422950385)
  ·
    refine ⟨16122258889346446067212789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21496345185795261422950385 16122258889346446067212789)
    ·
      refine ⟨1511461770876229318801199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16122258889346446067212789 1511461770876229318801199)
      ·
        refine ⟨2267192656314343978201799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1511461770876229318801199 2267192656314343978201799)
        ·
          refine ⟨3400788984471515967302699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2267192656314343978201799 3400788984471515967302699)
          ·
            refine ⟨5101183476707273950954049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3400788984471515967302699 5101183476707273950954049)
            ·
              refine ⟨3825887607530455463215537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5101183476707273950954049 3825887607530455463215537)
              ·
                refine ⟨2869415705647841597411653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3825887607530455463215537 2869415705647841597411653)
                ·
                  refine ⟨538015444808970299514685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2869415705647841597411653 538015444808970299514685)
                  ·
                    refine ⟨201755791803363862318007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 538015444808970299514685 201755791803363862318007)
                    ·
                      rfl

theorem cell22_589377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_589377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_589377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_589377 prefixEnd_589377 := by exact prefixLift 589377
  have htrace : WordTrace (prefixWord ++ tailWord_589377) baseStart_589377 baseEnd_589377 := by
    simpa [prefixWord, tailWord_589377, baseEnd_589377] using wordTrace_append hprefix tailTrace_589377
  have hstable : (prefixWord ++ tailWord_589377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589377).length < 2 ^ (prefixWord ++ tailWord_589377).sum := by decide
  have hdescent : baseEnd_589377 < baseStart_589377 := by decide
  rcases family_descends (prefixWord ++ tailWord_589377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589394 : List Nat := [3, 2, 2, 1, 2, 2, 3, 2, 2, 3]
def baseStart_589394 : Nat := 118140960795 + 589394 * 2 ^ 59
def prefixEnd_589394 : Nat := 4983230072969 + 3 ^ 40 * 589394 * 2
def baseEnd_589394 : Nat := 201761611250781484642955

theorem tailTrace_589394 : CollatzResearch.WordTrace tailWord_589394 prefixEnd_589394 201761611250781484642955 := by
  unfold tailWord_589394
  simp only [CollatzResearch.WordTrace]
  refine ⟨5374241306683418331579809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14331310151155782217546157 5374241306683418331579809)
  ·
    refine ⟨4030680980012563748684857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5374241306683418331579809 4030680980012563748684857)
    ·
      refine ⟨3023010735009422811513643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4030680980012563748684857 3023010735009422811513643)
      ·
        refine ⟨4534516102514134217270465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3023010735009422811513643 4534516102514134217270465)
        ·
          refine ⟨3400887076885600662952849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4534516102514134217270465 3400887076885600662952849)
          ·
            refine ⟨2550665307664200497214637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3400887076885600662952849 2550665307664200497214637)
            ·
              refine ⟨956499490374075186455489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2550665307664200497214637 956499490374075186455489)
              ·
                refine ⟨717374617780556389841617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 956499490374075186455489 717374617780556389841617)
                ·
                  refine ⟨538030963335417292381213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 717374617780556389841617 538030963335417292381213)
                  ·
                    refine ⟨201761611250781484642955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 538030963335417292381213 201761611250781484642955)
                    ·
                      rfl

theorem cell22_589394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 2, 2, 3].length) (baseStart_589394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_589394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_589394 prefixEnd_589394 := by exact prefixLift 589394
  have htrace : WordTrace (prefixWord ++ tailWord_589394) baseStart_589394 baseEnd_589394 := by
    simpa [prefixWord, tailWord_589394, baseEnd_589394] using wordTrace_append hprefix tailTrace_589394
  have hstable : (prefixWord ++ tailWord_589394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589394).length < 2 ^ (prefixWord ++ tailWord_589394).sum := by decide
  have hdescent : baseEnd_589394 < baseStart_589394 := by decide
  rcases family_descends (prefixWord ++ tailWord_589394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589529 : List Nat := [1, 2, 1, 2, 3, 3, 2, 3, 2, 3]
def baseStart_589529 : Nat := 118140960795 + 589529 * 2 ^ 59
def prefixEnd_589529 : Nat := 4983230072969 + 3 ^ 40 * 589529 * 2
def baseEnd_589529 : Nat := 201807824509686132517541

theorem tailTrace_589529 : CollatzResearch.WordTrace tailWord_589529 prefixEnd_589529 201807824509686132517541 := by
  unfold tailWord_589529
  simp only [CollatzResearch.WordTrace]
  refine ⟨21501889081244591382483641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14334592720829727588322427 21501889081244591382483641)
  ·
    refine ⟨16126416810933443536862731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21501889081244591382483641 16126416810933443536862731)
    ·
      refine ⟨24189625216400165305294097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16126416810933443536862731 24189625216400165305294097)
      ·
        refine ⟨18142218912300123978970573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24189625216400165305294097 18142218912300123978970573)
        ·
          refine ⟨6803332092112546492113965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18142218912300123978970573 6803332092112546492113965)
          ·
            refine ⟨2551249534542204934542737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6803332092112546492113965 2551249534542204934542737)
            ·
              refine ⟨1913437150906653700907053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2551249534542204934542737 1913437150906653700907053)
              ·
                refine ⟨717538931589995137840145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1913437150906653700907053 717538931589995137840145)
                ·
                  refine ⟨538154198692496353380109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 717538931589995137840145 538154198692496353380109)
                  ·
                    refine ⟨201807824509686132517541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 538154198692496353380109 201807824509686132517541)
                    ·
                      rfl

theorem cell22_589529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 3, 2, 3].length) (baseStart_589529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_589529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_589529 prefixEnd_589529 := by exact prefixLift 589529
  have htrace : WordTrace (prefixWord ++ tailWord_589529) baseStart_589529 baseEnd_589529 := by
    simpa [prefixWord, tailWord_589529, baseEnd_589529] using wordTrace_append hprefix tailTrace_589529
  have hstable : (prefixWord ++ tailWord_589529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589529).length < 2 ^ (prefixWord ++ tailWord_589529).sum := by decide
  have hdescent : baseEnd_589529 < baseStart_589529 := by decide
  rcases family_descends (prefixWord ++ tailWord_589529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589544 : List Nat := [2, 1, 4, 1, 3, 1, 3, 1, 2, 4]
def baseStart_589544 : Nat := 118140960795 + 589544 * 2 ^ 59
def prefixEnd_589544 : Nat := 4983230072969 + 3 ^ 40 * 589544 * 2
def baseEnd_589544 : Nat := 201812959316231093392495

theorem tailTrace_589544 : CollatzResearch.WordTrace tailWord_589544 prefixEnd_589544 201812959316231093392495 := by
  unfold tailWord_589544
  simp only [CollatzResearch.WordTrace]
  refine ⟨10751218088095124472139843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14334957450793499296186457 10751218088095124472139843)
  ·
    refine ⟨16126827132142686708209765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10751218088095124472139843 16126827132142686708209765)
    ·
      refine ⟨3023780087276753757789331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16126827132142686708209765 3023780087276753757789331)
      ·
        refine ⟨4535670130915130636683997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3023780087276753757789331 4535670130915130636683997)
        ·
          refine ⟨1700876299093173988756499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4535670130915130636683997 1700876299093173988756499)
          ·
            refine ⟨2551314448639760983134749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1700876299093173988756499 2551314448639760983134749)
            ·
              refine ⟨956742918239910368675531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2551314448639760983134749 956742918239910368675531)
              ·
                refine ⟨1435114377359865553013297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 956742918239910368675531 1435114377359865553013297)
                ·
                  refine ⟨1076335783019899164759973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1435114377359865553013297 1076335783019899164759973)
                  ·
                    refine ⟨201812959316231093392495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1076335783019899164759973 201812959316231093392495)
                    ·
                      rfl

theorem cell22_589544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_589544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_589544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_589544 prefixEnd_589544 := by exact prefixLift 589544
  have htrace : WordTrace (prefixWord ++ tailWord_589544) baseStart_589544 baseEnd_589544 := by
    simpa [prefixWord, tailWord_589544, baseEnd_589544] using wordTrace_append hprefix tailTrace_589544
  have hstable : (prefixWord ++ tailWord_589544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589544).length < 2 ^ (prefixWord ++ tailWord_589544).sum := by decide
  have hdescent : baseEnd_589544 < baseStart_589544 := by decide
  rcases family_descends (prefixWord ++ tailWord_589544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589608 : List Nat := [2, 1, 5, 1, 1, 2, 3, 3, 1, 3]
def baseStart_589608 : Nat := 118140960795 + 589608 * 2 ^ 59
def prefixEnd_589608 : Nat := 4983230072969 + 3 ^ 40 * 589608 * 2
def baseEnd_589608 : Nat := 201834867824156259792299

theorem tailTrace_589608 : CollatzResearch.WordTrace tailWord_589608 prefixEnd_589608 201834867824156259792299 := by
  unfold tailWord_589608
  simp only [CollatzResearch.WordTrace]
  refine ⟨10752385223979193937304739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14336513631972258583072985 10752385223979193937304739)
  ·
    refine ⟨16128577835968790905957109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10752385223979193937304739 16128577835968790905957109)
    ·
      refine ⟨1512054172122074147433479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16128577835968790905957109 1512054172122074147433479)
      ·
        refine ⟨2268081258183111221150219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1512054172122074147433479 2268081258183111221150219)
        ·
          refine ⟨3402121887274666831725329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2268081258183111221150219 3402121887274666831725329)
          ·
            refine ⟨2551591415456000123793997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3402121887274666831725329 2551591415456000123793997)
            ·
              refine ⟨956846780796000046422749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2551591415456000123793997 956846780796000046422749)
              ·
                refine ⟨358817542798500017408531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 956846780796000046422749 358817542798500017408531)
                ·
                  refine ⟨538226314197750026112797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 358817542798500017408531 538226314197750026112797)
                  ·
                    refine ⟨201834867824156259792299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 538226314197750026112797 201834867824156259792299)
                    ·
                      rfl

theorem cell22_589608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_589608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_589608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_589608 prefixEnd_589608 := by exact prefixLift 589608
  have htrace : WordTrace (prefixWord ++ tailWord_589608) baseStart_589608 baseEnd_589608 := by
    simpa [prefixWord, tailWord_589608, baseEnd_589608] using wordTrace_append hprefix tailTrace_589608
  have hstable : (prefixWord ++ tailWord_589608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589608).length < 2 ^ (prefixWord ++ tailWord_589608).sum := by decide
  have hdescent : baseEnd_589608 < baseStart_589608 := by decide
  rcases family_descends (prefixWord ++ tailWord_589608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589625 : List Nat := [1, 2, 1, 7, 2, 1, 1, 1, 3, 3]
def baseStart_589625 : Nat := 118140960795 + 589625 * 2 ^ 59
def prefixEnd_589625 : Nat := 4983230072969 + 3 ^ 40 * 589625 * 2
def baseEnd_589625 : Nat := 201840687271573882117247

theorem tailTrace_589625 : CollatzResearch.WordTrace tailWord_589625 prefixEnd_589625 201840687271573882117247 := by
  unfold tailWord_589625
  simp only [CollatzResearch.WordTrace]
  refine ⟨21505390488896799777978329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14336926992597866518652219 21505390488896799777978329)
  ·
    refine ⟨16129042866672599833483747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21505390488896799777978329 16129042866672599833483747)
    ·
      refine ⟨24193564300008899750225621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16129042866672599833483747 24193564300008899750225621)
      ·
        refine ⟨567036663281458587895913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 24193564300008899750225621 567036663281458587895913)
        ·
          refine ⟨425277497461093940921935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 567036663281458587895913 425277497461093940921935)
          ·
            refine ⟨637916246191640911382903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 425277497461093940921935 637916246191640911382903)
            ·
              refine ⟨956874369287461367074355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 637916246191640911382903 956874369287461367074355)
              ·
                refine ⟨1435311553931192050611533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 956874369287461367074355 1435311553931192050611533)
                ·
                  refine ⟨538241832724197018979325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1435311553931192050611533 538241832724197018979325)
                  ·
                    refine ⟨201840687271573882117247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 538241832724197018979325 201840687271573882117247)
                    ·
                      rfl

theorem cell22_589625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 1, 3, 3].length) (baseStart_589625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_589625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_589625 prefixEnd_589625 := by exact prefixLift 589625
  have htrace : WordTrace (prefixWord ++ tailWord_589625) baseStart_589625 baseEnd_589625 := by
    simpa [prefixWord, tailWord_589625, baseEnd_589625] using wordTrace_append hprefix tailTrace_589625
  have hstable : (prefixWord ++ tailWord_589625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589625).length < 2 ^ (prefixWord ++ tailWord_589625).sum := by decide
  have hdescent : baseEnd_589625 < baseStart_589625 := by decide
  rcases family_descends (prefixWord ++ tailWord_589625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589638 : List Nat := [6, 1, 1, 2, 1, 2, 1, 3, 5]
def baseStart_589638 : Nat := 118140960795 + 589638 * 2 ^ 59
def prefixEnd_589638 : Nat := 4983230072969 + 3 ^ 40 * 589638 * 2
def baseEnd_589638 : Nat := 67281712479082060514069

theorem tailTrace_589638 : CollatzResearch.WordTrace tailWord_589638 prefixEnd_589638 67281712479082060514069 := by
  unfold tailWord_589638
  simp only [CollatzResearch.WordTrace]
  refine ⟨672058269932803218693799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 14337243091899801998801045 672058269932803218693799)
  ·
    refine ⟨1008087404899204828040699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 672058269932803218693799 1008087404899204828040699)
    ·
      refine ⟨1512131107348807242061049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1008087404899204828040699 1512131107348807242061049)
      ·
        refine ⟨1134098330511605431545787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1512131107348807242061049 1134098330511605431545787)
        ·
          refine ⟨1701147495767408147318681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1134098330511605431545787 1701147495767408147318681)
          ·
            refine ⟨1275860621825556110489011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1701147495767408147318681 1275860621825556110489011)
            ·
              refine ⟨1913790932738334165733517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1275860621825556110489011 1913790932738334165733517)
              ·
                refine ⟨717671599776875312150069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1913790932738334165733517 717671599776875312150069)
                ·
                  refine ⟨67281712479082060514069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 717671599776875312150069 67281712479082060514069)
                  ·
                    rfl

theorem cell22_589638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_589638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_589638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_589638 prefixEnd_589638 := by exact prefixLift 589638
  have htrace : WordTrace (prefixWord ++ tailWord_589638) baseStart_589638 baseEnd_589638 := by
    simpa [prefixWord, tailWord_589638, baseEnd_589638] using wordTrace_append hprefix tailTrace_589638
  have hstable : (prefixWord ++ tailWord_589638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589638).length < 2 ^ (prefixWord ++ tailWord_589638).sum := by decide
  have hdescent : baseEnd_589638 < baseStart_589638 := by decide
  rcases family_descends (prefixWord ++ tailWord_589638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589664 : List Nat := [2, 1, 1, 3, 3, 3, 1, 2, 1, 5]
def baseStart_589664 : Nat := 118140960795 + 589664 * 2 ^ 59
def prefixEnd_589664 : Nat := 4983230072969 + 3 ^ 40 * 589664 * 2
def baseEnd_589664 : Nat := 201854037768590780392127

theorem tailTrace_589664 : CollatzResearch.WordTrace tailWord_589664 prefixEnd_589664 201854037768590780392127 := by
  unfold tailWord_589664
  simp only [CollatzResearch.WordTrace]
  refine ⟨10753406467877754719324023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14337875290503672959098697 10753406467877754719324023)
  ·
    refine ⟨16130109701816632078986035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10753406467877754719324023 16130109701816632078986035)
    ·
      refine ⟨24195164552724948118479053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16130109701816632078986035 24195164552724948118479053)
      ·
        refine ⟨9073186707271855544429645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24195164552724948118479053 9073186707271855544429645)
        ·
          refine ⟨3402445015226945829161117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9073186707271855544429645 3402445015226945829161117)
          ·
            refine ⟨1275916880710104685935419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3402445015226945829161117 1275916880710104685935419)
            ·
              refine ⟨1913875321065157028903129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1275916880710104685935419 1913875321065157028903129)
              ·
                refine ⟨1435406490798867771677347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1913875321065157028903129 1435406490798867771677347)
                ·
                  refine ⟨2153109736198301657516021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1435406490798867771677347 2153109736198301657516021)
                  ·
                    refine ⟨201854037768590780392127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2153109736198301657516021 201854037768590780392127)
                    ·
                      rfl

theorem cell22_589664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 2, 1, 5].length) (baseStart_589664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_589664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_589664 prefixEnd_589664 := by exact prefixLift 589664
  have htrace : WordTrace (prefixWord ++ tailWord_589664) baseStart_589664 baseEnd_589664 := by
    simpa [prefixWord, tailWord_589664, baseEnd_589664] using wordTrace_append hprefix tailTrace_589664
  have hstable : (prefixWord ++ tailWord_589664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589664).length < 2 ^ (prefixWord ++ tailWord_589664).sum := by decide
  have hdescent : baseEnd_589664 < baseStart_589664 := by decide
  rcases family_descends (prefixWord ++ tailWord_589664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589668 : List Nat := [2, 3, 1, 1, 5, 1, 3, 1, 1, 4]
def baseStart_589668 : Nat := 118140960795 + 589668 * 2 ^ 59
def prefixEnd_589668 : Nat := 4983230072969 + 3 ^ 40 * 589668 * 2
def baseEnd_589668 : Nat := 201855407050336103292115

theorem tailTrace_589668 : CollatzResearch.WordTrace tailWord_589668 prefixEnd_589668 201855407050336103292115 := by
  unfold tailWord_589668
  simp only [CollatzResearch.WordTrace]
  refine ⟨10753479413870509060896829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14337972551827345414529105 10753479413870509060896829)
  ·
    refine ⟨4032554780201440897836311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10753479413870509060896829 4032554780201440897836311)
    ·
      refine ⟨6048832170302161346754467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4032554780201440897836311 6048832170302161346754467)
      ·
        refine ⟨9073248255453242020131701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6048832170302161346754467 9073248255453242020131701)
        ·
          refine ⟨850617023948741439387347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9073248255453242020131701 850617023948741439387347)
          ·
            refine ⟨1275925535923112159081021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 850617023948741439387347 1275925535923112159081021)
            ·
              refine ⟨478472075971167059655383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1275925535923112159081021 478472075971167059655383)
              ·
                refine ⟨717708113956750589483075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 478472075971167059655383 717708113956750589483075)
                ·
                  refine ⟨1076562170935125884224613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 717708113956750589483075 1076562170935125884224613)
                  ·
                    refine ⟨201855407050336103292115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1076562170935125884224613 201855407050336103292115)
                    ·
                      rfl

theorem cell22_589668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 3, 1, 1, 4].length) (baseStart_589668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_589668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_589668 prefixEnd_589668 := by exact prefixLift 589668
  have htrace : WordTrace (prefixWord ++ tailWord_589668) baseStart_589668 baseEnd_589668 := by
    simpa [prefixWord, tailWord_589668, baseEnd_589668] using wordTrace_append hprefix tailTrace_589668
  have hstable : (prefixWord ++ tailWord_589668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589668).length < 2 ^ (prefixWord ++ tailWord_589668).sum := by decide
  have hdescent : baseEnd_589668 < baseStart_589668 := by decide
  rcases family_descends (prefixWord ++ tailWord_589668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589681 : List Nat := [1, 2, 2, 2, 1, 3, 4, 2, 2, 3]
def baseStart_589681 : Nat := 118140960795 + 589681 * 2 ^ 59
def prefixEnd_589681 : Nat := 4983230072969 + 3 ^ 40 * 589681 * 2
def baseEnd_589681 : Nat := 201859857216008402717075

theorem tailTrace_589681 : CollatzResearch.WordTrace tailWord_589681 prefixEnd_589681 201859857216008402717075 := by
  unfold tailWord_589681
  simp only [CollatzResearch.WordTrace]
  refine ⟨21507432976693921342016897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14338288651129280894677931 21507432976693921342016897)
  ·
    refine ⟨16130574732520441006512673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21507432976693921342016897 16130574732520441006512673)
    ·
      refine ⟨12097931049390330754884505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16130574732520441006512673 12097931049390330754884505)
      ·
        refine ⟨9073448287042748066163379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12097931049390330754884505 9073448287042748066163379)
        ·
          refine ⟨13610172430564122099245069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9073448287042748066163379 13610172430564122099245069)
          ·
            refine ⟨5103814661461545787216901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13610172430564122099245069 5103814661461545787216901)
            ·
              refine ⟨956965249024039835103169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5103814661461545787216901 956965249024039835103169)
              ·
                refine ⟨717723936768029876327377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 956965249024039835103169 717723936768029876327377)
                ·
                  refine ⟨538292952576022407245533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 717723936768029876327377 538292952576022407245533)
                  ·
                    refine ⟨201859857216008402717075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 538292952576022407245533 201859857216008402717075)
                    ·
                      rfl

theorem cell22_589681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 2, 2, 3].length) (baseStart_589681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_589681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_589681 prefixEnd_589681 := by exact prefixLift 589681
  have htrace : WordTrace (prefixWord ++ tailWord_589681) baseStart_589681 baseEnd_589681 := by
    simpa [prefixWord, tailWord_589681, baseEnd_589681] using wordTrace_append hprefix tailTrace_589681
  have hstable : (prefixWord ++ tailWord_589681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589681).length < 2 ^ (prefixWord ++ tailWord_589681).sum := by decide
  have hdescent : baseEnd_589681 < baseStart_589681 := by decide
  rcases family_descends (prefixWord ++ tailWord_589681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589692 : List Nat := [2, 2, 2, 1, 1, 1, 1, 1, 4, 7]
def baseStart_589692 : Nat := 118140960795 + 589692 * 2 ^ 59
def prefixEnd_589692 : Nat := 4983230072969 + 3 ^ 40 * 589692 * 2
def baseEnd_589692 : Nat := 201863622740808040692041

theorem tailTrace_589692 : CollatzResearch.WordTrace tailWord_589692 prefixEnd_589692 201863622740808040692041 := by
  unfold tailWord_589692
  simp only [CollatzResearch.WordTrace]
  refine ⟨10753917089827035110333665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14338556119769380147111553 10753917089827035110333665)
  ·
    refine ⟨8065437817370276332750249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10753917089827035110333665 8065437817370276332750249)
    ·
      refine ⟨6049078363027707249562687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8065437817370276332750249 6049078363027707249562687)
      ·
        refine ⟨9073617544541560874344031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6049078363027707249562687 9073617544541560874344031)
        ·
          refine ⟨13610426316812341311516047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9073617544541560874344031 13610426316812341311516047)
          ·
            refine ⟨20415639475218511967274071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13610426316812341311516047 20415639475218511967274071)
            ·
              refine ⟨30623459212827767950911107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20415639475218511967274071 30623459212827767950911107)
              ·
                refine ⟨45935188819241651926366661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30623459212827767950911107 45935188819241651926366661)
                ·
                  refine ⟨8612847903607809736193749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45935188819241651926366661 8612847903607809736193749)
                  ·
                    refine ⟨201863622740808040692041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8612847903607809736193749 201863622740808040692041)
                    ·
                      rfl

theorem cell22_589692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 4, 7].length) (baseStart_589692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_589692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_589692 prefixEnd_589692 := by exact prefixLift 589692
  have htrace : WordTrace (prefixWord ++ tailWord_589692) baseStart_589692 baseEnd_589692 := by
    simpa [prefixWord, tailWord_589692, baseEnd_589692] using wordTrace_append hprefix tailTrace_589692
  have hstable : (prefixWord ++ tailWord_589692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589692).length < 2 ^ (prefixWord ++ tailWord_589692).sum := by decide
  have hdescent : baseEnd_589692 < baseStart_589692 := by decide
  rcases family_descends (prefixWord ++ tailWord_589692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589707 : List Nat := [1, 1, 1, 1, 4, 2, 1, 1, 4, 6]
def baseStart_589707 : Nat := 118140960795 + 589707 * 2 ^ 59
def prefixEnd_589707 : Nat := 4983230072969 + 3 ^ 40 * 589707 * 2
def baseEnd_589707 : Nat := 201868757547353001566995

theorem tailTrace_589707 : CollatzResearch.WordTrace tailWord_589707 prefixEnd_589707 201868757547353001566995 := by
  unfold tailWord_589707
  simp only [CollatzResearch.WordTrace]
  refine ⟨21508381274599727782463375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14338920849733151854975583 21508381274599727782463375)
  ·
    refine ⟨32262571911899591673695063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21508381274599727782463375 32262571911899591673695063)
    ·
      refine ⟨48393857867849387510542595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32262571911899591673695063 48393857867849387510542595)
      ·
        refine ⟨72590786801774081265813893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48393857867849387510542595 72590786801774081265813893)
        ·
          refine ⟨13610772525332640237340105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72590786801774081265813893 13610772525332640237340105)
          ·
            refine ⟨10208079393999480178005079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13610772525332640237340105 10208079393999480178005079)
            ·
              refine ⟨15312119090999220267007619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10208079393999480178005079 15312119090999220267007619)
              ·
                refine ⟨22968178636498830400511429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15312119090999220267007619 22968178636498830400511429)
                ·
                  refine ⟨4306533494343530700095893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22968178636498830400511429 4306533494343530700095893)
                  ·
                    refine ⟨201868757547353001566995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4306533494343530700095893 201868757547353001566995)
                    ·
                      rfl

theorem cell22_589707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 4, 6].length) (baseStart_589707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_589707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_589707 prefixEnd_589707 := by exact prefixLift 589707
  have htrace : WordTrace (prefixWord ++ tailWord_589707) baseStart_589707 baseEnd_589707 := by
    simpa [prefixWord, tailWord_589707, baseEnd_589707] using wordTrace_append hprefix tailTrace_589707
  have hstable : (prefixWord ++ tailWord_589707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589707).length < 2 ^ (prefixWord ++ tailWord_589707).sum := by decide
  have hdescent : baseEnd_589707 < baseStart_589707 := by decide
  rcases family_descends (prefixWord ++ tailWord_589707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589794 : List Nat := [3, 3, 3, 1, 2, 1, 3, 2, 1, 3]
def baseStart_589794 : Nat := 118140960795 + 589794 * 2 ^ 59
def prefixEnd_589794 : Nat := 4983230072969 + 3 ^ 40 * 589794 * 2
def baseEnd_589794 : Nat := 201898539425313774641729

theorem tailTrace_589794 : CollatzResearch.WordTrace tailWord_589794 prefixEnd_589794 201898539425313774641729 := by
  unfold tailWord_589794
  simp only [CollatzResearch.WordTrace]
  refine ⟨5377888606321135410220109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14341036283523027760586957 5377888606321135410220109)
  ·
    refine ⟨2016708227370425778832541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5377888606321135410220109 2016708227370425778832541)
    ·
      refine ⟨756265585263909667062203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2016708227370425778832541 756265585263909667062203)
      ·
        refine ⟨1134398377895864500593305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 756265585263909667062203 1134398377895864500593305)
        ·
          refine ⟨850798783421898375444979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1134398377895864500593305 850798783421898375444979)
          ·
            refine ⟨1276198175132847563167469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 850798783421898375444979 1276198175132847563167469)
            ·
              refine ⟨478574315674817836187801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1276198175132847563167469 478574315674817836187801)
              ·
                refine ⟨358930736756113377140851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 478574315674817836187801 358930736756113377140851)
                ·
                  refine ⟨538396105134170065711277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 358930736756113377140851 538396105134170065711277)
                  ·
                    refine ⟨201898539425313774641729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 538396105134170065711277 201898539425313774641729)
                    ·
                      rfl

theorem cell22_589794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_589794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_589794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_589794 prefixEnd_589794 := by exact prefixLift 589794
  have htrace : WordTrace (prefixWord ++ tailWord_589794) baseStart_589794 baseEnd_589794 := by
    simpa [prefixWord, tailWord_589794, baseEnd_589794] using wordTrace_append hprefix tailTrace_589794
  have hstable : (prefixWord ++ tailWord_589794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589794).length < 2 ^ (prefixWord ++ tailWord_589794).sum := by decide
  have hdescent : baseEnd_589794 < baseStart_589794 := by decide
  rcases family_descends (prefixWord ++ tailWord_589794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589829 : List Nat := [1, 3, 1, 1, 2, 4, 2, 8]
def baseStart_589829 : Nat := 118140960795 + 589829 * 2 ^ 59
def prefixEnd_589829 : Nat := 4983230072969 + 3 ^ 40 * 589829 * 2
def baseEnd_589829 : Nat := 22434502293398372224069

theorem tailTrace_589829 : CollatzResearch.WordTrace tailWord_589829 prefixEnd_589829 22434502293398372224069 := by
  unfold tailWord_589829
  simp only [CollatzResearch.WordTrace]
  refine ⟨21512830980157742618404541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14341887320105161745603027 21512830980157742618404541)
  ·
    refine ⟨8067311617559153481901703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21512830980157742618404541 8067311617559153481901703)
    ·
      refine ⟨12100967426338730222852555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8067311617559153481901703 12100967426338730222852555)
      ·
        refine ⟨18151451139508095334278833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12100967426338730222852555 18151451139508095334278833)
        ·
          refine ⟨13613588354631071500709125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18151451139508095334278833 13613588354631071500709125)
          ·
            refine ⟨2552547816493325906382961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13613588354631071500709125 2552547816493325906382961)
            ·
              refine ⟨1914410862369994429787221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2552547816493325906382961 1914410862369994429787221)
              ·
                refine ⟨22434502293398372224069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1914410862369994429787221 22434502293398372224069)
                ·
                  rfl

theorem cell22_589829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 8].length) (baseStart_589829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_589829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_589829 prefixEnd_589829 := by exact prefixLift 589829
  have htrace : WordTrace (prefixWord ++ tailWord_589829) baseStart_589829 baseEnd_589829 := by
    simpa [prefixWord, tailWord_589829, baseEnd_589829] using wordTrace_append hprefix tailTrace_589829
  have hstable : (prefixWord ++ tailWord_589829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589829).length < 2 ^ (prefixWord ++ tailWord_589829).sum := by decide
  have hdescent : baseEnd_589829 < baseStart_589829 := by decide
  rcases family_descends (prefixWord ++ tailWord_589829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589831 : List Nat := [1, 1, 4, 3, 1, 2, 1, 3, 2, 4]
def baseStart_589831 : Nat := 118140960795 + 589831 * 2 ^ 59
def prefixEnd_589831 : Nat := 4983230072969 + 3 ^ 40 * 589831 * 2
def baseEnd_589831 : Nat := 201911205281458011466615

theorem tailTrace_589831 : CollatzResearch.WordTrace tailWord_589831 prefixEnd_589831 201911205281458011466615 := by
  unfold tailWord_589831
  simp only [CollatzResearch.WordTrace]
  refine ⟨21512903926150496959977347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14341935950766997973318231 21512903926150496959977347)
  ·
    refine ⟨32269355889225745439966021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21512903926150496959977347 32269355889225745439966021)
    ·
      refine ⟨6050504229229827269993629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32269355889225745439966021 6050504229229827269993629)
      ·
        refine ⟨2268939085961185226247611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6050504229229827269993629 2268939085961185226247611)
        ·
          refine ⟨3403408628941777839371417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2268939085961185226247611 3403408628941777839371417)
          ·
            refine ⟨2552556471706333379528563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3403408628941777839371417 2552556471706333379528563)
            ·
              refine ⟨3828834707559500069292845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2552556471706333379528563 3828834707559500069292845)
              ·
                refine ⟨1435813015334812525984817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3828834707559500069292845 1435813015334812525984817)
                ·
                  refine ⟨1076859761501109394488613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1435813015334812525984817 1076859761501109394488613)
                  ·
                    refine ⟨201911205281458011466615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1076859761501109394488613 201911205281458011466615)
                    ·
                      rfl

theorem cell22_589831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 3, 2, 4].length) (baseStart_589831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_589831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_589831 prefixEnd_589831 := by exact prefixLift 589831
  have htrace : WordTrace (prefixWord ++ tailWord_589831) baseStart_589831 baseEnd_589831 := by
    simpa [prefixWord, tailWord_589831, baseEnd_589831] using wordTrace_append hprefix tailTrace_589831
  have hstable : (prefixWord ++ tailWord_589831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589831).length < 2 ^ (prefixWord ++ tailWord_589831).sum := by decide
  have hdescent : baseEnd_589831 < baseStart_589831 := by decide
  rcases family_descends (prefixWord ++ tailWord_589831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589859 : List Nat := [1, 1, 1, 4, 3, 1, 1, 1, 1, 8]
def baseStart_589859 : Nat := 118140960795 + 589859 * 2 ^ 59
def prefixEnd_589859 : Nat := 4983230072969 + 3 ^ 40 * 589859 * 2
def baseEnd_589859 : Nat := 201920790253675271766529

theorem tailTrace_589859 : CollatzResearch.WordTrace tailWord_589859 prefixEnd_589859 201920790253675271766529 := by
  unfold tailWord_589859
  simp only [CollatzResearch.WordTrace]
  refine ⟨21513925170049057741996631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14342616780032705161331087 21513925170049057741996631)
  ·
    refine ⟨32270887755073586612994947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21513925170049057741996631 32270887755073586612994947)
    ·
      refine ⟨48406331632610379919492421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32270887755073586612994947 48406331632610379919492421)
      ·
        refine ⟨9076187181114446234904829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48406331632610379919492421 9076187181114446234904829)
        ·
          refine ⟨3403570192917917338089311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9076187181114446234904829 3403570192917917338089311)
          ·
            refine ⟨5105355289376876007133967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3403570192917917338089311 5105355289376876007133967)
            ·
              refine ⟨7658032934065314010700951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5105355289376876007133967 7658032934065314010700951)
              ·
                refine ⟨11487049401097971016051427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7658032934065314010700951 11487049401097971016051427)
                ·
                  refine ⟨17230574101646956524077141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11487049401097971016051427 17230574101646956524077141)
                  ·
                    refine ⟨201920790253675271766529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 17230574101646956524077141 201920790253675271766529)
                    ·
                      rfl

theorem cell22_589859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 8].length) (baseStart_589859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_589859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_589859 prefixEnd_589859 := by exact prefixLift 589859
  have htrace : WordTrace (prefixWord ++ tailWord_589859) baseStart_589859 baseEnd_589859 := by
    simpa [prefixWord, tailWord_589859, baseEnd_589859] using wordTrace_append hprefix tailTrace_589859
  have hstable : (prefixWord ++ tailWord_589859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589859).length < 2 ^ (prefixWord ++ tailWord_589859).sum := by decide
  have hdescent : baseEnd_589859 < baseStart_589859 := by decide
  rcases family_descends (prefixWord ++ tailWord_589859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589895 : List Nat := [1, 1, 4, 1, 3, 1, 4, 3, 1, 3]
def baseStart_589895 : Nat := 118140960795 + 589895 * 2 ^ 59
def prefixEnd_589895 : Nat := 4983230072969 + 3 ^ 40 * 589895 * 2
def baseEnd_589895 : Nat := 201933113789383177866419

theorem tailTrace_589895 : CollatzResearch.WordTrace tailWord_589895 prefixEnd_589895 201933113789383177866419 := by
  unfold tailWord_589895
  simp only [CollatzResearch.WordTrace]
  refine ⟨21515238197918635890307139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14343492131945757260204759 21515238197918635890307139)
  ·
    refine ⟨32272857296877953835460709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21515238197918635890307139 32272857296877953835460709)
    ·
      refine ⟨6051160743164616344148883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32272857296877953835460709 6051160743164616344148883)
      ·
        refine ⟨9076741114746924516223325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6051160743164616344148883 9076741114746924516223325)
        ·
          refine ⟨3403777918030096693583747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9076741114746924516223325 3403777918030096693583747)
          ·
            refine ⟨5105666877045145040375621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3403777918030096693583747 5105666877045145040375621)
            ·
              refine ⟨957312539445964695070429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5105666877045145040375621 957312539445964695070429)
              ·
                refine ⟨358992202292236760651411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 957312539445964695070429 358992202292236760651411)
                ·
                  refine ⟨538488303438355140977117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 358992202292236760651411 538488303438355140977117)
                  ·
                    refine ⟨201933113789383177866419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 538488303438355140977117 201933113789383177866419)
                    ·
                      rfl

theorem cell22_589895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 3, 1, 3].length) (baseStart_589895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_589895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_589895 prefixEnd_589895 := by exact prefixLift 589895
  have htrace : WordTrace (prefixWord ++ tailWord_589895) baseStart_589895 baseEnd_589895 := by
    simpa [prefixWord, tailWord_589895, baseEnd_589895] using wordTrace_append hprefix tailTrace_589895
  have hstable : (prefixWord ++ tailWord_589895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589895).length < 2 ^ (prefixWord ++ tailWord_589895).sum := by decide
  have hdescent : baseEnd_589895 < baseStart_589895 := by decide
  rcases family_descends (prefixWord ++ tailWord_589895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589936 : List Nat := [2, 1, 1, 1, 5, 2, 2, 2, 6]
def baseStart_589936 : Nat := 118140960795 + 589936 * 2 ^ 59
def prefixEnd_589936 : Nat := 4983230072969 + 3 ^ 40 * 589936 * 2
def baseEnd_589936 : Nat := 67315716309090912530431

theorem tailTrace_589936 : CollatzResearch.WordTrace tailWord_589936 prefixEnd_589936 67315716309090912530431 := by
  unfold tailWord_589936
  simp only [CollatzResearch.WordTrace]
  refine ⟨10758366795385049946274831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14344489060513399928366441 10758366795385049946274831)
  ·
    refine ⟨16137550193077574919412247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10758366795385049946274831 16137550193077574919412247)
    ·
      refine ⟨24206325289616362379118371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16137550193077574919412247 24206325289616362379118371)
      ·
        refine ⟨36309487934424543568677557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24206325289616362379118371 36309487934424543568677557)
        ·
          refine ⟨3404014493852300959563521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36309487934424543568677557 3404014493852300959563521)
          ·
            refine ⟨2553010870389225719672641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3404014493852300959563521 2553010870389225719672641)
            ·
              refine ⟨1914758152791919289754481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2553010870389225719672641 1914758152791919289754481)
              ·
                refine ⟨1436068614593939467315861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1914758152791919289754481 1436068614593939467315861)
                ·
                  refine ⟨67315716309090912530431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1436068614593939467315861 67315716309090912530431)
                  ·
                    rfl

theorem cell22_589936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 2, 6].length) (baseStart_589936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_589936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_589936 prefixEnd_589936 := by exact prefixLift 589936
  have htrace : WordTrace (prefixWord ++ tailWord_589936) baseStart_589936 baseEnd_589936 := by
    simpa [prefixWord, tailWord_589936, baseEnd_589936] using wordTrace_append hprefix tailTrace_589936
  have hstable : (prefixWord ++ tailWord_589936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589936).length < 2 ^ (prefixWord ++ tailWord_589936).sum := by decide
  have hdescent : baseEnd_589936 < baseStart_589936 := by decide
  rcases family_descends (prefixWord ++ tailWord_589936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589938 : List Nat := [3, 2, 1, 2, 2, 2, 1, 4, 1, 4]
def baseStart_589938 : Nat := 118140960795 + 589938 * 2 ^ 59
def prefixEnd_589938 : Nat := 4983230072969 + 3 ^ 40 * 589938 * 2
def baseEnd_589938 : Nat := 201947833568145399041287

theorem tailTrace_589938 : CollatzResearch.WordTrace tailWord_589938 prefixEnd_589938 201947833568145399041287 := by
  unfold tailWord_589938
  simp only [CollatzResearch.WordTrace]
  refine ⟨5379201634190713558530617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14344537691175236156081645 5379201634190713558530617)
  ·
    refine ⟨4034401225643035168897963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5379201634190713558530617 4034401225643035168897963)
    ·
      refine ⟨6051601838464552753346945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4034401225643035168897963 6051601838464552753346945)
      ·
        refine ⟨4538701378848414565010209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6051601838464552753346945 4538701378848414565010209)
        ·
          refine ⟨3404026034136310923757657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4538701378848414565010209 3404026034136310923757657)
          ·
            refine ⟨2553019525602233192818243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3404026034136310923757657 2553019525602233192818243)
            ·
              refine ⟨3829529288403349789227365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2553019525602233192818243 3829529288403349789227365)
              ·
                refine ⟨718036741575628085480131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3829529288403349789227365 718036741575628085480131)
                ·
                  refine ⟨1077055112363442128220197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 718036741575628085480131 1077055112363442128220197)
                  ·
                    refine ⟨201947833568145399041287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1077055112363442128220197 201947833568145399041287)
                    ·
                      rfl

theorem cell22_589938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 4, 1, 4].length) (baseStart_589938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_589938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_589938 prefixEnd_589938 := by exact prefixLift 589938
  have htrace : WordTrace (prefixWord ++ tailWord_589938) baseStart_589938 baseEnd_589938 := by
    simpa [prefixWord, tailWord_589938, baseEnd_589938] using wordTrace_append hprefix tailTrace_589938
  have hstable : (prefixWord ++ tailWord_589938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589938).length < 2 ^ (prefixWord ++ tailWord_589938).sum := by decide
  have hdescent : baseEnd_589938 < baseStart_589938 := by decide
  rcases family_descends (prefixWord ++ tailWord_589938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589968 : List Nat := [2, 1, 1, 1, 1, 1, 6, 4, 2, 3]
def baseStart_589968 : Nat := 118140960795 + 589968 * 2 ^ 59
def prefixEnd_589968 : Nat := 4983230072969 + 3 ^ 40 * 589968 * 2
def baseEnd_589968 : Nat := 201958103181235320791195

theorem tailTrace_589968 : CollatzResearch.WordTrace tailWord_589968 prefixEnd_589968 201958103181235320791195 := by
  unfold tailWord_589968
  simp only [CollatzResearch.WordTrace]
  refine ⟨10758950363327084678857279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14345267151102779571809705 10758950363327084678857279)
  ·
    refine ⟨16138425544990627018285919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10758950363327084678857279 16138425544990627018285919)
    ·
      refine ⟨24207638317485940527428879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16138425544990627018285919 24207638317485940527428879)
      ·
        refine ⟨36311457476228910791143319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24207638317485940527428879 36311457476228910791143319)
        ·
          refine ⟨54467186214343366186714979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36311457476228910791143319 54467186214343366186714979)
          ·
            refine ⟨81700779321515049280072469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54467186214343366186714979 81700779321515049280072469)
            ·
              refine ⟨3829724030696017935003397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 81700779321515049280072469 3829724030696017935003397)
              ·
                refine ⟨718073255755503362813137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3829724030696017935003397 718073255755503362813137)
                ·
                  refine ⟨538554941816627522109853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 718073255755503362813137 538554941816627522109853)
                  ·
                    refine ⟨201958103181235320791195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 538554941816627522109853 201958103181235320791195)
                    ·
                      rfl

theorem cell22_589968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 4, 2, 3].length) (baseStart_589968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_589968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_589968 prefixEnd_589968 := by exact prefixLift 589968
  have htrace : WordTrace (prefixWord ++ tailWord_589968) baseStart_589968 baseEnd_589968 := by
    simpa [prefixWord, tailWord_589968, baseEnd_589968] using wordTrace_append hprefix tailTrace_589968
  have hstable : (prefixWord ++ tailWord_589968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589968).length < 2 ^ (prefixWord ++ tailWord_589968).sum := by decide
  have hdescent : baseEnd_589968 < baseStart_589968 := by decide
  rcases family_descends (prefixWord ++ tailWord_589968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589981 : List Nat := [1, 4, 2, 1, 1, 3, 1, 9]
def baseStart_589981 : Nat := 118140960795 + 589981 * 2 ^ 59
def prefixEnd_589981 : Nat := 4983230072969 + 3 ^ 40 * 589981 * 2
def baseEnd_589981 : Nat := 22440283705211957801795

theorem tailTrace_589981 : CollatzResearch.WordTrace tailWord_589981 prefixEnd_589981 22440283705211957801795 := by
  unfold tailWord_589981
  simp only [CollatzResearch.WordTrace]
  refine ⟨21518374875607072577937797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14345583250404715051958531 21518374875607072577937797)
  ·
    refine ⟨4034695289176326108363337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21518374875607072577937797 4034695289176326108363337)
    ·
      refine ⟨3026021466882244581272503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4034695289176326108363337 3026021466882244581272503)
      ·
        refine ⟨4539032200323366871908755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3026021466882244581272503 4539032200323366871908755)
        ·
          refine ⟨6808548300485050307863133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4539032200323366871908755 6808548300485050307863133)
          ·
            refine ⟨2553205612681893865448675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6808548300485050307863133 2553205612681893865448675)
            ·
              refine ⟨3829808419022840798173013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2553205612681893865448675 3829808419022840798173013)
              ·
                refine ⟨22440283705211957801795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3829808419022840798173013 22440283705211957801795)
                ·
                  rfl

theorem cell22_589981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 9].length) (baseStart_589981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_589981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_589981 prefixEnd_589981 := by exact prefixLift 589981
  have htrace : WordTrace (prefixWord ++ tailWord_589981) baseStart_589981 baseEnd_589981 := by
    simpa [prefixWord, tailWord_589981, baseEnd_589981] using wordTrace_append hprefix tailTrace_589981
  have hstable : (prefixWord ++ tailWord_589981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589981).length < 2 ^ (prefixWord ++ tailWord_589981).sum := by decide
  have hdescent : baseEnd_589981 < baseStart_589981 := by decide
  rcases family_descends (prefixWord ++ tailWord_589981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589985 : List Nat := [1, 2, 3, 3, 1, 3, 1, 3, 2, 3]
def baseStart_589985 : Nat := 118140960795 + 589985 * 2 ^ 59
def prefixEnd_589985 : Nat := 4983230072969 + 3 ^ 40 * 589985 * 2
def baseEnd_589985 : Nat := 201963922628652943116143

theorem tailTrace_589985 : CollatzResearch.WordTrace tailWord_589985 prefixEnd_589985 201963922628652943116143 := by
  unfold tailWord_589985
  simp only [CollatzResearch.WordTrace]
  refine ⟨21518520767592581261083409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14345680511728387507388939 21518520767592581261083409)
  ·
    refine ⟨16138890575694435945812557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21518520767592581261083409 16138890575694435945812557)
    ·
      refine ⟨6052083965885413479679709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16138890575694435945812557 6052083965885413479679709)
      ·
        refine ⟨2269531487207030054879891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6052083965885413479679709 2269531487207030054879891)
        ·
          refine ⟨3404297230810545082319837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2269531487207030054879891 3404297230810545082319837)
          ·
            refine ⟨1276611461553954405869939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3404297230810545082319837 1276611461553954405869939)
            ·
              refine ⟨1914917192330931608804909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1276611461553954405869939 1914917192330931608804909)
              ·
                refine ⟨718093947124099353301841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1914917192330931608804909 718093947124099353301841)
                ·
                  refine ⟨538570460343074514976381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 718093947124099353301841 538570460343074514976381)
                  ·
                    refine ⟨201963922628652943116143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 538570460343074514976381 201963922628652943116143)
                    ·
                      rfl

theorem cell22_589985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 3, 2, 3].length) (baseStart_589985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_589985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_589985 prefixEnd_589985 := by exact prefixLift 589985
  have htrace : WordTrace (prefixWord ++ tailWord_589985) baseStart_589985 baseEnd_589985 := by
    simpa [prefixWord, tailWord_589985, baseEnd_589985] using wordTrace_append hprefix tailTrace_589985
  have hstable : (prefixWord ++ tailWord_589985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589985).length < 2 ^ (prefixWord ++ tailWord_589985).sum := by decide
  have hdescent : baseEnd_589985 < baseStart_589985 := by decide
  rcases family_descends (prefixWord ++ tailWord_589985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590041 : List Nat := [1, 2, 1, 2, 3, 1, 3, 1, 1, 7]
def baseStart_590041 : Nat := 118140960795 + 590041 * 2 ^ 59
def prefixEnd_590041 : Nat := 4983230072969 + 3 ^ 40 * 590041 * 2
def baseEnd_590041 : Nat := 201983092573087463715971

theorem tailTrace_590041 : CollatzResearch.WordTrace tailWord_590041 prefixEnd_590041 201983092573087463715971 := by
  unfold tailWord_590041
  simp only [CollatzResearch.WordTrace]
  refine ⟨21520563255389702825121977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14347042170259801883414651 21520563255389702825121977)
  ·
    refine ⟨16140422441542277118841483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21520563255389702825121977 16140422441542277118841483)
    ·
      refine ⟨24210633662313415678262225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16140422441542277118841483 24210633662313415678262225)
      ·
        refine ⟨18157975246735061758696669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24210633662313415678262225 18157975246735061758696669)
        ·
          refine ⟨6809240717525648159511251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18157975246735061758696669 6809240717525648159511251)
          ·
            refine ⟨10213861076288472239266877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6809240717525648159511251 10213861076288472239266877)
            ·
              refine ⟨3830197903608177089725079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10213861076288472239266877 3830197903608177089725079)
              ·
                refine ⟨5745296855412265634587619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3830197903608177089725079 5745296855412265634587619)
                ·
                  refine ⟨8617945283118398451881429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5745296855412265634587619 8617945283118398451881429)
                  ·
                    refine ⟨201983092573087463715971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8617945283118398451881429 201983092573087463715971)
                    ·
                      rfl

theorem cell22_590041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 7].length) (baseStart_590041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_590041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_590041 prefixEnd_590041 := by exact prefixLift 590041
  have htrace : WordTrace (prefixWord ++ tailWord_590041) baseStart_590041 baseEnd_590041 := by
    simpa [prefixWord, tailWord_590041, baseEnd_590041] using wordTrace_append hprefix tailTrace_590041
  have hstable : (prefixWord ++ tailWord_590041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590041).length < 2 ^ (prefixWord ++ tailWord_590041).sum := by decide
  have hdescent : baseEnd_590041 < baseStart_590041 := by decide
  rcases family_descends (prefixWord ++ tailWord_590041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590088 : List Nat := [2, 1, 3, 2, 3, 1, 1, 3, 6]
def baseStart_590088 : Nat := 118140960795 + 590088 * 2 ^ 59
def prefixEnd_590088 : Nat := 4983230072969 + 3 ^ 40 * 590088 * 2
def baseEnd_590088 : Nat := 67333060544531669263609

theorem tailTrace_590088 : CollatzResearch.WordTrace tailWord_590088 prefixEnd_590088 67333060544531669263609 := by
  unfold tailWord_590088
  simp only [CollatzResearch.WordTrace]
  refine ⟨10761138743109714926041459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14348184990812953234721945 10761138743109714926041459)
  ·
    refine ⟨16141708114664572389062189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10761138743109714926041459 16141708114664572389062189)
    ·
      refine ⟨6053140542999214645898321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16141708114664572389062189 6053140542999214645898321)
      ·
        refine ⟨4539855407249410984423741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6053140542999214645898321 4539855407249410984423741)
        ·
          refine ⟨1702445777718529119158903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4539855407249410984423741 1702445777718529119158903)
          ·
            refine ⟨2553668666577793678738355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1702445777718529119158903 2553668666577793678738355)
            ·
              refine ⟨3830502999866690518107533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2553668666577793678738355 3830502999866690518107533)
              ·
                refine ⟨1436438624950008944290325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3830502999866690518107533 1436438624950008944290325)
                ·
                  refine ⟨67333060544531669263609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1436438624950008944290325 67333060544531669263609)
                  ·
                    rfl

theorem cell22_590088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 3, 6].length) (baseStart_590088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_590088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_590088 prefixEnd_590088 := by exact prefixLift 590088
  have htrace : WordTrace (prefixWord ++ tailWord_590088) baseStart_590088 baseEnd_590088 := by
    simpa [prefixWord, tailWord_590088, baseEnd_590088] using wordTrace_append hprefix tailTrace_590088
  have hstable : (prefixWord ++ tailWord_590088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590088).length < 2 ^ (prefixWord ++ tailWord_590088).sum := by decide
  have hdescent : baseEnd_590088 < baseStart_590088 := by decide
  rcases family_descends (prefixWord ++ tailWord_590088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590193 : List Nat := [1, 2, 2, 2, 1, 2, 1, 4, 2, 5]
def baseStart_590193 : Nat := 118140960795 + 590193 * 2 ^ 59
def prefixEnd_590193 : Nat := 4983230072969 + 3 ^ 40 * 590193 * 2
def baseEnd_590193 : Nat := 202035125279409733915505

theorem tailTrace_590193 : CollatzResearch.WordTrace tailWord_590193 prefixEnd_590193 202035125279409733915505 := by
  unfold tailWord_590193
  simp only [CollatzResearch.WordTrace]
  refine ⟨21526107150839032784655233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14350738100559355189770155 21526107150839032784655233)
  ·
    refine ⟨16144580363129274588491425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21526107150839032784655233 16144580363129274588491425)
    ·
      refine ⟨12108435272346955941368569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16144580363129274588491425 12108435272346955941368569)
      ·
        refine ⟨9081326454260216956026427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12108435272346955941368569 9081326454260216956026427)
        ·
          refine ⟨13621989681390325434039641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9081326454260216956026427 13621989681390325434039641)
          ·
            refine ⟨10216492261042744075529731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13621989681390325434039641 10216492261042744075529731)
            ·
              refine ⟨15324738391564116113294597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10216492261042744075529731 15324738391564116113294597)
              ·
                refine ⟨2873388448418271771242737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15324738391564116113294597 2873388448418271771242737)
                ·
                  refine ⟨2155041336313703828432053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2873388448418271771242737 2155041336313703828432053)
                  ·
                    refine ⟨202035125279409733915505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2155041336313703828432053 202035125279409733915505)
                    ·
                      rfl

theorem cell22_590193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 4, 2, 5].length) (baseStart_590193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_590193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_590193 prefixEnd_590193 := by exact prefixLift 590193
  have htrace : WordTrace (prefixWord ++ tailWord_590193) baseStart_590193 baseEnd_590193 := by
    simpa [prefixWord, tailWord_590193, baseEnd_590193] using wordTrace_append hprefix tailTrace_590193
  have hstable : (prefixWord ++ tailWord_590193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590193).length < 2 ^ (prefixWord ++ tailWord_590193).sum := by decide
  have hdescent : baseEnd_590193 < baseStart_590193 := by decide
  rcases family_descends (prefixWord ++ tailWord_590193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590242 : List Nat := [3, 3, 1, 2, 1, 1, 3, 3, 1, 4]
def baseStart_590242 : Nat := 118140960795 + 590242 * 2 ^ 59
def prefixEnd_590242 : Nat := 4983230072969 + 3 ^ 40 * 590242 * 2
def baseEnd_590242 : Nat := 202051898980789939440355

theorem tailTrace_590242 : CollatzResearch.WordTrace tailWord_590242 prefixEnd_590242 202051898980789939440355 := by
  unfold tailWord_590242
  simp only [CollatzResearch.WordTrace]
  refine ⟨5381973581915378538297245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14351929551774342768792653 5381973581915378538297245)
  ·
    refine ⟨2018240093218266951861467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5381973581915378538297245 2018240093218266951861467)
    ·
      refine ⟨3027360139827400427792201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2018240093218266951861467 3027360139827400427792201)
      ·
        refine ⟨2270520104870550320844151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3027360139827400427792201 2270520104870550320844151)
        ·
          refine ⟨3405780157305825481266227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2270520104870550320844151 3405780157305825481266227)
          ·
            refine ⟨5108670235958738221899341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3405780157305825481266227 5108670235958738221899341)
            ·
              refine ⟨1915751338484526833212253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5108670235958738221899341 1915751338484526833212253)
              ·
                refine ⟨718406751931697562454595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1915751338484526833212253 718406751931697562454595)
                ·
                  refine ⟨1077610127897546343681893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 718406751931697562454595 1077610127897546343681893)
                  ·
                    refine ⟨202051898980789939440355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1077610127897546343681893 202051898980789939440355)
                    ·
                      rfl

theorem cell22_590242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_590242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_590242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_590242 prefixEnd_590242 := by exact prefixLift 590242
  have htrace : WordTrace (prefixWord ++ tailWord_590242) baseStart_590242 baseEnd_590242 := by
    simpa [prefixWord, tailWord_590242, baseEnd_590242] using wordTrace_append hprefix tailTrace_590242
  have hstable : (prefixWord ++ tailWord_590242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590242).length < 2 ^ (prefixWord ++ tailWord_590242).sum := by decide
  have hdescent : baseEnd_590242 < baseStart_590242 := by decide
  rcases family_descends (prefixWord ++ tailWord_590242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590257 : List Nat := [1, 2, 2, 4, 1, 2, 2, 4, 4]
def baseStart_590257 : Nat := 118140960795 + 590257 * 2 ^ 59
def prefixEnd_590257 : Nat := 4983230072969 + 3 ^ 40 * 590257 * 2
def baseEnd_590257 : Nat := 67352344595778300105103

theorem tailTrace_590257 : CollatzResearch.WordTrace tailWord_590257 prefixEnd_590257 67352344595778300105103 := by
  unfold tailWord_590257
  simp only [CollatzResearch.WordTrace]
  refine ⟨21528441422607171714985025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14352294281738114476656683 21528441422607171714985025)
  ·
    refine ⟨16146331066955378786238769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21528441422607171714985025 16146331066955378786238769)
    ·
      refine ⟨12109748300216534089679077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16146331066955378786238769 12109748300216534089679077)
      ·
        refine ⟨2270577806290600141814827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12109748300216534089679077 2270577806290600141814827)
        ·
          refine ⟨3405866709435900212722241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2270577806290600141814827 3405866709435900212722241)
          ·
            refine ⟨2554400032076925159541681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3405866709435900212722241 2554400032076925159541681)
            ·
              refine ⟨1915800024057693869656261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2554400032076925159541681 1915800024057693869656261)
              ·
                refine ⟨359212504510817600560549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1915800024057693869656261 359212504510817600560549)
                ·
                  refine ⟨67352344595778300105103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 359212504510817600560549 67352344595778300105103)
                  ·
                    rfl

theorem cell22_590257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 4, 4].length) (baseStart_590257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_590257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_590257 prefixEnd_590257 := by exact prefixLift 590257
  have htrace : WordTrace (prefixWord ++ tailWord_590257) baseStart_590257 baseEnd_590257 := by
    simpa [prefixWord, tailWord_590257, baseEnd_590257] using wordTrace_append hprefix tailTrace_590257
  have hstable : (prefixWord ++ tailWord_590257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590257).length < 2 ^ (prefixWord ++ tailWord_590257).sum := by decide
  have hdescent : baseEnd_590257 < baseStart_590257 := by decide
  rcases family_descends (prefixWord ++ tailWord_590257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590270 : List Nat := [4, 2, 1, 1, 1, 1, 3, 2, 1, 6]
def baseStart_590270 : Nat := 118140960795 + 590270 * 2 ^ 59
def prefixEnd_590270 : Nat := 4983230072969 + 3 ^ 40 * 590270 * 2
def baseEnd_590270 : Nat := 202061483953007199740269

theorem tailTrace_590270 : CollatzResearch.WordTrace tailWord_590270 prefixEnd_590270 202061483953007199740269 := by
  unfold tailWord_590270
  simp only [CollatzResearch.WordTrace]
  refine ⟨2691114446445009366901033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14352610381040049956805509 2691114446445009366901033)
  ·
    refine ⟨2018335834833757025175775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2691114446445009366901033 2018335834833757025175775)
    ·
      refine ⟨3027503752250635537763663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2018335834833757025175775 3027503752250635537763663)
      ·
        refine ⟨4541255628375953306645495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3027503752250635537763663 4541255628375953306645495)
        ·
          refine ⟨6811883442563929959968243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4541255628375953306645495 6811883442563929959968243)
          ·
            refine ⟨10217825163845894939952365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6811883442563929959968243 10217825163845894939952365)
            ·
              refine ⟨3831684436442210602482137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10217825163845894939952365 3831684436442210602482137)
              ·
                refine ⟨2873763327331657951861603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3831684436442210602482137 2873763327331657951861603)
                ·
                  refine ⟨4310644990997486927792405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2873763327331657951861603 4310644990997486927792405)
                  ·
                    refine ⟨202061483953007199740269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4310644990997486927792405 202061483953007199740269)
                    ·
                      rfl

theorem cell22_590270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_590270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_590270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_590270 prefixEnd_590270 := by exact prefixLift 590270
  have htrace : WordTrace (prefixWord ++ tailWord_590270) baseStart_590270 baseEnd_590270 := by
    simpa [prefixWord, tailWord_590270, baseEnd_590270] using wordTrace_append hprefix tailTrace_590270
  have hstable : (prefixWord ++ tailWord_590270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590270).length < 2 ^ (prefixWord ++ tailWord_590270).sum := by decide
  have hdescent : baseEnd_590270 < baseStart_590270 := by decide
  rcases family_descends (prefixWord ++ tailWord_590270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590283 : List Nat := [1, 1, 1, 1, 3, 3, 1, 1, 1, 9]
def baseStart_590283 : Nat := 118140960795 + 590283 * 2 ^ 59
def prefixEnd_590283 : Nat := 4983230072969 + 3 ^ 40 * 590283 * 2
def baseEnd_590283 : Nat := 202065934118679499165229

theorem tailTrace_590283 : CollatzResearch.WordTrace tailWord_590283 prefixEnd_590283 202065934118679499165229 := by
  unfold tailWord_590283
  simp only [CollatzResearch.WordTrace]
  refine ⟨21529389720512978155431503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14352926480341985436954335 21529389720512978155431503)
  ·
    refine ⟨32294084580769467233147255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21529389720512978155431503 32294084580769467233147255)
    ·
      refine ⟨48441126871154200849720883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32294084580769467233147255 48441126871154200849720883)
      ·
        refine ⟨72661690306731301274581325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48441126871154200849720883 72661690306731301274581325)
        ·
          refine ⟨27248133865024237977967997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72661690306731301274581325 27248133865024237977967997)
          ·
            refine ⟨10218050199384089241737999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27248133865024237977967997 10218050199384089241737999)
            ·
              refine ⟨15327075299076133862606999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10218050199384089241737999 15327075299076133862606999)
              ·
                refine ⟨22990612948614200793910499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15327075299076133862606999 22990612948614200793910499)
                ·
                  refine ⟨34485919422921301190865749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22990612948614200793910499 34485919422921301190865749)
                  ·
                    refine ⟨202065934118679499165229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 34485919422921301190865749 202065934118679499165229)
                    ·
                      rfl

theorem cell22_590283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 9].length) (baseStart_590283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_590283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_590283 prefixEnd_590283 := by exact prefixLift 590283
  have htrace : WordTrace (prefixWord ++ tailWord_590283) baseStart_590283 baseEnd_590283 := by
    simpa [prefixWord, tailWord_590283, baseEnd_590283] using wordTrace_append hprefix tailTrace_590283
  have hstable : (prefixWord ++ tailWord_590283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590283).length < 2 ^ (prefixWord ++ tailWord_590283).sum := by decide
  have hdescent : baseEnd_590283 < baseStart_590283 := by decide
  rcases family_descends (prefixWord ++ tailWord_590283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590407 : List Nat := [1, 1, 4, 1, 4, 1, 2, 2, 1, 5]
def baseStart_590407 : Nat := 118140960795 + 590407 * 2 ^ 59
def prefixEnd_590407 : Nat := 4983230072969 + 3 ^ 40 * 590407 * 2
def baseEnd_590407 : Nat := 202108381852784509064849

theorem tailTrace_590407 : CollatzResearch.WordTrace tailWord_590407 prefixEnd_590407 202108381852784509064849 := by
  unfold tailWord_590407
  simp only [CollatzResearch.WordTrace]
  refine ⟨21533912372063747332945475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14355941581375831555296983 21533912372063747332945475)
  ·
    refine ⟨32300868558095620999418213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21533912372063747332945475 32300868558095620999418213)
    ·
      refine ⟨6056412854642928937390915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32300868558095620999418213 6056412854642928937390915)
      ·
        refine ⟨9084619281964393406086373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6056412854642928937390915 9084619281964393406086373)
        ·
          refine ⟨1703366115368323763641195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9084619281964393406086373 1703366115368323763641195)
          ·
            refine ⟨2555049173052485645461793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1703366115368323763641195 2555049173052485645461793)
            ·
              refine ⟨1916286879789364234096345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2555049173052485645461793 1916286879789364234096345)
              ·
                refine ⟨1437215159842023175572259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1916286879789364234096345 1437215159842023175572259)
                ·
                  refine ⟨2155822739763034763358389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1437215159842023175572259 2155822739763034763358389)
                  ·
                    refine ⟨202108381852784509064849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2155822739763034763358389 202108381852784509064849)
                    ·
                      rfl

theorem cell22_590407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 2, 1, 5].length) (baseStart_590407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_590407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_590407 prefixEnd_590407 := by exact prefixLift 590407
  have htrace : WordTrace (prefixWord ++ tailWord_590407) baseStart_590407 baseEnd_590407 := by
    simpa [prefixWord, tailWord_590407, baseEnd_590407] using wordTrace_append hprefix tailTrace_590407
  have hstable : (prefixWord ++ tailWord_590407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590407).length < 2 ^ (prefixWord ++ tailWord_590407).sum := by decide
  have hdescent : baseEnd_590407 < baseStart_590407 := by decide
  rcases family_descends (prefixWord ++ tailWord_590407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590424 : List Nat := [2, 1, 2, 2, 1, 2, 5, 2, 2, 3]
def baseStart_590424 : Nat := 118140960795 + 590424 * 2 ^ 59
def prefixEnd_590424 : Nat := 4983230072969 + 3 ^ 40 * 590424 * 2
def baseEnd_590424 : Nat := 202114201300202131389797

theorem tailTrace_590424 : CollatzResearch.WordTrace tailWord_590424 prefixEnd_590424 202114201300202131389797 := by
  unfold tailWord_590424
  simp only [CollatzResearch.WordTrace]
  refine ⟨10767266206501079618157163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14356354942001439490876217 10767266206501079618157163)
  ·
    refine ⟨16150899309751619427235745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10767266206501079618157163 16150899309751619427235745)
    ·
      refine ⟨12113174482313714570426809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16150899309751619427235745 12113174482313714570426809)
      ·
        refine ⟨9084880861735285927820107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12113174482313714570426809 9084880861735285927820107)
        ·
          refine ⟨13627321292602928891730161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9084880861735285927820107 13627321292602928891730161)
          ·
            refine ⟨10220490969452196668797621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13627321292602928891730161 10220490969452196668797621)
            ·
              refine ⟨958171028386143437699777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10220490969452196668797621 958171028386143437699777)
              ·
                refine ⟨718628271289607578274833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 958171028386143437699777 718628271289607578274833)
                ·
                  refine ⟨538971203467205683706125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 718628271289607578274833 538971203467205683706125)
                  ·
                    refine ⟨202114201300202131389797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 538971203467205683706125 202114201300202131389797)
                    ·
                      rfl

theorem cell22_590424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 2, 2, 3].length) (baseStart_590424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_590424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_590424 prefixEnd_590424 := by exact prefixLift 590424
  have htrace : WordTrace (prefixWord ++ tailWord_590424) baseStart_590424 baseEnd_590424 := by
    simpa [prefixWord, tailWord_590424, baseEnd_590424] using wordTrace_append hprefix tailTrace_590424
  have hstable : (prefixWord ++ tailWord_590424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590424).length < 2 ^ (prefixWord ++ tailWord_590424).sum := by decide
  have hdescent : baseEnd_590424 < baseStart_590424 := by decide
  rcases family_descends (prefixWord ++ tailWord_590424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590454 : List Nat := [5, 1, 1, 2, 3, 1, 1, 8]
def baseStart_590454 : Nat := 118140960795 + 590454 * 2 ^ 59
def prefixEnd_590454 : Nat := 4983230072969 + 3 ^ 40 * 590454 * 2
def baseEnd_590454 : Nat := 22458274545921339237745

theorem tailTrace_590454 : CollatzResearch.WordTrace tailWord_590454 prefixEnd_590454 22458274545921339237745 := by
  unfold tailWord_590454
  simp only [CollatzResearch.WordTrace]
  refine ⟨1345976662680842147494151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14357084401928982906604277 1345976662680842147494151)
  ·
    refine ⟨2018964994021263221241227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1345976662680842147494151 2018964994021263221241227)
    ·
      refine ⟨3028447491031894831861841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2018964994021263221241227 3028447491031894831861841)
      ·
        refine ⟨2271335618273921123896381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3028447491031894831861841 2271335618273921123896381)
        ·
          refine ⟨851750856852720421461143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2271335618273921123896381 851750856852720421461143)
          ·
            refine ⟨1277626285279080632191715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 851750856852720421461143 1277626285279080632191715)
            ·
              refine ⟨1916439427918620948287573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1277626285279080632191715 1916439427918620948287573)
              ·
                refine ⟨22458274545921339237745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1916439427918620948287573 22458274545921339237745)
                ·
                  rfl

theorem cell22_590454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 8].length) (baseStart_590454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_590454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_590454 prefixEnd_590454 := by exact prefixLift 590454
  have htrace : WordTrace (prefixWord ++ tailWord_590454) baseStart_590454 baseEnd_590454 := by
    simpa [prefixWord, tailWord_590454, baseEnd_590454] using wordTrace_append hprefix tailTrace_590454
  have hstable : (prefixWord ++ tailWord_590454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590454).length < 2 ^ (prefixWord ++ tailWord_590454).sum := by decide
  have hdescent : baseEnd_590454 < baseStart_590454 := by decide
  rcases family_descends (prefixWord ++ tailWord_590454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590559 : List Nat := [1, 1, 2, 3, 2, 4, 2, 1, 1, 5]
def baseStart_590559 : Nat := 118140960795 + 590559 * 2 ^ 59
def prefixEnd_590559 : Nat := 4983230072969 + 3 ^ 40 * 590559 * 2
def baseEnd_590559 : Nat := 202160414559106779264383

theorem tailTrace_590559 : CollatzResearch.WordTrace tailWord_590559 prefixEnd_590559 202160414559106779264383 := by
  unfold tailWord_590559
  simp only [CollatzResearch.WordTrace]
  refine ⟨21539456267513077292478731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14359637511675384861652487 21539456267513077292478731)
  ·
    refine ⟨32309184401269615938718097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21539456267513077292478731 32309184401269615938718097)
    ·
      refine ⟨24231888300952211954038573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32309184401269615938718097 24231888300952211954038573)
      ·
        refine ⟨9086958112857079482764465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24231888300952211954038573 9086958112857079482764465)
        ·
          refine ⟨6815218584642809612073349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9086958112857079482764465 6815218584642809612073349)
          ·
            refine ⟨1277853484620526802263753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6815218584642809612073349 1277853484620526802263753)
            ·
              refine ⟨958390113465395101697815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1277853484620526802263753 958390113465395101697815)
              ·
                refine ⟨1437585170198092652546723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 958390113465395101697815 1437585170198092652546723)
                ·
                  refine ⟨2156377755297138978820085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1437585170198092652546723 2156377755297138978820085)
                  ·
                    refine ⟨202160414559106779264383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2156377755297138978820085 202160414559106779264383)
                    ·
                      rfl

theorem cell22_590559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 1, 1, 5].length) (baseStart_590559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_590559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_590559 prefixEnd_590559 := by exact prefixLift 590559
  have htrace : WordTrace (prefixWord ++ tailWord_590559) baseStart_590559 baseEnd_590559 := by
    simpa [prefixWord, tailWord_590559, baseEnd_590559] using wordTrace_append hprefix tailTrace_590559
  have hstable : (prefixWord ++ tailWord_590559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590559).length < 2 ^ (prefixWord ++ tailWord_590559).sum := by decide
  have hdescent : baseEnd_590559 < baseStart_590559 := by decide
  rcases family_descends (prefixWord ++ tailWord_590559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590574 : List Nat := [4, 1, 2, 1, 1, 4, 1, 1, 1, 6]
def baseStart_590574 : Nat := 118140960795 + 590574 * 2 ^ 59
def prefixEnd_590574 : Nat := 4983230072969 + 3 ^ 40 * 590574 * 2
def baseEnd_590574 : Nat := 202165549365651740139337

theorem tailTrace_590574 : CollatzResearch.WordTrace tailWord_590574 prefixEnd_590574 202165549365651740139337 := by
  unfold tailWord_590574
  simp only [CollatzResearch.WordTrace]
  refine ⟨2692500420307341856784347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14360002241639156569516517 2692500420307341856784347)
  ·
    refine ⟨4038750630461012785176521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2692500420307341856784347 4038750630461012785176521)
    ·
      refine ⟨3029062972845759588882391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4038750630461012785176521 3029062972845759588882391)
      ·
        refine ⟨4543594459268639383323587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3029062972845759588882391 4543594459268639383323587)
        ·
          refine ⟨6815391688902959074985381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4543594459268639383323587 6815391688902959074985381)
          ·
            refine ⟨1277885941669304826559759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6815391688902959074985381 1277885941669304826559759)
            ·
              refine ⟨1916828912503957239839639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1277885941669304826559759 1916828912503957239839639)
              ·
                refine ⟨2875243368755935859759459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1916828912503957239839639 2875243368755935859759459)
                ·
                  refine ⟨4312865053133903789639189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2875243368755935859759459 4312865053133903789639189)
                  ·
                    refine ⟨202165549365651740139337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4312865053133903789639189 202165549365651740139337)
                    ·
                      rfl

theorem cell22_590574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_590574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_590574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_590574 prefixEnd_590574 := by exact prefixLift 590574
  have htrace : WordTrace (prefixWord ++ tailWord_590574) baseStart_590574 baseEnd_590574 := by
    simpa [prefixWord, tailWord_590574, baseEnd_590574] using wordTrace_append hprefix tailTrace_590574
  have hstable : (prefixWord ++ tailWord_590574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590574).length < 2 ^ (prefixWord ++ tailWord_590574).sum := by decide
  have hdescent : baseEnd_590574 < baseStart_590574 := by decide
  rcases family_descends (prefixWord ++ tailWord_590574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590580 : List Nat := [2, 6, 1, 1, 2, 1, 1, 3, 1, 4]
def baseStart_590580 : Nat := 118140960795 + 590580 * 2 ^ 59
def prefixEnd_590580 : Nat := 4983230072969 + 3 ^ 40 * 590580 * 2
def baseEnd_590580 : Nat := 202167603288269724489319

theorem tailTrace_590580 : CollatzResearch.WordTrace tailWord_590580 prefixEnd_590580 202167603288269724489319 := by
  unfold tailWord_590580
  simp only [CollatzResearch.WordTrace]
  refine ⟨10770111100218498939496597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14360148133624665252662129 10770111100218498939496597)
  ·
    refine ⟨504848957822742137788903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 10770111100218498939496597 504848957822742137788903)
    ·
      refine ⟨757273436734113206683355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 504848957822742137788903 757273436734113206683355)
      ·
        refine ⟨1135910155101169810025033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 757273436734113206683355 1135910155101169810025033)
        ·
          refine ⟨851932616325877357518775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1135910155101169810025033 851932616325877357518775)
          ·
            refine ⟨1277898924488816036278163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 851932616325877357518775 1277898924488816036278163)
            ·
              refine ⟨1916848386733224054417245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1277898924488816036278163 1916848386733224054417245)
              ·
                refine ⟨718818145024959020406467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1916848386733224054417245 718818145024959020406467)
                ·
                  refine ⟨1078227217537438530609701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 718818145024959020406467 1078227217537438530609701)
                  ·
                    refine ⟨202167603288269724489319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1078227217537438530609701 202167603288269724489319)
                    ·
                      rfl

theorem cell22_590580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_590580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_590580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_590580 prefixEnd_590580 := by exact prefixLift 590580
  have htrace : WordTrace (prefixWord ++ tailWord_590580) baseStart_590580 baseEnd_590580 := by
    simpa [prefixWord, tailWord_590580, baseEnd_590580] using wordTrace_append hprefix tailTrace_590580
  have hstable : (prefixWord ++ tailWord_590580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590580).length < 2 ^ (prefixWord ++ tailWord_590580).sum := by decide
  have hdescent : baseEnd_590580 < baseStart_590580 := by decide
  rcases family_descends (prefixWord ++ tailWord_590580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590610 : List Nat := [3, 2, 4, 1, 3, 1, 1, 1, 1, 5]
def baseStart_590610 : Nat := 118140960795 + 590610 * 2 ^ 59
def prefixEnd_590610 : Nat := 4983230072969 + 3 ^ 40 * 590610 * 2
def baseEnd_590610 : Nat := 202177872901359646239227

theorem tailTrace_590610 : CollatzResearch.WordTrace tailWord_590610 prefixEnd_590610 202177872901359646239227 := by
  unfold tailWord_590610
  simp only [CollatzResearch.WordTrace]
  refine ⟨5385329097582078250646321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14360877593552208668390189 5385329097582078250646321)
  ·
    refine ⟨4038996823186558687984741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5385329097582078250646321 4038996823186558687984741)
    ·
      refine ⟨757311904347479753997139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4038996823186558687984741 757311904347479753997139)
      ·
        refine ⟨1135967856521219630995709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 757311904347479753997139 1135967856521219630995709)
        ·
          refine ⟨425987946195457361623391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1135967856521219630995709 425987946195457361623391)
          ·
            refine ⟨638981919293186042435087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 425987946195457361623391 638981919293186042435087)
            ·
              refine ⟨958472878939779063652631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 638981919293186042435087 958472878939779063652631)
              ·
                refine ⟨1437709318409668595478947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 958472878939779063652631 1437709318409668595478947)
                ·
                  refine ⟨2156563977614502893218421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1437709318409668595478947 2156563977614502893218421)
                  ·
                    refine ⟨202177872901359646239227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2156563977614502893218421 202177872901359646239227)
                    ·
                      rfl

theorem cell22_590610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_590610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_590610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_590610 prefixEnd_590610 := by exact prefixLift 590610
  have htrace : WordTrace (prefixWord ++ tailWord_590610) baseStart_590610 baseEnd_590610 := by
    simpa [prefixWord, tailWord_590610, baseEnd_590610] using wordTrace_append hprefix tailTrace_590610
  have hstable : (prefixWord ++ tailWord_590610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590610).length < 2 ^ (prefixWord ++ tailWord_590610).sum := by decide
  have hdescent : baseEnd_590610 < baseStart_590610 := by decide
  rcases family_descends (prefixWord ++ tailWord_590610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590655 : List Nat := [1, 1, 2, 2, 5, 2, 3, 2, 1, 3]
def baseStart_590655 : Nat := 118140960795 + 590655 * 2 ^ 59
def prefixEnd_590655 : Nat := 4983230072969 + 3 ^ 40 * 590655 * 2
def baseEnd_590655 : Nat := 202193277320994528864089

theorem tailTrace_590655 : CollatzResearch.WordTrace tailWord_590655 prefixEnd_590655 202193277320994528864089 := by
  unfold tailWord_590655
  simp only [CollatzResearch.WordTrace]
  refine ⟨21542957675165285687973419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14361971783443523791982279 21542957675165285687973419)
  ·
    refine ⟨32314436512747928531960129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21542957675165285687973419 32314436512747928531960129)
    ·
      refine ⟨24235827384560946398970097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32314436512747928531960129 24235827384560946398970097)
      ·
        refine ⟨18176870538420709799227573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24235827384560946398970097 18176870538420709799227573)
        ·
          refine ⟨1704081612976941543677585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18176870538420709799227573 1704081612976941543677585)
          ·
            refine ⟨1278061209732706157758189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1704081612976941543677585 1278061209732706157758189)
            ·
              refine ⟨479272953649764809159321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1278061209732706157758189 479272953649764809159321)
              ·
                refine ⟨359454715237323606869491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 479272953649764809159321 359454715237323606869491)
                ·
                  refine ⟨539182072855985410304237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 359454715237323606869491 539182072855985410304237)
                  ·
                    refine ⟨202193277320994528864089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 539182072855985410304237 202193277320994528864089)
                    ·
                      rfl

theorem cell22_590655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 3, 2, 1, 3].length) (baseStart_590655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_590655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_590655 prefixEnd_590655 := by exact prefixLift 590655
  have htrace : WordTrace (prefixWord ++ tailWord_590655) baseStart_590655 baseEnd_590655 := by
    simpa [prefixWord, tailWord_590655, baseEnd_590655] using wordTrace_append hprefix tailTrace_590655
  have hstable : (prefixWord ++ tailWord_590655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590655).length < 2 ^ (prefixWord ++ tailWord_590655).sum := by decide
  have hdescent : baseEnd_590655 < baseStart_590655 := by decide
  rcases family_descends (prefixWord ++ tailWord_590655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590664 : List Nat := [2, 1, 3, 1, 1, 3, 2, 2, 3, 4]
def baseStart_590664 : Nat := 118140960795 + 590664 * 2 ^ 59
def prefixEnd_590664 : Nat := 4983230072969 + 3 ^ 40 * 590664 * 2
def baseEnd_590664 : Nat := 202196358204921505389061

theorem tailTrace_590664 : CollatzResearch.WordTrace tailWord_590664 prefixEnd_590664 202196358204921505389061 := by
  unfold tailWord_590664
  simp only [CollatzResearch.WordTrace]
  refine ⟨10771642966066340112525523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14362190621421786816700697 10771642966066340112525523)
  ·
    refine ⟨16157464449099510168788285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10771642966066340112525523 16157464449099510168788285)
    ·
      refine ⟨6059049168412316313295607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16157464449099510168788285 6059049168412316313295607)
      ·
        refine ⟨9088573752618474469943411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6059049168412316313295607 9088573752618474469943411)
        ·
          refine ⟨13632860628927711704915117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9088573752618474469943411 13632860628927711704915117)
          ·
            refine ⟨5112322735847891889343169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13632860628927711704915117 5112322735847891889343169)
            ·
              refine ⟨3834242051885918917007377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5112322735847891889343169 3834242051885918917007377)
              ·
                refine ⟨2875681538914439187755533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3834242051885918917007377 2875681538914439187755533)
                ·
                  refine ⟨1078380577092914695408325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2875681538914439187755533 1078380577092914695408325)
                  ·
                    refine ⟨202196358204921505389061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1078380577092914695408325 202196358204921505389061)
                    ·
                      rfl

theorem cell22_590664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 2, 3, 4].length) (baseStart_590664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_590664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_590664 prefixEnd_590664 := by exact prefixLift 590664
  have htrace : WordTrace (prefixWord ++ tailWord_590664) baseStart_590664 baseEnd_590664 := by
    simpa [prefixWord, tailWord_590664, baseEnd_590664] using wordTrace_append hprefix tailTrace_590664
  have hstable : (prefixWord ++ tailWord_590664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590664).length < 2 ^ (prefixWord ++ tailWord_590664).sum := by decide
  have hdescent : baseEnd_590664 < baseStart_590664 := by decide
  rcases family_descends (prefixWord ++ tailWord_590664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590668 : List Nat := [2, 2, 1, 3, 3, 3, 2, 1, 5]
def baseStart_590668 : Nat := 118140960795 + 590668 * 2 ^ 59
def prefixEnd_590668 : Nat := 4983230072969 + 3 ^ 40 * 590668 * 2
def baseEnd_590668 : Nat := 67399242495555609429683

theorem tailTrace_590668 : CollatzResearch.WordTrace tailWord_590668 prefixEnd_590668 67399242495555609429683 := by
  unfold tailWord_590668
  simp only [CollatzResearch.WordTrace]
  refine ⟨10771715912059094454098329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14362287882745459272131105 10771715912059094454098329)
  ·
    refine ⟨8078786934044320840573747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10771715912059094454098329 8078786934044320840573747)
    ·
      refine ⟨12118180401066481260860621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8078786934044320840573747 12118180401066481260860621)
      ·
        refine ⟨4544317650399930472822733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12118180401066481260860621 4544317650399930472822733)
        ·
          refine ⟨1704119118899973927308525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4544317650399930472822733 1704119118899973927308525)
          ·
            refine ⟨639044669587490222740697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1704119118899973927308525 639044669587490222740697)
            ·
              refine ⟨479283502190617667055523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 639044669587490222740697 479283502190617667055523)
              ·
                refine ⟨718925253285926500583285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 479283502190617667055523 718925253285926500583285)
                ·
                  refine ⟨67399242495555609429683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 718925253285926500583285 67399242495555609429683)
                  ·
                    rfl

theorem cell22_590668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 2, 1, 5].length) (baseStart_590668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_590668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_590668 prefixEnd_590668 := by exact prefixLift 590668
  have htrace : WordTrace (prefixWord ++ tailWord_590668) baseStart_590668 baseEnd_590668 := by
    simpa [prefixWord, tailWord_590668, baseEnd_590668] using wordTrace_append hprefix tailTrace_590668
  have hstable : (prefixWord ++ tailWord_590668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590668).length < 2 ^ (prefixWord ++ tailWord_590668).sum := by decide
  have hdescent : baseEnd_590668 < baseStart_590668 := by decide
  rcases family_descends (prefixWord ++ tailWord_590668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590681 : List Nat := [1, 2, 1, 2, 2, 4, 3, 2, 1, 4]
def baseStart_590681 : Nat := 118140960795 + 590681 * 2 ^ 59
def prefixEnd_590681 : Nat := 4983230072969 + 3 ^ 40 * 590681 * 2
def baseEnd_590681 : Nat := 202202177652339127714009

theorem tailTrace_590681 : CollatzResearch.WordTrace tailWord_590681 prefixEnd_590681 202202177652339127714009 := by
  unfold tailWord_590681
  simp only [CollatzResearch.WordTrace]
  refine ⟨21543905973071092128419897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14362603982047394752279931 21543905973071092128419897)
  ·
    refine ⟨16157929479803319096314923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21543905973071092128419897 16157929479803319096314923)
    ·
      refine ⟨24236894219704978644472385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16157929479803319096314923 24236894219704978644472385)
      ·
        refine ⟨18177670664778733983354289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24236894219704978644472385 18177670664778733983354289)
        ·
          refine ⟨13633252998584050487515717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18177670664778733983354289 13633252998584050487515717)
          ·
            refine ⟨2556234937234509466409197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13633252998584050487515717 2556234937234509466409197)
            ·
              refine ⟨958588101462941049903449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2556234937234509466409197 958588101462941049903449)
              ·
                refine ⟨718941076097205787427587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 958588101462941049903449 718941076097205787427587)
                ·
                  refine ⟨1078411614145808681141381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 718941076097205787427587 1078411614145808681141381)
                  ·
                    refine ⟨202202177652339127714009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1078411614145808681141381 202202177652339127714009)
                    ·
                      rfl

theorem cell22_590681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 2, 1, 4].length) (baseStart_590681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_590681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_590681 prefixEnd_590681 := by exact prefixLift 590681
  have htrace : WordTrace (prefixWord ++ tailWord_590681) baseStart_590681 baseEnd_590681 := by
    simpa [prefixWord, tailWord_590681, baseEnd_590681] using wordTrace_append hprefix tailTrace_590681
  have hstable : (prefixWord ++ tailWord_590681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590681).length < 2 ^ (prefixWord ++ tailWord_590681).sum := by decide
  have hdescent : baseEnd_590681 < baseStart_590681 := by decide
  rcases family_descends (prefixWord ++ tailWord_590681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590713 : List Nat := [1, 2, 1, 3, 2, 3, 4, 2, 4]
def baseStart_590713 : Nat := 118140960795 + 590713 * 2 ^ 59
def prefixEnd_590713 : Nat := 4983230072969 + 3 ^ 40 * 590713 * 2
def baseEnd_590713 : Nat := 67404377302100570304637

theorem tailTrace_590713 : CollatzResearch.WordTrace tailWord_590713 prefixEnd_590713 67404377302100570304637 := by
  unfold tailWord_590713
  simp only [CollatzResearch.WordTrace]
  refine ⟨21545073108955161593584793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14363382072636774395723195 21545073108955161593584793)
  ·
    refine ⟨16158804831716371195188595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21545073108955161593584793 16158804831716371195188595)
    ·
      refine ⟨24238207247574556792782893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16158804831716371195188595 24238207247574556792782893)
      ·
        refine ⟨9089327717840458797293585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24238207247574556792782893 9089327717840458797293585)
        ·
          refine ⟨6816995788380344097970189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9089327717840458797293585 6816995788380344097970189)
          ·
            refine ⟨2556373420642629036738821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6816995788380344097970189 2556373420642629036738821)
            ·
              refine ⟨479320016370492944388529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2556373420642629036738821 479320016370492944388529)
              ·
                refine ⟨359490012277869708291397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 479320016370492944388529 359490012277869708291397)
                ·
                  refine ⟨67404377302100570304637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 359490012277869708291397 67404377302100570304637)
                  ·
                    rfl

theorem cell22_590713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 4, 2, 4].length) (baseStart_590713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_590713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_590713 prefixEnd_590713 := by exact prefixLift 590713
  have htrace : WordTrace (prefixWord ++ tailWord_590713) baseStart_590713 baseEnd_590713 := by
    simpa [prefixWord, tailWord_590713, baseEnd_590713] using wordTrace_append hprefix tailTrace_590713
  have hstable : (prefixWord ++ tailWord_590713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590713).length < 2 ^ (prefixWord ++ tailWord_590713).sum := by decide
  have hdescent : baseEnd_590713 < baseStart_590713 := by decide
  rcases family_descends (prefixWord ++ tailWord_590713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590728 : List Nat := [2, 1, 3, 3, 2, 1, 2, 3, 2, 3]
def baseStart_590728 : Nat := 118140960795 + 590728 * 2 ^ 59
def prefixEnd_590728 : Nat := 4983230072969 + 3 ^ 40 * 590728 * 2
def baseEnd_590728 : Nat := 202218266712846671788865

theorem tailTrace_590728 : CollatzResearch.WordTrace tailWord_590728 prefixEnd_590728 202218266712846671788865 := by
  unfold tailWord_590728
  simp only [CollatzResearch.WordTrace]
  refine ⟨10772810101950409577690419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14363746802600546103587225 10772810101950409577690419)
  ·
    refine ⟨16159215152925614366535629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10772810101950409577690419 16159215152925614366535629)
    ·
      refine ⟨6059705682347105387450861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16159215152925614366535629 6059705682347105387450861)
      ·
        refine ⟨2272389630880164520294073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6059705682347105387450861 2272389630880164520294073)
        ·
          refine ⟨1704292223160123390220555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2272389630880164520294073 1704292223160123390220555)
          ·
            refine ⟨2556438334740185085330833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1704292223160123390220555 2556438334740185085330833)
            ·
              refine ⟨1917328751055138813998125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2556438334740185085330833 1917328751055138813998125)
              ·
                refine ⟨718998281645677055249297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1917328751055138813998125 718998281645677055249297)
                ·
                  refine ⟨539248711234257791436973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 718998281645677055249297 539248711234257791436973)
                  ·
                    refine ⟨202218266712846671788865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 539248711234257791436973 202218266712846671788865)
                    ·
                      rfl

theorem cell22_590728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 3, 2, 3].length) (baseStart_590728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_590728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_590728 prefixEnd_590728 := by exact prefixLift 590728
  have htrace : WordTrace (prefixWord ++ tailWord_590728) baseStart_590728 baseEnd_590728 := by
    simpa [prefixWord, tailWord_590728, baseEnd_590728] using wordTrace_append hprefix tailTrace_590728
  have hstable : (prefixWord ++ tailWord_590728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590728).length < 2 ^ (prefixWord ++ tailWord_590728).sum := by decide
  have hdescent : baseEnd_590728 < baseStart_590728 := by decide
  rcases family_descends (prefixWord ++ tailWord_590728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590741 : List Nat := [1, 3, 2, 1, 1, 5, 3, 6]
def baseStart_590741 : Nat := 118140960795 + 590741 * 2 ^ 59
def prefixEnd_590741 : Nat := 4983230072969 + 3 ^ 40 * 590741 * 2
def baseEnd_590741 : Nat := 22469190764279885690425

theorem tailTrace_590741 : CollatzResearch.WordTrace tailWord_590741 prefixEnd_590741 22469190764279885690425 := by
  unfold tailWord_590741
  simp only [CollatzResearch.WordTrace]
  refine ⟨21546094352853722375604077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14364062901902481583736051 21546094352853722375604077)
  ·
    refine ⟨8079785382320145890851529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21546094352853722375604077 8079785382320145890851529)
    ·
      refine ⟨6059839036740109418138647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8079785382320145890851529 6059839036740109418138647)
      ·
        refine ⟨9089758555110164127207971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6059839036740109418138647 9089758555110164127207971)
        ·
          refine ⟨13634637832665246190811957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9089758555110164127207971 13634637832665246190811957)
          ·
            refine ⟨1278247296812366830388621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13634637832665246190811957 1278247296812366830388621)
            ·
              refine ⟨479342736304637561395733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1278247296812366830388621 479342736304637561395733)
              ·
                refine ⟨22469190764279885690425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 479342736304637561395733 22469190764279885690425)
                ·
                  rfl

theorem cell22_590741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 3, 6].length) (baseStart_590741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_590741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_590741 prefixEnd_590741 := by exact prefixLift 590741
  have htrace : WordTrace (prefixWord ++ tailWord_590741) baseStart_590741 baseEnd_590741 := by
    simpa [prefixWord, tailWord_590741, baseEnd_590741] using wordTrace_append hprefix tailTrace_590741
  have hstable : (prefixWord ++ tailWord_590741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590741).length < 2 ^ (prefixWord ++ tailWord_590741).sum := by decide
  have hdescent : baseEnd_590741 < baseStart_590741 := by decide
  rcases family_descends (prefixWord ++ tailWord_590741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590756 : List Nat := [2, 3, 1, 2, 1, 2, 1, 2, 5, 3]
def baseStart_590756 : Nat := 118140960795 + 590756 * 2 ^ 59
def prefixEnd_590756 : Nat := 4983230072969 + 3 ^ 40 * 590756 * 2
def baseEnd_590756 : Nat := 202227851685063932088779

theorem tailTrace_590756 : CollatzResearch.WordTrace tailWord_590756 prefixEnd_590756 202227851685063932088779 := by
  unfold tailWord_590756
  simp only [CollatzResearch.WordTrace]
  refine ⟨10773320723899689968700061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14364427631866253291600081 10773320723899689968700061)
  ·
    refine ⟨4039995271462383738262523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10773320723899689968700061 4039995271462383738262523)
    ·
      refine ⟨6059992907193575607393785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4039995271462383738262523 6059992907193575607393785)
      ·
        refine ⟨4544994680395181705545339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6059992907193575607393785 4544994680395181705545339)
        ·
          refine ⟨6817492020592772558318009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4544994680395181705545339 6817492020592772558318009)
          ·
            refine ⟨5113119015444579418738507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6817492020592772558318009 5113119015444579418738507)
            ·
              refine ⟨7669678523166869128107761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5113119015444579418738507 7669678523166869128107761)
              ·
                refine ⟨5752258892375151846080821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7669678523166869128107761 5752258892375151846080821)
                ·
                  refine ⟨539274271160170485570077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5752258892375151846080821 539274271160170485570077)
                  ·
                    refine ⟨202227851685063932088779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 539274271160170485570077 202227851685063932088779)
                    ·
                      rfl

theorem cell22_590756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 5, 3].length) (baseStart_590756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_590756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_590756 prefixEnd_590756 := by exact prefixLift 590756
  have htrace : WordTrace (prefixWord ++ tailWord_590756) baseStart_590756 baseEnd_590756 := by
    simpa [prefixWord, tailWord_590756, baseEnd_590756] using wordTrace_append hprefix tailTrace_590756
  have hstable : (prefixWord ++ tailWord_590756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590756).length < 2 ^ (prefixWord ++ tailWord_590756).sum := by decide
  have hdescent : baseEnd_590756 < baseStart_590756 := by decide
  rcases family_descends (prefixWord ++ tailWord_590756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590773 : List Nat := [1, 3, 3, 2, 1, 1, 4, 1, 3, 3]
def baseStart_590773 : Nat := 118140960795 + 590773 * 2 ^ 59
def prefixEnd_590773 : Nat := 4983230072969 + 3 ^ 40 * 590773 * 2
def baseEnd_590773 : Nat := 202233671132481554413727

theorem tailTrace_590773 : CollatzResearch.WordTrace tailWord_590773 prefixEnd_590773 202233671132481554413727 := by
  unfold tailWord_590773
  simp only [CollatzResearch.WordTrace]
  refine ⟨21547261488737791840768973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14364840992491861227179315 21547261488737791840768973)
  ·
    refine ⟨8080223058276671940288365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21547261488737791840768973 8080223058276671940288365)
    ·
      refine ⟨3030083646853751977608137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8080223058276671940288365 3030083646853751977608137)
      ·
        refine ⟨2272562735140313983206103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3030083646853751977608137 2272562735140313983206103)
        ·
          refine ⟨3408844102710470974809155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2272562735140313983206103 3408844102710470974809155)
          ·
            refine ⟨5113266154065706462213733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3408844102710470974809155 5113266154065706462213733)
            ·
              refine ⟨958737403887319961665075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5113266154065706462213733 958737403887319961665075)
              ·
                refine ⟨1438106105830979942497613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 958737403887319961665075 1438106105830979942497613)
                ·
                  refine ⟨539289789686617478436605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1438106105830979942497613 539289789686617478436605)
                  ·
                    refine ⟨202233671132481554413727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 539289789686617478436605 202233671132481554413727)
                    ·
                      rfl

theorem cell22_590773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 1, 3, 3].length) (baseStart_590773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_590773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_590773 prefixEnd_590773 := by exact prefixLift 590773
  have htrace : WordTrace (prefixWord ++ tailWord_590773) baseStart_590773 baseEnd_590773 := by
    simpa [prefixWord, tailWord_590773, baseEnd_590773] using wordTrace_append hprefix tailTrace_590773
  have hstable : (prefixWord ++ tailWord_590773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590773).length < 2 ^ (prefixWord ++ tailWord_590773).sum := by decide
  have hdescent : baseEnd_590773 < baseStart_590773 := by decide
  rcases family_descends (prefixWord ++ tailWord_590773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590831 : List Nat := [1, 1, 2, 1, 4, 3, 3, 1, 6]
def baseStart_590831 : Nat := 118140960795 + 590831 * 2 ^ 59
def prefixEnd_590831 : Nat := 4983230072969 + 3 ^ 40 * 590831 * 2
def baseEnd_590831 : Nat := 67417841905929578821183

theorem tailTrace_590831 : CollatzResearch.WordTrace tailWord_590831 prefixEnd_590831 67417841905929578821183 := by
  unfold tailWord_590831
  simp only [CollatzResearch.WordTrace]
  refine ⟨21549376922527667746380347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14366251281685111830920231 21549376922527667746380347)
  ·
    refine ⟨32324065383791501619570521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21549376922527667746380347 32324065383791501619570521)
    ·
      refine ⟨24243049037843626214677891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32324065383791501619570521 24243049037843626214677891)
      ·
        refine ⟨36364573556765439322016837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24243049037843626214677891 36364573556765439322016837)
        ·
          refine ⟨6818357541893519872878157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36364573556765439322016837 6818357541893519872878157)
          ·
            refine ⟨2556884078210069952329309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6818357541893519872878157 2556884078210069952329309)
            ·
              refine ⟨958831529328776232123491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2556884078210069952329309 958831529328776232123491)
              ·
                refine ⟨1438247293993164348185237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 958831529328776232123491 1438247293993164348185237)
                ·
                  refine ⟨67417841905929578821183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1438247293993164348185237 67417841905929578821183)
                  ·
                    rfl

theorem cell22_590831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 1, 6].length) (baseStart_590831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_590831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_590831 prefixEnd_590831 := by exact prefixLift 590831
  have htrace : WordTrace (prefixWord ++ tailWord_590831) baseStart_590831 baseEnd_590831 := by
    simpa [prefixWord, tailWord_590831, baseEnd_590831] using wordTrace_append hprefix tailTrace_590831
  have hstable : (prefixWord ++ tailWord_590831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590831).length < 2 ^ (prefixWord ++ tailWord_590831).sum := by decide
  have hdescent : baseEnd_590831 < baseStart_590831 := by decide
  rcases family_descends (prefixWord ++ tailWord_590831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590876 : List Nat := [2, 2, 3, 1, 4, 10]
def baseStart_590876 : Nat := 118140960795 + 590876 * 2 ^ 59
def prefixEnd_590876 : Nat := 4983230072969 + 3 ^ 40 * 590876 * 2
def baseEnd_590876 : Nat := 2497147285647205173931

theorem tailTrace_590876 : CollatzResearch.WordTrace tailWord_590876 prefixEnd_590876 2497147285647205173931 := by
  unfold tailWord_590876
  simp only [CollatzResearch.WordTrace]
  refine ⟨10775509103682320215884241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14367345471576426954512321 10775509103682320215884241)
  ·
    refine ⟨8081631827761740161913181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10775509103682320215884241 8081631827761740161913181)
    ·
      refine ⟨3030611935410652560717443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8081631827761740161913181 3030611935410652560717443)
      ·
        refine ⟨4545917903115978841076165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3030611935410652560717443 4545917903115978841076165)
        ·
          refine ⟨852359606834246032701781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4545917903115978841076165 852359606834246032701781)
          ·
            refine ⟨2497147285647205173931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 852359606834246032701781 2497147285647205173931)
            ·
              rfl

theorem cell22_590876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 10].length) (baseStart_590876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_590876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_590876 prefixEnd_590876 := by exact prefixLift 590876
  have htrace : WordTrace (prefixWord ++ tailWord_590876) baseStart_590876 baseEnd_590876 := by
    simpa [prefixWord, tailWord_590876, baseEnd_590876] using wordTrace_append hprefix tailTrace_590876
  have hstable : (prefixWord ++ tailWord_590876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590876).length < 2 ^ (prefixWord ++ tailWord_590876).sum := by decide
  have hdescent : baseEnd_590876 < baseStart_590876 := by decide
  rcases family_descends (prefixWord ++ tailWord_590876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590882 : List Nat := [3, 3, 1, 1, 1, 5, 2, 2, 4]
def baseStart_590882 : Nat := 118140960795 + 590882 * 2 ^ 59
def prefixEnd_590882 : Nat := 4983230072969 + 3 ^ 40 * 590882 * 2
def baseEnd_590882 : Nat := 67423661353347201146131

theorem tailTrace_590882 : CollatzResearch.WordTrace tailWord_590882 prefixEnd_590882 67423661353347201146131 := by
  unfold tailWord_590882
  simp only [CollatzResearch.WordTrace]
  refine ⟨5387809261335725864121725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14367491363561935637657933 5387809261335725864121725)
  ·
    refine ⟨2020428473000897199045647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5387809261335725864121725 2020428473000897199045647)
    ·
      refine ⟨3030642709501345798568471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2020428473000897199045647 3030642709501345798568471)
      ·
        refine ⟨4545964064252018697852707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3030642709501345798568471 4545964064252018697852707)
        ·
          refine ⟨6818946096378028046779061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4545964064252018697852707 6818946096378028046779061)
          ·
            refine ⟨639276196535440129385537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6818946096378028046779061 639276196535440129385537)
            ·
              refine ⟨479457147401580097039153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 639276196535440129385537 479457147401580097039153)
              ·
                refine ⟨359592860551185072779365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 479457147401580097039153 359592860551185072779365)
                ·
                  refine ⟨67423661353347201146131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 359592860551185072779365 67423661353347201146131)
                  ·
                    rfl

theorem cell22_590882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 2, 2, 4].length) (baseStart_590882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_590882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_590882 prefixEnd_590882 := by exact prefixLift 590882
  have htrace : WordTrace (prefixWord ++ tailWord_590882) baseStart_590882 baseEnd_590882 := by
    simpa [prefixWord, tailWord_590882, baseEnd_590882] using wordTrace_append hprefix tailTrace_590882
  have hstable : (prefixWord ++ tailWord_590882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590882).length < 2 ^ (prefixWord ++ tailWord_590882).sum := by decide
  have hdescent : baseEnd_590882 < baseStart_590882 := by decide
  rcases family_descends (prefixWord ++ tailWord_590882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590908 : List Nat := [2, 2, 2, 2, 2, 2, 1, 1, 5, 3]
def baseStart_590908 : Nat := 118140960795 + 590908 * 2 ^ 59
def prefixEnd_590908 : Nat := 4983230072969 + 3 ^ 40 * 590908 * 2
def baseEnd_590908 : Nat := 202279884391386202288313

theorem tailTrace_590908 : CollatzResearch.WordTrace tailWord_590908 prefixEnd_590908 202279884391386202288313 := by
  unfold tailWord_590908
  simp only [CollatzResearch.WordTrace]
  refine ⟨10776092671624354948466689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14368123562165806597955585 10776092671624354948466689)
  ·
    refine ⟨8082069503718266211350017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10776092671624354948466689 8082069503718266211350017)
    ·
      refine ⟨6061552127788699658512513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8082069503718266211350017 6061552127788699658512513)
      ·
        refine ⟨4546164095841524743884385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6061552127788699658512513 4546164095841524743884385)
        ·
          refine ⟨3409623071881143557913289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4546164095841524743884385 3409623071881143557913289)
          ·
            refine ⟨2557217303910857668434967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3409623071881143557913289 2557217303910857668434967)
            ·
              refine ⟨3835825955866286502652451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2557217303910857668434967 3835825955866286502652451)
              ·
                refine ⟨5753738933799429753978677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3835825955866286502652451 5753738933799429753978677)
                ·
                  refine ⟨539413025043696539435501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5753738933799429753978677 539413025043696539435501)
                  ·
                    refine ⟨202279884391386202288313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 539413025043696539435501 202279884391386202288313)
                    ·
                      rfl

theorem cell22_590908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 5, 3].length) (baseStart_590908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_590908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_590908 prefixEnd_590908 := by exact prefixLift 590908
  have htrace : WordTrace (prefixWord ++ tailWord_590908) baseStart_590908 baseEnd_590908 := by
    simpa [prefixWord, tailWord_590908, baseEnd_590908] using wordTrace_append hprefix tailTrace_590908
  have hstable : (prefixWord ++ tailWord_590908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590908).length < 2 ^ (prefixWord ++ tailWord_590908).sum := by decide
  have hdescent : baseEnd_590908 < baseStart_590908 := by decide
  rcases family_descends (prefixWord ++ tailWord_590908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590910 : List Nat := [4, 2, 1, 3, 1, 2, 3, 6]
def baseStart_590910 : Nat := 118140960795 + 590910 * 2 ^ 59
def prefixEnd_590910 : Nat := 4983230072969 + 3 ^ 40 * 590910 * 2
def baseEnd_590910 : Nat := 22475618781362095970923

theorem tailTrace_590910 : CollatzResearch.WordTrace tailWord_590910 prefixEnd_590910 22475618781362095970923 := by
  unfold tailWord_590910
  simp only [CollatzResearch.WordTrace]
  refine ⟨2694032286155183029813273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14368172192827642825670789 2694032286155183029813273)
  ·
    refine ⟨2020524214616387272359955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2694032286155183029813273 2020524214616387272359955)
    ·
      refine ⟨3030786321924580908539933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2020524214616387272359955 3030786321924580908539933)
      ·
        refine ⟨1136544870721717840702475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3030786321924580908539933 1136544870721717840702475)
        ·
          refine ⟨1704817306082576761053713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1136544870721717840702475 1704817306082576761053713)
          ·
            refine ⟨1278612979561932570790285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1704817306082576761053713 1278612979561932570790285)
            ·
              refine ⟨479479867335724714046357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1278612979561932570790285 479479867335724714046357)
              ·
                refine ⟨22475618781362095970923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 479479867335724714046357 22475618781362095970923)
                ·
                  rfl

theorem cell22_590910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 3, 6].length) (baseStart_590910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_590910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_590910 prefixEnd_590910 := by exact prefixLift 590910
  have htrace : WordTrace (prefixWord ++ tailWord_590910) baseStart_590910 baseEnd_590910 := by
    simpa [prefixWord, tailWord_590910, baseEnd_590910] using wordTrace_append hprefix tailTrace_590910
  have hstable : (prefixWord ++ tailWord_590910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590910).length < 2 ^ (prefixWord ++ tailWord_590910).sum := by decide
  have hdescent : baseEnd_590910 < baseStart_590910 := by decide
  rcases family_descends (prefixWord ++ tailWord_590910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590936 : List Nat := [2, 1, 2, 2, 1, 3, 1, 1, 4, 5]
def baseStart_590936 : Nat := 118140960795 + 590936 * 2 ^ 59
def prefixEnd_590936 : Nat := 4983230072969 + 3 ^ 40 * 590936 * 2
def baseEnd_590936 : Nat := 202289469363603462588227

theorem tailTrace_590936 : CollatzResearch.WordTrace tailWord_590936 prefixEnd_590936 202289469363603462588227 := by
  unfold tailWord_590936
  simp only [CollatzResearch.WordTrace]
  refine ⟨10776603293573635339476331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14368804391431513785968441 10776603293573635339476331)
  ·
    refine ⟨16164904940360453009214497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10776603293573635339476331 16164904940360453009214497)
    ·
      refine ⟨12123678705270339756910873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16164904940360453009214497 12123678705270339756910873)
      ·
        refine ⟨9092759028952754817683155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12123678705270339756910873 9092759028952754817683155)
        ·
          refine ⟨13639138543429132226524733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9092759028952754817683155 13639138543429132226524733)
          ·
            refine ⟨5114676953785924584946775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13639138543429132226524733 5114676953785924584946775)
            ·
              refine ⟨7672015430678886877420163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5114676953785924584946775 7672015430678886877420163)
              ·
                refine ⟨11508023146018330316130245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7672015430678886877420163 11508023146018330316130245)
                ·
                  refine ⟨2157754339878436934274421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11508023146018330316130245 2157754339878436934274421)
                  ·
                    refine ⟨202289469363603462588227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2157754339878436934274421 202289469363603462588227)
                    ·
                      rfl

theorem cell22_590936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 4, 5].length) (baseStart_590936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_590936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_590936 prefixEnd_590936 := by exact prefixLift 590936
  have htrace : WordTrace (prefixWord ++ tailWord_590936) baseStart_590936 baseEnd_590936 := by
    simpa [prefixWord, tailWord_590936, baseEnd_590936] using wordTrace_append hprefix tailTrace_590936
  have hstable : (prefixWord ++ tailWord_590936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590936).length < 2 ^ (prefixWord ++ tailWord_590936).sum := by decide
  have hdescent : baseEnd_590936 < baseStart_590936 := by decide
  rcases family_descends (prefixWord ++ tailWord_590936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590968 : List Nat := [2, 1, 2, 1, 1, 1, 5, 4, 1, 4]
def baseStart_590968 : Nat := 118140960795 + 590968 * 2 ^ 59
def prefixEnd_590968 : Nat := 4983230072969 + 3 ^ 40 * 590968 * 2
def baseEnd_590968 : Nat := 202300423617566045788129

theorem tailTrace_590968 : CollatzResearch.WordTrace tailWord_590968 prefixEnd_590968 202300423617566045788129 := by
  unfold tailWord_590968
  simp only [CollatzResearch.WordTrace]
  refine ⟨10777186861515670072058779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14369582482020893429411705 10777186861515670072058779)
  ·
    refine ⟨16165780292273505108088169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10777186861515670072058779 16165780292273505108088169)
    ·
      refine ⟨12124335219205128831066127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16165780292273505108088169 12124335219205128831066127)
      ·
        refine ⟨18186502828807693246599191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12124335219205128831066127 18186502828807693246599191)
        ·
          refine ⟨27279754243211539869898787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18186502828807693246599191 27279754243211539869898787)
          ·
            refine ⟨40919631364817309804848181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27279754243211539869898787 40919631364817309804848181)
            ·
              refine ⟨3836215440451622794204517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40919631364817309804848181 3836215440451622794204517)
              ·
                refine ⟨719290395084679273913347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3836215440451622794204517 719290395084679273913347)
                ·
                  refine ⟨1078935592627018910870021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 719290395084679273913347 1078935592627018910870021)
                  ·
                    refine ⟨202300423617566045788129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1078935592627018910870021 202300423617566045788129)
                    ·
                      rfl

theorem cell22_590968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 4, 1, 4].length) (baseStart_590968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_590968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_590968 prefixEnd_590968 := by exact prefixLift 590968
  have htrace : WordTrace (prefixWord ++ tailWord_590968) baseStart_590968 baseEnd_590968 := by
    simpa [prefixWord, tailWord_590968, baseEnd_590968] using wordTrace_append hprefix tailTrace_590968
  have hstable : (prefixWord ++ tailWord_590968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590968).length < 2 ^ (prefixWord ++ tailWord_590968).sum := by decide
  have hdescent : baseEnd_590968 < baseStart_590968 := by decide
  rcases family_descends (prefixWord ++ tailWord_590968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591000 : List Nat := [2, 1, 2, 4, 2, 3, 1, 1, 6]
def baseStart_591000 : Nat := 118140960795 + 591000 * 2 ^ 59
def prefixEnd_591000 : Nat := 4983230072969 + 3 ^ 40 * 591000 * 2
def baseEnd_591000 : Nat := 67437125957176209662677

theorem tailTrace_591000 : CollatzResearch.WordTrace tailWord_591000 prefixEnd_591000 67437125957176209662677 := by
  unfold tailWord_591000
  simp only [CollatzResearch.WordTrace]
  refine ⟨10777770429457704804641227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14370360572610273072854969 10777770429457704804641227)
  ·
    refine ⟨16166655644186557206961841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10777770429457704804641227 16166655644186557206961841)
    ·
      refine ⟨12124991733139917905221381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16166655644186557206961841 12124991733139917905221381)
      ·
        refine ⟨2273435949963734607229009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12124991733139917905221381 2273435949963734607229009)
        ·
          refine ⟨1705076962472800955421757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2273435949963734607229009 1705076962472800955421757)
          ·
            refine ⟨639403860927300358283159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1705076962472800955421757 639403860927300358283159)
            ·
              refine ⟨959105791390950537424739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 639403860927300358283159 959105791390950537424739)
              ·
                refine ⟨1438658687086425806137109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 959105791390950537424739 1438658687086425806137109)
                ·
                  refine ⟨67437125957176209662677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1438658687086425806137109 67437125957176209662677)
                  ·
                    rfl

theorem cell22_591000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 1, 6].length) (baseStart_591000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_591000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_591000 prefixEnd_591000 := by exact prefixLift 591000
  have htrace : WordTrace (prefixWord ++ tailWord_591000) baseStart_591000 baseEnd_591000 := by
    simpa [prefixWord, tailWord_591000, baseEnd_591000] using wordTrace_append hprefix tailTrace_591000
  have hstable : (prefixWord ++ tailWord_591000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591000).length < 2 ^ (prefixWord ++ tailWord_591000).sum := by decide
  have hdescent : baseEnd_591000 < baseStart_591000 := by decide
  rcases family_descends (prefixWord ++ tailWord_591000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591043 : List Nat := [1, 1, 1, 3, 1, 1, 1, 3, 7, 3]
def baseStart_591043 : Nat := 118140960795 + 591043 * 2 ^ 59
def prefixEnd_591043 : Nat := 4983230072969 + 3 ^ 40 * 591043 * 2
def baseEnd_591043 : Nat := 202326097650290850162899

theorem tailTrace_591043 : CollatzResearch.WordTrace tailWord_591043 prefixEnd_591043 202326097650290850162899 := by
  unfold tailWord_591043
  simp only [CollatzResearch.WordTrace]
  refine ⟨21557109197759627953097783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14371406131839751968731855 21557109197759627953097783)
  ·
    refine ⟨32335663796639441929646675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21557109197759627953097783 32335663796639441929646675)
    ·
      refine ⟨48503495694959162894470013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32335663796639441929646675 48503495694959162894470013)
      ·
        refine ⟨18188810885609686085426255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48503495694959162894470013 18188810885609686085426255)
        ·
          refine ⟨27283216328414529128139383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18188810885609686085426255 27283216328414529128139383)
          ·
            refine ⟨40924824492621793692209075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27283216328414529128139383 40924824492621793692209075)
            ·
              refine ⟨61387236738932690538313613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40924824492621793692209075 61387236738932690538313613)
              ·
                refine ⟨23020213777099758951867605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61387236738932690538313613 23020213777099758951867605)
                ·
                  refine ⟨539536260400775600434397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 23020213777099758951867605 539536260400775600434397)
                  ·
                    refine ⟨202326097650290850162899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 539536260400775600434397 202326097650290850162899)
                    ·
                      rfl

theorem cell22_591043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 7, 3].length) (baseStart_591043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_591043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_591043 prefixEnd_591043 := by exact prefixLift 591043
  have htrace : WordTrace (prefixWord ++ tailWord_591043) baseStart_591043 baseEnd_591043 := by
    simpa [prefixWord, tailWord_591043, baseEnd_591043] using wordTrace_append hprefix tailTrace_591043
  have hstable : (prefixWord ++ tailWord_591043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591043).length < 2 ^ (prefixWord ++ tailWord_591043).sum := by decide
  have hdescent : baseEnd_591043 < baseStart_591043 := by decide
  rcases family_descends (prefixWord ++ tailWord_591043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591058 : List Nat := [3, 2, 2, 2, 1, 1, 1, 1, 1, 8]
def baseStart_591058 : Nat := 118140960795 + 591058 * 2 ^ 59
def prefixEnd_591058 : Nat := 4983230072969 + 3 ^ 40 * 591058 * 2
def baseEnd_591058 : Nat := 202331232456835811037853

theorem tailTrace_591058 : CollatzResearch.WordTrace tailWord_591058 prefixEnd_591058 202331232456835811037853 := by
  unfold tailWord_591058
  simp only [CollatzResearch.WordTrace]
  refine ⟨5389414073176321378723457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14371770861803523676595885 5389414073176321378723457)
  ·
    refine ⟨4042060554882241034042593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5389414073176321378723457 4042060554882241034042593)
    ·
      refine ⟨3031545416161680775531945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4042060554882241034042593 3031545416161680775531945)
      ·
        refine ⟨2273659062121260581648959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3031545416161680775531945 2273659062121260581648959)
        ·
          refine ⟨3410488593181890872473439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2273659062121260581648959 3410488593181890872473439)
          ·
            refine ⟨5115732889772836308710159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3410488593181890872473439 5115732889772836308710159)
            ·
              refine ⟨7673599334659254463065239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5115732889772836308710159 7673599334659254463065239)
              ·
                refine ⟨11510399001988881694597859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7673599334659254463065239 11510399001988881694597859)
                ·
                  refine ⟨17265598502983322541896789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11510399001988881694597859 17265598502983322541896789)
                  ·
                    refine ⟨202331232456835811037853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 17265598502983322541896789 202331232456835811037853)
                    ·
                      rfl

theorem cell22_591058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_591058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_591058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_591058 prefixEnd_591058 := by exact prefixLift 591058
  have htrace : WordTrace (prefixWord ++ tailWord_591058) baseStart_591058 baseEnd_591058 := by
    simpa [prefixWord, tailWord_591058, baseEnd_591058] using wordTrace_append hprefix tailTrace_591058
  have hstable : (prefixWord ++ tailWord_591058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591058).length < 2 ^ (prefixWord ++ tailWord_591058).sum := by decide
  have hdescent : baseEnd_591058 < baseStart_591058 := by decide
  rcases family_descends (prefixWord ++ tailWord_591058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591077 : List Nat := [1, 3, 1, 4, 3, 1, 1, 2, 3, 3]
def baseStart_591077 : Nat := 118140960795 + 591077 * 2 ^ 59
def prefixEnd_591077 : Nat := 4983230072969 + 3 ^ 40 * 591077 * 2
def baseEnd_591077 : Nat := 202337736545126094812795

theorem tailTrace_591077 : CollatzResearch.WordTrace tailWord_591077 prefixEnd_591077 202337736545126094812795 := by
  unfold tailWord_591077
  simp only [CollatzResearch.WordTrace]
  refine ⟨21558349279636451759835485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14372232853090967839890323 21558349279636451759835485)
  ·
    refine ⟨8084380979863669409938307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21558349279636451759835485 8084380979863669409938307)
    ·
      refine ⟨12126571469795504114907461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8084380979863669409938307 12126571469795504114907461)
      ·
        refine ⟨2273732150586657021545149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12126571469795504114907461 2273732150586657021545149)
        ·
          refine ⟨852649556469996383079431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2273732150586657021545149 852649556469996383079431)
          ·
            refine ⟨1278974334704994574619147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 852649556469996383079431 1278974334704994574619147)
            ·
              refine ⟨1918461502057491861928721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1278974334704994574619147 1918461502057491861928721)
              ·
                refine ⟨1438846126543118896446541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1918461502057491861928721 1438846126543118896446541)
                ·
                  refine ⟨539567297453669586167453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1438846126543118896446541 539567297453669586167453)
                  ·
                    refine ⟨202337736545126094812795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 539567297453669586167453 202337736545126094812795)
                    ·
                      rfl

theorem cell22_591077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 2, 3, 3].length) (baseStart_591077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_591077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_591077 prefixEnd_591077 := by exact prefixLift 591077
  have htrace : WordTrace (prefixWord ++ tailWord_591077) baseStart_591077 baseEnd_591077 := by
    simpa [prefixWord, tailWord_591077, baseEnd_591077] using wordTrace_append hprefix tailTrace_591077
  have hstable : (prefixWord ++ tailWord_591077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591077).length < 2 ^ (prefixWord ++ tailWord_591077).sum := by decide
  have hdescent : baseEnd_591077 < baseStart_591077 := by decide
  rcases family_descends (prefixWord ++ tailWord_591077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591180 : List Nat := [2, 2, 1, 3, 2, 3, 2, 7]
def baseStart_591180 : Nat := 118140960795 + 591180 * 2 ^ 59
def prefixEnd_591180 : Nat := 4983230072969 + 3 ^ 40 * 591180 * 2
def baseEnd_591180 : Nat := 22485888394452017720831

theorem tailTrace_591180 : CollatzResearch.WordTrace tailWord_591180 prefixEnd_591180 22485888394452017720831 := by
  unfold tailWord_591180
  simp only [CollatzResearch.WordTrace]
  refine ⟨10781052999131650175417497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14374737332175533567223329 10781052999131650175417497)
  ·
    refine ⟨8085789749348737631563123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10781052999131650175417497 8085789749348737631563123)
    ·
      refine ⟨12128684624023106447344685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8085789749348737631563123 12128684624023106447344685)
      ·
        refine ⟨4548256734008664917754257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12128684624023106447344685 4548256734008664917754257)
        ·
          refine ⟨3411192550506498688315693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4548256734008664917754257 3411192550506498688315693)
          ·
            refine ⟨1279197206439937008118385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3411192550506498688315693 1279197206439937008118385)
            ·
              refine ⟨959397904829952756088789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1279197206439937008118385 959397904829952756088789)
              ·
                refine ⟨22485888394452017720831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 959397904829952756088789 22485888394452017720831)
                ·
                  rfl

theorem cell22_591180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 7].length) (baseStart_591180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_591180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_591180 prefixEnd_591180 := by exact prefixLift 591180
  have htrace : WordTrace (prefixWord ++ tailWord_591180) baseStart_591180 baseEnd_591180 := by
    simpa [prefixWord, tailWord_591180, baseEnd_591180] using wordTrace_append hprefix tailTrace_591180
  have hstable : (prefixWord ++ tailWord_591180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591180).length < 2 ^ (prefixWord ++ tailWord_591180).sum := by decide
  have hdescent : baseEnd_591180 < baseStart_591180 := by decide
  rcases family_descends (prefixWord ++ tailWord_591180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591225 : List Nat := [1, 2, 1, 3, 2, 1, 3, 4, 5]
def baseStart_591225 : Nat := 118140960795 + 591225 * 2 ^ 59
def prefixEnd_591225 : Nat := 4983230072969 + 3 ^ 40 * 591225 * 2
def baseEnd_591225 : Nat := 67462799989901014037447

theorem tailTrace_591225 : CollatzResearch.WordTrace tailWord_591225 prefixEnd_591225 67462799989901014037447 := by
  unfold tailWord_591225
  simp only [CollatzResearch.WordTrace]
  refine ⟨21563747283100273036223129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14375831522066848690815419 21563747283100273036223129)
  ·
    refine ⟨16172810462325204777167347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21563747283100273036223129 16172810462325204777167347)
    ·
      refine ⟨24259215693487807165751021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16172810462325204777167347 24259215693487807165751021)
      ·
        refine ⟨9097205885057927687156633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24259215693487807165751021 9097205885057927687156633)
        ·
          refine ⟨6822904413793445765367475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9097205885057927687156633 6822904413793445765367475)
          ·
            refine ⟨10234356620690168648051213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6822904413793445765367475 10234356620690168648051213)
            ·
              refine ⟨3837883732758813243019205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10234356620690168648051213 3837883732758813243019205)
              ·
                refine ⟨719603199892277483066101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3837883732758813243019205 719603199892277483066101)
                ·
                  refine ⟨67462799989901014037447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 719603199892277483066101 67462799989901014037447)
                  ·
                    rfl

theorem cell22_591225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 4, 5].length) (baseStart_591225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_591225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_591225 prefixEnd_591225 := by exact prefixLift 591225
  have htrace : WordTrace (prefixWord ++ tailWord_591225) baseStart_591225 baseEnd_591225 := by
    simpa [prefixWord, tailWord_591225, baseEnd_591225] using wordTrace_append hprefix tailTrace_591225
  have hstable : (prefixWord ++ tailWord_591225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591225).length < 2 ^ (prefixWord ++ tailWord_591225).sum := by decide
  have hdescent : baseEnd_591225 < baseStart_591225 := by decide
  rcases family_descends (prefixWord ++ tailWord_591225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591229 : List Nat := [1, 4, 1, 1, 2, 2, 3, 4, 1, 3]
def baseStart_591229 : Nat := 118140960795 + 591229 * 2 ^ 59
def prefixEnd_591229 : Nat := 4983230072969 + 3 ^ 40 * 591229 * 2
def baseEnd_591229 : Nat := 202389769251448365012329

theorem tailTrace_591229 : CollatzResearch.WordTrace tailWord_591229 prefixEnd_591229 202389769251448365012329 := by
  unfold tailWord_591229
  simp only [CollatzResearch.WordTrace]
  refine ⟨21563893175085781719368741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14375928783390521146245827 21563893175085781719368741)
  ·
    refine ⟨4043229970328584072381639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21563893175085781719368741 4043229970328584072381639)
    ·
      refine ⟨6064844955492876108572459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4043229970328584072381639 6064844955492876108572459)
      ·
        refine ⟨9097267433239314162858689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6064844955492876108572459 9097267433239314162858689)
        ·
          refine ⟨6822950574929485622144017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9097267433239314162858689 6822950574929485622144017)
          ·
            refine ⟨5117212931197114216608013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6822950574929485622144017 5117212931197114216608013)
            ·
              refine ⟨1918954849198917831228005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5117212931197114216608013 1918954849198917831228005)
              ·
                refine ⟨359804034224797093355251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1918954849198917831228005 359804034224797093355251)
                ·
                  refine ⟨539706051337195640032877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 359804034224797093355251 539706051337195640032877)
                  ·
                    refine ⟨202389769251448365012329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 539706051337195640032877 202389769251448365012329)
                    ·
                      rfl

theorem cell22_591229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 4, 1, 3].length) (baseStart_591229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_591229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_591229 prefixEnd_591229 := by exact prefixLift 591229
  have htrace : WordTrace (prefixWord ++ tailWord_591229) baseStart_591229 baseEnd_591229 := by
    simpa [prefixWord, tailWord_591229, baseEnd_591229] using wordTrace_append hprefix tailTrace_591229
  have hstable : (prefixWord ++ tailWord_591229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591229).length < 2 ^ (prefixWord ++ tailWord_591229).sum := by decide
  have hdescent : baseEnd_591229 < baseStart_591229 := by decide
  rcases family_descends (prefixWord ++ tailWord_591229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591240 : List Nat := [2, 1, 3, 3, 1, 2, 1, 1, 1, 7]
def baseStart_591240 : Nat := 118140960795 + 591240 * 2 ^ 59
def prefixEnd_591240 : Nat := 4983230072969 + 3 ^ 40 * 591240 * 2
def baseEnd_591240 : Nat := 202393534776248002987295

theorem tailTrace_591240 : CollatzResearch.WordTrace tailWord_591240 prefixEnd_591240 202393534776248002987295 := by
  unfold tailWord_591240
  simp only [CollatzResearch.WordTrace]
  refine ⟨10782147189022965299009587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14376196252030620398679449 10782147189022965299009587)
  ·
    refine ⟨16173220783534447948514381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10782147189022965299009587 16173220783534447948514381)
    ·
      refine ⟨6064957793825417980692893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16173220783534447948514381 6064957793825417980692893)
      ·
        refine ⟨2274359172684531742759835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6064957793825417980692893 2274359172684531742759835)
        ·
          refine ⟨3411538759026797614139753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2274359172684531742759835 3411538759026797614139753)
          ·
            refine ⟨2558654069270098210604815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3411538759026797614139753 2558654069270098210604815)
            ·
              refine ⟨3837981103905147315907223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2558654069270098210604815 3837981103905147315907223)
              ·
                refine ⟨5756971655857720973860835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3837981103905147315907223 5756971655857720973860835)
                ·
                  refine ⟨8635457483786581460791253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5756971655857720973860835 8635457483786581460791253)
                  ·
                    refine ⟨202393534776248002987295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8635457483786581460791253 202393534776248002987295)
                    ·
                      rfl

theorem cell22_591240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 1, 7].length) (baseStart_591240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_591240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_591240 prefixEnd_591240 := by exact prefixLift 591240
  have htrace : WordTrace (prefixWord ++ tailWord_591240) baseStart_591240 baseEnd_591240 := by
    simpa [prefixWord, tailWord_591240, baseEnd_591240] using wordTrace_append hprefix tailTrace_591240
  have hstable : (prefixWord ++ tailWord_591240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591240).length < 2 ^ (prefixWord ++ tailWord_591240).sum := by decide
  have hdescent : baseEnd_591240 < baseStart_591240 := by decide
  rcases family_descends (prefixWord ++ tailWord_591240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591287 : List Nat := [1, 1, 3, 1, 3, 2, 1, 6, 4]
def baseStart_591287 : Nat := 118140960795 + 591287 * 2 ^ 59
def prefixEnd_591287 : Nat := 4983230072969 + 3 ^ 40 * 591287 * 2
def baseEnd_591287 : Nat := 67469874612251849020717

theorem tailTrace_591287 : CollatzResearch.WordTrace tailWord_591287 prefixEnd_591287 67469874612251849020717 := by
  unfold tailWord_591287
  simp only [CollatzResearch.WordTrace]
  refine ⟨21566008608875657624980115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14377339072583771749986743 21566008608875657624980115)
  ·
    refine ⟨32349012913313486437470173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21566008608875657624980115 32349012913313486437470173)
    ·
      refine ⟨12130879842492557414051315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32349012913313486437470173 12130879842492557414051315)
      ·
        refine ⟨18196319763738836121076973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12130879842492557414051315 18196319763738836121076973)
        ·
          refine ⟨6823619911402063545403865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18196319763738836121076973 6823619911402063545403865)
          ·
            refine ⟨5117714933551547659052899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6823619911402063545403865 5117714933551547659052899)
            ·
              refine ⟨7676572400327321488579349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5117714933551547659052899 7676572400327321488579349)
              ·
                refine ⟨359839331265343194777157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7676572400327321488579349 359839331265343194777157)
                ·
                  refine ⟨67469874612251849020717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 359839331265343194777157 67469874612251849020717)
                  ·
                    rfl

theorem cell22_591287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 6, 4].length) (baseStart_591287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_591287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_591287 prefixEnd_591287 := by exact prefixLift 591287
  have htrace : WordTrace (prefixWord ++ tailWord_591287) baseStart_591287 baseEnd_591287 := by
    simpa [prefixWord, tailWord_591287, baseEnd_591287] using wordTrace_append hprefix tailTrace_591287
  have hstable : (prefixWord ++ tailWord_591287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591287).length < 2 ^ (prefixWord ++ tailWord_591287).sum := by decide
  have hdescent : baseEnd_591287 < baseStart_591287 := by decide
  rcases family_descends (prefixWord ++ tailWord_591287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591317 : List Nat := [1, 3, 2, 3, 1, 1, 2, 3, 2, 4]
def baseStart_591317 : Nat := 118140960795 + 591317 * 2 ^ 59
def prefixEnd_591317 : Nat := 4983230072969 + 3 ^ 40 * 591317 * 2
def baseEnd_591317 : Nat := 202419893449845468812059

theorem tailTrace_591317 : CollatzResearch.WordTrace tailWord_591317 prefixEnd_591317 202419893449845468812059 := by
  unfold tailWord_591317
  simp only [CollatzResearch.WordTrace]
  refine ⟨21567102798766972748572205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14378068532511315165714803 21567102798766972748572205)
  ·
    refine ⟨8087663549537614780714577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21567102798766972748572205 8087663549537614780714577)
    ·
      refine ⟨6065747662153211085535933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8087663549537614780714577 6065747662153211085535933)
      ·
        refine ⟨2274655373307454157075975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6065747662153211085535933 2274655373307454157075975)
        ·
          refine ⟨3411983059961181235613963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2274655373307454157075975 3411983059961181235613963)
          ·
            refine ⟨5117974589941771853420945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3411983059961181235613963 5117974589941771853420945)
            ·
              refine ⟨3838480942456328890065709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5117974589941771853420945 3838480942456328890065709)
              ·
                refine ⟨1439430353421123333774641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3838480942456328890065709 1439430353421123333774641)
                ·
                  refine ⟨1079572765065842500330981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1439430353421123333774641 1079572765065842500330981)
                  ·
                    refine ⟨202419893449845468812059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1079572765065842500330981 202419893449845468812059)
                    ·
                      rfl

theorem cell22_591317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 3, 2, 4].length) (baseStart_591317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_591317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_591317 prefixEnd_591317 := by exact prefixLift 591317
  have htrace : WordTrace (prefixWord ++ tailWord_591317) baseStart_591317 baseEnd_591317 := by
    simpa [prefixWord, tailWord_591317, baseEnd_591317] using wordTrace_append hprefix tailTrace_591317
  have hstable : (prefixWord ++ tailWord_591317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591317).length < 2 ^ (prefixWord ++ tailWord_591317).sum := by decide
  have hdescent : baseEnd_591317 < baseStart_591317 := by decide
  rcases family_descends (prefixWord ++ tailWord_591317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591347 : List Nat := [1, 1, 1, 2, 2, 2, 2, 5, 3, 3]
def baseStart_591347 : Nat := 118140960795 + 591347 * 2 ^ 59
def prefixEnd_591347 : Nat := 4983230072969 + 3 ^ 40 * 591347 * 2
def baseEnd_591347 : Nat := 202430163062935390561967

theorem tailTrace_591347 : CollatzResearch.WordTrace tailWord_591347 prefixEnd_591347 202430163062935390561967 := by
  unfold tailWord_591347
  simp only [CollatzResearch.WordTrace]
  refine ⟨21568196988658287872164295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14378797992438858581442863 21568196988658287872164295)
  ·
    refine ⟨32352295482987431808246443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21568196988658287872164295 32352295482987431808246443)
    ·
      refine ⟨48528443224481147712369665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32352295482987431808246443 48528443224481147712369665)
      ·
        refine ⟨36396332418360860784277249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48528443224481147712369665 36396332418360860784277249)
        ·
          refine ⟨27297249313770645588207937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36396332418360860784277249 27297249313770645588207937)
          ·
            refine ⟨20472936985327984191155953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27297249313770645588207937 20472936985327984191155953)
            ·
              refine ⟨15354702738995988143366965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20472936985327984191155953 15354702738995988143366965)
              ·
                refine ⟨1439503381780873888440653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15354702738995988143366965 1439503381780873888440653)
                ·
                  refine ⟨539813768167827708165245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1439503381780873888440653 539813768167827708165245)
                  ·
                    refine ⟨202430163062935390561967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 539813768167827708165245 202430163062935390561967)
                    ·
                      rfl

theorem cell22_591347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5, 3, 3].length) (baseStart_591347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_591347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_591347 prefixEnd_591347 := by exact prefixLift 591347
  have htrace : WordTrace (prefixWord ++ tailWord_591347) baseStart_591347 baseEnd_591347 := by
    simpa [prefixWord, tailWord_591347, baseEnd_591347] using wordTrace_append hprefix tailTrace_591347
  have hstable : (prefixWord ++ tailWord_591347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591347).length < 2 ^ (prefixWord ++ tailWord_591347).sum := by decide
  have hdescent : baseEnd_591347 < baseStart_591347 := by decide
  rcases family_descends (prefixWord ++ tailWord_591347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591349 : List Nat := [1, 3, 5, 1, 1, 2, 2, 7]
def baseStart_591349 : Nat := 118140960795 + 591349 * 2 ^ 59
def prefixEnd_591349 : Nat := 4983230072969 + 3 ^ 40 * 591349 * 2
def baseEnd_591349 : Nat := 22492316411534228001329

theorem tailTrace_591349 : CollatzResearch.WordTrace tailWord_591349 prefixEnd_591349 22492316411534228001329 := by
  unfold tailWord_591349
  simp only [CollatzResearch.WordTrace]
  refine ⟨21568269934651042213737101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14378846623100694809158067 21568269934651042213737101)
  ·
    refine ⟨8088101225494140830151413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21568269934651042213737101 8088101225494140830151413)
    ·
      refine ⟨758259489890075702826695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8088101225494140830151413 758259489890075702826695)
      ·
        refine ⟨1137389234835113554240043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 758259489890075702826695 1137389234835113554240043)
        ·
          refine ⟨1706083852252670331360065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1137389234835113554240043 1706083852252670331360065)
          ·
            refine ⟨1279562889189502748520049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1706083852252670331360065 1279562889189502748520049)
            ·
              refine ⟨959672166892127061390037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1279562889189502748520049 959672166892127061390037)
              ·
                refine ⟨22492316411534228001329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 959672166892127061390037 22492316411534228001329)
                ·
                  rfl

theorem cell22_591349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 7].length) (baseStart_591349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_591349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_591349 prefixEnd_591349 := by exact prefixLift 591349
  have htrace : WordTrace (prefixWord ++ tailWord_591349) baseStart_591349 baseEnd_591349 := by
    simpa [prefixWord, tailWord_591349, baseEnd_591349] using wordTrace_append hprefix tailTrace_591349
  have hstable : (prefixWord ++ tailWord_591349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591349).length < 2 ^ (prefixWord ++ tailWord_591349).sum := by decide
  have hdescent : baseEnd_591349 < baseStart_591349 := by decide
  rcases family_descends (prefixWord ++ tailWord_591349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591522 : List Nat := [3, 3, 1, 4, 1, 2, 2, 1, 2, 3]
def baseStart_591522 : Nat := 118140960795 + 591522 * 2 ^ 59
def prefixEnd_591522 : Nat := 4983230072969 + 3 ^ 40 * 591522 * 2
def baseEnd_591522 : Nat := 202490069139293267436431

theorem tailTrace_591522 : CollatzResearch.WordTrace tailWord_591522 prefixEnd_591522 202490069139293267436431 := by
  unfold tailWord_591522
  simp only [CollatzResearch.WordTrace]
  refine ⟨5393644940756073189946205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14383053175349528506523213 5393644940756073189946205)
  ·
    refine ⟨2022616852783527446229827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5393644940756073189946205 2022616852783527446229827)
    ·
      refine ⟨3033925279175291169344741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2022616852783527446229827 3033925279175291169344741)
      ·
        refine ⟨568860989845367094252139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3033925279175291169344741 568860989845367094252139)
        ·
          refine ⟨853291484768050641378209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 568860989845367094252139 853291484768050641378209)
          ·
            refine ⟨639968613576037981033657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 853291484768050641378209 639968613576037981033657)
            ·
              refine ⟨479976460182028485775243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 639968613576037981033657 479976460182028485775243)
              ·
                refine ⟨719964690273042728662865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 479976460182028485775243 719964690273042728662865)
                ·
                  refine ⟨539973517704782046497149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 719964690273042728662865 539973517704782046497149)
                  ·
                    refine ⟨202490069139293267436431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 539973517704782046497149 202490069139293267436431)
                    ·
                      rfl

theorem cell22_591522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 2, 1, 2, 3].length) (baseStart_591522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_591522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_591522 prefixEnd_591522 := by exact prefixLift 591522
  have htrace : WordTrace (prefixWord ++ tailWord_591522) baseStart_591522 baseEnd_591522 := by
    simpa [prefixWord, tailWord_591522, baseEnd_591522] using wordTrace_append hprefix tailTrace_591522
  have hstable : (prefixWord ++ tailWord_591522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591522).length < 2 ^ (prefixWord ++ tailWord_591522).sum := by decide
  have hdescent : baseEnd_591522 < baseStart_591522 := by decide
  rcases family_descends (prefixWord ++ tailWord_591522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591557 : List Nat := [1, 3, 1, 1, 1, 1, 2, 4, 8]
def baseStart_591557 : Nat := 118140960795 + 591557 * 2 ^ 59
def prefixEnd_591557 : Nat := 4983230072969 + 3 ^ 40 * 591557 * 2
def baseEnd_591557 : Nat := 67500683451521614270441

theorem tailTrace_591557 : CollatzResearch.WordTrace tailWord_591557 prefixEnd_591557 67500683451521614270441 := by
  unfold tailWord_591557
  simp only [CollatzResearch.WordTrace]
  refine ⟨21575856317897493737308925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14383904211931662491539283 21575856317897493737308925)
  ·
    refine ⟨8090946119211560151490847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21575856317897493737308925 8090946119211560151490847)
    ·
      refine ⟨12136419178817340227236271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8090946119211560151490847 12136419178817340227236271)
      ·
        refine ⟨18204628768226010340854407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12136419178817340227236271 18204628768226010340854407)
        ·
          refine ⟨27306943152339015511281611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18204628768226010340854407 27306943152339015511281611)
          ·
            refine ⟨40960414728508523266922417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27306943152339015511281611 40960414728508523266922417)
            ·
              refine ⟨30720311046381392450191813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40960414728508523266922417 30720311046381392450191813)
              ·
                refine ⟨5760058321196511084410965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30720311046381392450191813 5760058321196511084410965)
                ·
                  refine ⟨67500683451521614270441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5760058321196511084410965 67500683451521614270441)
                  ·
                    rfl

theorem cell22_591557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 8].length) (baseStart_591557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_591557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_591557 prefixEnd_591557 := by exact prefixLift 591557
  have htrace : WordTrace (prefixWord ++ tailWord_591557) baseStart_591557 baseEnd_591557 := by
    simpa [prefixWord, tailWord_591557, baseEnd_591557] using wordTrace_append hprefix tailTrace_591557
  have hstable : (prefixWord ++ tailWord_591557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591557).length < 2 ^ (prefixWord ++ tailWord_591557).sum := by decide
  have hdescent : baseEnd_591557 < baseStart_591557 := by decide
  rcases family_descends (prefixWord ++ tailWord_591557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591606 : List Nat := [5, 1, 1, 1, 1, 3, 2, 2, 1, 5]
def baseStart_591606 : Nat := 118140960795 + 591606 * 2 ^ 59
def prefixEnd_591606 : Nat := 4983230072969 + 3 ^ 40 * 591606 * 2
def baseEnd_591606 : Nat := 202518824055945048336173

theorem tailTrace_591606 : CollatzResearch.WordTrace tailWord_591606 prefixEnd_591606 202518824055945048336173 := by
  unfold tailWord_591606
  simp only [CollatzResearch.WordTrace]
  refine ⟨1348602718419998444115167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14385095663146650070561781 1348602718419998444115167)
  ·
    refine ⟨2022904077629997666172751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1348602718419998444115167 2022904077629997666172751)
    ·
      refine ⟨3034356116444996499259127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2022904077629997666172751 3034356116444996499259127)
      ·
        refine ⟨4551534174667494748888691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3034356116444996499259127 4551534174667494748888691)
        ·
          refine ⟨6827301262001242123333037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4551534174667494748888691 6827301262001242123333037)
          ·
            refine ⟨2560237973250465796249889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6827301262001242123333037 2560237973250465796249889)
            ·
              refine ⟨1920178479937849347187417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2560237973250465796249889 1920178479937849347187417)
              ·
                refine ⟨1440133859953387010390563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1920178479937849347187417 1440133859953387010390563)
                ·
                  refine ⟨2160200789930080515585845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1440133859953387010390563 2160200789930080515585845)
                  ·
                    refine ⟨202518824055945048336173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2160200789930080515585845 202518824055945048336173)
                    ·
                      rfl

theorem cell22_591606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_591606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_591606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_591606 prefixEnd_591606 := by exact prefixLift 591606
  have htrace : WordTrace (prefixWord ++ tailWord_591606) baseStart_591606 baseEnd_591606 := by
    simpa [prefixWord, tailWord_591606, baseEnd_591606] using wordTrace_append hprefix tailTrace_591606
  have hstable : (prefixWord ++ tailWord_591606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591606).length < 2 ^ (prefixWord ++ tailWord_591606).sum := by decide
  have hdescent : baseEnd_591606 < baseStart_591606 := by decide
  rcases family_descends (prefixWord ++ tailWord_591606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591623 : List Nat := [1, 1, 4, 4, 2, 1, 1, 1, 4, 3]
def baseStart_591623 : Nat := 118140960795 + 591623 * 2 ^ 59
def prefixEnd_591623 : Nat := 4983230072969 + 3 ^ 40 * 591623 * 2
def baseEnd_591623 : Nat := 202524643503362670661121

theorem tailTrace_591623 : CollatzResearch.WordTrace tailWord_591623 prefixEnd_591623 202524643503362670661121 := by
  unfold tailWord_591623
  simp only [CollatzResearch.WordTrace]
  refine ⟨21578263535658387009211523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14385509023772258006141015 21578263535658387009211523)
  ·
    refine ⟨32367395303487580513817285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21578263535658387009211523 32367395303487580513817285)
    ·
      refine ⟨6068886619403921346340741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32367395303487580513817285 6068886619403921346340741)
      ·
        refine ⟨1137916241138235252438889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6068886619403921346340741 1137916241138235252438889)
        ·
          refine ⟨853437180853676439329167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1137916241138235252438889 853437180853676439329167)
          ·
            refine ⟨1280155771280514658993751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 853437180853676439329167 1280155771280514658993751)
            ·
              refine ⟨1920233656920771988490627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1280155771280514658993751 1920233656920771988490627)
              ·
                refine ⟨2880350485381157982735941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1920233656920771988490627 2880350485381157982735941)
                ·
                  refine ⟨540065716008967121762989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2880350485381157982735941 540065716008967121762989)
                  ·
                    refine ⟨202524643503362670661121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 540065716008967121762989 202524643503362670661121)
                    ·
                      rfl

theorem cell22_591623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 1, 4, 3].length) (baseStart_591623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_591623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_591623 prefixEnd_591623 := by exact prefixLift 591623
  have htrace : WordTrace (prefixWord ++ tailWord_591623) baseStart_591623 baseEnd_591623 := by
    simpa [prefixWord, tailWord_591623, baseEnd_591623] using wordTrace_append hprefix tailTrace_591623
  have hstable : (prefixWord ++ tailWord_591623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591623).length < 2 ^ (prefixWord ++ tailWord_591623).sum := by decide
  have hdescent : baseEnd_591623 < baseStart_591623 := by decide
  rcases family_descends (prefixWord ++ tailWord_591623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591651 : List Nat := [1, 1, 1, 4, 2, 1, 4, 2, 3, 3]
def baseStart_591651 : Nat := 118140960795 + 591651 * 2 ^ 59
def prefixEnd_591651 : Nat := 4983230072969 + 3 ^ 40 * 591651 * 2
def baseEnd_591651 : Nat := 202534228475579930961035

theorem tailTrace_591651 : CollatzResearch.WordTrace tailWord_591651 prefixEnd_591651 202534228475579930961035 := by
  unfold tailWord_591651
  simp only [CollatzResearch.WordTrace]
  refine ⟨21579284779556947791230807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14386189853037965194153871 21579284779556947791230807)
  ·
    refine ⟨32368927169335421686846211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21579284779556947791230807 32368927169335421686846211)
    ·
      refine ⟨48553390754003132530269317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32368927169335421686846211 48553390754003132530269317)
      ·
        refine ⟨9103760766375587349425497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48553390754003132530269317 9103760766375587349425497)
        ·
          refine ⟨6827820574781690512069123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9103760766375587349425497 6827820574781690512069123)
          ·
            refine ⟨10241730862172535768103685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6827820574781690512069123 10241730862172535768103685)
            ·
              refine ⟨1920324536657350456519441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10241730862172535768103685 1920324536657350456519441)
              ·
                refine ⟨1440243402493012842389581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1920324536657350456519441 1440243402493012842389581)
                ·
                  refine ⟨540091275934879815896093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1440243402493012842389581 540091275934879815896093)
                  ·
                    refine ⟨202534228475579930961035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 540091275934879815896093 202534228475579930961035)
                    ·
                      rfl

theorem cell22_591651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 2, 3, 3].length) (baseStart_591651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_591651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_591651 prefixEnd_591651 := by exact prefixLift 591651
  have htrace : WordTrace (prefixWord ++ tailWord_591651) baseStart_591651 baseEnd_591651 := by
    simpa [prefixWord, tailWord_591651, baseEnd_591651] using wordTrace_append hprefix tailTrace_591651
  have hstable : (prefixWord ++ tailWord_591651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591651).length < 2 ^ (prefixWord ++ tailWord_591651).sum := by decide
  have hdescent : baseEnd_591651 < baseStart_591651 := by decide
  rcases family_descends (prefixWord ++ tailWord_591651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591685 : List Nat := [1, 3, 1, 1, 1, 2, 7, 2, 1, 3]
def baseStart_591685 : Nat := 118140960795 + 591685 * 2 ^ 59
def prefixEnd_591685 : Nat := 4983230072969 + 3 ^ 40 * 591685 * 2
def baseEnd_591685 : Nat := 202545867370415175610931

theorem tailTrace_591685 : CollatzResearch.WordTrace tailWord_591685 prefixEnd_591685 202545867370415175610931 := by
  unfold tailWord_591685
  simp only [CollatzResearch.WordTrace]
  refine ⟨21580524861433771597968509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14387016574289181065312339 21580524861433771597968509)
  ·
    refine ⟨8092696823037664349238191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21580524861433771597968509 8092696823037664349238191)
    ·
      refine ⟨12139045234556496523857287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8092696823037664349238191 12139045234556496523857287)
      ·
        refine ⟨18208567851834744785785931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12139045234556496523857287 18208567851834744785785931)
        ·
          refine ⟨27312851777752117178678897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18208567851834744785785931 27312851777752117178678897)
          ·
            refine ⟨20484638833314087884009173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27312851777752117178678897 20484638833314087884009173)
            ·
              refine ⟨480108722655798934781465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 20484638833314087884009173 480108722655798934781465)
              ·
                refine ⟨360081541991849201086099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 480108722655798934781465 360081541991849201086099)
                ·
                  refine ⟨540122312987773801629149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 360081541991849201086099 540122312987773801629149)
                  ·
                    refine ⟨202545867370415175610931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 540122312987773801629149 202545867370415175610931)
                    ·
                      rfl

theorem cell22_591685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 7, 2, 1, 3].length) (baseStart_591685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_591685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_591685 prefixEnd_591685 := by exact prefixLift 591685
  have htrace : WordTrace (prefixWord ++ tailWord_591685) baseStart_591685 baseEnd_591685 := by
    simpa [prefixWord, tailWord_591685, baseEnd_591685] using wordTrace_append hprefix tailTrace_591685
  have hstable : (prefixWord ++ tailWord_591685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591685).length < 2 ^ (prefixWord ++ tailWord_591685).sum := by decide
  have hdescent : baseEnd_591685 < baseStart_591685 := by decide
  rcases family_descends (prefixWord ++ tailWord_591685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591694 : List Nat := [4, 1, 1, 1, 1, 1, 1, 1, 1, 10]
def baseStart_591694 : Nat := 118140960795 + 591694 * 2 ^ 59
def prefixEnd_591694 : Nat := 4983230072969 + 3 ^ 40 * 591694 * 2
def baseEnd_591694 : Nat := 202548948254342152135903

theorem tailTrace_591694 : CollatzResearch.WordTrace tailWord_591694 prefixEnd_591694 202548948254342152135903 := by
  unfold tailWord_591694
  simp only [CollatzResearch.WordTrace]
  refine ⟨2697606639800145766880767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14387235412267444090030757 2697606639800145766880767)
  ·
    refine ⟨4046409959700218650321151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2697606639800145766880767 4046409959700218650321151)
    ·
      refine ⟨6069614939550327975481727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4046409959700218650321151 6069614939550327975481727)
      ·
        refine ⟨9104422409325491963222591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6069614939550327975481727 9104422409325491963222591)
        ·
          refine ⟨13656633613988237944833887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9104422409325491963222591 13656633613988237944833887)
          ·
            refine ⟨20484950420982356917250831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13656633613988237944833887 20484950420982356917250831)
            ·
              refine ⟨30727425631473535375876247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20484950420982356917250831 30727425631473535375876247)
              ·
                refine ⟨46091138447210303063814371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30727425631473535375876247 46091138447210303063814371)
                ·
                  refine ⟨69136707670815454595721557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46091138447210303063814371 69136707670815454595721557)
                  ·
                    refine ⟨202548948254342152135903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 69136707670815454595721557 202548948254342152135903)
                    ·
                      rfl

theorem cell22_591694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 1, 10].length) (baseStart_591694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_591694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_591694 prefixEnd_591694 := by exact prefixLift 591694
  have htrace : WordTrace (prefixWord ++ tailWord_591694) baseStart_591694 baseEnd_591694 := by
    simpa [prefixWord, tailWord_591694, baseEnd_591694] using wordTrace_append hprefix tailTrace_591694
  have hstable : (prefixWord ++ tailWord_591694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591694).length < 2 ^ (prefixWord ++ tailWord_591694).sum := by decide
  have hdescent : baseEnd_591694 < baseStart_591694 := by decide
  rcases family_descends (prefixWord ++ tailWord_591694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591698 : List Nat := [3, 2, 2, 1, 1, 3, 4, 1, 5]
def baseStart_591698 : Nat := 118140960795 + 591698 * 2 ^ 59
def prefixEnd_591698 : Nat := 4983230072969 + 3 ^ 40 * 591698 * 2
def baseEnd_591698 : Nat := 67516772512029158345297

theorem tailTrace_591698 : CollatzResearch.WordTrace tailWord_591698 prefixEnd_591698 67516772512029158345297 := by
  unfold tailWord_591698
  simp only [CollatzResearch.WordTrace]
  refine ⟨5395249752596668704547937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14387332673591116545461165 5395249752596668704547937)
  ·
    refine ⟨4046437314447501528410953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5395249752596668704547937 4046437314447501528410953)
    ·
      refine ⟨3034827985835626146308215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4046437314447501528410953 3034827985835626146308215)
      ·
        refine ⟨4552241978753439219462323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3034827985835626146308215 4552241978753439219462323)
        ·
          refine ⟨6828362968130158829193485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4552241978753439219462323 6828362968130158829193485)
          ·
            refine ⟨2560636113048809560947557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6828362968130158829193485 2560636113048809560947557)
            ·
              refine ⟨480119271196651792677667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2560636113048809560947557 480119271196651792677667)
              ·
                refine ⟨720178906794977689016501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 480119271196651792677667 720178906794977689016501)
                ·
                  refine ⟨67516772512029158345297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 720178906794977689016501 67516772512029158345297)
                  ·
                    rfl

theorem cell22_591698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 4, 1, 5].length) (baseStart_591698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_591698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_591698 prefixEnd_591698 := by exact prefixLift 591698
  have htrace : WordTrace (prefixWord ++ tailWord_591698) baseStart_591698 baseEnd_591698 := by
    simpa [prefixWord, tailWord_591698, baseEnd_591698] using wordTrace_append hprefix tailTrace_591698
  have hstable : (prefixWord ++ tailWord_591698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591698).length < 2 ^ (prefixWord ++ tailWord_591698).sum := by decide
  have hdescent : baseEnd_591698 < baseStart_591698 := by decide
  rcases family_descends (prefixWord ++ tailWord_591698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591711 : List Nat := [1, 1, 2, 3, 1, 5, 1, 1, 3, 4]
def baseStart_591711 : Nat := 118140960795 + 591711 * 2 ^ 59
def prefixEnd_591711 : Nat := 4983230072969 + 3 ^ 40 * 591711 * 2
def baseEnd_591711 : Nat := 202554767701759774460851

theorem tailTrace_591711 : CollatzResearch.WordTrace tailWord_591711 prefixEnd_591711 202554767701759774460851 := by
  unfold tailWord_591711
  simp only [CollatzResearch.WordTrace]
  refine ⟨21581473159339578038414987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14387648772893052025609991 21581473159339578038414987)
  ·
    refine ⟨32372209739009367057622481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21581473159339578038414987 32372209739009367057622481)
    ·
      refine ⟨24279157304257025293216861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32372209739009367057622481 24279157304257025293216861)
      ·
        refine ⟨9104683989096384484956323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24279157304257025293216861 9104683989096384484956323)
        ·
          refine ⟨13657025983644576727434485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9104683989096384484956323 13657025983644576727434485)
          ·
            refine ⟨1280346185966679068196983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13657025983644576727434485 1280346185966679068196983)
            ·
              refine ⟨1920519278950018602295475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1280346185966679068196983 1920519278950018602295475)
              ·
                refine ⟨2880778918425027903443213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1920519278950018602295475 2880778918425027903443213)
                ·
                  refine ⟨1080292094409385463791205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2880778918425027903443213 1080292094409385463791205)
                  ·
                    refine ⟨202554767701759774460851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1080292094409385463791205 202554767701759774460851)
                    ·
                      rfl

theorem cell22_591711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 1, 3, 4].length) (baseStart_591711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_591711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_591711 prefixEnd_591711 := by exact prefixLift 591711
  have htrace : WordTrace (prefixWord ++ tailWord_591711) baseStart_591711 baseEnd_591711 := by
    simpa [prefixWord, tailWord_591711, baseEnd_591711] using wordTrace_append hprefix tailTrace_591711
  have hstable : (prefixWord ++ tailWord_591711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591711).length < 2 ^ (prefixWord ++ tailWord_591711).sum := by decide
  have hdescent : baseEnd_591711 < baseStart_591711 := by decide
  rcases family_descends (prefixWord ++ tailWord_591711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591739 : List Nat := [1, 1, 1, 1, 1, 5, 1, 2, 3, 6]
def baseStart_591739 : Nat := 118140960795 + 591739 * 2 ^ 59
def prefixEnd_591739 : Nat := 4983230072969 + 3 ^ 40 * 591739 * 2
def baseEnd_591739 : Nat := 202564352673977034760765

theorem tailTrace_591739 : CollatzResearch.WordTrace tailWord_591739 prefixEnd_591739 202564352673977034760765 := by
  unfold tailWord_591739
  simp only [CollatzResearch.WordTrace]
  refine ⟨21582494403238138820434271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14388329602158759213622847 21582494403238138820434271)
  ·
    refine ⟨32373741604857208230651407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21582494403238138820434271 32373741604857208230651407)
    ·
      refine ⟨48560612407285812345977111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32373741604857208230651407 48560612407285812345977111)
      ·
        refine ⟨72840918610928718518965667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48560612407285812345977111 72840918610928718518965667)
        ·
          refine ⟨109261377916393077778448501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72840918610928718518965667 109261377916393077778448501)
          ·
            refine ⟨10243254179661851041729547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 109261377916393077778448501 10243254179661851041729547)
            ·
              refine ⟨15364881269492776562594321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10243254179661851041729547 15364881269492776562594321)
              ·
                refine ⟨11523660952119582421945741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15364881269492776562594321 11523660952119582421945741)
                ·
                  refine ⟨4321372857044843408229653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11523660952119582421945741 4321372857044843408229653)
                  ·
                    refine ⟨202564352673977034760765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4321372857044843408229653 202564352673977034760765)
                    ·
                      rfl

theorem cell22_591739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 3, 6].length) (baseStart_591739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_591739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_591739 prefixEnd_591739 := by exact prefixLift 591739
  have htrace : WordTrace (prefixWord ++ tailWord_591739) baseStart_591739 baseEnd_591739 := by
    simpa [prefixWord, tailWord_591739, baseEnd_591739] using wordTrace_append hprefix tailTrace_591739
  have hstable : (prefixWord ++ tailWord_591739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591739).length < 2 ^ (prefixWord ++ tailWord_591739).sum := by decide
  have hdescent : baseEnd_591739 < baseStart_591739 := by decide
  rcases family_descends (prefixWord ++ tailWord_591739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591773 : List Nat := [1, 4, 2, 1, 2, 2, 3, 1, 2, 4]
def baseStart_591773 : Nat := 118140960795 + 591773 * 2 ^ 59
def prefixEnd_591773 : Nat := 4983230072969 + 3 ^ 40 * 591773 * 2
def baseEnd_591773 : Nat := 202575991568812279410661

theorem tailTrace_591773 : CollatzResearch.WordTrace tailWord_591773 prefixEnd_591773 202575991568812279410661 := by
  unfold tailWord_591773
  simp only [CollatzResearch.WordTrace]
  refine ⟨21583734485114962627171973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14389156323409975084781315 21583734485114962627171973)
  ·
    refine ⟨4046950215959055492594745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21583734485114962627171973 4046950215959055492594745)
    ·
      refine ⟨3035212661969291619446059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4046950215959055492594745 3035212661969291619446059)
      ·
        refine ⟨4552818992953937429169089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3035212661969291619446059 4552818992953937429169089)
        ·
          refine ⟨3414614244715453071876817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4552818992953937429169089 3414614244715453071876817)
          ·
            refine ⟨2560960683536589803907613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3414614244715453071876817 2560960683536589803907613)
            ·
              refine ⟨960360256326221176465355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2560960683536589803907613 960360256326221176465355)
              ·
                refine ⟨1440540384489331764698033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 960360256326221176465355 1440540384489331764698033)
                ·
                  refine ⟨1080405288366998823523525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1440540384489331764698033 1080405288366998823523525)
                  ·
                    refine ⟨202575991568812279410661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1080405288366998823523525 202575991568812279410661)
                    ·
                      rfl

theorem cell22_591773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_591773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_591773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_591773 prefixEnd_591773 := by exact prefixLift 591773
  have htrace : WordTrace (prefixWord ++ tailWord_591773) baseStart_591773 baseEnd_591773 := by
    simpa [prefixWord, tailWord_591773, baseEnd_591773] using wordTrace_append hprefix tailTrace_591773
  have hstable : (prefixWord ++ tailWord_591773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591773).length < 2 ^ (prefixWord ++ tailWord_591773).sum := by decide
  have hdescent : baseEnd_591773 < baseStart_591773 := by decide
  rcases family_descends (prefixWord ++ tailWord_591773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591854 : List Nat := [4, 1, 2, 1, 3, 2, 3, 2, 1, 3]
def baseStart_591854 : Nat := 118140960795 + 591854 * 2 ^ 59
def prefixEnd_591854 : Nat := 4983230072969 + 3 ^ 40 * 591854 * 2
def baseEnd_591854 : Nat := 202603719524155068135413

theorem tailTrace_591854 : CollatzResearch.WordTrace tailWord_591854 prefixEnd_591854 202603719524155068135413 := by
  unfold tailWord_591854
  simp only [CollatzResearch.WordTrace]
  refine ⟨2698336099727689182608827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14391125865214342307247077 2698336099727689182608827)
  ·
    refine ⟨4047504149591533773913241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2698336099727689182608827 4047504149591533773913241)
    ·
      refine ⟨3035628112193650330434931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4047504149591533773913241 3035628112193650330434931)
      ·
        refine ⟨4553442168290475495652397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3035628112193650330434931 4553442168290475495652397)
        ·
          refine ⟨1707540813108928310869649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4553442168290475495652397 1707540813108928310869649)
          ·
            refine ⟨1280655609831696233152237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1707540813108928310869649 1280655609831696233152237)
            ·
              refine ⟨480245853686886087432089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1280655609831696233152237 480245853686886087432089)
              ·
                refine ⟨360184390265164565574067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 480245853686886087432089 360184390265164565574067)
                ·
                  refine ⟨540276585397746848361101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 360184390265164565574067 540276585397746848361101)
                  ·
                    refine ⟨202603719524155068135413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 540276585397746848361101 202603719524155068135413)
                    ·
                      rfl

theorem cell22_591854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 3, 2, 1, 3].length) (baseStart_591854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_591854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_591854 prefixEnd_591854 := by exact prefixLift 591854
  have htrace : WordTrace (prefixWord ++ tailWord_591854) baseStart_591854 baseEnd_591854 := by
    simpa [prefixWord, tailWord_591854, baseEnd_591854] using wordTrace_append hprefix tailTrace_591854
  have hstable : (prefixWord ++ tailWord_591854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591854).length < 2 ^ (prefixWord ++ tailWord_591854).sum := by decide
  have hdescent : baseEnd_591854 < baseStart_591854 := by decide
  rcases family_descends (prefixWord ++ tailWord_591854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591891 : List Nat := [1, 1, 1, 2, 1, 4, 2, 3, 1, 6]
def baseStart_591891 : Nat := 118140960795 + 591891 * 2 ^ 59
def prefixEnd_591891 : Nat := 4983230072969 + 3 ^ 40 * 591891 * 2
def baseEnd_591891 : Nat := 202616385380299304960299

theorem tailTrace_591891 : CollatzResearch.WordTrace tailWord_591891 prefixEnd_591891 202616385380299304960299 := by
  unfold tailWord_591891
  simp only [CollatzResearch.WordTrace]
  refine ⟨21588038298687468779967527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14392025532458312519978351 21588038298687468779967527)
  ·
    refine ⟨32382057448031203169951291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21588038298687468779967527 32382057448031203169951291)
    ·
      refine ⟨48573086172046804754926937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32382057448031203169951291 48573086172046804754926937)
      ·
        refine ⟨36429814629035103566195203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48573086172046804754926937 36429814629035103566195203)
        ·
          refine ⟨54644721943552655349292805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36429814629035103566195203 54644721943552655349292805)
          ·
            refine ⟨10245885364416122877992401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54644721943552655349292805 10245885364416122877992401)
            ·
              refine ⟨7684414023312092158494301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10245885364416122877992401 7684414023312092158494301)
              ·
                refine ⟨2881655258742034559435363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7684414023312092158494301 2881655258742034559435363)
                ·
                  refine ⟨4322482888113051839153045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2881655258742034559435363 4322482888113051839153045)
                  ·
                    refine ⟨202616385380299304960299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4322482888113051839153045 202616385380299304960299)
                    ·
                      rfl

theorem cell22_591891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 3, 1, 6].length) (baseStart_591891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_591891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_591891 prefixEnd_591891 := by exact prefixLift 591891
  have htrace : WordTrace (prefixWord ++ tailWord_591891) baseStart_591891 baseEnd_591891 := by
    simpa [prefixWord, tailWord_591891, baseEnd_591891] using wordTrace_append hprefix tailTrace_591891
  have hstable : (prefixWord ++ tailWord_591891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591891).length < 2 ^ (prefixWord ++ tailWord_591891).sum := by decide
  have hdescent : baseEnd_591891 < baseStart_591891 := by decide
  rcases family_descends (prefixWord ++ tailWord_591891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591951 : List Nat := [1, 1, 2, 1, 1, 2, 2, 3, 9]
def baseStart_591951 : Nat := 118140960795 + 591951 * 2 ^ 59
def prefixEnd_591951 : Nat := 4983230072969 + 3 ^ 40 * 591951 * 2
def baseEnd_591951 : Nat := 67545641535493049486705

theorem tailTrace_591951 : CollatzResearch.WordTrace tailWord_591951 prefixEnd_591951 67545641535493049486705 := by
  unfold tailWord_591951
  simp only [CollatzResearch.WordTrace]
  refine ⟨21590226678470099027151707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14393484452313399351434471 21590226678470099027151707)
  ·
    refine ⟨32385340017705148540727561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21590226678470099027151707 32385340017705148540727561)
    ·
      refine ⟨24289005013278861405545671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32385340017705148540727561 24289005013278861405545671)
      ·
        refine ⟨36433507519918292108318507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24289005013278861405545671 36433507519918292108318507)
        ·
          refine ⟨54650261279877438162477761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36433507519918292108318507 54650261279877438162477761)
          ·
            refine ⟨40987695959908078621858321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54650261279877438162477761 40987695959908078621858321)
            ·
              refine ⟨30740771969931058966393741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40987695959908078621858321 30740771969931058966393741)
              ·
                refine ⟨11527789488724147112397653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30740771969931058966393741 11527789488724147112397653)
                ·
                  refine ⟨67545641535493049486705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 11527789488724147112397653 67545641535493049486705)
                  ·
                    rfl

theorem cell22_591951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 9].length) (baseStart_591951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_591951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_591951 prefixEnd_591951 := by exact prefixLift 591951
  have htrace : WordTrace (prefixWord ++ tailWord_591951) baseStart_591951 baseEnd_591951 := by
    simpa [prefixWord, tailWord_591951, baseEnd_591951] using wordTrace_append hprefix tailTrace_591951
  have hstable : (prefixWord ++ tailWord_591951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591951).length < 2 ^ (prefixWord ++ tailWord_591951).sum := by decide
  have hdescent : baseEnd_591951 < baseStart_591951 := by decide
  rcases family_descends (prefixWord ++ tailWord_591951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591968 : List Nat := [2, 1, 1, 3, 2, 4, 1, 1, 7]
def baseStart_591968 : Nat := 118140960795 + 591968 * 2 ^ 59
def prefixEnd_591968 : Nat := 4983230072969 + 3 ^ 40 * 591968 * 2
def baseEnd_591968 : Nat := 67547581351298923595021

theorem tailTrace_591968 : CollatzResearch.WordTrace tailWord_591968 prefixEnd_591968 67547581351298923595021 := by
  unfold tailWord_591968
  simp only [CollatzResearch.WordTrace]
  refine ⟨10795423359704255465260279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14393897812939007287013705 10795423359704255465260279)
  ·
    refine ⟨16193135039556383197890419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10795423359704255465260279 16193135039556383197890419)
    ·
      refine ⟨24289702559334574796835629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16193135039556383197890419 24289702559334574796835629)
      ·
        refine ⟨9108638459750465548813361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24289702559334574796835629 9108638459750465548813361)
        ·
          refine ⟨6831478844812849161610021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9108638459750465548813361 6831478844812849161610021)
          ·
            refine ⟨1280902283402409217801879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6831478844812849161610021 1280902283402409217801879)
            ·
              refine ⟨1921353425103613826702819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1280902283402409217801879 1921353425103613826702819)
              ·
                refine ⟨2882030137655420740054229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1921353425103613826702819 2882030137655420740054229)
                ·
                  refine ⟨67547581351298923595021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2882030137655420740054229 67547581351298923595021)
                  ·
                    rfl

theorem cell22_591968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 1, 7].length) (baseStart_591968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_591968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_591968 prefixEnd_591968 := by exact prefixLift 591968
  have htrace : WordTrace (prefixWord ++ tailWord_591968) baseStart_591968 baseEnd_591968 := by
    simpa [prefixWord, tailWord_591968, baseEnd_591968] using wordTrace_append hprefix tailTrace_591968
  have hstable : (prefixWord ++ tailWord_591968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591968).length < 2 ^ (prefixWord ++ tailWord_591968).sum := by decide
  have hdescent : baseEnd_591968 < baseStart_591968 := by decide
  rcases family_descends (prefixWord ++ tailWord_591968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591972 : List Nat := [2, 3, 1, 1, 2, 1, 4, 4, 1, 3]
def baseStart_591972 : Nat := 118140960795 + 591972 * 2 ^ 59
def prefixEnd_591972 : Nat := 4983230072969 + 3 ^ 40 * 591972 * 2
def baseEnd_591972 : Nat := 202644113335642093685051

theorem tailTrace_591972 : CollatzResearch.WordTrace tailWord_591972 prefixEnd_591972 202644113335642093685051 := by
  unfold tailWord_591972
  simp only [CollatzResearch.WordTrace]
  refine ⟨10795496305697009806833085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14393995074262679742444113 10795496305697009806833085)
  ·
    refine ⟨4048311114636378677562407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10795496305697009806833085 4048311114636378677562407)
    ·
      refine ⟨6072466671954568016343611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4048311114636378677562407 6072466671954568016343611)
      ·
        refine ⟨9108700007931852024515417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6072466671954568016343611 9108700007931852024515417)
        ·
          refine ⟨6831525005948889018386563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9108700007931852024515417 6831525005948889018386563)
          ·
            refine ⟨10247287508923333527579845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6831525005948889018386563 10247287508923333527579845)
            ·
              refine ⟨1921366407923125036421221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10247287508923333527579845 1921366407923125036421221)
              ·
                refine ⟨360256201485585944328979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1921366407923125036421221 360256201485585944328979)
                ·
                  refine ⟨540384302228378916493469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 360256201485585944328979 540384302228378916493469)
                  ·
                    refine ⟨202644113335642093685051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 540384302228378916493469 202644113335642093685051)
                    ·
                      rfl

theorem cell22_591972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 4, 1, 3].length) (baseStart_591972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_591972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_591972 prefixEnd_591972 := by exact prefixLift 591972
  have htrace : WordTrace (prefixWord ++ tailWord_591972) baseStart_591972 baseEnd_591972 := by
    simpa [prefixWord, tailWord_591972, baseEnd_591972] using wordTrace_append hprefix tailTrace_591972
  have hstable : (prefixWord ++ tailWord_591972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591972).length < 2 ^ (prefixWord ++ tailWord_591972).sum := by decide
  have hdescent : baseEnd_591972 < baseStart_591972 := by decide
  rcases family_descends (prefixWord ++ tailWord_591972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591983 : List Nat := [1, 1, 2, 1, 3, 4, 2, 1, 2, 5]
def baseStart_591983 : Nat := 118140960795 + 591983 * 2 ^ 59
def prefixEnd_591983 : Nat := 4983230072969 + 3 ^ 40 * 591983 * 2
def baseEnd_591983 : Nat := 202647878860441731660017

theorem tailTrace_591983 : CollatzResearch.WordTrace tailWord_591983 prefixEnd_591983 202647878860441731660017 := by
  unfold tailWord_591983
  simp only [CollatzResearch.WordTrace]
  refine ⟨21591393814354168492316603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14394262542902778994877735 21591393814354168492316603)
  ·
    refine ⟨32387090721531252738474905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21591393814354168492316603 32387090721531252738474905)
    ·
      refine ⟨24290318041148439553856179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32387090721531252738474905 24290318041148439553856179)
      ·
        refine ⟨36435477061722659330784269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24290318041148439553856179 36435477061722659330784269)
        ·
          refine ⟨13663303898145997249044101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36435477061722659330784269 13663303898145997249044101)
          ·
            refine ⟨2561869480902374484195769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13663303898145997249044101 2561869480902374484195769)
            ·
              refine ⟨1921402110676780863146827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2561869480902374484195769 1921402110676780863146827)
              ·
                refine ⟨2882103166015171294720241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1921402110676780863146827 2882103166015171294720241)
                ·
                  refine ⟨2161577374511378471040181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2882103166015171294720241 2161577374511378471040181)
                  ·
                    refine ⟨202647878860441731660017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2161577374511378471040181 202647878860441731660017)
                    ·
                      rfl

theorem cell22_591983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 1, 2, 5].length) (baseStart_591983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_591983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_591983 prefixEnd_591983 := by exact prefixLift 591983
  have htrace : WordTrace (prefixWord ++ tailWord_591983) baseStart_591983 baseEnd_591983 := by
    simpa [prefixWord, tailWord_591983, baseEnd_591983] using wordTrace_append hprefix tailTrace_591983
  have hstable : (prefixWord ++ tailWord_591983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591983).length < 2 ^ (prefixWord ++ tailWord_591983).sum := by decide
  have hdescent : baseEnd_591983 < baseStart_591983 := by decide
  rcases family_descends (prefixWord ++ tailWord_591983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591985 : List Nat := [1, 2, 2, 2, 1, 1, 7, 1, 5]
def baseStart_591985 : Nat := 118140960795 + 591985 * 2 ^ 59
def prefixEnd_591985 : Nat := 4983230072969 + 3 ^ 40 * 591985 * 2
def baseEnd_591985 : Nat := 67549521167104797703337

theorem tailTrace_591985 : CollatzResearch.WordTrace tailWord_591985 prefixEnd_591985 67549521167104797703337 := by
  unfold tailWord_591985
  simp only [CollatzResearch.WordTrace]
  refine ⟨21591466760346922833889409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14394311173564615222592939 21591466760346922833889409)
  ·
    refine ⟨16193600070260192125417057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21591466760346922833889409 16193600070260192125417057)
    ·
      refine ⟨12145200052695144094062793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16193600070260192125417057 12145200052695144094062793)
      ·
        refine ⟨9108900039521358070547095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12145200052695144094062793 9108900039521358070547095)
        ·
          refine ⟨13663350059282037105820643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9108900039521358070547095 13663350059282037105820643)
          ·
            refine ⟨20495025088923055658730965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13663350059282037105820643 20495025088923055658730965)
            ·
              refine ⟨480352150521634117001507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 20495025088923055658730965 480352150521634117001507)
              ·
                refine ⟨720528225782451175502261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 480352150521634117001507 720528225782451175502261)
                ·
                  refine ⟨67549521167104797703337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 720528225782451175502261 67549521167104797703337)
                  ·
                    rfl

theorem cell22_591985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 7, 1, 5].length) (baseStart_591985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_591985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_591985 prefixEnd_591985 := by exact prefixLift 591985
  have htrace : WordTrace (prefixWord ++ tailWord_591985) baseStart_591985 baseEnd_591985 := by
    simpa [prefixWord, tailWord_591985, baseEnd_591985] using wordTrace_append hprefix tailTrace_591985
  have hstable : (prefixWord ++ tailWord_591985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591985).length < 2 ^ (prefixWord ++ tailWord_591985).sum := by decide
  have hdescent : baseEnd_591985 < baseStart_591985 := by decide
  rcases family_descends (prefixWord ++ tailWord_591985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592049 : List Nat := [1, 2, 2, 5, 2, 2, 1, 2, 1, 4]
def baseStart_592049 : Nat := 118140960795 + 592049 * 2 ^ 59
def prefixEnd_592049 : Nat := 4983230072969 + 3 ^ 40 * 592049 * 2
def baseEnd_592049 : Nat := 202670472009239559509815

theorem tailTrace_592049 : CollatzResearch.WordTrace tailWord_592049 prefixEnd_592049 202670472009239559509815 := by
  unfold tailWord_592049
  simp only [CollatzResearch.WordTrace]
  refine ⟨21593801032115061764219201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14395867354743374509479467 21593801032115061764219201)
  ·
    refine ⟨16195350774086296323164401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21593801032115061764219201 16195350774086296323164401)
    ·
      refine ⟨12146513080564722242373301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16195350774086296323164401 12146513080564722242373301)
      ·
        refine ⟨1138735601302942710222497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12146513080564722242373301 1138735601302942710222497)
        ·
          refine ⟨854051700977207032666873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1138735601302942710222497 854051700977207032666873)
          ·
            refine ⟨640538775732905274500155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 854051700977207032666873 640538775732905274500155)
            ·
              refine ⟨960808163599357911750233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 640538775732905274500155 960808163599357911750233)
              ·
                refine ⟨720606122699518433812675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 960808163599357911750233 720606122699518433812675)
                ·
                  refine ⟨1080909184049277650719013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 720606122699518433812675 1080909184049277650719013)
                  ·
                    refine ⟨202670472009239559509815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1080909184049277650719013 202670472009239559509815)
                    ·
                      rfl

theorem cell22_592049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 2, 1, 4].length) (baseStart_592049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_592049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_592049 prefixEnd_592049 := by exact prefixLift 592049
  have htrace : WordTrace (prefixWord ++ tailWord_592049) baseStart_592049 baseEnd_592049 := by
    simpa [prefixWord, tailWord_592049, baseEnd_592049] using wordTrace_append hprefix tailTrace_592049
  have hstable : (prefixWord ++ tailWord_592049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592049).length < 2 ^ (prefixWord ++ tailWord_592049).sum := by decide
  have hdescent : baseEnd_592049 < baseStart_592049 := by decide
  rcases family_descends (prefixWord ++ tailWord_592049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592058 : List Nat := [3, 1, 1, 1, 2, 2, 4, 8]
def baseStart_592058 : Nat := 118140960795 + 592058 * 2 ^ 59
def prefixEnd_592058 : Nat := 4983230072969 + 3 ^ 40 * 592058 * 2
def baseEnd_592058 : Nat := 22519283654796281781643

theorem tailTrace_592058 : CollatzResearch.WordTrace tailWord_592058 prefixEnd_592058 22519283654796281781643 := by
  unfold tailWord_592058
  simp only [CollatzResearch.WordTrace]
  refine ⟨5398532322270614075324207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14396086192721637534197885 5398532322270614075324207)
  ·
    refine ⟨8097798483405921112986311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5398532322270614075324207 8097798483405921112986311)
    ·
      refine ⟨12146697725108881669479467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8097798483405921112986311 12146697725108881669479467)
      ·
        refine ⟨18220046587663322504219201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12146697725108881669479467 18220046587663322504219201)
        ·
          refine ⟨13665034940747491878164401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18220046587663322504219201 13665034940747491878164401)
          ·
            refine ⟨10248776205560618908623301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13665034940747491878164401 10248776205560618908623301)
            ·
              refine ⟨1921645538542616045366869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10248776205560618908623301 1921645538542616045366869)
              ·
                refine ⟨22519283654796281781643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1921645538542616045366869 22519283654796281781643)
                ·
                  rfl

theorem cell22_592058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 8].length) (baseStart_592058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_592058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_592058 prefixEnd_592058 := by exact prefixLift 592058
  have htrace : WordTrace (prefixWord ++ tailWord_592058) baseStart_592058 baseEnd_592058 := by
    simpa [prefixWord, tailWord_592058, baseEnd_592058] using wordTrace_append hprefix tailTrace_592058
  have hstable : (prefixWord ++ tailWord_592058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592058).length < 2 ^ (prefixWord ++ tailWord_592058).sum := by decide
  have hdescent : baseEnd_592058 < baseStart_592058 := by decide
  rcases family_descends (prefixWord ++ tailWord_592058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592062 : List Nat := [4, 2, 1, 1, 4, 1, 1, 2, 1, 5]
def baseStart_592062 : Nat := 118140960795 + 592062 * 2 ^ 59
def prefixEnd_592062 : Nat := 4983230072969 + 3 ^ 40 * 592062 * 2
def baseEnd_592062 : Nat := 202674922174911858934775

theorem tailTrace_592062 : CollatzResearch.WordTrace tailWord_592062 prefixEnd_592062 202674922174911858934775 := by
  unfold tailWord_592062
  simp only [CollatzResearch.WordTrace]
  refine ⟨2699284397633495623055305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14396183454045309989628293 2699284397633495623055305)
  ·
    refine ⟨2024463298225121717291479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2699284397633495623055305 2024463298225121717291479)
    ·
      refine ⟨3036694947337682575937219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2024463298225121717291479 3036694947337682575937219)
      ·
        refine ⟨4555042421006523863905829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3036694947337682575937219 4555042421006523863905829)
        ·
          refine ⟨854070453938723224482343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4555042421006523863905829 854070453938723224482343)
          ·
            refine ⟨1281105680908084836723515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 854070453938723224482343 1281105680908084836723515)
            ·
              refine ⟨1921658521362127255085273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1281105680908084836723515 1921658521362127255085273)
              ·
                refine ⟨1441243891021595441313955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1921658521362127255085273 1441243891021595441313955)
                ·
                  refine ⟨2161865836532393161970933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1441243891021595441313955 2161865836532393161970933)
                  ·
                    refine ⟨202674922174911858934775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2161865836532393161970933 202674922174911858934775)
                    ·
                      rfl

theorem cell22_592062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_592062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_592062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_592062 prefixEnd_592062 := by exact prefixLift 592062
  have htrace : WordTrace (prefixWord ++ tailWord_592062) baseStart_592062 baseEnd_592062 := by
    simpa [prefixWord, tailWord_592062, baseEnd_592062] using wordTrace_append hprefix tailTrace_592062
  have hstable : (prefixWord ++ tailWord_592062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592062).length < 2 ^ (prefixWord ++ tailWord_592062).sum := by decide
  have hdescent : baseEnd_592062 < baseStart_592062 := by decide
  rcases family_descends (prefixWord ++ tailWord_592062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592124 : List Nat := [2, 2, 2, 1, 4, 1, 1, 5, 1, 3]
def baseStart_592124 : Nat := 118140960795 + 592124 * 2 ^ 59
def prefixEnd_592124 : Nat := 4983230072969 + 3 ^ 40 * 592124 * 2
def baseEnd_592124 : Nat := 202696146041964363884585

theorem tailTrace_592124 : CollatzResearch.WordTrace tailWord_592124 prefixEnd_592124 202696146041964363884585 := by
  unfold tailWord_592124
  simp only [CollatzResearch.WordTrace]
  refine ⟨10798268253421674786599713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14397691004562233048799617 10798268253421674786599713)
  ·
    refine ⟨8098701190066256089949785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10798268253421674786599713 8098701190066256089949785)
    ·
      refine ⟨6074025892549692067462339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8098701190066256089949785 6074025892549692067462339)
      ·
        refine ⟨9111038838824538101193509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6074025892549692067462339 9111038838824538101193509)
        ·
          refine ⟨1708319782279600893973783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9111038838824538101193509 1708319782279600893973783)
          ·
            refine ⟨2562479673419401340960675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1708319782279600893973783 2562479673419401340960675)
            ·
              refine ⟨3843719510129102011441013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2562479673419401340960675 3843719510129102011441013)
              ·
                refine ⟨360348704074603313572595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3843719510129102011441013 360348704074603313572595)
                ·
                  refine ⟨540523056111904970358893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 360348704074603313572595 540523056111904970358893)
                  ·
                    refine ⟨202696146041964363884585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 540523056111904970358893 202696146041964363884585)
                    ·
                      rfl

theorem cell22_592124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 5, 1, 3].length) (baseStart_592124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_592124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_592124 prefixEnd_592124 := by exact prefixLift 592124
  have htrace : WordTrace (prefixWord ++ tailWord_592124) baseStart_592124 baseEnd_592124 := by
    simpa [prefixWord, tailWord_592124, baseEnd_592124] using wordTrace_append hprefix tailTrace_592124
  have hstable : (prefixWord ++ tailWord_592124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592124).length < 2 ^ (prefixWord ++ tailWord_592124).sum := by decide
  have hdescent : baseEnd_592124 < baseStart_592124 := by decide
  rcases family_descends (prefixWord ++ tailWord_592124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592137 : List Nat := [1, 2, 1, 1, 3, 6, 1, 2, 5]
def baseStart_592137 : Nat := 118140960795 + 592137 * 2 ^ 59
def prefixEnd_592137 : Nat := 4983230072969 + 3 ^ 40 * 592137 * 2
def baseEnd_592137 : Nat := 67566865402545554436515

theorem tailTrace_592137 : CollatzResearch.WordTrace tailWord_592137 prefixEnd_592137 67566865402545554436515 := by
  unfold tailWord_592137
  simp only [CollatzResearch.WordTrace]
  refine ⟨21597010655796252793422665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14398007103864168528948443 21597010655796252793422665)
  ·
    refine ⟨16197757991847189595066999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21597010655796252793422665 16197757991847189595066999)
    ·
      refine ⟨24296636987770784392600499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16197757991847189595066999 24296636987770784392600499)
      ·
        refine ⟨36444955481656176588900749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24296636987770784392600499 36444955481656176588900749)
        ·
          refine ⟨13666858305621066220837781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36444955481656176588900749 13666858305621066220837781)
          ·
            refine ⟨640633983075987479101771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 13666858305621066220837781 640633983075987479101771)
            ·
              refine ⟨960950974613981218652657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 640633983075987479101771 960950974613981218652657)
              ·
                refine ⟨720713230960485913989493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 960950974613981218652657 720713230960485913989493)
                ·
                  refine ⟨67566865402545554436515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 720713230960485913989493 67566865402545554436515)
                  ·
                    rfl

theorem cell22_592137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 2, 5].length) (baseStart_592137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_592137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_592137 prefixEnd_592137 := by exact prefixLift 592137
  have htrace : WordTrace (prefixWord ++ tailWord_592137) baseStart_592137 baseEnd_592137 := by
    simpa [prefixWord, tailWord_592137, baseEnd_592137] using wordTrace_append hprefix tailTrace_592137
  have hstable : (prefixWord ++ tailWord_592137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592137).length < 2 ^ (prefixWord ++ tailWord_592137).sum := by decide
  have hdescent : baseEnd_592137 < baseStart_592137 := by decide
  rcases family_descends (prefixWord ++ tailWord_592137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592154 : List Nat := [3, 1, 1, 3, 4, 1, 3, 1, 5]
def baseStart_592154 : Nat := 118140960795 + 592154 * 2 ^ 59
def prefixEnd_592154 : Nat := 4983230072969 + 3 ^ 40 * 592154 * 2
def baseEnd_592154 : Nat := 67568805218351428544831

theorem tailTrace_592154 : CollatzResearch.WordTrace tailWord_592154 prefixEnd_592154 67568805218351428544831 := by
  unfold tailWord_592154
  simp only [CollatzResearch.WordTrace]
  refine ⟨5399407674183666174197879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14398420464489776464527677 5399407674183666174197879)
  ·
    refine ⟨8099111511275499261296819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5399407674183666174197879 8099111511275499261296819)
    ·
      refine ⟨12148667266913248891945229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8099111511275499261296819 12148667266913248891945229)
      ·
        refine ⟨4555750225092468334479461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12148667266913248891945229 4555750225092468334479461)
        ·
          refine ⟨854203167204837812714899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4555750225092468334479461 854203167204837812714899)
          ·
            refine ⟨1281304750807256719072349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 854203167204837812714899 1281304750807256719072349)
            ·
              refine ⟨480489281552721269652131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1281304750807256719072349 480489281552721269652131)
              ·
                refine ⟨720733922329081904478197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 480489281552721269652131 720733922329081904478197)
                ·
                  refine ⟨67568805218351428544831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 720733922329081904478197 67568805218351428544831)
                  ·
                    rfl

theorem cell22_592154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 3, 1, 5].length) (baseStart_592154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_592154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_592154 prefixEnd_592154 := by exact prefixLift 592154
  have htrace : WordTrace (prefixWord ++ tailWord_592154) baseStart_592154 baseEnd_592154 := by
    simpa [prefixWord, tailWord_592154, baseEnd_592154] using wordTrace_append hprefix tailTrace_592154
  have hstable : (prefixWord ++ tailWord_592154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592154).length < 2 ^ (prefixWord ++ tailWord_592154).sum := by decide
  have hdescent : baseEnd_592154 < baseStart_592154 := by decide
  rcases family_descends (prefixWord ++ tailWord_592154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592195 : List Nat := [1, 1, 1, 3, 1, 3, 3, 1, 4, 4]
def baseStart_592195 : Nat := 118140960795 + 592195 * 2 ^ 59
def prefixEnd_592195 : Nat := 4983230072969 + 3 ^ 40 * 592195 * 2
def baseEnd_592195 : Nat := 202720450792943845359367

theorem tailTrace_592195 : CollatzResearch.WordTrace tailWord_592195 prefixEnd_592195 202720450792943845359367 := by
  unfold tailWord_592195
  simp only [CollatzResearch.WordTrace]
  refine ⟨21599126089586128699034039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14399417393057419132689359 21599126089586128699034039)
  ·
    refine ⟨32398689134379193048551059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21599126089586128699034039 32398689134379193048551059)
    ·
      refine ⟨48598033701568789572826589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32398689134379193048551059 48598033701568789572826589)
      ·
        refine ⟨18224262638088296089809971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48598033701568789572826589 18224262638088296089809971)
        ·
          refine ⟨27336393957132444134714957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18224262638088296089809971 27336393957132444134714957)
          ·
            refine ⟨10251147733924666550518109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27336393957132444134714957 10251147733924666550518109)
            ·
              refine ⟨3844180400221749956444291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10251147733924666550518109 3844180400221749956444291)
              ·
                refine ⟨5766270600332624934666437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3844180400221749956444291 5766270600332624934666437)
                ·
                  refine ⟨1081175737562367175249957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5766270600332624934666437 1081175737562367175249957)
                  ·
                    refine ⟨202720450792943845359367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1081175737562367175249957 202720450792943845359367)
                    ·
                      rfl

theorem cell22_592195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 4, 4].length) (baseStart_592195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_592195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_592195 prefixEnd_592195 := by exact prefixLift 592195
  have htrace : WordTrace (prefixWord ++ tailWord_592195) baseStart_592195 baseEnd_592195 := by
    simpa [prefixWord, tailWord_592195, baseEnd_592195] using wordTrace_append hprefix tailTrace_592195
  have hstable : (prefixWord ++ tailWord_592195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592195).length < 2 ^ (prefixWord ++ tailWord_592195).sum := by decide
  have hdescent : baseEnd_592195 < baseStart_592195 := by decide
  rcases family_descends (prefixWord ++ tailWord_592195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592199 : List Nat := [1, 1, 4, 1, 2, 2, 5, 2, 4]
def baseStart_592199 : Nat := 118140960795 + 592199 * 2 ^ 59
def prefixEnd_592199 : Nat := 4983230072969 + 3 ^ 40 * 592199 * 2
def baseEnd_592199 : Nat := 67573940024896389419785

theorem tailTrace_592199 : CollatzResearch.WordTrace tailWord_592199 prefixEnd_592199 67573940024896389419785 := by
  unfold tailWord_592199
  simp only [CollatzResearch.WordTrace]
  refine ⟨21599271981571637382179651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14399514654381091588119767 21599271981571637382179651)
  ·
    refine ⟨32398907972357456073269477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21599271981571637382179651 32398907972357456073269477)
    ·
      refine ⟨6074795244817023013738027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32398907972357456073269477 6074795244817023013738027)
      ·
        refine ⟨9112192867225534520607041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6074795244817023013738027 9112192867225534520607041)
        ·
          refine ⟨6834144650419150890455281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9112192867225534520607041 6834144650419150890455281)
          ·
            refine ⟨5125608487814363167841461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6834144650419150890455281 5125608487814363167841461)
            ·
              refine ⟨480525795732596546985137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5125608487814363167841461 480525795732596546985137)
              ·
                refine ⟨360394346799447410238853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 480525795732596546985137 360394346799447410238853)
                ·
                  refine ⟨67573940024896389419785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 360394346799447410238853 67573940024896389419785)
                  ·
                    rfl

theorem cell22_592199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 5, 2, 4].length) (baseStart_592199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_592199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_592199 prefixEnd_592199 := by exact prefixLift 592199
  have htrace : WordTrace (prefixWord ++ tailWord_592199) baseStart_592199 baseEnd_592199 := by
    simpa [prefixWord, tailWord_592199, baseEnd_592199] using wordTrace_append hprefix tailTrace_592199
  have hstable : (prefixWord ++ tailWord_592199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592199).length < 2 ^ (prefixWord ++ tailWord_592199).sum := by decide
  have hdescent : baseEnd_592199 < baseStart_592199 := by decide
  rcases family_descends (prefixWord ++ tailWord_592199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592210 : List Nat := [3, 2, 2, 1, 1, 1, 3, 9]
def baseStart_592210 : Nat := 118140960795 + 592210 * 2 ^ 59
def prefixEnd_592210 : Nat := 4983230072969 + 3 ^ 40 * 592210 * 2
def baseEnd_592210 : Nat := 22525065066609867359369

theorem tailTrace_592210 : CollatzResearch.WordTrace tailWord_592210 prefixEnd_592210 22525065066609867359369 := by
  unfold tailWord_592210
  simp only [CollatzResearch.WordTrace]
  refine ⟨5399918296132946565207521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14399782123021190840553389 5399918296132946565207521)
  ·
    refine ⟨4049938722099709923905641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5399918296132946565207521 4049938722099709923905641)
    ·
      refine ⟨3037454041574782442929231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4049938722099709923905641 3037454041574782442929231)
      ·
        refine ⟨4556181062362173664393847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3037454041574782442929231 4556181062362173664393847)
        ·
          refine ⟨6834271593543260496590771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4556181062362173664393847 6834271593543260496590771)
          ·
            refine ⟨10251407390314890744886157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6834271593543260496590771 10251407390314890744886157)
            ·
              refine ⟨3844277771368084029332309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10251407390314890744886157 3844277771368084029332309)
              ·
                refine ⟨22525065066609867359369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3844277771368084029332309 22525065066609867359369)
                ·
                  rfl

theorem cell22_592210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 9].length) (baseStart_592210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_592210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_592210 prefixEnd_592210 := by exact prefixLift 592210
  have htrace : WordTrace (prefixWord ++ tailWord_592210) baseStart_592210 baseEnd_592210 := by
    simpa [prefixWord, tailWord_592210, baseEnd_592210] using wordTrace_append hprefix tailTrace_592210
  have hstable : (prefixWord ++ tailWord_592210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592210).length < 2 ^ (prefixWord ++ tailWord_592210).sum := by decide
  have hdescent : baseEnd_592210 < baseStart_592210 := by decide
  rcases family_descends (prefixWord ++ tailWord_592210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592257 : List Nat := [1, 2, 4, 3, 1, 1, 1, 1, 2, 6]
def baseStart_592257 : Nat := 118140960795 + 592257 * 2 ^ 59
def prefixEnd_592257 : Nat := 4983230072969 + 3 ^ 40 * 592257 * 2
def baseEnd_592257 : Nat := 202741674659996350309177

theorem tailTrace_592257 : CollatzResearch.WordTrace tailWord_592257 prefixEnd_592257 202741674659996350309177 := by
  unfold tailWord_592257
  simp only [CollatzResearch.WordTrace]
  refine ⟨21601387415361513287791025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14400924943574342191860683 21601387415361513287791025)
  ·
    refine ⟨16201040561521134965843269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21601387415361513287791025 16201040561521134965843269)
    ·
      refine ⟨3037695105285212806095613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16201040561521134965843269 3037695105285212806095613)
      ·
        refine ⟨1139135664481954802285855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3037695105285212806095613 1139135664481954802285855)
        ·
          refine ⟨1708703496722932203428783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1139135664481954802285855 1708703496722932203428783)
          ·
            refine ⟨2563055245084398305143175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1708703496722932203428783 2563055245084398305143175)
            ·
              refine ⟨3844582867626597457714763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2563055245084398305143175 3844582867626597457714763)
              ·
                refine ⟨5766874301439896186572145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3844582867626597457714763 5766874301439896186572145)
                ·
                  refine ⟨4325155726079922139929109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5766874301439896186572145 4325155726079922139929109)
                  ·
                    refine ⟨202741674659996350309177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4325155726079922139929109 202741674659996350309177)
                    ·
                      rfl

theorem cell22_592257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_592257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_592257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_592257 prefixEnd_592257 := by exact prefixLift 592257
  have htrace : WordTrace (prefixWord ++ tailWord_592257) baseStart_592257 baseEnd_592257 := by
    simpa [prefixWord, tailWord_592257, baseEnd_592257] using wordTrace_append hprefix tailTrace_592257
  have hstable : (prefixWord ++ tailWord_592257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592257).length < 2 ^ (prefixWord ++ tailWord_592257).sum := by decide
  have hdescent : baseEnd_592257 < baseStart_592257 := by decide
  rcases family_descends (prefixWord ++ tailWord_592257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592276 : List Nat := [2, 4, 2, 1, 3, 1, 1, 2, 3, 3]
def baseStart_592276 : Nat := 118140960795 + 592276 * 2 ^ 59
def prefixEnd_592276 : Nat := 4983230072969 + 3 ^ 40 * 592276 * 2
def baseEnd_592276 : Nat := 202748178748286634084119

theorem tailTrace_592276 : CollatzResearch.WordTrace tailWord_592276 prefixEnd_592276 202748178748286634084119 := by
  unfold tailWord_592276
  simp only [CollatzResearch.WordTrace]
  refine ⟨10801040201146339766366341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14401386934861786355155121 10801040201146339766366341)
  ·
    refine ⟨2025195037714938706193689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10801040201146339766366341 2025195037714938706193689)
    ·
      refine ⟨1518896278286204029645267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2025195037714938706193689 1518896278286204029645267)
      ·
        refine ⟨2278344417429306044467901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1518896278286204029645267 2278344417429306044467901)
        ·
          refine ⟨854379156535989766675463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2278344417429306044467901 854379156535989766675463)
          ·
            refine ⟨1281568734803984650013195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 854379156535989766675463 1281568734803984650013195)
            ·
              refine ⟨1922353102205976975019793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1281568734803984650013195 1922353102205976975019793)
              ·
                refine ⟨1441764826654482731264845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1922353102205976975019793 1441764826654482731264845)
                ·
                  refine ⟨540661809995431024224317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1441764826654482731264845 540661809995431024224317)
                  ·
                    refine ⟨202748178748286634084119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 540661809995431024224317 202748178748286634084119)
                    ·
                      rfl

theorem cell22_592276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_592276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_592276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_592276 prefixEnd_592276 := by exact prefixLift 592276
  have htrace : WordTrace (prefixWord ++ tailWord_592276) baseStart_592276 baseEnd_592276 := by
    simpa [prefixWord, tailWord_592276, baseEnd_592276] using wordTrace_append hprefix tailTrace_592276
  have hstable : (prefixWord ++ tailWord_592276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592276).length < 2 ^ (prefixWord ++ tailWord_592276).sum := by decide
  have hdescent : baseEnd_592276 < baseStart_592276 := by decide
  rcases family_descends (prefixWord ++ tailWord_592276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592300 : List Nat := [2, 2, 1, 1, 1, 1, 3, 1, 10]
def baseStart_592300 : Nat := 118140960795 + 592300 * 2 ^ 59
def prefixEnd_592300 : Nat := 4983230072969 + 3 ^ 40 * 592300 * 2
def baseEnd_592300 : Nat := 67585464812919523828015

theorem tailTrace_592300 : CollatzResearch.WordTrace tailWord_592300 prefixEnd_592300 67585464812919523828015 := by
  unfold tailWord_592300
  simp only [CollatzResearch.WordTrace]
  refine ⟨10801477877102865815803177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14401970502803821087737569 10801477877102865815803177)
  ·
    refine ⟨8101108407827149361852383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10801477877102865815803177 8101108407827149361852383)
    ·
      refine ⟨12151662611740724042778575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8101108407827149361852383 12151662611740724042778575)
      ·
        refine ⟨18227493917611086064167863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12151662611740724042778575 18227493917611086064167863)
        ·
          refine ⟨27341240876416629096251795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18227493917611086064167863 27341240876416629096251795)
          ·
            refine ⟨41011861314624943644377693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27341240876416629096251795 41011861314624943644377693)
            ·
              refine ⟨15379447992984353866641635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41011861314624943644377693 15379447992984353866641635)
              ·
                refine ⟨23069171989476530799962453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15379447992984353866641635 23069171989476530799962453)
                ·
                  refine ⟨67585464812919523828015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 23069171989476530799962453 67585464812919523828015)
                  ·
                    rfl

theorem cell22_592300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 10].length) (baseStart_592300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_592300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_592300 prefixEnd_592300 := by exact prefixLift 592300
  have htrace : WordTrace (prefixWord ++ tailWord_592300) baseStart_592300 baseEnd_592300 := by
    simpa [prefixWord, tailWord_592300, baseEnd_592300] using wordTrace_append hprefix tailTrace_592300
  have hstable : (prefixWord ++ tailWord_592300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592300).length < 2 ^ (prefixWord ++ tailWord_592300).sum := by decide
  have hdescent : baseEnd_592300 < baseStart_592300 := by decide
  rcases family_descends (prefixWord ++ tailWord_592300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592317 : List Nat := [1, 4, 1, 2, 2, 2, 1, 3, 6]
def baseStart_592317 : Nat := 118140960795 + 592317 * 2 ^ 59
def prefixEnd_592317 : Nat := 4983230072969 + 3 ^ 40 * 592317 * 2
def baseEnd_592317 : Nat := 67587404628725397936331

theorem tailTrace_592317 : CollatzResearch.WordTrace tailWord_592317 prefixEnd_592317 67587404628725397936331 := by
  unfold tailWord_592317
  simp only [CollatzResearch.WordTrace]
  refine ⟨21603575795144143534975205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14402383863429429023316803 21603575795144143534975205)
  ·
    refine ⟨4050670461589526912807851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21603575795144143534975205 4050670461589526912807851)
    ·
      refine ⟨6076005692384290369211777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4050670461589526912807851 6076005692384290369211777)
      ·
        refine ⟨4557004269288217776908833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6076005692384290369211777 4557004269288217776908833)
        ·
          refine ⟨3417753201966163332681625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4557004269288217776908833 3417753201966163332681625)
          ·
            refine ⟨2563314901474622499511219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3417753201966163332681625 2563314901474622499511219)
            ·
              refine ⟨3844972352211933749266829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2563314901474622499511219 3844972352211933749266829)
              ·
                refine ⟨1441864632079475155975061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3844972352211933749266829 1441864632079475155975061)
                ·
                  refine ⟨67587404628725397936331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1441864632079475155975061 67587404628725397936331)
                  ·
                    rfl

theorem cell22_592317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 3, 6].length) (baseStart_592317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_592317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_592317 prefixEnd_592317 := by exact prefixLift 592317
  have htrace : WordTrace (prefixWord ++ tailWord_592317) baseStart_592317 baseEnd_592317 := by
    simpa [prefixWord, tailWord_592317, baseEnd_592317] using wordTrace_append hprefix tailTrace_592317
  have hstable : (prefixWord ++ tailWord_592317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592317).length < 2 ^ (prefixWord ++ tailWord_592317).sum := by decide
  have hdescent : baseEnd_592317 < baseStart_592317 := by decide
  rcases family_descends (prefixWord ++ tailWord_592317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592349 : List Nat := [1, 4, 3, 1, 1, 1, 1, 1, 6, 3]
def baseStart_592349 : Nat := 118140960795 + 592349 * 2 ^ 59
def prefixEnd_592349 : Nat := 4983230072969 + 3 ^ 40 * 592349 * 2
def baseEnd_592349 : Nat := 202773168140138777008895

theorem tailTrace_592349 : CollatzResearch.WordTrace tailWord_592349 prefixEnd_592349 202773168140138777008895 := by
  unfold tailWord_592349
  simp only [CollatzResearch.WordTrace]
  refine ⟨21604742931028213000140101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14403161954018808666760067 21604742931028213000140101)
  ·
    refine ⟨4050889299567789937526269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21604742931028213000140101 4050889299567789937526269)
    ·
      refine ⟨1519083487337921226572351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4050889299567789937526269 1519083487337921226572351)
      ·
        refine ⟨2278625231006881839858527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1519083487337921226572351 2278625231006881839858527)
        ·
          refine ⟨3417937846510322759787791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2278625231006881839858527 3417937846510322759787791)
          ·
            refine ⟨5126906769765484139681687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3417937846510322759787791 5126906769765484139681687)
            ·
              refine ⟨7690360154648226209522531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5126906769765484139681687 7690360154648226209522531)
              ·
                refine ⟨11535540231972339314283797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7690360154648226209522531 11535540231972339314283797)
                ·
                  refine ⟨540728448373703405357053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 11535540231972339314283797 540728448373703405357053)
                  ·
                    refine ⟨202773168140138777008895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 540728448373703405357053 202773168140138777008895)
                    ·
                      rfl

theorem cell22_592349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_592349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_592349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_592349 prefixEnd_592349 := by exact prefixLift 592349
  have htrace : WordTrace (prefixWord ++ tailWord_592349) baseStart_592349 baseEnd_592349 := by
    simpa [prefixWord, tailWord_592349, baseEnd_592349] using wordTrace_append hprefix tailTrace_592349
  have hstable : (prefixWord ++ tailWord_592349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592349).length < 2 ^ (prefixWord ++ tailWord_592349).sum := by decide
  have hdescent : baseEnd_592349 < baseStart_592349 := by decide
  rcases family_descends (prefixWord ++ tailWord_592349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592351 : List Nat := [1, 1, 2, 3, 3, 4, 1, 3, 4]
def baseStart_592351 : Nat := 118140960795 + 592351 * 2 ^ 59
def prefixEnd_592351 : Nat := 4983230072969 + 3 ^ 40 * 592351 * 2
def baseEnd_592351 : Nat := 67591284260337146152963

theorem tailTrace_592351 : CollatzResearch.WordTrace tailWord_592351 prefixEnd_592351 67591284260337146152963 := by
  unfold tailWord_592351
  simp only [CollatzResearch.WordTrace]
  refine ⟨21604815877020967341712907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14403210584680644894475271 21604815877020967341712907)
  ·
    refine ⟨32407223815531451012569361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21604815877020967341712907 32407223815531451012569361)
    ·
      refine ⟨24305417861648588259427021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32407223815531451012569361 24305417861648588259427021)
      ·
        refine ⟨9114531698118220597285133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24305417861648588259427021 9114531698118220597285133)
        ·
          refine ⟨3417949386794332723981925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9114531698118220597285133 3417949386794332723981925)
          ·
            refine ⟨640865510023937385746611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3417949386794332723981925 640865510023937385746611)
            ·
              refine ⟨961298265035906078619917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 640865510023937385746611 961298265035906078619917)
              ·
                refine ⟨360486849388464779482469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 961298265035906078619917 360486849388464779482469)
                ·
                  refine ⟨67591284260337146152963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 360486849388464779482469 67591284260337146152963)
                  ·
                    rfl

theorem cell22_592351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 3, 4].length) (baseStart_592351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_592351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_592351 prefixEnd_592351 := by exact prefixLift 592351
  have htrace : WordTrace (prefixWord ++ tailWord_592351) baseStart_592351 baseEnd_592351 := by
    simpa [prefixWord, tailWord_592351, baseEnd_592351] using wordTrace_append hprefix tailTrace_592351
  have hstable : (prefixWord ++ tailWord_592351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592351).length < 2 ^ (prefixWord ++ tailWord_592351).sum := by decide
  have hdescent : baseEnd_592351 < baseStart_592351 := by decide
  rcases family_descends (prefixWord ++ tailWord_592351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592362 : List Nat := [3, 1, 3, 1, 3, 1, 10]
def baseStart_592362 : Nat := 118140960795 + 592362 * 2 ^ 59
def prefixEnd_592362 : Nat := 4983230072969 + 3 ^ 40 * 592362 * 2
def baseEnd_592362 : Nat := 7510282159474484312365

theorem tailTrace_592362 : CollatzResearch.WordTrace tailWord_592362 prefixEnd_592362 7510282159474484312365 := by
  unfold tailWord_592362
  simp only [CollatzResearch.WordTrace]
  refine ⟨5401304269995279055090835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14403478053320744146908893 5401304269995279055090835)
  ·
    refine ⟨8101956404992918582636253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5401304269995279055090835 8101956404992918582636253)
    ·
      refine ⟨3038233651872344468488595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8101956404992918582636253 3038233651872344468488595)
      ·
        refine ⟨4557350477808516702732893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3038233651872344468488595 4557350477808516702732893)
        ·
          refine ⟨1709006429178193763524835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4557350477808516702732893 1709006429178193763524835)
          ·
            refine ⟨2563509643767290645287253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1709006429178193763524835 2563509643767290645287253)
            ·
              refine ⟨7510282159474484312365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2563509643767290645287253 7510282159474484312365)
              ·
                rfl

theorem cell22_592362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 10].length) (baseStart_592362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_592362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_592362 prefixEnd_592362 := by exact prefixLift 592362
  have htrace : WordTrace (prefixWord ++ tailWord_592362) baseStart_592362 baseEnd_592362 := by
    simpa [prefixWord, tailWord_592362, baseEnd_592362] using wordTrace_append hprefix tailTrace_592362
  have hstable : (prefixWord ++ tailWord_592362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592362).length < 2 ^ (prefixWord ++ tailWord_592362).sum := by decide
  have hdescent : baseEnd_592362 < baseStart_592362 := by decide
  rcases family_descends (prefixWord ++ tailWord_592362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592394 : List Nat := [3, 1, 2, 2, 2, 1, 2, 1, 5, 3]
def baseStart_592394 : Nat := 118140960795 + 592394 * 2 ^ 59
def prefixEnd_592394 : Nat := 4983230072969 + 3 ^ 40 * 592394 * 2
def baseEnd_592394 : Nat := 202788572559773659633757

theorem tailTrace_592394 : CollatzResearch.WordTrace tailWord_592394 prefixEnd_592394 202788572559773659633757 := by
  unfold tailWord_592394
  simp only [CollatzResearch.WordTrace]
  refine ⟨5401596053966296421382059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14404256143910123790352157 5401596053966296421382059)
  ·
    refine ⟨8102394080949444632073089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5401596053966296421382059 8102394080949444632073089)
    ·
      refine ⟨6076795560712083474054817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8102394080949444632073089 6076795560712083474054817)
      ·
        refine ⟨4557596670534062605541113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6076795560712083474054817 4557596670534062605541113)
        ·
          refine ⟨3418197502900546954155835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4557596670534062605541113 3418197502900546954155835)
          ·
            refine ⟨5127296254350820431233753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3418197502900546954155835 5127296254350820431233753)
            ·
              refine ⟨3845472190763115323425315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5127296254350820431233753 3845472190763115323425315)
              ·
                refine ⟨5768208286144672985137973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3845472190763115323425315 5768208286144672985137973)
                ·
                  refine ⟨540769526826063092356685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5768208286144672985137973 540769526826063092356685)
                  ·
                    refine ⟨202788572559773659633757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 540769526826063092356685 202788572559773659633757)
                    ·
                      rfl

theorem cell22_592394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 5, 3].length) (baseStart_592394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_592394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_592394 prefixEnd_592394 := by exact prefixLift 592394
  have htrace : WordTrace (prefixWord ++ tailWord_592394) baseStart_592394 baseEnd_592394 := by
    simpa [prefixWord, tailWord_592394, baseEnd_592394] using wordTrace_append hprefix tailTrace_592394
  have hstable : (prefixWord ++ tailWord_592394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592394).length < 2 ^ (prefixWord ++ tailWord_592394).sum := by decide
  have hdescent : baseEnd_592394 < baseStart_592394 := by decide
  rcases family_descends (prefixWord ++ tailWord_592394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592597 : List Nat := [1, 3, 2, 5, 1, 1, 1, 4, 1, 3]
def baseStart_592597 : Nat := 118140960795 + 592597 * 2 ^ 59
def prefixEnd_592597 : Nat := 4983230072969 + 3 ^ 40 * 592597 * 2
def baseEnd_592597 : Nat := 202858063608348796808135

theorem tailTrace_592597 : CollatzResearch.WordTrace tailWord_592597 prefixEnd_592597 202858063608348796808135 := by
  unfold tailWord_592597
  simp only [CollatzResearch.WordTrace]
  refine ⟨21613788234129751355168045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14409192156086500903445363 21613788234129751355168045)
  ·
    refine ⟨8105170587798656758188017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21613788234129751355168045 8105170587798656758188017)
    ·
      refine ⟨6078877940848992568641013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8105170587798656758188017 6078877940848992568641013)
      ·
        refine ⟨569894806954593053310095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6078877940848992568641013 569894806954593053310095)
        ·
          refine ⟨854842210431889579965143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 569894806954593053310095 854842210431889579965143)
          ·
            refine ⟨1282263315647834369947715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 854842210431889579965143 1282263315647834369947715)
            ·
              refine ⟨1923394973471751554921573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1282263315647834369947715 1923394973471751554921573)
              ·
                refine ⟨360636557525953416547795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1923394973471751554921573 360636557525953416547795)
                ·
                  refine ⟨540954836288930124821693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 360636557525953416547795 540954836288930124821693)
                  ·
                    refine ⟨202858063608348796808135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 540954836288930124821693 202858063608348796808135)
                    ·
                      rfl

theorem cell22_592597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 4, 1, 3].length) (baseStart_592597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_592597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_592597 prefixEnd_592597 := by exact prefixLift 592597
  have htrace : WordTrace (prefixWord ++ tailWord_592597) baseStart_592597 baseEnd_592597 := by
    simpa [prefixWord, tailWord_592597, baseEnd_592597] using wordTrace_append hprefix tailTrace_592597
  have hstable : (prefixWord ++ tailWord_592597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592597).length < 2 ^ (prefixWord ++ tailWord_592597).sum := by decide
  have hdescent : baseEnd_592597 < baseStart_592597 := by decide
  rcases family_descends (prefixWord ++ tailWord_592597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592621 : List Nat := [1, 5, 1, 2, 1, 1, 3, 2, 6]
def baseStart_592621 : Nat := 118140960795 + 592621 * 2 ^ 59
def prefixEnd_592621 : Nat := 4983230072969 + 3 ^ 40 * 592621 * 2
def baseEnd_592621 : Nat := 67622093099606911402687

theorem tailTrace_592621 : CollatzResearch.WordTrace tailWord_592621 prefixEnd_592621 67622093099606911402687 := by
  unfold tailWord_592621
  simp only [CollatzResearch.WordTrace]
  refine ⟨21614663586042803454041717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14409775724028535636027811 21614663586042803454041717)
  ·
    refine ⟨2026374711191512823816411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21614663586042803454041717 2026374711191512823816411)
    ·
      refine ⟨3039562066787269235724617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2026374711191512823816411 3039562066787269235724617)
      ·
        refine ⟨2279671550090451926793463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3039562066787269235724617 2279671550090451926793463)
        ·
          refine ⟨3419507325135677890190195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2279671550090451926793463 3419507325135677890190195)
          ·
            refine ⟨5129260987703516835285293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3419507325135677890190195 5129260987703516835285293)
            ·
              refine ⟨1923472870388818813231985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5129260987703516835285293 1923472870388818813231985)
              ·
                refine ⟨1442604652791614109923989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1923472870388818813231985 1442604652791614109923989)
                ·
                  refine ⟨67622093099606911402687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1442604652791614109923989 67622093099606911402687)
                  ·
                    rfl

theorem cell22_592621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 2, 6].length) (baseStart_592621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_592621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_592621 prefixEnd_592621 := by exact prefixLift 592621
  have htrace : WordTrace (prefixWord ++ tailWord_592621) baseStart_592621 baseEnd_592621 := by
    simpa [prefixWord, tailWord_592621, baseEnd_592621] using wordTrace_append hprefix tailTrace_592621
  have hstable : (prefixWord ++ tailWord_592621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592621).length < 2 ^ (prefixWord ++ tailWord_592621).sum := by decide
  have hdescent : baseEnd_592621 < baseStart_592621 := by decide
  rcases family_descends (prefixWord ++ tailWord_592621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592636 : List Nat := [2, 2, 2, 1, 3, 2, 2, 2, 1, 5]
def baseStart_592636 : Nat := 118140960795 + 592636 * 2 ^ 59
def prefixEnd_592636 : Nat := 4983230072969 + 3 ^ 40 * 592636 * 2
def baseEnd_592636 : Nat := 202871414105365695083015

theorem tailTrace_592636 : CollatzResearch.WordTrace tailWord_592636 prefixEnd_592636 202871414105365695083015 := by
  unfold tailWord_592636
  simp only [CollatzResearch.WordTrace]
  refine ⟨10807605340494230507918881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14410140453992307343891841 10807605340494230507918881)
  ·
    refine ⟨8105704005370672880939161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10807605340494230507918881 8105704005370672880939161)
    ·
      refine ⟨6079278004028004660704371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8105704005370672880939161 6079278004028004660704371)
      ·
        refine ⟨9118917006042006991056557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6079278004028004660704371 9118917006042006991056557)
        ·
          refine ⟨3419593877265752621646209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9118917006042006991056557 3419593877265752621646209)
          ·
            refine ⟨2564695407949314466234657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3419593877265752621646209 2564695407949314466234657)
            ·
              refine ⟨1923521555961985849675993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2564695407949314466234657 1923521555961985849675993)
              ·
                refine ⟨1442641166971489387256995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1923521555961985849675993 1442641166971489387256995)
                ·
                  refine ⟨2163961750457234080885493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1442641166971489387256995 2163961750457234080885493)
                  ·
                    refine ⟨202871414105365695083015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2163961750457234080885493 202871414105365695083015)
                    ·
                      rfl

theorem cell22_592636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 2, 1, 5].length) (baseStart_592636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_592636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_592636 prefixEnd_592636 := by exact prefixLift 592636
  have htrace : WordTrace (prefixWord ++ tailWord_592636) baseStart_592636 baseEnd_592636 := by
    simpa [prefixWord, tailWord_592636, baseEnd_592636] using wordTrace_append hprefix tailTrace_592636
  have hstable : (prefixWord ++ tailWord_592636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592636).length < 2 ^ (prefixWord ++ tailWord_592636).sum := by decide
  have hdescent : baseEnd_592636 < baseStart_592636 := by decide
  rcases family_descends (prefixWord ++ tailWord_592636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592711 : List Nat := [1, 1, 4, 1, 2, 1, 1, 6, 5]
def baseStart_592711 : Nat := 118140960795 + 592711 * 2 ^ 59
def prefixEnd_592711 : Nat := 4983230072969 + 3 ^ 40 * 592711 * 2
def baseEnd_592711 : Nat := 67632362712696833152595

theorem tailTrace_592711 : CollatzResearch.WordTrace tailWord_592711 prefixEnd_592711 67632362712696833152595 := by
  unfold tailWord_592711
  simp only [CollatzResearch.WordTrace]
  refine ⟨21617946155716748824817987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14411964103811165883211991 21617946155716748824817987)
  ·
    refine ⟨32426919233575123237226981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21617946155716748824817987 32426919233575123237226981)
    ·
      refine ⟨6080047356295335606980059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32426919233575123237226981 6080047356295335606980059)
      ·
        refine ⟨9120071034443003410470089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6080047356295335606980059 9120071034443003410470089)
        ·
          refine ⟨6840053275832252557852567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9120071034443003410470089 6840053275832252557852567)
          ·
            refine ⟨10260079913748378836778851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6840053275832252557852567 10260079913748378836778851)
            ·
              refine ⟨15390119870622568255168277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10260079913748378836778851 15390119870622568255168277)
              ·
                refine ⟨721411868935432886961013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15390119870622568255168277 721411868935432886961013)
                ·
                  refine ⟨67632362712696833152595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 721411868935432886961013 67632362712696833152595)
                  ·
                    rfl

theorem cell22_592711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 6, 5].length) (baseStart_592711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_592711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_592711 prefixEnd_592711 := by exact prefixLift 592711
  have htrace : WordTrace (prefixWord ++ tailWord_592711) baseStart_592711 baseEnd_592711 := by
    simpa [prefixWord, tailWord_592711, baseEnd_592711] using wordTrace_append hprefix tailTrace_592711
  have hstable : (prefixWord ++ tailWord_592711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592711).length < 2 ^ (prefixWord ++ tailWord_592711).sum := by decide
  have hdescent : baseEnd_592711 < baseStart_592711 := by decide
  rcases family_descends (prefixWord ++ tailWord_592711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592771 : List Nat := [1, 1, 1, 3, 4, 1, 1, 2, 3, 5]
def baseStart_592771 : Nat := 118140960795 + 592771 * 2 ^ 59
def prefixEnd_592771 : Nat := 4983230072969 + 3 ^ 40 * 592771 * 2
def baseEnd_592771 : Nat := 202917627364270342957601

theorem tailTrace_592771 : CollatzResearch.WordTrace tailWord_592771 prefixEnd_592771 202917627364270342957601 := by
  unfold tailWord_592771
  simp only [CollatzResearch.WordTrace]
  refine ⟨21620134535499379072002167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14413423023666252714668111 21620134535499379072002167)
  ·
    refine ⟨32430201803249068608003251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21620134535499379072002167 32430201803249068608003251)
    ·
      refine ⟨48645302704873602912004877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32430201803249068608003251 48645302704873602912004877)
      ·
        refine ⟨18241988514327601092001829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48645302704873602912004877 18241988514327601092001829)
        ·
          refine ⟨3420372846436425204750343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18241988514327601092001829 3420372846436425204750343)
          ·
            refine ⟨5130559269654637807125515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3420372846436425204750343 5130559269654637807125515)
            ·
              refine ⟨7695838904481956710688273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5130559269654637807125515 7695838904481956710688273)
              ·
                refine ⟨5771879178361467533016205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7695838904481956710688273 5771879178361467533016205)
                ·
                  refine ⟨2164454691885550324881077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5771879178361467533016205 2164454691885550324881077)
                  ·
                    refine ⟨202917627364270342957601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2164454691885550324881077 202917627364270342957601)
                    ·
                      rfl

theorem cell22_592771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 3, 5].length) (baseStart_592771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_592771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_592771 prefixEnd_592771 := by exact prefixLift 592771
  have htrace : WordTrace (prefixWord ++ tailWord_592771) baseStart_592771 baseEnd_592771 := by
    simpa [prefixWord, tailWord_592771, baseEnd_592771] using wordTrace_append hprefix tailTrace_592771
  have hstable : (prefixWord ++ tailWord_592771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592771).length < 2 ^ (prefixWord ++ tailWord_592771).sum := by decide
  have hdescent : baseEnd_592771 < baseStart_592771 := by decide
  rcases family_descends (prefixWord ++ tailWord_592771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592803 : List Nat := [1, 1, 1, 4, 1, 2, 5, 1, 2, 4]
def baseStart_592803 : Nat := 118140960795 + 592803 * 2 ^ 59
def prefixEnd_592803 : Nat := 4983230072969 + 3 ^ 40 * 592803 * 2
def baseEnd_592803 : Nat := 202928581618232926157503

theorem tailTrace_592803 : CollatzResearch.WordTrace tailWord_592803 prefixEnd_592803 202928581618232926157503 := by
  unfold tailWord_592803
  simp only [CollatzResearch.WordTrace]
  refine ⟨21621301671383448537167063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14414201114255632358111375 21621301671383448537167063)
  ·
    refine ⟨32431952507075172805750595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21621301671383448537167063 32431952507075172805750595)
    ·
      refine ⟨48647928760612759208625893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32431952507075172805750595 48647928760612759208625893)
      ·
        refine ⟨9121486642614892351617355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48647928760612759208625893 9121486642614892351617355)
        ·
          refine ⟨13682229963922338527426033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9121486642614892351617355 13682229963922338527426033)
          ·
            refine ⟨10261672472941753895569525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13682229963922338527426033 10261672472941753895569525)
            ·
              refine ⟨962031794338289427709643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10261672472941753895569525 962031794338289427709643)
              ·
                refine ⟨1443047691507434141564465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 962031794338289427709643 1443047691507434141564465)
                ·
                  refine ⟨1082285768630575606173349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1443047691507434141564465 1082285768630575606173349)
                  ·
                    refine ⟨202928581618232926157503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1082285768630575606173349 202928581618232926157503)
                    ·
                      rfl

theorem cell22_592803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 1, 2, 4].length) (baseStart_592803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_592803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_592803 prefixEnd_592803 := by exact prefixLift 592803
  have htrace : WordTrace (prefixWord ++ tailWord_592803) baseStart_592803 baseEnd_592803 := by
    simpa [prefixWord, tailWord_592803, baseEnd_592803] using wordTrace_append hprefix tailTrace_592803
  have hstable : (prefixWord ++ tailWord_592803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592803).length < 2 ^ (prefixWord ++ tailWord_592803).sum := by decide
  have hdescent : baseEnd_592803 < baseStart_592803 := by decide
  rcases family_descends (prefixWord ++ tailWord_592803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592807 : List Nat := [1, 1, 6, 1, 3, 1, 2, 3, 4]
def baseStart_592807 : Nat := 118140960795 + 592807 * 2 ^ 59
def prefixEnd_592807 : Nat := 4983230072969 + 3 ^ 40 * 592807 * 2
def baseEnd_592807 : Nat := 67643316966659416352497

theorem tailTrace_592807 : CollatzResearch.WordTrace tailWord_592807 prefixEnd_592807 67643316966659416352497 := by
  unfold tailWord_592807
  simp only [CollatzResearch.WordTrace]
  refine ⟨21621447563368957220312675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14414298375579304813541783 21621447563368957220312675)
  ·
    refine ⟨32432171345053435830469013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21621447563368957220312675 32432171345053435830469013)
    ·
      refine ⟨1520258031799379804553235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 32432171345053435830469013 1520258031799379804553235)
      ·
        refine ⟨2280387047699069706829853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1520258031799379804553235 2280387047699069706829853)
        ·
          refine ⟨855145142887151140061195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2280387047699069706829853 855145142887151140061195)
          ·
            refine ⟨1282717714330726710091793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 855145142887151140061195 1282717714330726710091793)
            ·
              refine ⟨962038285748045032568845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1282717714330726710091793 962038285748045032568845)
              ·
                refine ⟨360764357155516887213317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 962038285748045032568845 360764357155516887213317)
                ·
                  refine ⟨67643316966659416352497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 360764357155516887213317 67643316966659416352497)
                  ·
                    rfl

theorem cell22_592807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 3, 4].length) (baseStart_592807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_592807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_592807 prefixEnd_592807 := by exact prefixLift 592807
  have htrace : WordTrace (prefixWord ++ tailWord_592807) baseStart_592807 baseEnd_592807 := by
    simpa [prefixWord, tailWord_592807, baseEnd_592807] using wordTrace_append hprefix tailTrace_592807
  have hstable : (prefixWord ++ tailWord_592807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592807).length < 2 ^ (prefixWord ++ tailWord_592807).sum := by decide
  have hdescent : baseEnd_592807 < baseStart_592807 := by decide
  rcases family_descends (prefixWord ++ tailWord_592807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592831 : List Nat := [1, 1, 2, 2, 2, 1, 2, 3, 2, 6]
def baseStart_592831 : Nat := 118140960795 + 592831 * 2 ^ 59
def prefixEnd_592831 : Nat := 4983230072969 + 3 ^ 40 * 592831 * 2
def baseEnd_592831 : Nat := 202938166590450186457417

theorem tailTrace_592831 : CollatzResearch.WordTrace tailWord_592831 prefixEnd_592831 202938166590450186457417 := by
  unfold tailWord_592831
  simp only [CollatzResearch.WordTrace]
  refine ⟨21622322915282009319186347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14414881943521339546124231 21622322915282009319186347)
  ·
    refine ⟨32433484372923013978779521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21622322915282009319186347 32433484372923013978779521)
    ·
      refine ⟨24325113279692260484084641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32433484372923013978779521 24325113279692260484084641)
      ·
        refine ⟨18243834959769195363063481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24325113279692260484084641 18243834959769195363063481)
        ·
          refine ⟨13682876219826896522297611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18243834959769195363063481 13682876219826896522297611)
          ·
            refine ⟨20524314329740344783446417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13682876219826896522297611 20524314329740344783446417)
            ·
              refine ⟨15393235747305258587584813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20524314329740344783446417 15393235747305258587584813)
              ·
                refine ⟨5772463405239471970344305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15393235747305258587584813 5772463405239471970344305)
                ·
                  refine ⟨4329347553929603977758229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5772463405239471970344305 4329347553929603977758229)
                  ·
                    refine ⟨202938166590450186457417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4329347553929603977758229 202938166590450186457417)
                    ·
                      rfl

theorem cell22_592831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 2, 6].length) (baseStart_592831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_592831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_592831 prefixEnd_592831 := by exact prefixLift 592831
  have htrace : WordTrace (prefixWord ++ tailWord_592831) baseStart_592831 baseEnd_592831 := by
    simpa [prefixWord, tailWord_592831, baseEnd_592831] using wordTrace_append hprefix tailTrace_592831
  have hstable : (prefixWord ++ tailWord_592831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592831).length < 2 ^ (prefixWord ++ tailWord_592831).sum := by decide
  have hdescent : baseEnd_592831 < baseStart_592831 := by decide
  rcases family_descends (prefixWord ++ tailWord_592831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592893 : List Nat := [1, 4, 1, 1, 1, 2, 1, 4, 3, 4]
def baseStart_592893 : Nat := 118140960795 + 592893 * 2 ^ 59
def prefixEnd_592893 : Nat := 4983230072969 + 3 ^ 40 * 592893 * 2
def baseEnd_592893 : Nat := 202959390457502691407227

theorem tailTrace_592893 : CollatzResearch.WordTrace tailWord_592893 prefixEnd_592893 202959390457502691407227 := by
  unfold tailWord_592893
  simp only [CollatzResearch.WordTrace]
  refine ⟨21624584241057393907943333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14416389494038262605295555 21624584241057393907943333)
  ·
    refine ⟨4054609545198261357739375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21624584241057393907943333 4054609545198261357739375)
    ·
      refine ⟨6081914317797392036609063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4054609545198261357739375 6081914317797392036609063)
      ·
        refine ⟨9122871476696088054913595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6081914317797392036609063 9122871476696088054913595)
        ·
          refine ⟨13684307215044132082370393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9122871476696088054913595 13684307215044132082370393)
          ·
            refine ⟨10263230411283099061777795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13684307215044132082370393 10263230411283099061777795)
            ·
              refine ⟨15394845616924648592666693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10263230411283099061777795 15394845616924648592666693)
              ·
                refine ⟨2886533553173371611125005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15394845616924648592666693 2886533553173371611125005)
                ·
                  refine ⟨1082450082440014354171877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2886533553173371611125005 1082450082440014354171877)
                  ·
                    refine ⟨202959390457502691407227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1082450082440014354171877 202959390457502691407227)
                    ·
                      rfl

theorem cell22_592893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 4, 3, 4].length) (baseStart_592893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_592893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_592893 prefixEnd_592893 := by exact prefixLift 592893
  have htrace : WordTrace (prefixWord ++ tailWord_592893) baseStart_592893 baseEnd_592893 := by
    simpa [prefixWord, tailWord_592893, baseEnd_592893] using wordTrace_append hprefix tailTrace_592893
  have hstable : (prefixWord ++ tailWord_592893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592893).length < 2 ^ (prefixWord ++ tailWord_592893).sum := by decide
  have hdescent : baseEnd_592893 < baseStart_592893 := by decide
  rcases family_descends (prefixWord ++ tailWord_592893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592897 : List Nat := [1, 2, 4, 1, 2, 4, 2, 1, 5]
def baseStart_592897 : Nat := 118140960795 + 592897 * 2 ^ 59
def prefixEnd_592897 : Nat := 4983230072969 + 3 ^ 40 * 592897 * 2
def baseEnd_592897 : Nat := 67653586579749338102405

theorem tailTrace_592897 : CollatzResearch.WordTrace tailWord_592897 prefixEnd_592897 67653586579749338102405 := by
  unfold tailWord_592897
  simp only [CollatzResearch.WordTrace]
  refine ⟨21624730133042902591088945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14416486755361935060725963 21624730133042902591088945)
  ·
    refine ⟨16218547599782176943316709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21624730133042902591088945 16218547599782176943316709)
    ·
      refine ⟨3040977674959158176871883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16218547599782176943316709 3040977674959158176871883)
      ·
        refine ⟨4561466512438737265307825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3040977674959158176871883 4561466512438737265307825)
        ·
          refine ⟨3421099884329052948980869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4561466512438737265307825 3421099884329052948980869)
          ·
            refine ⟨641456228311697427933913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3421099884329052948980869 641456228311697427933913)
            ·
              refine ⟨481092171233773070950435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 641456228311697427933913 481092171233773070950435)
              ·
                refine ⟨721638256850659606425653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 481092171233773070950435 721638256850659606425653)
                ·
                  refine ⟨67653586579749338102405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 721638256850659606425653 67653586579749338102405)
                  ·
                    rfl

theorem cell22_592897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 2, 1, 5].length) (baseStart_592897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_592897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_592897 prefixEnd_592897 := by exact prefixLift 592897
  have htrace : WordTrace (prefixWord ++ tailWord_592897) baseStart_592897 baseEnd_592897 := by
    simpa [prefixWord, tailWord_592897, baseEnd_592897] using wordTrace_append hprefix tailTrace_592897
  have hstable : (prefixWord ++ tailWord_592897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592897).length < 2 ^ (prefixWord ++ tailWord_592897).sum := by decide
  have hdescent : baseEnd_592897 < baseStart_592897 := by decide
  rcases family_descends (prefixWord ++ tailWord_592897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592910 : List Nat := [4, 1, 1, 2, 2, 3, 1, 1, 3, 4]
def baseStart_592910 : Nat := 118140960795 + 592910 * 2 ^ 59
def prefixEnd_592910 : Nat := 4983230072969 + 3 ^ 40 * 592910 * 2
def baseEnd_592910 : Nat := 202965209904920313732175

theorem tailTrace_592910 : CollatzResearch.WordTrace tailWord_592910 prefixEnd_592910 202965209904920313732175 := by
  unfold tailWord_592910
  simp only [CollatzResearch.WordTrace]
  refine ⟨2703150535249475726414023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14416802854663870540874789 2703150535249475726414023)
  ·
    refine ⟨4054725802874213589621035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2703150535249475726414023 4054725802874213589621035)
    ·
      refine ⟨6082088704311320384431553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4054725802874213589621035 6082088704311320384431553)
      ·
        refine ⟨4561566528233490288323665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6082088704311320384431553 4561566528233490288323665)
        ·
          refine ⟨3421174896175117716242749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4561566528233490288323665 3421174896175117716242749)
          ·
            refine ⟨1282940586065669143591031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3421174896175117716242749 1282940586065669143591031)
            ·
              refine ⟨1924410879098503715386547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1282940586065669143591031 1924410879098503715386547)
              ·
                refine ⟨2886616318647755573079821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1924410879098503715386547 2886616318647755573079821)
                ·
                  refine ⟨1082481119492908339904933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2886616318647755573079821 1082481119492908339904933)
                  ·
                    refine ⟨202965209904920313732175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1082481119492908339904933 202965209904920313732175)
                    ·
                      rfl

theorem cell22_592910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 1, 3, 4].length) (baseStart_592910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_592910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_592910 prefixEnd_592910 := by exact prefixLift 592910
  have htrace : WordTrace (prefixWord ++ tailWord_592910) baseStart_592910 baseEnd_592910 := by
    simpa [prefixWord, tailWord_592910, baseEnd_592910] using wordTrace_append hprefix tailTrace_592910
  have hstable : (prefixWord ++ tailWord_592910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592910).length < 2 ^ (prefixWord ++ tailWord_592910).sum := by decide
  have hdescent : baseEnd_592910 < baseStart_592910 := by decide
  rcases family_descends (prefixWord ++ tailWord_592910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592927 : List Nat := [1, 1, 2, 4, 1, 4, 3, 1, 1, 4]
def baseStart_592927 : Nat := 118140960795 + 592927 * 2 ^ 59
def prefixEnd_592927 : Nat := 4983230072969 + 3 ^ 40 * 592927 * 2
def baseEnd_592927 : Nat := 202971029352337936057123

theorem tailTrace_592927 : CollatzResearch.WordTrace tailWord_592927 prefixEnd_592927 202971029352337936057123 := by
  unfold tailWord_592927
  simp only [CollatzResearch.WordTrace]
  refine ⟨21625824322934217714681035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14417216215289478476454023 21625824322934217714681035)
  ·
    refine ⟨32438736484401326572021553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21625824322934217714681035 32438736484401326572021553)
    ·
      refine ⟨24329052363300994929016165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32438736484401326572021553 24329052363300994929016165)
      ·
        refine ⟨4561697318118936549190531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24329052363300994929016165 4561697318118936549190531)
        ·
          refine ⟨6842545977178404823785797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4561697318118936549190531 6842545977178404823785797)
          ·
            refine ⟨1282977370720950904459837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6842545977178404823785797 1282977370720950904459837)
            ·
              refine ⟨481116514020356589172439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1282977370720950904459837 481116514020356589172439)
              ·
                refine ⟨721674771030534883758659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 481116514020356589172439 721674771030534883758659)
                ·
                  refine ⟨1082512156545802325637989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 721674771030534883758659 1082512156545802325637989)
                  ·
                    refine ⟨202971029352337936057123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1082512156545802325637989 202971029352337936057123)
                    ·
                      rfl

theorem cell22_592927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 3, 1, 1, 4].length) (baseStart_592927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_592927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_592927 prefixEnd_592927 := by exact prefixLift 592927
  have htrace : WordTrace (prefixWord ++ tailWord_592927) baseStart_592927 baseEnd_592927 := by
    simpa [prefixWord, tailWord_592927, baseEnd_592927] using wordTrace_append hprefix tailTrace_592927
  have hstable : (prefixWord ++ tailWord_592927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592927).length < 2 ^ (prefixWord ++ tailWord_592927).sum := by decide
  have hdescent : baseEnd_592927 < baseStart_592927 := by decide
  rcases family_descends (prefixWord ++ tailWord_592927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592942 : List Nat := [4, 1, 3, 1, 1, 1, 3, 4, 4]
def baseStart_592942 : Nat := 118140960795 + 592942 * 2 ^ 59
def prefixEnd_592942 : Nat := 4983230072969 + 3 ^ 40 * 592942 * 2
def baseEnd_592942 : Nat := 67658721386294298977359

theorem tailTrace_592942 : CollatzResearch.WordTrace tailWord_592942 prefixEnd_592942 67658721386294298977359 := by
  unfold tailWord_592942
  simp only [CollatzResearch.WordTrace]
  refine ⟨2703296427234984409559635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14417580945253250184318053 2703296427234984409559635)
  ·
    refine ⟨4054944640852476614339453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2703296427234984409559635 4054944640852476614339453)
    ·
      refine ⟨1520604240319678730377295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4054944640852476614339453 1520604240319678730377295)
      ·
        refine ⟨2280906360479518095565943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1520604240319678730377295 2280906360479518095565943)
        ·
          refine ⟨3421359540719277143348915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2280906360479518095565943 3421359540719277143348915)
          ·
            refine ⟨5132039311078915715023373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3421359540719277143348915 5132039311078915715023373)
            ·
              refine ⟨1924514741654593393133765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5132039311078915715023373 1924514741654593393133765)
              ·
                refine ⟨360846514060236261212581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1924514741654593393133765 360846514060236261212581)
                ·
                  refine ⟨67658721386294298977359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 360846514060236261212581 67658721386294298977359)
                  ·
                    rfl

theorem cell22_592942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 4, 4].length) (baseStart_592942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_592942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_592942 prefixEnd_592942 := by exact prefixLift 592942
  have htrace : WordTrace (prefixWord ++ tailWord_592942) baseStart_592942 baseEnd_592942 := by
    simpa [prefixWord, tailWord_592942, baseEnd_592942] using wordTrace_append hprefix tailTrace_592942
  have hstable : (prefixWord ++ tailWord_592942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592942).length < 2 ^ (prefixWord ++ tailWord_592942).sum := by decide
  have hdescent : baseEnd_592942 < baseStart_592942 := by decide
  rcases family_descends (prefixWord ++ tailWord_592942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592957 : List Nat := [1, 4, 1, 3, 1, 2, 2, 3, 2, 3]
def baseStart_592957 : Nat := 118140960795 + 592957 * 2 ^ 59
def prefixEnd_592957 : Nat := 4983230072969 + 3 ^ 40 * 592957 * 2
def baseEnd_592957 : Nat := 202981298965427857807031

theorem tailTrace_592957 : CollatzResearch.WordTrace tailWord_592957 prefixEnd_592957 202981298965427857807031 := by
  unfold tailWord_592957
  simp only [CollatzResearch.WordTrace]
  refine ⟨21626918512825532838273125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14417945675217021892182083 21626918512825532838273125)
  ·
    refine ⟨4055047221154787407176211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21626918512825532838273125 4055047221154787407176211)
    ·
      refine ⟨6082570831732181110764317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4055047221154787407176211 6082570831732181110764317)
      ·
        refine ⟨2280964061899567916536619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6082570831732181110764317 2280964061899567916536619)
        ·
          refine ⟨3421446092849351874804929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2280964061899567916536619 3421446092849351874804929)
          ·
            refine ⟨2566084569637013906103697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3421446092849351874804929 2566084569637013906103697)
            ·
              refine ⟨1924563427227760429577773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2566084569637013906103697 1924563427227760429577773)
              ·
                refine ⟨721711285210410161091665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1924563427227760429577773 721711285210410161091665)
                ·
                  refine ⟨541283463907807620818749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 721711285210410161091665 541283463907807620818749)
                  ·
                    refine ⟨202981298965427857807031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 541283463907807620818749 202981298965427857807031)
                    ·
                      rfl

theorem cell22_592957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 3, 2, 3].length) (baseStart_592957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_592957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_592957 prefixEnd_592957 := by exact prefixLift 592957
  have htrace : WordTrace (prefixWord ++ tailWord_592957) baseStart_592957 baseEnd_592957 := by
    simpa [prefixWord, tailWord_592957, baseEnd_592957] using wordTrace_append hprefix tailTrace_592957
  have hstable : (prefixWord ++ tailWord_592957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592957).length < 2 ^ (prefixWord ++ tailWord_592957).sum := by decide
  have hdescent : baseEnd_592957 < baseStart_592957 := by decide
  rcases family_descends (prefixWord ++ tailWord_592957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593002 : List Nat := [3, 1, 3, 2, 2, 1, 1, 3, 3, 3]
def baseStart_593002 : Nat := 118140960795 + 593002 * 2 ^ 59
def prefixEnd_593002 : Nat := 4983230072969 + 3 ^ 40 * 593002 * 2
def baseEnd_593002 : Nat := 202996703385062740431893

theorem tailTrace_593002 : CollatzResearch.WordTrace tailWord_593002 prefixEnd_593002 202996703385062740431893 := by
  unfold tailWord_593002
  simp only [CollatzResearch.WordTrace]
  refine ⟨5407139949415626380915315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14419039865108337015774173 5407139949415626380915315)
  ·
    refine ⟨8110709924123439571372973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5407139949415626380915315 8110709924123439571372973)
    ·
      refine ⟨3041516221546289839264865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8110709924123439571372973 3041516221546289839264865)
      ·
        refine ⟨2281137166159717379448649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3041516221546289839264865 2281137166159717379448649)
        ·
          refine ⟨1710852874619788034586487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2281137166159717379448649 1710852874619788034586487)
          ·
            refine ⟨2566279311929682051879731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1710852874619788034586487 2566279311929682051879731)
            ·
              refine ⟨3849418967894523077819597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2566279311929682051879731 3849418967894523077819597)
              ·
                refine ⟨1443532112960446154182349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3849418967894523077819597 1443532112960446154182349)
                ·
                  refine ⟨541324542360167307818381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1443532112960446154182349 541324542360167307818381)
                  ·
                    refine ⟨202996703385062740431893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 541324542360167307818381 202996703385062740431893)
                    ·
                      rfl

theorem cell22_593002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 3, 3, 3].length) (baseStart_593002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_593002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_593002 prefixEnd_593002 := by exact prefixLift 593002
  have htrace : WordTrace (prefixWord ++ tailWord_593002) baseStart_593002 baseEnd_593002 := by
    simpa [prefixWord, tailWord_593002, baseEnd_593002] using wordTrace_append hprefix tailTrace_593002
  have hstable : (prefixWord ++ tailWord_593002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593002).length < 2 ^ (prefixWord ++ tailWord_593002).sum := by decide
  have hdescent : baseEnd_593002 < baseStart_593002 := by decide
  rcases family_descends (prefixWord ++ tailWord_593002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593043 : List Nat := [1, 1, 1, 2, 1, 2, 4, 2, 8]
def baseStart_593043 : Nat := 118140960795 + 593043 * 2 ^ 59
def prefixEnd_593043 : Nat := 4983230072969 + 3 ^ 40 * 593043 * 2
def baseEnd_593043 : Nat := 67670246174317433385589

theorem tailTrace_593043 : CollatzResearch.WordTrace tailWord_593043 prefixEnd_593043 67670246174317433385589 := by
  unfold tailWord_593043
  simp only [CollatzResearch.WordTrace]
  refine ⟨21630055190513969525903783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14420036793675979683935855 21630055190513969525903783)
  ·
    refine ⟨32445082785770954288855675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21630055190513969525903783 32445082785770954288855675)
    ·
      refine ⟨48667624178656431433283513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32445082785770954288855675 48667624178656431433283513)
      ·
        refine ⟨36500718133992323574962635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48667624178656431433283513 36500718133992323574962635)
        ·
          refine ⟨54751077200988485362443953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36500718133992323574962635 54751077200988485362443953)
          ·
            refine ⟨41063307900741364021832965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54751077200988485362443953 41063307900741364021832965)
            ·
              refine ⟨7699370231389005754093681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41063307900741364021832965 7699370231389005754093681)
              ·
                refine ⟨5774527673541754315570261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7699370231389005754093681 5774527673541754315570261)
                ·
                  refine ⟨67670246174317433385589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5774527673541754315570261 67670246174317433385589)
                  ·
                    rfl

theorem cell22_593043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 8].length) (baseStart_593043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_593043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_593043 prefixEnd_593043 := by exact prefixLift 593043
  have htrace : WordTrace (prefixWord ++ tailWord_593043) baseStart_593043 baseEnd_593043 := by
    simpa [prefixWord, tailWord_593043, baseEnd_593043] using wordTrace_append hprefix tailTrace_593043
  have hstable : (prefixWord ++ tailWord_593043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593043).length < 2 ^ (prefixWord ++ tailWord_593043).sum := by decide
  have hdescent : baseEnd_593043 < baseStart_593043 := by decide
  rcases family_descends (prefixWord ++ tailWord_593043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593066 : List Nat := [3, 1, 5, 1, 1, 3, 2, 1, 5]
def baseStart_593066 : Nat := 118140960795 + 593066 * 2 ^ 59
def prefixEnd_593066 : Nat := 4983230072969 + 3 ^ 40 * 593066 * 2
def baseEnd_593066 : Nat := 67672870630995968943899

theorem tailTrace_593066 : CollatzResearch.WordTrace tailWord_593066 prefixEnd_593066 67672870630995968943899 := by
  unfold tailWord_593066
  simp only [CollatzResearch.WordTrace]
  refine ⟨5407723517357661113497763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14420596046287096302660701 5407723517357661113497763)
  ·
    refine ⟨8111585276036491670246645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5407723517357661113497763 8111585276036491670246645)
    ·
      refine ⟨760461119628421094085623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8111585276036491670246645 760461119628421094085623)
      ·
        refine ⟨1140691679442631641128435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 760461119628421094085623 1140691679442631641128435)
        ·
          refine ⟨1711037519163947461692653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1140691679442631641128435 1711037519163947461692653)
          ·
            refine ⟨641639069686480298134745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1711037519163947461692653 641639069686480298134745)
            ·
              refine ⟨481229302264860223601059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 641639069686480298134745 481229302264860223601059)
              ·
                refine ⟨721843953397290335401589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 481229302264860223601059 721843953397290335401589)
                ·
                  refine ⟨67672870630995968943899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 721843953397290335401589 67672870630995968943899)
                  ·
                    rfl

theorem cell22_593066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 2, 1, 5].length) (baseStart_593066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_593066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_593066 prefixEnd_593066 := by exact prefixLift 593066
  have htrace : WordTrace (prefixWord ++ tailWord_593066) baseStart_593066 baseEnd_593066 := by
    simpa [prefixWord, tailWord_593066, baseEnd_593066] using wordTrace_append hprefix tailTrace_593066
  have hstable : (prefixWord ++ tailWord_593066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593066).length < 2 ^ (prefixWord ++ tailWord_593066).sum := by decide
  have hdescent : baseEnd_593066 < baseStart_593066 := by decide
  rcases family_descends (prefixWord ++ tailWord_593066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593109 : List Nat := [1, 3, 2, 4, 1, 1, 1, 4, 2, 3]
def baseStart_593109 : Nat := 118140960795 + 593109 * 2 ^ 59
def prefixEnd_593109 : Nat := 4983230072969 + 3 ^ 40 * 593109 * 2
def baseEnd_593109 : Nat := 203033331671750128006565

theorem tailTrace_593109 : CollatzResearch.WordTrace tailWord_593109 prefixEnd_593109 203033331671750128006565 := by
  unfold tailWord_593109
  simp only [CollatzResearch.WordTrace]
  refine ⟨21632462408274862797806381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14421641605516575198537587 21632462408274862797806381)
  ·
    refine ⟨8112173403103073549177393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21632462408274862797806381 8112173403103073549177393)
    ·
      refine ⟨6084130052327305161883045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8112173403103073549177393 6084130052327305161883045)
      ·
        refine ⟨1140774384811369717853071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6084130052327305161883045 1140774384811369717853071)
        ·
          refine ⟨1711161577217054576779607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1140774384811369717853071 1711161577217054576779607)
          ·
            refine ⟨2566742365825581865169411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1711161577217054576779607 2566742365825581865169411)
            ·
              refine ⟨3850113548738372797754117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2566742365825581865169411 3850113548738372797754117)
              ·
                refine ⟨721896290388444899578897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3850113548738372797754117 721896290388444899578897)
                ·
                  refine ⟨541422217791333674684173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 721896290388444899578897 541422217791333674684173)
                  ·
                    refine ⟨203033331671750128006565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 541422217791333674684173 203033331671750128006565)
                    ·
                      rfl

theorem cell22_593109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 4, 2, 3].length) (baseStart_593109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_593109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_593109 prefixEnd_593109 := by exact prefixLift 593109
  have htrace : WordTrace (prefixWord ++ tailWord_593109) baseStart_593109 baseEnd_593109 := by
    simpa [prefixWord, tailWord_593109, baseEnd_593109] using wordTrace_append hprefix tailTrace_593109
  have hstable : (prefixWord ++ tailWord_593109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593109).length < 2 ^ (prefixWord ++ tailWord_593109).sum := by decide
  have hdescent : baseEnd_593109 < baseStart_593109 := by decide
  rcases family_descends (prefixWord ++ tailWord_593109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593214 : List Nat := [4, 2, 1, 2, 1, 1, 1, 5, 1, 4]
def baseStart_593214 : Nat := 118140960795 + 593214 * 2 ^ 59
def prefixEnd_593214 : Nat := 4983230072969 + 3 ^ 40 * 593214 * 2
def baseEnd_593214 : Nat := 203069275317564854131243

theorem tailTrace_593214 : CollatzResearch.WordTrace tailWord_593214 prefixEnd_593214 203069275317564854131243 := by
  unfold tailWord_593214
  simp only [CollatzResearch.WordTrace]
  refine ⟨2704536509111808216297337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14424194715262977153585797 2704536509111808216297337)
  ·
    refine ⟨2028402381833856162223003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2704536509111808216297337 2028402381833856162223003)
    ·
      refine ⟨3042603572750784243334505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2028402381833856162223003 3042603572750784243334505)
      ·
        refine ⟨2281952679563088182500879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3042603572750784243334505 2281952679563088182500879)
        ·
          refine ⟨3422929019344632273751319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2281952679563088182500879 3422929019344632273751319)
          ·
            refine ⟨5134393529016948410626979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3422929019344632273751319 5134393529016948410626979)
            ·
              refine ⟨7701590293525422615940469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5134393529016948410626979 7701590293525422615940469)
              ·
                refine ⟨722024090018008370244419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7701590293525422615940469 722024090018008370244419)
                ·
                  refine ⟨1083036135027012555366629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 722024090018008370244419 1083036135027012555366629)
                  ·
                    refine ⟨203069275317564854131243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1083036135027012555366629 203069275317564854131243)
                    ·
                      rfl

theorem cell22_593214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_593214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_593214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_593214 prefixEnd_593214 := by exact prefixLift 593214
  have htrace : WordTrace (prefixWord ++ tailWord_593214) baseStart_593214 baseEnd_593214 := by
    simpa [prefixWord, tailWord_593214, baseEnd_593214] using wordTrace_append hprefix tailTrace_593214
  have hstable : (prefixWord ++ tailWord_593214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593214).length < 2 ^ (prefixWord ++ tailWord_593214).sum := by decide
  have hdescent : baseEnd_593214 < baseStart_593214 := by decide
  rcases family_descends (prefixWord ++ tailWord_593214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593222 : List Nat := [6, 1, 1, 3, 2, 1, 1, 1, 3, 3]
def baseStart_593222 : Nat := 118140960795 + 593222 * 2 ^ 59
def prefixEnd_593222 : Nat := 4983230072969 + 3 ^ 40 * 593222 * 2
def baseEnd_593222 : Nat := 203072013881055499931219

theorem tailTrace_593222 : CollatzResearch.WordTrace tailWord_593222 prefixEnd_593222 203072013881055499931219 := by
  unfold tailWord_593222
  simp only [CollatzResearch.WordTrace]
  refine ⟨676143245527046346770935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 14424389237910322064446613 676143245527046346770935)
  ·
    refine ⟨1014214868290569520156403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 676143245527046346770935 1014214868290569520156403)
    ·
      refine ⟨1521322302435854280234605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1014214868290569520156403 1521322302435854280234605)
      ·
        refine ⟨570495863413445355087977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1521322302435854280234605 570495863413445355087977)
        ·
          refine ⟨427871897560084016315983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 570495863413445355087977 427871897560084016315983)
          ·
            refine ⟨641807846340126024473975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 427871897560084016315983 641807846340126024473975)
            ·
              refine ⟨962711769510189036710963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 641807846340126024473975 962711769510189036710963)
              ·
                refine ⟨1444067654265283555066445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 962711769510189036710963 1444067654265283555066445)
                ·
                  refine ⟨541525370349481333149917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1444067654265283555066445 541525370349481333149917)
                  ·
                    refine ⟨203072013881055499931219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 541525370349481333149917 203072013881055499931219)
                    ·
                      rfl

theorem cell22_593222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_593222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_593222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_593222 prefixEnd_593222 := by exact prefixLift 593222
  have htrace : WordTrace (prefixWord ++ tailWord_593222) baseStart_593222 baseEnd_593222 := by
    simpa [prefixWord, tailWord_593222, baseEnd_593222] using wordTrace_append hprefix tailTrace_593222
  have hstable : (prefixWord ++ tailWord_593222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593222).length < 2 ^ (prefixWord ++ tailWord_593222).sum := by decide
  have hdescent : baseEnd_593222 < baseStart_593222 := by decide
  rcases family_descends (prefixWord ++ tailWord_593222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593287 : List Nat := [1, 1, 4, 2, 2, 2, 1, 1, 2, 6]
def baseStart_593287 : Nat := 118140960795 + 593287 * 2 ^ 59
def prefixEnd_593287 : Nat := 4983230072969 + 3 ^ 40 * 593287 * 2
def baseEnd_593287 : Nat := 203094264709416997056019

theorem tailTrace_593287 : CollatzResearch.WordTrace tailWord_593287 prefixEnd_593287 203094264709416997056019 := by
  unfold tailWord_593287
  simp only [CollatzResearch.WordTrace]
  refine ⟨21638954601629999197786115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14425969734419999465190743 21638954601629999197786115)
  ·
    refine ⟨32458431902444998796679173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21638954601629999197786115 32458431902444998796679173)
    ·
      refine ⟨6085955981708437274377345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32458431902444998796679173 6085955981708437274377345)
      ·
        refine ⟨4564466986281327955783009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6085955981708437274377345 4564466986281327955783009)
        ·
          refine ⟨3423350239710995966837257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4564466986281327955783009 3423350239710995966837257)
          ·
            refine ⟨2567512679783246975127943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3423350239710995966837257 2567512679783246975127943)
            ·
              refine ⟨3851269019674870462691915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2567512679783246975127943 3851269019674870462691915)
              ·
                refine ⟨5776903529512305694037873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3851269019674870462691915 5776903529512305694037873)
                ·
                  refine ⟨4332677647134229270528405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5776903529512305694037873 4332677647134229270528405)
                  ·
                    refine ⟨203094264709416997056019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4332677647134229270528405 203094264709416997056019)
                    ·
                      rfl

theorem cell22_593287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 2, 6].length) (baseStart_593287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_593287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_593287 prefixEnd_593287 := by exact prefixLift 593287
  have htrace : WordTrace (prefixWord ++ tailWord_593287) baseStart_593287 baseEnd_593287 := by
    simpa [prefixWord, tailWord_593287, baseEnd_593287] using wordTrace_append hprefix tailTrace_593287
  have hstable : (prefixWord ++ tailWord_593287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593287).length < 2 ^ (prefixWord ++ tailWord_593287).sum := by decide
  have hdescent : baseEnd_593287 < baseStart_593287 := by decide
  rcases family_descends (prefixWord ++ tailWord_593287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593310 : List Nat := [4, 3, 1, 2, 3, 1, 1, 1, 2, 4]
def baseStart_593310 : Nat := 118140960795 + 593310 * 2 ^ 59
def prefixEnd_593310 : Nat := 4983230072969 + 3 ^ 40 * 593310 * 2
def baseEnd_593310 : Nat := 203102138079452603730949

theorem tailTrace_593310 : CollatzResearch.WordTrace tailWord_593310 prefixEnd_593310 203102138079452603730949 := by
  unfold tailWord_593310
  simp only [CollatzResearch.WordTrace]
  refine ⟨2704974185068334265734173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14426528987031116083915589 2704974185068334265734173)
  ·
    refine ⟨1014365319400625349650315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2704974185068334265734173 1014365319400625349650315)
    ·
      refine ⟨1521547979100938024475473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1014365319400625349650315 1521547979100938024475473)
      ·
        refine ⟨1141160984325703518356605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1521547979100938024475473 1141160984325703518356605)
        ·
          refine ⟨427935369122138819383727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1141160984325703518356605 427935369122138819383727)
          ·
            refine ⟨641903053683208229075591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 427935369122138819383727 641903053683208229075591)
            ·
              refine ⟨962854580524812343613387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 641903053683208229075591 962854580524812343613387)
              ·
                refine ⟨1444281870787218515420081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 962854580524812343613387 1444281870787218515420081)
                ·
                  refine ⟨1083211403090413886565061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1444281870787218515420081 1083211403090413886565061)
                  ·
                    refine ⟨203102138079452603730949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1083211403090413886565061 203102138079452603730949)
                    ·
                      rfl

theorem cell22_593310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_593310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_593310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_593310 prefixEnd_593310 := by exact prefixLift 593310
  have htrace : WordTrace (prefixWord ++ tailWord_593310) baseStart_593310 baseEnd_593310 := by
    simpa [prefixWord, tailWord_593310, baseEnd_593310] using wordTrace_append hprefix tailTrace_593310
  have hstable : (prefixWord ++ tailWord_593310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593310).length < 2 ^ (prefixWord ++ tailWord_593310).sum := by decide
  have hdescent : baseEnd_593310 < baseStart_593310 := by decide
  rcases family_descends (prefixWord ++ tailWord_593310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593347 : List Nat := [1, 1, 1, 3, 1, 1, 5, 3, 6]
def baseStart_593347 : Nat := 118140960795 + 593347 * 2 ^ 59
def prefixEnd_593347 : Nat := 4983230072969 + 3 ^ 40 * 593347 * 2
def baseEnd_593347 : Nat := 67704934645198946851945

theorem tailTrace_593347 : CollatzResearch.WordTrace tailWord_593347 prefixEnd_593347 67704934645198946851945 := by
  unfold tailWord_593347
  simp only [CollatzResearch.WordTrace]
  refine ⟨21641142981412629444970295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14427428654275086296646863 21641142981412629444970295)
  ·
    refine ⟨32461714472118944167455443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21641142981412629444970295 32461714472118944167455443)
    ·
      refine ⟨48692571708178416251183165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32461714472118944167455443 48692571708178416251183165)
      ·
        refine ⟨18259714390566906094193687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48692571708178416251183165 18259714390566906094193687)
        ·
          refine ⟨27389571585850359141290531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18259714390566906094193687 27389571585850359141290531)
          ·
            refine ⟨41084357378775538711935797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27389571585850359141290531 41084357378775538711935797)
            ·
              refine ⟨3851658504260206754243981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41084357378775538711935797 3851658504260206754243981)
              ·
                refine ⟨1444371939097577532841493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3851658504260206754243981 1444371939097577532841493)
                ·
                  refine ⟨67704934645198946851945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1444371939097577532841493 67704934645198946851945)
                  ·
                    rfl

theorem cell22_593347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 3, 6].length) (baseStart_593347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_593347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_593347 prefixEnd_593347 := by exact prefixLift 593347
  have htrace : WordTrace (prefixWord ++ tailWord_593347) baseStart_593347 baseEnd_593347 := by
    simpa [prefixWord, tailWord_593347, baseEnd_593347] using wordTrace_append hprefix tailTrace_593347
  have hstable : (prefixWord ++ tailWord_593347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593347).length < 2 ^ (prefixWord ++ tailWord_593347).sum := by decide
  have hdescent : baseEnd_593347 < baseStart_593347 := by decide
  rcases family_descends (prefixWord ++ tailWord_593347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593392 : List Nat := [2, 1, 1, 1, 3, 4, 10]
def baseStart_593392 : Nat := 118140960795 + 593392 * 2 ^ 59
def prefixEnd_593392 : Nat := 4983230072969 + 3 ^ 40 * 593392 * 2
def baseEnd_593392 : Nat := 7523341050193767525211

theorem tailTrace_593392 : CollatzResearch.WordTrace tailWord_593392 prefixEnd_593392 7523341050193767525211 := by
  unfold tailWord_593392
  simp only [CollatzResearch.WordTrace]
  refine ⟨10821392133124801065179215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14428522844166401420238953 10821392133124801065179215)
  ·
    refine ⟨16232088199687201597768823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10821392133124801065179215 16232088199687201597768823)
    ·
      refine ⟨24348132299530802396653235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16232088199687201597768823 24348132299530802396653235)
      ·
        refine ⟨36522198449296203594979853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24348132299530802396653235 36522198449296203594979853)
        ·
          refine ⟨13695824418486076348117445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36522198449296203594979853 13695824418486076348117445)
          ·
            refine ⟨2567967078466139315272021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13695824418486076348117445 2567967078466139315272021)
            ·
              refine ⟨7523341050193767525211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2567967078466139315272021 7523341050193767525211)
              ·
                rfl

theorem cell22_593392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 10].length) (baseStart_593392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_593392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_593392 prefixEnd_593392 := by exact prefixLift 593392
  have htrace : WordTrace (prefixWord ++ tailWord_593392) baseStart_593392 baseEnd_593392 := by
    simpa [prefixWord, tailWord_593392, baseEnd_593392] using wordTrace_append hprefix tailTrace_593392
  have hstable : (prefixWord ++ tailWord_593392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593392).length < 2 ^ (prefixWord ++ tailWord_593392).sum := by decide
  have hdescent : baseEnd_593392 < baseStart_593392 := by decide
  rcases family_descends (prefixWord ++ tailWord_593392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593407 : List Nat := [1, 1, 2, 2, 1, 2, 2, 2, 2, 7]
def baseStart_593407 : Nat := 118140960795 + 593407 * 2 ^ 59
def prefixEnd_593407 : Nat := 4983230072969 + 3 ^ 40 * 593407 * 2
def baseEnd_593407 : Nat := 203135343161776684055651

theorem tailTrace_593407 : CollatzResearch.WordTrace tailWord_593407 prefixEnd_593407 203135343161776684055651 := by
  unfold tailWord_593407
  simp only [CollatzResearch.WordTrace]
  refine ⟨21643331361195259692154475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14428887574130173128102983 21643331361195259692154475)
  ·
    refine ⟨32464997041792889538231713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21643331361195259692154475 32464997041792889538231713)
    ·
      refine ⟨24348747781344667153673785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32464997041792889538231713 24348747781344667153673785)
      ·
        refine ⟨18261560836008500365255339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24348747781344667153673785 18261560836008500365255339)
        ·
          refine ⟨27392341254012750547883009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18261560836008500365255339 27392341254012750547883009)
          ·
            refine ⟨20544255940509562910912257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27392341254012750547883009 20544255940509562910912257)
            ·
              refine ⟨15408191955382172183184193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20544255940509562910912257 15408191955382172183184193)
              ·
                refine ⟨11556143966536629137388145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15408191955382172183184193 11556143966536629137388145)
                ·
                  refine ⟨8667107974902471853041109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11556143966536629137388145 8667107974902471853041109)
                  ·
                    refine ⟨203135343161776684055651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8667107974902471853041109 203135343161776684055651)
                    ·
                      rfl

theorem cell22_593407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 7].length) (baseStart_593407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_593407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_593407 prefixEnd_593407 := by exact prefixLift 593407
  have htrace : WordTrace (prefixWord ++ tailWord_593407) baseStart_593407 baseEnd_593407 := by
    simpa [prefixWord, tailWord_593407, baseEnd_593407] using wordTrace_append hprefix tailTrace_593407
  have hstable : (prefixWord ++ tailWord_593407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593407).length < 2 ^ (prefixWord ++ tailWord_593407).sum := by decide
  have hdescent : baseEnd_593407 < baseStart_593407 := by decide
  rcases family_descends (prefixWord ++ tailWord_593407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593529 : List Nat := [1, 2, 1, 3, 3, 1, 1, 1, 3, 6]
def baseStart_593529 : Nat := 118140960795 + 593529 * 2 ^ 59
def prefixEnd_593529 : Nat := 4983230072969 + 3 ^ 40 * 593529 * 2
def baseEnd_593529 : Nat := 203177106255009032505277

theorem tailTrace_593529 : CollatzResearch.WordTrace tailWord_593529 prefixEnd_593529 203177106255009032505277 := by
  unfold tailWord_593529
  simp only [CollatzResearch.WordTrace]
  refine ⟨21647781066753274528095641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14431854044502183018730427 21647781066753274528095641)
  ·
    refine ⟨16235835800064955896071731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21647781066753274528095641 16235835800064955896071731)
    ·
      refine ⟨24353753700097433844107597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16235835800064955896071731 24353753700097433844107597)
      ·
        refine ⟨9132657637536537691540349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24353753700097433844107597 9132657637536537691540349)
        ·
          refine ⟨3424746614076201634327631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9132657637536537691540349 3424746614076201634327631)
          ·
            refine ⟨5137119921114302451491447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3424746614076201634327631 5137119921114302451491447)
            ·
              refine ⟨7705679881671453677237171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5137119921114302451491447 7705679881671453677237171)
              ·
                refine ⟨11558519822507180515855757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7705679881671453677237171 11558519822507180515855757)
                ·
                  refine ⟨4334444933440192693445909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11558519822507180515855757 4334444933440192693445909)
                  ·
                    refine ⟨203177106255009032505277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4334444933440192693445909 203177106255009032505277)
                    ·
                      rfl

theorem cell22_593529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 3, 6].length) (baseStart_593529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_593529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_593529 prefixEnd_593529 := by exact prefixLift 593529
  have htrace : WordTrace (prefixWord ++ tailWord_593529) baseStart_593529 baseEnd_593529 := by
    simpa [prefixWord, tailWord_593529, baseEnd_593529] using wordTrace_append hprefix tailTrace_593529
  have hstable : (prefixWord ++ tailWord_593529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593529).length < 2 ^ (prefixWord ++ tailWord_593529).sum := by decide
  have hdescent : baseEnd_593529 < baseStart_593529 := by decide
  rcases family_descends (prefixWord ++ tailWord_593529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593546 : List Nat := [3, 1, 2, 3, 2, 1, 2, 1, 1, 6]
def baseStart_593546 : Nat := 118140960795 + 593546 * 2 ^ 59
def prefixEnd_593546 : Nat := 4983230072969 + 3 ^ 40 * 593546 * 2
def baseEnd_593546 : Nat := 203182925702426654830225

theorem tailTrace_593546 : CollatzResearch.WordTrace tailWord_593546 prefixEnd_593546 203182925702426654830225 := by
  unfold tailWord_593546
  simp only [CollatzResearch.WordTrace]
  refine ⟨5412100276922921607866123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14432267405127790954309661 5412100276922921607866123)
  ·
    refine ⟨8118150415384382411799185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5412100276922921607866123 8118150415384382411799185)
    ·
      refine ⟨6088612811538286808849389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8118150415384382411799185 6088612811538286808849389)
      ·
        refine ⟨2283229804326857553318521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6088612811538286808849389 2283229804326857553318521)
        ·
          refine ⟨1712422353245143164988891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2283229804326857553318521 1712422353245143164988891)
          ·
            refine ⟨2568633529867714747483337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1712422353245143164988891 2568633529867714747483337)
            ·
              refine ⟨1926475147400786060612503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2568633529867714747483337 1926475147400786060612503)
              ·
                refine ⟨2889712721101179090918755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1926475147400786060612503 2889712721101179090918755)
                ·
                  refine ⟨4334569081651768636378133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2889712721101179090918755 4334569081651768636378133)
                  ·
                    refine ⟨203182925702426654830225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4334569081651768636378133 203182925702426654830225)
                    ·
                      rfl

theorem cell22_593546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 1, 1, 6].length) (baseStart_593546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_593546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_593546 prefixEnd_593546 := by exact prefixLift 593546
  have htrace : WordTrace (prefixWord ++ tailWord_593546) baseStart_593546 baseEnd_593546 := by
    simpa [prefixWord, tailWord_593546, baseEnd_593546] using wordTrace_append hprefix tailTrace_593546
  have hstable : (prefixWord ++ tailWord_593546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593546).length < 2 ^ (prefixWord ++ tailWord_593546).sum := by decide
  have hdescent : baseEnd_593546 < baseStart_593546 := by decide
  rcases family_descends (prefixWord ++ tailWord_593546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593550 : List Nat := [4, 1, 1, 3, 1, 4, 1, 3, 4]
def baseStart_593550 : Nat := 118140960795 + 593550 * 2 ^ 59
def prefixEnd_593550 : Nat := 4983230072969 + 3 ^ 40 * 593550 * 2
def baseEnd_593550 : Nat := 67728098328057325910071

theorem tailTrace_593550 : CollatzResearch.WordTrace tailWord_593550 prefixEnd_593550 67728098328057325910071 := by
  unfold tailWord_593550
  simp only [CollatzResearch.WordTrace]
  refine ⟨2706068374959649389326263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14432364666451463409740069 2706068374959649389326263)
  ·
    refine ⟨4059102562439474083989395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2706068374959649389326263 4059102562439474083989395)
    ·
      refine ⟨6088653843659211125984093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4059102562439474083989395 6088653843659211125984093)
      ·
        refine ⟨2283245191372204172244035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6088653843659211125984093 2283245191372204172244035)
        ·
          refine ⟨3424867787058306258366053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2283245191372204172244035 3424867787058306258366053)
          ·
            refine ⟨642162710073432423443635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3424867787058306258366053 642162710073432423443635)
            ·
              refine ⟨963244065110148635165453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 642162710073432423443635 963244065110148635165453)
              ·
                refine ⟨361216524416305738187045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 963244065110148635165453 361216524416305738187045)
                ·
                  refine ⟨67728098328057325910071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 361216524416305738187045 67728098328057325910071)
                  ·
                    rfl

theorem cell22_593550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 3, 4].length) (baseStart_593550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_593550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_593550 prefixEnd_593550 := by exact prefixLift 593550
  have htrace : WordTrace (prefixWord ++ tailWord_593550) baseStart_593550 baseEnd_593550 := by
    simpa [prefixWord, tailWord_593550, baseEnd_593550] using wordTrace_append hprefix tailTrace_593550
  have hstable : (prefixWord ++ tailWord_593550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593550).length < 2 ^ (prefixWord ++ tailWord_593550).sum := by decide
  have hdescent : baseEnd_593550 < baseStart_593550 := by decide
  rcases family_descends (prefixWord ++ tailWord_593550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593567 : List Nat := [1, 1, 2, 7, 1, 1, 3, 2, 4]
def baseStart_593567 : Nat := 118140960795 + 593567 * 2 ^ 59
def prefixEnd_593567 : Nat := 4983230072969 + 3 ^ 40 * 593567 * 2
def baseEnd_593567 : Nat := 67730038143863200018387

theorem tailTrace_593567 : CollatzResearch.WordTrace tailWord_593567 prefixEnd_593567 67730038143863200018387 := by
  unfold tailWord_593567
  simp only [CollatzResearch.WordTrace]
  refine ⟨21649167040615607017978955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14432778027077071345319303 21649167040615607017978955)
  ·
    refine ⟨32473750560923410526968433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21649167040615607017978955 32473750560923410526968433)
    ·
      refine ⟨24355312920692557895226325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32473750560923410526968433 24355312920692557895226325)
      ·
        refine ⟨570827646578731825669367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 24355312920692557895226325 570827646578731825669367)
        ·
          refine ⟨856241469868097738504051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 570827646578731825669367 856241469868097738504051)
          ·
            refine ⟨1284362204802146607756077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 856241469868097738504051 1284362204802146607756077)
            ·
              refine ⟨481635826800804977908529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1284362204802146607756077 481635826800804977908529)
              ·
                refine ⟨361226870100603733431397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 481635826800804977908529 361226870100603733431397)
                ·
                  refine ⟨67730038143863200018387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 361226870100603733431397 67730038143863200018387)
                  ·
                    rfl

theorem cell22_593567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 3, 2, 4].length) (baseStart_593567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_593567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_593567 prefixEnd_593567 := by exact prefixLift 593567
  have htrace : WordTrace (prefixWord ++ tailWord_593567) baseStart_593567 baseEnd_593567 := by
    simpa [prefixWord, tailWord_593567, baseEnd_593567] using wordTrace_append hprefix tailTrace_593567
  have hstable : (prefixWord ++ tailWord_593567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593567).length < 2 ^ (prefixWord ++ tailWord_593567).sum := by decide
  have hdescent : baseEnd_593567 < baseStart_593567 := by decide
  rcases family_descends (prefixWord ++ tailWord_593567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593582 : List Nat := [4, 1, 4, 1, 2, 1, 1, 3, 2, 3]
def baseStart_593582 : Nat := 118140960795 + 593582 * 2 ^ 59
def prefixEnd_593582 : Nat := 4983230072969 + 3 ^ 40 * 593582 * 2
def baseEnd_593582 : Nat := 203195249238134560930115

theorem tailTrace_593582 : CollatzResearch.WordTrace tailWord_593582 prefixEnd_593582 203195249238134560930115 := by
  unfold tailWord_593582
  simp only [CollatzResearch.WordTrace]
  refine ⟨2706214266945158072471875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14433142757040843053183333 2706214266945158072471875)
  ·
    refine ⟨4059321400417737108707813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2706214266945158072471875 4059321400417737108707813)
    ·
      refine ⟨761122762578325707882715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4059321400417737108707813 761122762578325707882715)
      ·
        refine ⟨1141684143867488561824073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 761122762578325707882715 1141684143867488561824073)
        ·
          refine ⟨856263107900616421368055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1141684143867488561824073 856263107900616421368055)
          ·
            refine ⟨1284394661850924632052083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 856263107900616421368055 1284394661850924632052083)
            ·
              refine ⟨1926591992776386948078125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1284394661850924632052083 1926591992776386948078125)
              ·
                refine ⟨722471997291145105529297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1926591992776386948078125 722471997291145105529297)
                ·
                  refine ⟨541853997968358829146973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 722471997291145105529297 541853997968358829146973)
                  ·
                    refine ⟨203195249238134560930115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 541853997968358829146973 203195249238134560930115)
                    ·
                      rfl

theorem cell22_593582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_593582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_593582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_593582 prefixEnd_593582 := by exact prefixLift 593582
  have htrace : WordTrace (prefixWord ++ tailWord_593582) baseStart_593582 baseEnd_593582 := by
    simpa [prefixWord, tailWord_593582, baseEnd_593582] using wordTrace_append hprefix tailTrace_593582
  have hstable : (prefixWord ++ tailWord_593582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593582).length < 2 ^ (prefixWord ++ tailWord_593582).sum := by decide
  have hdescent : baseEnd_593582 < baseStart_593582 := by decide
  rcases family_descends (prefixWord ++ tailWord_593582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593619 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 4, 8]
def baseStart_593619 : Nat := 118140960795 + 593619 * 2 ^ 59
def prefixEnd_593619 : Nat := 4983230072969 + 3 ^ 40 * 593619 * 2
def baseEnd_593619 : Nat := 203207915094278797755001

theorem tailTrace_593619 : CollatzResearch.WordTrace tailWord_593619 prefixEnd_593619 203207915094278797755001 := by
  unfold tailWord_593619
  simp only [CollatzResearch.WordTrace]
  refine ⟨21651063636427219898871911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14434042424284813265914607 21651063636427219898871911)
  ·
    refine ⟨32476595454640829848307867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21651063636427219898871911 32476595454640829848307867)
    ·
      refine ⟨48714893181961244772461801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32476595454640829848307867 48714893181961244772461801)
      ·
        refine ⟨36536169886470933579346351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48714893181961244772461801 36536169886470933579346351)
        ·
          refine ⟨54804254829706400369019527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36536169886470933579346351 54804254829706400369019527)
          ·
            refine ⟨82206382244559600553529291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54804254829706400369019527 82206382244559600553529291)
            ·
              refine ⟨123309573366839400830293937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82206382244559600553529291 123309573366839400830293937)
              ·
                refine ⟨92482180025129550622720453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 123309573366839400830293937 92482180025129550622720453)
                ·
                  refine ⟨17340408754711790741760085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 92482180025129550622720453 17340408754711790741760085)
                  ·
                    refine ⟨203207915094278797755001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 17340408754711790741760085 203207915094278797755001)
                    ·
                      rfl

theorem cell22_593619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 8].length) (baseStart_593619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_593619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_593619 prefixEnd_593619 := by exact prefixLift 593619
  have htrace : WordTrace (prefixWord ++ tailWord_593619) baseStart_593619 baseEnd_593619 := by
    simpa [prefixWord, tailWord_593619, baseEnd_593619] using wordTrace_append hprefix tailTrace_593619
  have hstable : (prefixWord ++ tailWord_593619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593619).length < 2 ^ (prefixWord ++ tailWord_593619).sum := by decide
  have hdescent : baseEnd_593619 < baseStart_593619 := by decide
  rcases family_descends (prefixWord ++ tailWord_593619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593636 : List Nat := [2, 3, 1, 1, 1, 3, 1, 1, 5, 4]
def baseStart_593636 : Nat := 118140960795 + 593636 * 2 ^ 59
def prefixEnd_593636 : Nat := 4983230072969 + 3 ^ 40 * 593636 * 2
def baseEnd_593636 : Nat := 203213734541696420079949

theorem tailTrace_593636 : CollatzResearch.WordTrace tailWord_593636 prefixEnd_593636 203213734541696420079949 := by
  unfold tailWord_593636
  simp only [CollatzResearch.WordTrace]
  refine ⟨10825841838682815901120381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14434455784910421201493841 10825841838682815901120381)
  ·
    refine ⟨4059690689506055962920143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10825841838682815901120381 4059690689506055962920143)
    ·
      refine ⟨6089536034259083944380215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4059690689506055962920143 6089536034259083944380215)
      ·
        refine ⟨9134304051388625916570323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6089536034259083944380215 9134304051388625916570323)
        ·
          refine ⟨13701456077082938874855485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9134304051388625916570323 13701456077082938874855485)
          ·
            refine ⟨5138046028906102078070807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13701456077082938874855485 5138046028906102078070807)
            ·
              refine ⟨7707069043359153117106211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5138046028906102078070807 7707069043359153117106211)
              ·
                refine ⟨11560603565038729675659317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7707069043359153117106211 11560603565038729675659317)
                ·
                  refine ⟨1083806584222380907093061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11560603565038729675659317 1083806584222380907093061)
                  ·
                    refine ⟨203213734541696420079949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1083806584222380907093061 203213734541696420079949)
                    ·
                      rfl

theorem cell22_593636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 5, 4].length) (baseStart_593636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_593636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_593636 prefixEnd_593636 := by exact prefixLift 593636
  have htrace : WordTrace (prefixWord ++ tailWord_593636) baseStart_593636 baseEnd_593636 := by
    simpa [prefixWord, tailWord_593636, baseEnd_593636] using wordTrace_append hprefix tailTrace_593636
  have hstable : (prefixWord ++ tailWord_593636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593636).length < 2 ^ (prefixWord ++ tailWord_593636).sum := by decide
  have hdescent : baseEnd_593636 < baseStart_593636 := by decide
  rcases family_descends (prefixWord ++ tailWord_593636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593681 : List Nat := [1, 2, 2, 1, 1, 3, 1, 3, 4, 4]
def baseStart_593681 : Nat := 118140960795 + 593681 * 2 ^ 59
def prefixEnd_593681 : Nat := 4983230072969 + 3 ^ 40 * 593681 * 2
def baseEnd_593681 : Nat := 203229138961331302704811

theorem tailTrace_593681 : CollatzResearch.WordTrace tailWord_593681 prefixEnd_593681 203229138961331302704811 := by
  unfold tailWord_593681
  simp only [CollatzResearch.WordTrace]
  refine ⟨21653324962202604487628897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14435549974801736325085931 21653324962202604487628897)
  ·
    refine ⟨16239993721651953365721673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21653324962202604487628897 16239993721651953365721673)
    ·
      refine ⟨12179995291238965024291255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16239993721651953365721673 12179995291238965024291255)
      ·
        refine ⟨18269992936858447536436883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12179995291238965024291255 18269992936858447536436883)
        ·
          refine ⟨27404989405287671304655325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18269992936858447536436883 27404989405287671304655325)
          ·
            refine ⟨10276871026982876739245747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27404989405287671304655325 10276871026982876739245747)
            ·
              refine ⟨15415306540474315108868621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10276871026982876739245747 15415306540474315108868621)
              ·
                refine ⟨5780739952677868165825733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15415306540474315108868621 5780739952677868165825733)
                ·
                  refine ⟨1083888741127100281092325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5780739952677868165825733 1083888741127100281092325)
                  ·
                    refine ⟨203229138961331302704811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1083888741127100281092325 203229138961331302704811)
                    ·
                      rfl

theorem cell22_593681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 4].length) (baseStart_593681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_593681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_593681 prefixEnd_593681 := by exact prefixLift 593681
  have htrace : WordTrace (prefixWord ++ tailWord_593681) baseStart_593681 baseEnd_593681 := by
    simpa [prefixWord, tailWord_593681, baseEnd_593681] using wordTrace_append hprefix tailTrace_593681
  have hstable : (prefixWord ++ tailWord_593681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593681).length < 2 ^ (prefixWord ++ tailWord_593681).sum := by decide
  have hdescent : baseEnd_593681 < baseStart_593681 := by decide
  rcases family_descends (prefixWord ++ tailWord_593681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593683 : List Nat := [1, 1, 1, 2, 1, 3, 2, 6, 2, 3]
def baseStart_593683 : Nat := 118140960795 + 593683 * 2 ^ 59
def prefixEnd_593683 : Nat := 4983230072969 + 3 ^ 40 * 593683 * 2
def baseEnd_593683 : Nat := 203229823602203964154805

theorem tailTrace_593683 : CollatzResearch.WordTrace tailWord_593683 prefixEnd_593683 203229823602203964154805 := by
  unfold tailWord_593683
  simp only [CollatzResearch.WordTrace]
  refine ⟨21653397908195358829201703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14435598605463572552801135 21653397908195358829201703)
  ·
    refine ⟨32480096862293038243802555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21653397908195358829201703 32480096862293038243802555)
    ·
      refine ⟨48720145293439557365703833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32480096862293038243802555 48720145293439557365703833)
      ·
        refine ⟨36540108970079668024277875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48720145293439557365703833 36540108970079668024277875)
        ·
          refine ⟨54810163455119502036416813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36540108970079668024277875 54810163455119502036416813)
          ·
            refine ⟨20553811295669813263656305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54810163455119502036416813 20553811295669813263656305)
            ·
              refine ⟨15415358471752359947742229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20553811295669813263656305 15415358471752359947742229)
              ·
                refine ⟨722594928363391872550417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15415358471752359947742229 722594928363391872550417)
                ·
                  refine ⟨541946196272543904412813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 722594928363391872550417 541946196272543904412813)
                  ·
                    refine ⟨203229823602203964154805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 541946196272543904412813 203229823602203964154805)
                    ·
                      rfl

theorem cell22_593683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 6, 2, 3].length) (baseStart_593683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_593683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_593683 prefixEnd_593683 := by exact prefixLift 593683
  have htrace : WordTrace (prefixWord ++ tailWord_593683) baseStart_593683 baseEnd_593683 := by
    simpa [prefixWord, tailWord_593683, baseEnd_593683] using wordTrace_append hprefix tailTrace_593683
  have hstable : (prefixWord ++ tailWord_593683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593683).length < 2 ^ (prefixWord ++ tailWord_593683).sum := by decide
  have hdescent : baseEnd_593683 < baseStart_593683 := by decide
  rcases family_descends (prefixWord ++ tailWord_593683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593696 : List Nat := [2, 1, 1, 5, 1, 1, 2, 9]
def baseStart_593696 : Nat := 118140960795 + 593696 * 2 ^ 59
def prefixEnd_593696 : Nat := 4983230072969 + 3 ^ 40 * 593696 * 2
def baseEnd_593696 : Nat := 22581585974208473731085

theorem tailTrace_593696 : CollatzResearch.WordTrace tailWord_593696 prefixEnd_593696 22581585974208473731085 := by
  unfold tailWord_593696
  simp only [CollatzResearch.WordTrace]
  refine ⟨10826936028574131024712471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14435914704765508032949961 10826936028574131024712471)
  ·
    refine ⟨16240404042861196537068707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10826936028574131024712471 16240404042861196537068707)
    ·
      refine ⟨24360606064291794805603061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16240404042861196537068707 24360606064291794805603061)
      ·
        refine ⟨2283806818527355763025287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24360606064291794805603061 2283806818527355763025287)
        ·
          refine ⟨3425710227791033644537931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2283806818527355763025287 3425710227791033644537931)
          ·
            refine ⟨5138565341686550466806897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3425710227791033644537931 5138565341686550466806897)
            ·
              refine ⟨3853924006264912850105173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5138565341686550466806897 3853924006264912850105173)
              ·
                refine ⟨22581585974208473731085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3853924006264912850105173 22581585974208473731085)
                ·
                  rfl

theorem cell22_593696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 9].length) (baseStart_593696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_593696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_593696 prefixEnd_593696 := by exact prefixLift 593696
  have htrace : WordTrace (prefixWord ++ tailWord_593696) baseStart_593696 baseEnd_593696 := by
    simpa [prefixWord, tailWord_593696, baseEnd_593696] using wordTrace_append hprefix tailTrace_593696
  have hstable : (prefixWord ++ tailWord_593696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593696).length < 2 ^ (prefixWord ++ tailWord_593696).sum := by decide
  have hdescent : baseEnd_593696 < baseStart_593696 := by decide
  rcases family_descends (prefixWord ++ tailWord_593696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593700 : List Nat := [2, 3, 1, 3, 2, 3, 1, 1, 1, 5]
def baseStart_593700 : Nat := 118140960795 + 593700 * 2 ^ 59
def prefixEnd_593700 : Nat := 4983230072969 + 3 ^ 40 * 593700 * 2
def baseEnd_593700 : Nat := 203235643049621586479753

theorem tailTrace_593700 : CollatzResearch.WordTrace tailWord_593700 prefixEnd_593700 203235643049621586479753 := by
  unfold tailWord_593700
  simp only [CollatzResearch.WordTrace]
  refine ⟨10827008974566885366285277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14436011966089180488380369 10827008974566885366285277)
  ·
    refine ⟨4060128365462582012356979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10827008974566885366285277 4060128365462582012356979)
    ·
      refine ⟨6090192548193873018535469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4060128365462582012356979 6090192548193873018535469)
      ·
        refine ⟨2283822205572702381950801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6090192548193873018535469 2283822205572702381950801)
        ·
          refine ⟨1712866654179526786463101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2283822205572702381950801 1712866654179526786463101)
          ·
            refine ⟨642324995317322544923663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1712866654179526786463101 642324995317322544923663)
            ·
              refine ⟨963487492975983817385495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 642324995317322544923663 963487492975983817385495)
              ·
                refine ⟨1445231239463975726078243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 963487492975983817385495 1445231239463975726078243)
                ·
                  refine ⟨2167846859195963589117365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1445231239463975726078243 2167846859195963589117365)
                  ·
                    refine ⟨203235643049621586479753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2167846859195963589117365 203235643049621586479753)
                    ·
                      rfl

theorem cell22_593700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 1, 1, 5].length) (baseStart_593700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_593700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_593700 prefixEnd_593700 := by exact prefixLift 593700
  have htrace : WordTrace (prefixWord ++ tailWord_593700) baseStart_593700 baseEnd_593700 := by
    simpa [prefixWord, tailWord_593700, baseEnd_593700] using wordTrace_append hprefix tailTrace_593700
  have hstable : (prefixWord ++ tailWord_593700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593700).length < 2 ^ (prefixWord ++ tailWord_593700).sum := by decide
  have hdescent : baseEnd_593700 < baseStart_593700 := by decide
  rcases family_descends (prefixWord ++ tailWord_593700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593713 : List Nat := [1, 2, 2, 3, 2, 2, 4, 6]
def baseStart_593713 : Nat := 118140960795 + 593713 * 2 ^ 59
def prefixEnd_593713 : Nat := 4983230072969 + 3 ^ 40 * 593713 * 2
def baseEnd_593713 : Nat := 22582232579477098433857

theorem tailTrace_593713 : CollatzResearch.WordTrace tailWord_593713 prefixEnd_593713 22582232579477098433857 := by
  unfold tailWord_593713
  simp only [CollatzResearch.WordTrace]
  refine ⟨21654492098086673952793793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14436328065391115968529195 21654492098086673952793793)
  ·
    refine ⟨16240869073565005464595345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21654492098086673952793793 16240869073565005464595345)
    ·
      refine ⟨12180651805173754098446509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16240869073565005464595345 12180651805173754098446509)
      ·
        refine ⟨4567744426940157786917441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12180651805173754098446509 4567744426940157786917441)
        ·
          refine ⟨3425808320205118340188081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4567744426940157786917441 3425808320205118340188081)
          ·
            refine ⟨2569356240153838755141061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3425808320205118340188081 2569356240153838755141061)
            ·
              refine ⟨481754295028844766588949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2569356240153838755141061 481754295028844766588949)
              ·
                refine ⟨22582232579477098433857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 481754295028844766588949 22582232579477098433857)
                ·
                  rfl

theorem cell22_593713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 4, 6].length) (baseStart_593713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_593713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_593713 prefixEnd_593713 := by exact prefixLift 593713
  have htrace : WordTrace (prefixWord ++ tailWord_593713) baseStart_593713 baseEnd_593713 := by
    simpa [prefixWord, tailWord_593713, baseEnd_593713] using wordTrace_append hprefix tailTrace_593713
  have hstable : (prefixWord ++ tailWord_593713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593713).length < 2 ^ (prefixWord ++ tailWord_593713).sum := by decide
  have hdescent : baseEnd_593713 < baseStart_593713 := by decide
  rcases family_descends (prefixWord ++ tailWord_593713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593745 : List Nat := [1, 2, 2, 1, 5, 1, 3, 1, 3, 3]
def baseStart_593745 : Nat := 118140960795 + 593745 * 2 ^ 59
def prefixEnd_593745 : Nat := 4983230072969 + 3 ^ 40 * 593745 * 2
def baseEnd_593745 : Nat := 203251047469256469104615

theorem tailTrace_593745 : CollatzResearch.WordTrace tailWord_593745 prefixEnd_593745 203251047469256469104615 := by
  unfold tailWord_593745
  simp only [CollatzResearch.WordTrace]
  refine ⟨21655659233970743417958689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14437106155980495611972459 21655659233970743417958689)
  ·
    refine ⟨16241744425478057563469017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21655659233970743417958689 16241744425478057563469017)
    ·
      refine ⟨12181308319108543172601763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16241744425478057563469017 12181308319108543172601763)
      ·
        refine ⟨18271962478662814758902645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12181308319108543172601763 18271962478662814758902645)
        ·
          refine ⟨1712996482374638883647123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18271962478662814758902645 1712996482374638883647123)
          ·
            refine ⟨2569494723561958325470685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1712996482374638883647123 2569494723561958325470685)
            ·
              refine ⟨963560521335734372051507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2569494723561958325470685 963560521335734372051507)
              ·
                refine ⟨1445340782003601558077261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 963560521335734372051507 1445340782003601558077261)
                ·
                  refine ⟨542002793251350584278973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1445340782003601558077261 542002793251350584278973)
                  ·
                    refine ⟨203251047469256469104615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 542002793251350584278973 203251047469256469104615)
                    ·
                      rfl

theorem cell22_593745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 1, 3, 3].length) (baseStart_593745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_593745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_593745 prefixEnd_593745 := by exact prefixLift 593745
  have htrace : WordTrace (prefixWord ++ tailWord_593745) baseStart_593745 baseEnd_593745 := by
    simpa [prefixWord, tailWord_593745, baseEnd_593745] using wordTrace_append hprefix tailTrace_593745
  have hstable : (prefixWord ++ tailWord_593745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593745).length < 2 ^ (prefixWord ++ tailWord_593745).sum := by decide
  have hdescent : baseEnd_593745 < baseStart_593745 := by decide
  rcases family_descends (prefixWord ++ tailWord_593745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593820 : List Nat := [2, 2, 3, 3, 1, 2, 1, 2, 6]
def baseStart_593820 : Nat := 118140960795 + 593820 * 2 ^ 59
def prefixEnd_593820 : Nat := 4983230072969 + 3 ^ 40 * 593820 * 2
def baseEnd_593820 : Nat := 67758907167327091159795

theorem tailTrace_593820 : CollatzResearch.WordTrace tailWord_593820 prefixEnd_593820 67758907167327091159795 := by
  unfold tailWord_593820
  simp only [CollatzResearch.WordTrace]
  refine ⟨10829197354349515613469457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14438929805799354151292609 10829197354349515613469457)
  ·
    refine ⟨8121898015762136710102093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10829197354349515613469457 8121898015762136710102093)
    ·
      refine ⟨3045711755910801266288285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8121898015762136710102093 3045711755910801266288285)
      ·
        refine ⟨1142141908466550474858107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3045711755910801266288285 1142141908466550474858107)
        ·
          refine ⟨1713212862699825712287161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1142141908466550474858107 1713212862699825712287161)
          ·
            refine ⟨1284909647024869284215371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1713212862699825712287161 1284909647024869284215371)
            ·
              refine ⟨1927364470537303926323057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1284909647024869284215371 1927364470537303926323057)
              ·
                refine ⟨1445523352902977944742293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1927364470537303926323057 1445523352902977944742293)
                ·
                  refine ⟨67758907167327091159795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1445523352902977944742293 67758907167327091159795)
                  ·
                    rfl

theorem cell22_593820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 2, 6].length) (baseStart_593820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_593820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_593820 prefixEnd_593820 := by exact prefixLift 593820
  have htrace : WordTrace (prefixWord ++ tailWord_593820) baseStart_593820 baseEnd_593820 := by
    simpa [prefixWord, tailWord_593820, baseEnd_593820] using wordTrace_append hprefix tailTrace_593820
  have hstable : (prefixWord ++ tailWord_593820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593820).length < 2 ^ (prefixWord ++ tailWord_593820).sum := by decide
  have hdescent : baseEnd_593820 < baseStart_593820 := by decide
  rcases family_descends (prefixWord ++ tailWord_593820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593833 : List Nat := [1, 2, 1, 1, 1, 1, 4, 5, 2, 4]
def baseStart_593833 : Nat := 118140960795 + 593833 * 2 ^ 59
def prefixEnd_593833 : Nat := 4983230072969 + 3 ^ 40 * 593833 * 2
def baseEnd_593833 : Nat := 203281171667653572904345

theorem tailTrace_593833 : CollatzResearch.WordTrace tailWord_593833 prefixEnd_593833 203281171667653572904345 := by
  unfold tailWord_593833
  simp only [CollatzResearch.WordTrace]
  refine ⟨21658868857651934447162153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14439245905101289631441435 21658868857651934447162153)
  ·
    refine ⟨16244151643238950835371615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21658868857651934447162153 16244151643238950835371615)
    ·
      refine ⟨24366227464858426253057423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16244151643238950835371615 24366227464858426253057423)
      ·
        refine ⟨36549341197287639379586135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24366227464858426253057423 36549341197287639379586135)
        ·
          refine ⟨54824011795931459069379203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36549341197287639379586135 54824011795931459069379203)
          ·
            refine ⟨82236017693897188604068805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54824011795931459069379203 82236017693897188604068805)
            ·
              refine ⟨15419253317605722863262901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82236017693897188604068805 15419253317605722863262901)
              ·
                refine ⟨1445554998525536518430897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15419253317605722863262901 1445554998525536518430897)
                ·
                  refine ⟨1084166248894152388823173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1445554998525536518430897 1084166248894152388823173)
                  ·
                    refine ⟨203281171667653572904345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1084166248894152388823173 203281171667653572904345)
                    ·
                      rfl

theorem cell22_593833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 5, 2, 4].length) (baseStart_593833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_593833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_593833 prefixEnd_593833 := by exact prefixLift 593833
  have htrace : WordTrace (prefixWord ++ tailWord_593833) baseStart_593833 baseEnd_593833 := by
    simpa [prefixWord, tailWord_593833, baseEnd_593833] using wordTrace_append hprefix tailTrace_593833
  have hstable : (prefixWord ++ tailWord_593833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593833).length < 2 ^ (prefixWord ++ tailWord_593833).sum := by decide
  have hdescent : baseEnd_593833 < baseStart_593833 := by decide
  rcases family_descends (prefixWord ++ tailWord_593833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593880 : List Nat := [2, 1, 2, 2, 2, 2, 1, 4, 3, 3]
def baseStart_593880 : Nat := 118140960795 + 593880 * 2 ^ 59
def prefixEnd_593880 : Nat := 4983230072969 + 3 ^ 40 * 593880 * 2
def baseEnd_593880 : Nat := 203297260728161116979201

theorem tailTrace_593880 : CollatzResearch.WordTrace tailWord_593880 prefixEnd_593880 203297260728161116979201 := by
  unfold tailWord_593880
  simp only [CollatzResearch.WordTrace]
  refine ⟨10830291544240830737061547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14440388725654440982748729 10830291544240830737061547)
  ·
    refine ⟨16245437316361246105592321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10830291544240830737061547 16245437316361246105592321)
    ·
      refine ⟨12184077987270934579194241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16245437316361246105592321 12184077987270934579194241)
      ·
        refine ⟨9138058490453200934395681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12184077987270934579194241 9138058490453200934395681)
        ·
          refine ⟨6853543867839900700796761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9138058490453200934395681 6853543867839900700796761)
          ·
            refine ⟨5140157900879925525597571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6853543867839900700796761 5140157900879925525597571)
            ·
              refine ⟨7710236851319888288396357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5140157900879925525597571 7710236851319888288396357)
              ·
                refine ⟨1445669409622479054074317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7710236851319888288396357 1445669409622479054074317)
                ·
                  refine ⟨542126028608429645277869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1445669409622479054074317 542126028608429645277869)
                  ·
                    refine ⟨203297260728161116979201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 542126028608429645277869 203297260728161116979201)
                    ·
                      rfl

theorem cell22_593880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 4, 3, 3].length) (baseStart_593880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_593880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_593880 prefixEnd_593880 := by exact prefixLift 593880
  have htrace : WordTrace (prefixWord ++ tailWord_593880) baseStart_593880 baseEnd_593880 := by
    simpa [prefixWord, tailWord_593880, baseEnd_593880] using wordTrace_append hprefix tailTrace_593880
  have hstable : (prefixWord ++ tailWord_593880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593880).length < 2 ^ (prefixWord ++ tailWord_593880).sum := by decide
  have hdescent : baseEnd_593880 < baseStart_593880 := by decide
  rcases family_descends (prefixWord ++ tailWord_593880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593882 : List Nat := [3, 1, 1, 2, 5, 2, 2, 6]
def baseStart_593882 : Nat := 118140960795 + 593882 * 2 ^ 59
def prefixEnd_593882 : Nat := 4983230072969 + 3 ^ 40 * 593882 * 2
def baseEnd_593882 : Nat := 22588660596559308714355

theorem tailTrace_593882 : CollatzResearch.WordTrace tailWord_593882 prefixEnd_593882 22588660596559308714355 := by
  unfold tailWord_593882
  simp only [CollatzResearch.WordTrace]
  refine ⟨5415164008618603953923975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14440437356316277210463933 5415164008618603953923975)
  ·
    refine ⟨8122746012927905930885963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5415164008618603953923975 8122746012927905930885963)
    ·
      refine ⟨12184119019391858896328945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8122746012927905930885963 12184119019391858896328945)
      ·
        refine ⟨9138089264543894172246709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12184119019391858896328945 9138089264543894172246709)
        ·
          refine ⟨856695868550990078648129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9138089264543894172246709 856695868550990078648129)
          ·
            refine ⟨642521901413242558986097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 856695868550990078648129 642521901413242558986097)
            ·
              refine ⟨481891426059931919239573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 642521901413242558986097 481891426059931919239573)
              ·
                refine ⟨22588660596559308714355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 481891426059931919239573 22588660596559308714355)
                ·
                  rfl

theorem cell22_593882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 2, 6].length) (baseStart_593882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_593882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_593882 prefixEnd_593882 := by exact prefixLift 593882
  have htrace : WordTrace (prefixWord ++ tailWord_593882) baseStart_593882 baseEnd_593882 := by
    simpa [prefixWord, tailWord_593882, baseEnd_593882] using wordTrace_append hprefix tailTrace_593882
  have hstable : (prefixWord ++ tailWord_593882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593882).length < 2 ^ (prefixWord ++ tailWord_593882).sum := by decide
  have hdescent : baseEnd_593882 < baseStart_593882 := by decide
  rcases family_descends (prefixWord ++ tailWord_593882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593927 : List Nat := [1, 1, 4, 3, 1, 2, 4, 1, 5]
def baseStart_593927 : Nat := 118140960795 + 593927 * 2 ^ 59
def prefixEnd_593927 : Nat := 4983230072969 + 3 ^ 40 * 593927 * 2
def baseEnd_593927 : Nat := 67771116596222887018019

theorem tailTrace_593927 : CollatzResearch.WordTrace tailWord_593927 prefixEnd_593927 67771116596222887018019 := by
  unfold tailWord_593927
  simp only [CollatzResearch.WordTrace]
  refine ⟨21662297319311388501084035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14441531546207592334056023 21662297319311388501084035)
  ·
    refine ⟨32493445978967082751626053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21662297319311388501084035 32493445978967082751626053)
    ·
      refine ⟨6092521121056328015929885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32493445978967082751626053 6092521121056328015929885)
      ·
        refine ⟨2284695420396123005973707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6092521121056328015929885 2284695420396123005973707)
        ·
          refine ⟨3427043130594184508960561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2284695420396123005973707 3427043130594184508960561)
          ·
            refine ⟨2570282347945638381720421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3427043130594184508960561 2570282347945638381720421)
            ·
              refine ⟨481927940239807196572579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2570282347945638381720421 481927940239807196572579)
              ·
                refine ⟨722891910359710794858869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 481927940239807196572579 722891910359710794858869)
                ·
                  refine ⟨67771116596222887018019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 722891910359710794858869 67771116596222887018019)
                  ·
                    rfl

theorem cell22_593927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 4, 1, 5].length) (baseStart_593927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_593927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_593927 prefixEnd_593927 := by exact prefixLift 593927
  have htrace : WordTrace (prefixWord ++ tailWord_593927) baseStart_593927 baseEnd_593927 := by
    simpa [prefixWord, tailWord_593927, baseEnd_593927] using wordTrace_append hprefix tailTrace_593927
  have hstable : (prefixWord ++ tailWord_593927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593927).length < 2 ^ (prefixWord ++ tailWord_593927).sum := by decide
  have hdescent : baseEnd_593927 < baseStart_593927 := by decide
  rcases family_descends (prefixWord ++ tailWord_593927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
