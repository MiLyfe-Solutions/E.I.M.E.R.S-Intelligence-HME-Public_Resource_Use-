import V185TrunkScan22Chunk281

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2515519 : List Nat := [1, 1, 2, 2, 3, 2, 3, 3, 5]
def baseStart_2515519 : Nat := 118140960795 + 2515519 * 2 ^ 59
def prefixEnd_2515519 : Nat := 4983230072969 + 3 ^ 40 * 2515519 * 2
def baseEnd_2515519 : Nat := 287037853892766389787521

theorem tailTrace_2515519 : CollatzResearch.WordTrace tailWord_2515519 prefixEnd_2515519 287037853892766389787521 := by
  unfold tailWord_2515519
  simp only [CollatzResearch.WordTrace]
  refine ⟨91748515373711754286797611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61165676915807836191198407 91748515373711754286797611)
  ·
    refine ⟨137622773060567631430196417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91748515373711754286797611 137622773060567631430196417)
    ·
      refine ⟨103217079795425723572647313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137622773060567631430196417 103217079795425723572647313)
      ·
        refine ⟨77412809846569292679485485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103217079795425723572647313 77412809846569292679485485)
        ·
          refine ⟨29029803692463484754807057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77412809846569292679485485 29029803692463484754807057)
          ·
            refine ⟨21772352769347613566105293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29029803692463484754807057 21772352769347613566105293)
            ·
              refine ⟨8164632288505355087289485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21772352769347613566105293 8164632288505355087289485)
              ·
                refine ⟨3061737108189508157733557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8164632288505355087289485 3061737108189508157733557)
                ·
                  refine ⟨287037853892766389787521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3061737108189508157733557 287037853892766389787521)
                  ·
                    rfl

theorem cell22_2515519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 3, 5].length) (baseStart_2515519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2515519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2515519 prefixEnd_2515519 := by exact prefixLift 2515519
  have htrace : WordTrace (prefixWord ++ tailWord_2515519) baseStart_2515519 baseEnd_2515519 := by
    simpa [prefixWord, tailWord_2515519, baseEnd_2515519] using wordTrace_append hprefix tailTrace_2515519
  have hstable : (prefixWord ++ tailWord_2515519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515519).length < 2 ^ (prefixWord ++ tailWord_2515519).sum := by decide
  have hdescent : baseEnd_2515519 < baseStart_2515519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515557 : List Nat := [1, 3, 1, 3, 4, 2, 2, 2, 1, 3]
def baseStart_2515557 : Nat := 118140960795 + 2515557 * 2 ^ 59
def prefixEnd_2515557 : Nat := 4983230072969 + 3 ^ 40 * 2515557 * 2
def baseEnd_2515557 : Nat := 861126569854879736912447

theorem tailTrace_2515557 : CollatzResearch.WordTrace tailWord_2515557 prefixEnd_2515557 861126569854879736912447 := by
  unfold tailWord_2515557
  simp only [CollatzResearch.WordTrace]
  refine ⟨91749901347574086776680925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61166600898382724517787283 91749901347574086776680925)
  ·
    refine ⟨34406213005340282541255347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91749901347574086776680925 34406213005340282541255347)
    ·
      refine ⟨51609319508010423811883021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34406213005340282541255347 51609319508010423811883021)
      ·
        refine ⟨19353494815503908929456133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51609319508010423811883021 19353494815503908929456133)
        ·
          refine ⟨3628780277906982924273025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19353494815503908929456133 3628780277906982924273025)
          ·
            refine ⟨2721585208430237193204769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3628780277906982924273025 2721585208430237193204769)
            ·
              refine ⟨2041188906322677894903577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2721585208430237193204769 2041188906322677894903577)
              ·
                refine ⟨1530891679742008421177683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2041188906322677894903577 1530891679742008421177683)
                ·
                  refine ⟨2296337519613012631766525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1530891679742008421177683 2296337519613012631766525)
                  ·
                    refine ⟨861126569854879736912447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2296337519613012631766525 861126569854879736912447)
                    ·
                      rfl

theorem cell22_2515557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 2, 2, 1, 3].length) (baseStart_2515557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2515557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2515557 prefixEnd_2515557 := by exact prefixLift 2515557
  have htrace : WordTrace (prefixWord ++ tailWord_2515557) baseStart_2515557 baseEnd_2515557 := by
    simpa [prefixWord, tailWord_2515557, baseEnd_2515557] using wordTrace_append hprefix tailTrace_2515557
  have hstable : (prefixWord ++ tailWord_2515557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515557).length < 2 ^ (prefixWord ++ tailWord_2515557).sum := by decide
  have hdescent : baseEnd_2515557 < baseStart_2515557 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515566 : List Nat := [4, 1, 2, 2, 2, 1, 1, 2, 3, 4]
def baseStart_2515566 : Nat := 118140960795 + 2515566 * 2 ^ 59
def prefixEnd_2515566 : Nat := 4983230072969 + 3 ^ 40 * 2515566 * 2
def baseEnd_2515566 : Nat := 861129650738806713437419

theorem tailTrace_2515566 : CollatzResearch.WordTrace tailWord_2515566 prefixEnd_2515566 861129650738806713437419 := by
  unfold tailWord_2515566
  simp only [CollatzResearch.WordTrace]
  refine ⟨11468778700567685164219819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61166819736360987542505701 11468778700567685164219819)
  ·
    refine ⟨17203168050851527746329729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11468778700567685164219819 17203168050851527746329729)
    ·
      refine ⟨12902376038138645809747297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17203168050851527746329729 12902376038138645809747297)
      ·
        refine ⟨9676782028603984357310473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12902376038138645809747297 9676782028603984357310473)
        ·
          refine ⟨7257586521452988267982855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9676782028603984357310473 7257586521452988267982855)
          ·
            refine ⟨10886379782179482401974283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7257586521452988267982855 10886379782179482401974283)
            ·
              refine ⟨16329569673269223602961425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10886379782179482401974283 16329569673269223602961425)
              ·
                refine ⟨12247177254951917702221069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16329569673269223602961425 12247177254951917702221069)
                ·
                  refine ⟨4592691470606969138332901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12247177254951917702221069 4592691470606969138332901)
                  ·
                    refine ⟨861129650738806713437419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4592691470606969138332901 861129650738806713437419)
                    ·
                      rfl

theorem cell22_2515566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_2515566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2515566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2515566 prefixEnd_2515566 := by exact prefixLift 2515566
  have htrace : WordTrace (prefixWord ++ tailWord_2515566) baseStart_2515566 baseEnd_2515566 := by
    simpa [prefixWord, tailWord_2515566, baseEnd_2515566] using wordTrace_append hprefix tailTrace_2515566
  have hstable : (prefixWord ++ tailWord_2515566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515566).length < 2 ^ (prefixWord ++ tailWord_2515566).sum := by decide
  have hdescent : baseEnd_2515566 < baseStart_2515566 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515581 : List Nat := [1, 4, 1, 1, 5, 1, 1, 2, 6]
def baseStart_2515581 : Nat := 118140960795 + 2515581 * 2 ^ 59
def prefixEnd_2515581 : Nat := 4983230072969 + 3 ^ 40 * 2515581 * 2
def baseEnd_2515581 : Nat := 287044928515117224770791

theorem tailTrace_2515581 : CollatzResearch.WordTrace tailWord_2515581 prefixEnd_2515581 287044928515117224770791 := by
  unfold tailWord_2515581
  simp only [CollatzResearch.WordTrace]
  refine ⟨91750776699487138875554597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61167184466324759250369731 91750776699487138875554597)
  ·
    refine ⟨17203270631153838539166487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91750776699487138875554597 17203270631153838539166487)
    ·
      refine ⟨25804905946730757808749731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17203270631153838539166487 25804905946730757808749731)
      ·
        refine ⟨38707358920096136713124597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25804905946730757808749731 38707358920096136713124597)
        ·
          refine ⟨3628814898759012816855431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38707358920096136713124597 3628814898759012816855431)
          ·
            refine ⟨5443222348138519225283147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3628814898759012816855431 5443222348138519225283147)
            ·
              refine ⟨8164833522207778837924721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5443222348138519225283147 8164833522207778837924721)
              ·
                refine ⟨6123625141655834128443541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8164833522207778837924721 6123625141655834128443541)
                ·
                  refine ⟨287044928515117224770791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6123625141655834128443541 287044928515117224770791)
                  ·
                    rfl

theorem cell22_2515581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 2, 6].length) (baseStart_2515581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2515581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2515581 prefixEnd_2515581 := by exact prefixLift 2515581
  have htrace : WordTrace (prefixWord ++ tailWord_2515581) baseStart_2515581 baseEnd_2515581 := by
    simpa [prefixWord, tailWord_2515581, baseEnd_2515581] using wordTrace_append hprefix tailTrace_2515581
  have hstable : (prefixWord ++ tailWord_2515581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515581).length < 2 ^ (prefixWord ++ tailWord_2515581).sum := by decide
  have hdescent : baseEnd_2515581 < baseStart_2515581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515598 : List Nat := [4, 1, 1, 3, 1, 1, 4, 3, 4]
def baseStart_2515598 : Nat := 118140960795 + 2515598 * 2 ^ 59
def prefixEnd_2515598 : Nat := 4983230072969 + 3 ^ 40 * 2515598 * 2
def baseEnd_2515598 : Nat := 287046868330923098879107

theorem tailTrace_2515598 : CollatzResearch.WordTrace tailWord_2515598 prefixEnd_2515598 287046868330923098879107 := by
  unfold tailWord_2515598
  simp only [CollatzResearch.WordTrace]
  refine ⟨11468924592553193847365431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61167597826950367185948965 11468924592553193847365431)
  ·
    refine ⟨17203386888829790771048147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11468924592553193847365431 17203386888829790771048147)
    ·
      refine ⟨25805080333244686156572221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17203386888829790771048147 25805080333244686156572221)
      ·
        refine ⟨9676905124966757308714583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25805080333244686156572221 9676905124966757308714583)
        ·
          refine ⟨14515357687450135963071875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9676905124966757308714583 14515357687450135963071875)
          ·
            refine ⟨21773036531175203944607813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14515357687450135963071875 21773036531175203944607813)
            ·
              refine ⟨4082444349595350739613965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21773036531175203944607813 4082444349595350739613965)
              ·
                refine ⟨1530916631098256527355237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4082444349595350739613965 1530916631098256527355237)
                ·
                  refine ⟨287046868330923098879107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1530916631098256527355237 287046868330923098879107)
                  ·
                    rfl

theorem cell22_2515598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 3, 4].length) (baseStart_2515598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2515598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2515598 prefixEnd_2515598 := by exact prefixLift 2515598
  have htrace : WordTrace (prefixWord ++ tailWord_2515598) baseStart_2515598 baseEnd_2515598 := by
    simpa [prefixWord, tailWord_2515598, baseEnd_2515598] using wordTrace_append hprefix tailTrace_2515598
  have hstable : (prefixWord ++ tailWord_2515598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515598).length < 2 ^ (prefixWord ++ tailWord_2515598).sum := by decide
  have hdescent : baseEnd_2515598 < baseStart_2515598 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515613 : List Nat := [1, 4, 2, 1, 1, 1, 5, 2, 2, 3]
def baseStart_2515613 : Nat := 118140960795 + 2515613 * 2 ^ 59
def prefixEnd_2515613 : Nat := 4983230072969 + 3 ^ 40 * 2515613 * 2
def baseEnd_2515613 : Nat := 861145739799314257512275

theorem tailTrace_2515613 : CollatzResearch.WordTrace tailWord_2515613 prefixEnd_2515613 861145739799314257512275 := by
  unfold tailWord_2515613
  simp only [CollatzResearch.WordTrace]
  refine ⟨91751943835371208340719493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61167962556914138893812995 91751943835371208340719493)
  ·
    refine ⟨17203489469132101563884905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91751943835371208340719493 17203489469132101563884905)
    ·
      refine ⟨12902617101849076172913679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17203489469132101563884905 12902617101849076172913679)
      ·
        refine ⟨19353925652773614259370519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12902617101849076172913679 19353925652773614259370519)
        ·
          refine ⟨29030888479160421389055779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19353925652773614259370519 29030888479160421389055779)
          ·
            refine ⟨43546332718740632083583669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29030888479160421389055779 43546332718740632083583669)
            ·
              refine ⟨4082468692381934257835969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43546332718740632083583669 4082468692381934257835969)
              ·
                refine ⟨3061851519286450693376977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4082468692381934257835969 3061851519286450693376977)
                ·
                  refine ⟨2296388639464838020032733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3061851519286450693376977 2296388639464838020032733)
                  ·
                    refine ⟨861145739799314257512275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2296388639464838020032733 861145739799314257512275)
                    ·
                      rfl

theorem cell22_2515613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 2, 2, 3].length) (baseStart_2515613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2515613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2515613 prefixEnd_2515613 := by exact prefixLift 2515613
  have htrace : WordTrace (prefixWord ++ tailWord_2515613) baseStart_2515613 baseEnd_2515613 := by
    simpa [prefixWord, tailWord_2515613, baseEnd_2515613] using wordTrace_append hprefix tailTrace_2515613
  have hstable : (prefixWord ++ tailWord_2515613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515613).length < 2 ^ (prefixWord ++ tailWord_2515613).sum := by decide
  have hdescent : baseEnd_2515613 < baseStart_2515613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515630 : List Nat := [4, 1, 4, 1, 1, 3, 1, 1, 1, 5]
def baseStart_2515630 : Nat := 118140960795 + 2515630 * 2 ^ 59
def prefixEnd_2515630 : Nat := 4983230072969 + 3 ^ 40 * 2515630 * 2
def baseEnd_2515630 : Nat := 861151559246731879837223

theorem tailTrace_2515630 : CollatzResearch.WordTrace tailWord_2515630 prefixEnd_2515630 861151559246731879837223 := by
  unfold tailWord_2515630
  simp only [CollatzResearch.WordTrace]
  refine ⟨11469070484538702530511043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61168375917539746829392229 11469070484538702530511043)
  ·
    refine ⟨17203605726808053795766565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11469070484538702530511043 17203605726808053795766565)
    ·
      refine ⟨3225676073776510086706231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17203605726808053795766565 3225676073776510086706231)
      ·
        refine ⟨4838514110664765130059347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3225676073776510086706231 4838514110664765130059347)
        ·
          refine ⟨7257771165997147695089021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4838514110664765130059347 7257771165997147695089021)
          ·
            refine ⟨2721664187248930385658383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7257771165997147695089021 2721664187248930385658383)
            ·
              refine ⟨4082496280873395578487575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2721664187248930385658383 4082496280873395578487575)
              ·
                refine ⟨6123744421310093367731363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4082496280873395578487575 6123744421310093367731363)
                ·
                  refine ⟨9185616631965140051597045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6123744421310093367731363 9185616631965140051597045)
                  ·
                    refine ⟨861151559246731879837223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9185616631965140051597045 861151559246731879837223)
                    ·
                      rfl

theorem cell22_2515630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_2515630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2515630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2515630 prefixEnd_2515630 := by exact prefixLift 2515630
  have htrace : WordTrace (prefixWord ++ tailWord_2515630) baseStart_2515630 baseEnd_2515630 := by
    simpa [prefixWord, tailWord_2515630, baseEnd_2515630] using wordTrace_append hprefix tailTrace_2515630
  have hstable : (prefixWord ++ tailWord_2515630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515630).length < 2 ^ (prefixWord ++ tailWord_2515630).sum := by decide
  have hdescent : baseEnd_2515630 < baseStart_2515630 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515649 : List Nat := [1, 2, 6, 2, 2, 1, 1, 3, 4]
def baseStart_2515649 : Nat := 118140960795 + 2515649 * 2 ^ 59
def prefixEnd_2515649 : Nat := 4983230072969 + 3 ^ 40 * 2515649 * 2
def baseEnd_2515649 : Nat := 287052687778340721204055

theorem tailTrace_2515649 : CollatzResearch.WordTrace tailWord_2515649 prefixEnd_2515649 287052687778340721204055 := by
  unfold tailWord_2515649
  simp only [CollatzResearch.WordTrace]
  refine ⟨91753256863240786489030001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61168837908827190992686667 91753256863240786489030001)
  ·
    refine ⟨68814942647430589866772501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91753256863240786489030001 68814942647430589866772501)
    ·
      refine ⟨3225700436598308900004961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 68814942647430589866772501 3225700436598308900004961)
      ·
        refine ⟨2419275327448731675003721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3225700436598308900004961 2419275327448731675003721)
        ·
          refine ⟨1814456495586548756252791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2419275327448731675003721 1814456495586548756252791)
          ·
            refine ⟨2721684743379823134379187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1814456495586548756252791 2721684743379823134379187)
            ·
              refine ⟨4082527115069734701568781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2721684743379823134379187 4082527115069734701568781)
              ·
                refine ⟨1530947668151150513088293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4082527115069734701568781 1530947668151150513088293)
                ·
                  refine ⟨287052687778340721204055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1530947668151150513088293 287052687778340721204055)
                  ·
                    rfl

theorem cell22_2515649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 3, 4].length) (baseStart_2515649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2515649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2515649 prefixEnd_2515649 := by exact prefixLift 2515649
  have htrace : WordTrace (prefixWord ++ tailWord_2515649) baseStart_2515649 baseEnd_2515649 := by
    simpa [prefixWord, tailWord_2515649, baseEnd_2515649] using wordTrace_append hprefix tailTrace_2515649
  have hstable : (prefixWord ++ tailWord_2515649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515649).length < 2 ^ (prefixWord ++ tailWord_2515649).sum := by decide
  have hdescent : baseEnd_2515649 < baseStart_2515649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515688 : List Nat := [2, 1, 4, 1, 4, 1, 1, 3, 5]
def baseStart_2515688 : Nat := 118140960795 + 2515688 * 2 ^ 59
def prefixEnd_2515688 : Nat := 4983230072969 + 3 ^ 40 * 2515688 * 2
def baseEnd_2515688 : Nat := 287057137944013020629015

theorem tailTrace_2515688 : CollatzResearch.WordTrace tailWord_2515688 prefixEnd_2515688 287057137944013020629015 := by
  unfold tailWord_2515688
  simp only [CollatzResearch.WordTrace]
  refine ⟨45877339655049748074849859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61169786206732997433133145 45877339655049748074849859)
  ·
    refine ⟨68816009482574622112274789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45877339655049748074849859 68816009482574622112274789)
    ·
      refine ⟨12903001777982741646051523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68816009482574622112274789 12903001777982741646051523)
      ·
        refine ⟨19354502666974112469077285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12903001777982741646051523 19354502666974112469077285)
        ·
          refine ⟨3628969250057646087951991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19354502666974112469077285 3628969250057646087951991)
          ·
            refine ⟨5443453875086469131927987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3628969250057646087951991 5443453875086469131927987)
            ·
              refine ⟨8165180812629703697891981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5443453875086469131927987 8165180812629703697891981)
              ·
                refine ⟨3061942804736138886709493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8165180812629703697891981 3061942804736138886709493)
                ·
                  refine ⟨287057137944013020629015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3061942804736138886709493 287057137944013020629015)
                  ·
                    rfl

theorem cell22_2515688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 3, 5].length) (baseStart_2515688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2515688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2515688 prefixEnd_2515688 := by exact prefixLift 2515688
  have htrace : WordTrace (prefixWord ++ tailWord_2515688) baseStart_2515688 baseEnd_2515688 := by
    simpa [prefixWord, tailWord_2515688, baseEnd_2515688] using wordTrace_append hprefix tailTrace_2515688
  have hstable : (prefixWord ++ tailWord_2515688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515688).length < 2 ^ (prefixWord ++ tailWord_2515688).sum := by decide
  have hdescent : baseEnd_2515688 < baseStart_2515688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515699 : List Nat := [1, 1, 1, 2, 2, 3, 1, 3, 8]
def baseStart_2515699 : Nat := 118140960795 + 2515699 * 2 ^ 59
def prefixEnd_2515699 : Nat := 4983230072969 + 3 ^ 40 * 2515699 * 2
def baseEnd_2515699 : Nat := 287058393118946233287337

theorem tailTrace_2515699 : CollatzResearch.WordTrace tailWord_2515699 prefixEnd_2515699 287058393118946233287337 := by
  unfold tailWord_2515699
  simp only [CollatzResearch.WordTrace]
  refine ⟨91755080513059645028350151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61170053675373096685566767 91755080513059645028350151)
  ·
    refine ⟨137632620769589467542525227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91755080513059645028350151 137632620769589467542525227)
    ·
      refine ⟨206448931154384201313787841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137632620769589467542525227 206448931154384201313787841)
      ·
        refine ⟨154836698365788150985340881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 206448931154384201313787841 154836698365788150985340881)
        ·
          refine ⟨116127523774341113239005661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154836698365788150985340881 116127523774341113239005661)
          ·
            refine ⟨43547821415377917464627123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116127523774341113239005661 43547821415377917464627123)
            ·
              refine ⟨65321732123066876196940685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43547821415377917464627123 65321732123066876196940685)
              ·
                refine ⟨24495649546150078573852757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65321732123066876196940685 24495649546150078573852757)
                ·
                  refine ⟨287058393118946233287337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24495649546150078573852757 287058393118946233287337)
                  ·
                    rfl

theorem cell22_2515699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 8].length) (baseStart_2515699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2515699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2515699 prefixEnd_2515699 := by exact prefixLift 2515699
  have htrace : WordTrace (prefixWord ++ tailWord_2515699) baseStart_2515699 baseEnd_2515699 := by
    simpa [prefixWord, tailWord_2515699, baseEnd_2515699] using wordTrace_append hprefix tailTrace_2515699
  have hstable : (prefixWord ++ tailWord_2515699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515699).length < 2 ^ (prefixWord ++ tailWord_2515699).sum := by decide
  have hdescent : baseEnd_2515699 < baseStart_2515699 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515733 : List Nat := [1, 3, 2, 1, 2, 2, 3, 4, 4]
def baseStart_2515733 : Nat := 118140960795 + 2515733 * 2 ^ 59
def prefixEnd_2515733 : Nat := 4983230072969 + 3 ^ 40 * 2515733 * 2
def baseEnd_2515733 : Nat := 287062272750557981503969

theorem tailTrace_2515733 : CollatzResearch.WordTrace tailWord_2515733 prefixEnd_2515733 287062272750557981503969 := by
  unfold tailWord_2515733
  simp only [CollatzResearch.WordTrace]
  refine ⟨91756320594936468835087853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61170880396624312556725235 91756320594936468835087853)
  ·
    refine ⟨34408620223101175813157945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91756320594936468835087853 34408620223101175813157945)
    ·
      refine ⟨25806465167325881859868459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34408620223101175813157945 25806465167325881859868459)
      ·
        refine ⟨38709697750988822789802689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25806465167325881859868459 38709697750988822789802689)
        ·
          refine ⟨29032273313241617092352017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38709697750988822789802689 29032273313241617092352017)
          ·
            refine ⟨21774204984931212819264013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29032273313241617092352017 21774204984931212819264013)
            ·
              refine ⟨8165326869349204807224005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21774204984931212819264013 8165326869349204807224005)
              ·
                refine ⟨1530998788002975901354501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8165326869349204807224005 1530998788002975901354501)
                ·
                  refine ⟨287062272750557981503969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1530998788002975901354501 287062272750557981503969)
                  ·
                    rfl

theorem cell22_2515733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 4, 4].length) (baseStart_2515733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2515733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2515733 prefixEnd_2515733 := by exact prefixLift 2515733
  have htrace : WordTrace (prefixWord ++ tailWord_2515733) baseStart_2515733 baseEnd_2515733 := by
    simpa [prefixWord, tailWord_2515733, baseEnd_2515733] using wordTrace_append hprefix tailTrace_2515733
  have hstable : (prefixWord ++ tailWord_2515733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515733).length < 2 ^ (prefixWord ++ tailWord_2515733).sum := by decide
  have hdescent : baseEnd_2515733 < baseStart_2515733 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515763 : List Nat := [1, 1, 1, 2, 6, 1, 3, 1, 2, 4]
def baseStart_2515763 : Nat := 118140960795 + 2515763 * 2 ^ 59
def prefixEnd_2515763 : Nat := 4983230072969 + 3 ^ 40 * 2515763 * 2
def baseEnd_2515763 : Nat := 861197087864763866261815

theorem tailTrace_2515763 : CollatzResearch.WordTrace tailWord_2515763 prefixEnd_2515763 861197087864763866261815 := by
  unfold tailWord_2515763
  simp only [CollatzResearch.WordTrace]
  refine ⟨91757414784827783958679943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61171609856551855972453295 91757414784827783958679943)
  ·
    refine ⟨137636122177241675938019915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91757414784827783958679943 137636122177241675938019915)
    ·
      refine ⟨206454183265862513907029873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137636122177241675938019915 206454183265862513907029873)
      ·
        refine ⟨154840637449396885430272405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 206454183265862513907029873 154840637449396885430272405)
        ·
          refine ⟨7258154880440479004544019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 154840637449396885430272405 7258154880440479004544019)
          ·
            refine ⟨10887232320660718506816029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7258154880440479004544019 10887232320660718506816029)
            ·
              refine ⟨4082712120247769440056011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10887232320660718506816029 4082712120247769440056011)
              ·
                refine ⟨6124068180371654160084017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4082712120247769440056011 6124068180371654160084017)
                ·
                  refine ⟨4593051135278740620063013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6124068180371654160084017 4593051135278740620063013)
                  ·
                    refine ⟨861197087864763866261815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4593051135278740620063013 861197087864763866261815)
                    ·
                      rfl

theorem cell22_2515763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 1, 2, 4].length) (baseStart_2515763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2515763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2515763 prefixEnd_2515763 := by exact prefixLift 2515763
  have htrace : WordTrace (prefixWord ++ tailWord_2515763) baseStart_2515763 baseEnd_2515763 := by
    simpa [prefixWord, tailWord_2515763, baseEnd_2515763] using wordTrace_append hprefix tailTrace_2515763
  have hstable : (prefixWord ++ tailWord_2515763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515763).length < 2 ^ (prefixWord ++ tailWord_2515763).sum := by decide
  have hdescent : baseEnd_2515763 < baseStart_2515763 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515896 : List Nat := [2, 1, 2, 1, 2, 14]
def baseStart_2515896 : Nat := 118140960795 + 2515896 * 2 ^ 59
def prefixEnd_2515896 : Nat := 4983230072969 + 3 ^ 40 * 2515896 * 2
def baseEnd_2515896 : Nat := 10632624894849331514647

theorem tailTrace_2515896 : CollatzResearch.WordTrace tailWord_2515896 prefixEnd_2515896 10632624894849331514647 := by
  unfold tailWord_2515896
  simp only [CollatzResearch.WordTrace]
  refine ⟨45881132846672973836635771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61174843795563965115514361 45881132846672973836635771)
  ·
    refine ⟨68821699270009460754953657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45881132846672973836635771 68821699270009460754953657)
    ·
      refine ⟨51616274452507095566215243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68821699270009460754953657 51616274452507095566215243)
      ·
        refine ⟨77424411678760643349322865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51616274452507095566215243 77424411678760643349322865)
        ·
          refine ⟨58068308759070482511992149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77424411678760643349322865 58068308759070482511992149)
          ·
            refine ⟨10632624894849331514647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 58068308759070482511992149 10632624894849331514647)
            ·
              rfl

theorem cell22_2515896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 14].length) (baseStart_2515896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2515896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2515896 prefixEnd_2515896 := by exact prefixLift 2515896
  have htrace : WordTrace (prefixWord ++ tailWord_2515896) baseStart_2515896 baseEnd_2515896 := by
    simpa [prefixWord, tailWord_2515896, baseEnd_2515896] using wordTrace_append hprefix tailTrace_2515896
  have hstable : (prefixWord ++ tailWord_2515896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515896).length < 2 ^ (prefixWord ++ tailWord_2515896).sum := by decide
  have hdescent : baseEnd_2515896 < baseStart_2515896 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515898 : List Nat := [3, 1, 1, 1, 2, 1, 3, 4, 2, 4]
def baseStart_2515898 : Nat := 118140960795 + 2515898 * 2 ^ 59
def prefixEnd_2515898 : Nat := 4983230072969 + 3 ^ 40 * 2515898 * 2
def baseEnd_2515898 : Nat := 861243301123668514136401

theorem tailTrace_2515898 : CollatzResearch.WordTrace tailWord_2515898 prefixEnd_2515898 861243301123668514136401 := by
  unfold tailWord_2515898
  simp only [CollatzResearch.WordTrace]
  refine ⟨22940584659834675503711087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61174892426225801343229565 22940584659834675503711087)
  ·
    refine ⟨34410876989752013255566631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22940584659834675503711087 34410876989752013255566631)
    ·
      refine ⟨51616315484628019883349947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34410876989752013255566631 51616315484628019883349947)
      ·
        refine ⟨77424473226942029825024921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51616315484628019883349947 77424473226942029825024921)
        ·
          refine ⟨58068354920206522368768691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77424473226942029825024921 58068354920206522368768691)
          ·
            refine ⟨87102532380309783553153037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58068354920206522368768691 87102532380309783553153037)
            ·
              refine ⟨32663449642616168832432389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87102532380309783553153037 32663449642616168832432389)
              ·
                refine ⟨6124396807990531656081073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32663449642616168832432389 6124396807990531656081073)
                ·
                  refine ⟨4593297605992898742060805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6124396807990531656081073 4593297605992898742060805)
                  ·
                    refine ⟨861243301123668514136401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4593297605992898742060805 861243301123668514136401)
                    ·
                      rfl

theorem cell22_2515898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 4, 2, 4].length) (baseStart_2515898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2515898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2515898 prefixEnd_2515898 := by exact prefixLift 2515898
  have htrace : WordTrace (prefixWord ++ tailWord_2515898) baseStart_2515898 baseEnd_2515898 := by
    simpa [prefixWord, tailWord_2515898, baseEnd_2515898] using wordTrace_append hprefix tailTrace_2515898
  have hstable : (prefixWord ++ tailWord_2515898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515898).length < 2 ^ (prefixWord ++ tailWord_2515898).sum := by decide
  have hdescent : baseEnd_2515898 < baseStart_2515898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515930 : List Nat := [3, 1, 1, 2, 4, 2, 3, 6]
def baseStart_2515930 : Nat := 118140960795 + 2515930 * 2 ^ 59
def prefixEnd_2515930 : Nat := 4983230072969 + 3 ^ 40 * 2515930 * 2
def baseEnd_2515930 : Nat := 95694917264181233037367

theorem tailTrace_2515930 : CollatzResearch.WordTrace tailWord_2515930 prefixEnd_2515930 95694917264181233037367 := by
  unfold tailWord_2515930
  simp only [CollatzResearch.WordTrace]
  refine ⟨22940876443805692870002311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61175670516815180986672829 22940876443805692870002311)
  ·
    refine ⟨34411314665708539305003467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22940876443805692870002311 34411314665708539305003467)
    ·
      refine ⟨51616971998562808957505201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34411314665708539305003467 51616971998562808957505201)
      ·
        refine ⟨38712728998922106718128901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51616971998562808957505201 38712728998922106718128901)
        ·
          refine ⟨7258636687297895009649169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38712728998922106718128901 7258636687297895009649169)
          ·
            refine ⟨5443977515473421257236877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7258636687297895009649169 5443977515473421257236877)
            ·
              refine ⟨2041491568302532971463829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5443977515473421257236877 2041491568302532971463829)
              ·
                refine ⟨95694917264181233037367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2041491568302532971463829 95694917264181233037367)
                ·
                  rfl

theorem cell22_2515930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 3, 6].length) (baseStart_2515930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2515930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2515930 prefixEnd_2515930 := by exact prefixLift 2515930
  have htrace : WordTrace (prefixWord ++ tailWord_2515930) baseStart_2515930 baseEnd_2515930 := by
    simpa [prefixWord, tailWord_2515930, baseEnd_2515930] using wordTrace_append hprefix tailTrace_2515930
  have hstable : (prefixWord ++ tailWord_2515930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515930).length < 2 ^ (prefixWord ++ tailWord_2515930).sum := by decide
  have hdescent : baseEnd_2515930 < baseStart_2515930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515973 : List Nat := [1, 3, 1, 1, 2, 3, 1, 3, 2, 5]
def baseStart_2515973 : Nat := 118140960795 + 2515973 * 2 ^ 59
def prefixEnd_2515973 : Nat := 4983230072969 + 3 ^ 40 * 2515973 * 2
def baseEnd_2515973 : Nat := 861268975156393318511171

theorem tailTrace_2515973 : CollatzResearch.WordTrace tailWord_2515973 prefixEnd_2515973 861268975156393318511171 := by
  unfold tailWord_2515973
  simp only [CollatzResearch.WordTrace]
  refine ⟨91765074114066989823824573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61176716076044659882549715 91765074114066989823824573)
  ·
    refine ⟨34411902792775121183934215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91765074114066989823824573 34411902792775121183934215)
    ·
      refine ⟨51617854189162681775901323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34411902792775121183934215 51617854189162681775901323)
      ·
        refine ⟨77426781283744022663851985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51617854189162681775901323 77426781283744022663851985)
        ·
          refine ⟨58070085962808016997888989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77426781283744022663851985 58070085962808016997888989)
          ·
            refine ⟨21776282236053006374208371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58070085962808016997888989 21776282236053006374208371)
            ·
              refine ⟨32664423354079509561312557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21776282236053006374208371 32664423354079509561312557)
              ·
                refine ⟨12249158757779816085492209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32664423354079509561312557 12249158757779816085492209)
                ·
                  refine ⟨9186869068334862064119157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12249158757779816085492209 9186869068334862064119157)
                  ·
                    refine ⟨861268975156393318511171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9186869068334862064119157 861268975156393318511171)
                    ·
                      rfl

theorem cell22_2515973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 3, 2, 5].length) (baseStart_2515973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2515973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2515973 prefixEnd_2515973 := by exact prefixLift 2515973
  have htrace : WordTrace (prefixWord ++ tailWord_2515973) baseStart_2515973 baseEnd_2515973 := by
    simpa [prefixWord, tailWord_2515973, baseEnd_2515973] using wordTrace_append hprefix tailTrace_2515973
  have hstable : (prefixWord ++ tailWord_2515973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515973).length < 2 ^ (prefixWord ++ tailWord_2515973).sum := by decide
  have hdescent : baseEnd_2515973 < baseStart_2515973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515996 : List Nat := [2, 2, 3, 1, 4, 2, 1, 3, 1, 3]
def baseStart_2515996 : Nat := 118140960795 + 2515996 * 2 ^ 59
def prefixEnd_2515996 : Nat := 4983230072969 + 3 ^ 40 * 2515996 * 2
def baseEnd_2515996 : Nat := 861276848526428925186101

theorem tailTrace_2515996 : CollatzResearch.WordTrace tailWord_2515996 prefixEnd_2515996 861276848526428925186101 := by
  unfold tailWord_2515996
  simp only [CollatzResearch.WordTrace]
  refine ⟨45882956496491832375955921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61177275328655776501274561 45882956496491832375955921)
  ·
    refine ⟨34412217372368874281966941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45882956496491832375955921 34412217372368874281966941)
    ·
      refine ⟨12904581514638327855737603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34412217372368874281966941 12904581514638327855737603)
      ·
        refine ⟨19356872271957491783606405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12904581514638327855737603 19356872271957491783606405)
        ·
          refine ⟨3629413550992029709426201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19356872271957491783606405 3629413550992029709426201)
          ·
            refine ⟨2722060163244022282069651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3629413550992029709426201 2722060163244022282069651)
            ·
              refine ⟨4083090244866033423104477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2722060163244022282069651 4083090244866033423104477)
              ·
                refine ⟨1531158841824762533664179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4083090244866033423104477 1531158841824762533664179)
                ·
                  refine ⟨2296738262737143800496269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1531158841824762533664179 2296738262737143800496269)
                  ·
                    refine ⟨861276848526428925186101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2296738262737143800496269 861276848526428925186101)
                    ·
                      rfl

theorem cell22_2515996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 3, 1, 3].length) (baseStart_2515996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2515996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2515996 prefixEnd_2515996 := by exact prefixLift 2515996
  have htrace : WordTrace (prefixWord ++ tailWord_2515996) baseStart_2515996 baseEnd_2515996 := by
    simpa [prefixWord, tailWord_2515996, baseEnd_2515996] using wordTrace_append hprefix tailTrace_2515996
  have hstable : (prefixWord ++ tailWord_2515996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515996).length < 2 ^ (prefixWord ++ tailWord_2515996).sum := by decide
  have hdescent : baseEnd_2515996 < baseStart_2515996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2516005 : List Nat := [1, 3, 1, 2, 2, 2, 1, 5, 1, 4]
def baseStart_2516005 : Nat := 118140960795 + 2516005 * 2 ^ 59
def prefixEnd_2516005 : Nat := 4983230072969 + 3 ^ 40 * 2516005 * 2
def baseEnd_2516005 : Nat := 861279929410355901711073

theorem tailTrace_2516005 : CollatzResearch.WordTrace tailWord_2516005 prefixEnd_2516005 861279929410355901711073 := by
  unfold tailWord_2516005
  simp only [CollatzResearch.WordTrace]
  refine ⟨91766241249951059288989469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61177494166634039525992979 91766241249951059288989469)
  ·
    refine ⟨34412340468731647233371051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91766241249951059288989469 34412340468731647233371051)
    ·
      refine ⟨51618510703097470850056577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34412340468731647233371051 51618510703097470850056577)
      ·
        refine ⟨38713883027323103137542433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51618510703097470850056577 38713883027323103137542433)
        ·
          refine ⟨29035412270492327353156825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38713883027323103137542433 29035412270492327353156825)
          ·
            refine ⟨21776559202869245514867619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29035412270492327353156825 21776559202869245514867619)
            ·
              refine ⟨32664838804303868272301429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21776559202869245514867619 32664838804303868272301429)
              ·
                refine ⟨3062328637903487650528259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32664838804303868272301429 3062328637903487650528259)
                ·
                  refine ⟨4593492956855231475792389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3062328637903487650528259 4593492956855231475792389)
                  ·
                    refine ⟨861279929410355901711073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4593492956855231475792389 861279929410355901711073)
                    ·
                      rfl

theorem cell22_2516005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 5, 1, 4].length) (baseStart_2516005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2516005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2516005 prefixEnd_2516005 := by exact prefixLift 2516005
  have htrace : WordTrace (prefixWord ++ tailWord_2516005) baseStart_2516005 baseEnd_2516005 := by
    simpa [prefixWord, tailWord_2516005, baseEnd_2516005] using wordTrace_append hprefix tailTrace_2516005
  have hstable : (prefixWord ++ tailWord_2516005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2516005).length < 2 ^ (prefixWord ++ tailWord_2516005).sum := by decide
  have hdescent : baseEnd_2516005 < baseStart_2516005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2516005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2516097 : List Nat := [1, 2, 4, 2, 2, 1, 1, 1, 5, 3]
def baseStart_2516097 : Nat := 118140960795 + 2516097 * 2 ^ 59
def prefixEnd_2516097 : Nat := 4983230072969 + 3 ^ 40 * 2516097 * 2
def baseEnd_2516097 : Nat := 861311422890498328410791

theorem tailTrace_2516097 : CollatzResearch.WordTrace tailWord_2516097 prefixEnd_2516097 861311422890498328410791 := by
  unfold tailWord_2516097
  simp only [CollatzResearch.WordTrace]
  refine ⟨91769596765617759001338545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61179731177078506000892363 91769596765617759001338545)
  ·
    refine ⟨68827197574213319251003909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91769596765617759001338545 68827197574213319251003909)
    ·
      refine ⟨12905099545164997359563233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68827197574213319251003909 12905099545164997359563233)
      ·
        refine ⟨9678824658873748019672425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12905099545164997359563233 9678824658873748019672425)
        ·
          refine ⟨7259118494155311014754319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9678824658873748019672425 7259118494155311014754319)
          ·
            refine ⟨10888677741232966522131479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7259118494155311014754319 10888677741232966522131479)
            ·
              refine ⟨16333016611849449783197219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10888677741232966522131479 16333016611849449783197219)
              ·
                refine ⟨24499524917774174674795829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16333016611849449783197219 24499524917774174674795829)
                ·
                  refine ⟨2296830461041328875762109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24499524917774174674795829 2296830461041328875762109)
                  ·
                    refine ⟨861311422890498328410791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2296830461041328875762109 861311422890498328410791)
                    ·
                      rfl

theorem cell22_2516097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 5, 3].length) (baseStart_2516097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2516097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2516097 prefixEnd_2516097 := by exact prefixLift 2516097
  have htrace : WordTrace (prefixWord ++ tailWord_2516097) baseStart_2516097 baseEnd_2516097 := by
    simpa [prefixWord, tailWord_2516097, baseEnd_2516097] using wordTrace_append hprefix tailTrace_2516097
  have hstable : (prefixWord ++ tailWord_2516097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2516097).length < 2 ^ (prefixWord ++ tailWord_2516097).sum := by decide
  have hdescent : baseEnd_2516097 < baseStart_2516097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2516097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2516125 : List Nat := [1, 4, 2, 1, 1, 2, 1, 1, 4, 5]
def baseStart_2516125 : Nat := 118140960795 + 2516125 * 2 ^ 59
def prefixEnd_2516125 : Nat := 4983230072969 + 3 ^ 40 * 2516125 * 2
def baseEnd_2516125 : Nat := 861321007862715588710705

theorem tailTrace_2516125 : CollatzResearch.WordTrace tailWord_2516125 prefixEnd_2516125 861321007862715588710705 := by
  unfold tailWord_2516125
  simp only [CollatzResearch.WordTrace]
  refine ⟨91770618009516319783357829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61180412006344213188905219 91770618009516319783357829)
  ·
    refine ⟨17206990876784309959379593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91770618009516319783357829 17206990876784309959379593)
    ·
      refine ⟨12905243157588232469534695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17206990876784309959379593 12905243157588232469534695)
      ·
        refine ⟨19357864736382348704302043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12905243157588232469534695 19357864736382348704302043)
        ·
          refine ⟨29036797104573523056453065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19357864736382348704302043 29036797104573523056453065)
          ·
            refine ⟨21777597828430142292339799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29036797104573523056453065 21777597828430142292339799)
            ·
              refine ⟨32666396742645213438509699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21777597828430142292339799 32666396742645213438509699)
              ·
                refine ⟨48999595113967820157764549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32666396742645213438509699 48999595113967820157764549)
                ·
                  refine ⟨9187424083868966279580853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48999595113967820157764549 9187424083868966279580853)
                  ·
                    refine ⟨861321007862715588710705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9187424083868966279580853 861321007862715588710705)
                    ·
                      rfl

theorem cell22_2516125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_2516125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2516125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2516125 prefixEnd_2516125 := by exact prefixLift 2516125
  have htrace : WordTrace (prefixWord ++ tailWord_2516125) baseStart_2516125 baseEnd_2516125 := by
    simpa [prefixWord, tailWord_2516125, baseEnd_2516125] using wordTrace_append hprefix tailTrace_2516125
  have hstable : (prefixWord ++ tailWord_2516125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2516125).length < 2 ^ (prefixWord ++ tailWord_2516125).sum := by decide
  have hdescent : baseEnd_2516125 < baseStart_2516125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2516125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2516127 : List Nat := [1, 1, 2, 6, 2, 1, 1, 1, 7]
def baseStart_2516127 : Nat := 118140960795 + 2516127 * 2 ^ 59
def prefixEnd_2516127 : Nat := 4983230072969 + 3 ^ 40 * 2516127 * 2
def baseEnd_2516127 : Nat := 287107230834529416720233

theorem tailTrace_2516127 : CollatzResearch.WordTrace tailWord_2516127 prefixEnd_2516127 287107230834529416720233 := by
  unfold tailWord_2516127
  simp only [CollatzResearch.WordTrace]
  refine ⟨91770690955509074124930635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61180460637006049416620423 91770690955509074124930635)
  ·
    refine ⟨137656036433263611187395953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91770690955509074124930635 137656036433263611187395953)
    ·
      refine ⟨103242027324947708390546965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137656036433263611187395953 103242027324947708390546965)
      ·
        refine ⟨4839470030856923830806889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 103242027324947708390546965 4839470030856923830806889)
        ·
          refine ⟨3629602523142692873105167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4839470030856923830806889 3629602523142692873105167)
          ·
            refine ⟨5444403784714039309657751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3629602523142692873105167 5444403784714039309657751)
            ·
              refine ⟨8166605677071058964486627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5444403784714039309657751 8166605677071058964486627)
              ·
                refine ⟨12249908515606588446729941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8166605677071058964486627 12249908515606588446729941)
                ·
                  refine ⟨287107230834529416720233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12249908515606588446729941 287107230834529416720233)
                  ·
                    rfl

theorem cell22_2516127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 1, 7].length) (baseStart_2516127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2516127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2516127 prefixEnd_2516127 := by exact prefixLift 2516127
  have htrace : WordTrace (prefixWord ++ tailWord_2516127) baseStart_2516127 baseEnd_2516127 := by
    simpa [prefixWord, tailWord_2516127, baseEnd_2516127] using wordTrace_append hprefix tailTrace_2516127
  have hstable : (prefixWord ++ tailWord_2516127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2516127).length < 2 ^ (prefixWord ++ tailWord_2516127).sum := by decide
  have hdescent : baseEnd_2516127 < baseStart_2516127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2516127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2516140 : List Nat := [2, 2, 1, 1, 1, 1, 1, 6, 3, 4]
def baseStart_2516140 : Nat := 118140960795 + 2516140 * 2 ^ 59
def prefixEnd_2516140 : Nat := 4983230072969 + 3 ^ 40 * 2516140 * 2
def baseEnd_2516140 : Nat := 861326142669260549585659

theorem tailTrace_2516140 : CollatzResearch.WordTrace tailWord_2516140 prefixEnd_2516140 861326142669260549585659 := by
  unfold tailWord_2516140
  simp only [CollatzResearch.WordTrace]
  refine ⟨45885582552230988672576937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61180776736307984896769249 45885582552230988672576937)
  ·
    refine ⟨34414186914173241504432703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45885582552230988672576937 34414186914173241504432703)
    ·
      refine ⟨51621280371259862256649055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34414186914173241504432703 51621280371259862256649055)
      ·
        refine ⟨77431920556889793384973583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51621280371259862256649055 77431920556889793384973583)
        ·
          refine ⟨116147880835334690077460375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77431920556889793384973583 116147880835334690077460375)
          ·
            refine ⟨174221821253002035116190563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116147880835334690077460375 174221821253002035116190563)
            ·
              refine ⟨261332731879503052674285845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174221821253002035116190563 261332731879503052674285845)
              ·
                refine ⟨12249971806851705594107149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 261332731879503052674285845 12249971806851705594107149)
                ·
                  refine ⟨4593739427569389597790181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12249971806851705594107149 4593739427569389597790181)
                  ·
                    refine ⟨861326142669260549585659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4593739427569389597790181 861326142669260549585659)
                    ·
                      rfl

theorem cell22_2516140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 4].length) (baseStart_2516140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2516140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2516140 prefixEnd_2516140 := by exact prefixLift 2516140
  have htrace : WordTrace (prefixWord ++ tailWord_2516140) baseStart_2516140 baseEnd_2516140 := by
    simpa [prefixWord, tailWord_2516140, baseEnd_2516140] using wordTrace_append hprefix tailTrace_2516140
  have hstable : (prefixWord ++ tailWord_2516140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2516140).length < 2 ^ (prefixWord ++ tailWord_2516140).sum := by decide
  have hdescent : baseEnd_2516140 < baseStart_2516140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2516140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2516157 : List Nat := [1, 4, 1, 2, 1, 1, 3, 4, 1, 4]
def baseStart_2516157 : Nat := 118140960795 + 2516157 * 2 ^ 59
def prefixEnd_2516157 : Nat := 4983230072969 + 3 ^ 40 * 2516157 * 2
def baseEnd_2516157 : Nat := 861331962116678171910607

theorem tailTrace_2516157 : CollatzResearch.WordTrace tailWord_2516157 prefixEnd_2516157 861331962116678171910607 := by
  unfold tailWord_2516157
  simp only [CollatzResearch.WordTrace]
  refine ⟨91771785145400389248522725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61181190096933592832348483 91771785145400389248522725)
  ·
    refine ⟨17207209714762572984098011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91771785145400389248522725 17207209714762572984098011)
    ·
      refine ⟨25810814572143859476147017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17207209714762572984098011 25810814572143859476147017)
      ·
        refine ⟨19358110929107894607110263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25810814572143859476147017 19358110929107894607110263)
        ·
          refine ⟨29037166393661841910665395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19358110929107894607110263 29037166393661841910665395)
          ·
            refine ⟨43555749590492762865998093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29037166393661841910665395 43555749590492762865998093)
            ·
              refine ⟨16333406096434786074749285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43555749590492762865998093 16333406096434786074749285)
              ·
                refine ⟨3062513643081522389015491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16333406096434786074749285 3062513643081522389015491)
                ·
                  refine ⟨4593770464622283583523237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3062513643081522389015491 4593770464622283583523237)
                  ·
                    refine ⟨861331962116678171910607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4593770464622283583523237 861331962116678171910607)
                    ·
                      rfl

theorem cell22_2516157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 4, 1, 4].length) (baseStart_2516157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2516157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2516157 prefixEnd_2516157 := by exact prefixLift 2516157
  have htrace : WordTrace (prefixWord ++ tailWord_2516157) baseStart_2516157 baseEnd_2516157 := by
    simpa [prefixWord, tailWord_2516157, baseEnd_2516157] using wordTrace_append hprefix tailTrace_2516157
  have hstable : (prefixWord ++ tailWord_2516157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2516157).length < 2 ^ (prefixWord ++ tailWord_2516157).sum := by decide
  have hdescent : baseEnd_2516157 < baseStart_2516157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2516157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2516204 : List Nat := [2, 2, 1, 1, 2, 5, 1, 3, 2, 3]
def baseStart_2516204 : Nat := 118140960795 + 2516204 * 2 ^ 59
def prefixEnd_2516204 : Nat := 4983230072969 + 3 ^ 40 * 2516204 * 2
def baseEnd_2516204 : Nat := 861348051177185715985463

theorem tailTrace_2516204 : CollatzResearch.WordTrace tailWord_2516204 prefixEnd_2516204 861348051177185715985463 := by
  unfold tailWord_2516204
  simp only [CollatzResearch.WordTrace]
  refine ⟨45886749688115058137741833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61182332917486744183655777 45886749688115058137741833)
  ·
    refine ⟨34415062266086293603306375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45886749688115058137741833 34415062266086293603306375)
    ·
      refine ⟨51622593399129440404959563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34415062266086293603306375 51622593399129440404959563)
      ·
        refine ⟨77433890098694160607439345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51622593399129440404959563 77433890098694160607439345)
        ·
          refine ⟨58075417574020620455579509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77433890098694160607439345 58075417574020620455579509)
          ·
            refine ⟨5444570397564433167710579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58075417574020620455579509 5444570397564433167710579)
            ·
              refine ⟨8166855596346649751565869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5444570397564433167710579 8166855596346649751565869)
              ·
                refine ⟨3062570848629993656837201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8166855596346649751565869 3062570848629993656837201)
                ·
                  refine ⟨2296928136472495242627901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3062570848629993656837201 2296928136472495242627901)
                  ·
                    refine ⟨861348051177185715985463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2296928136472495242627901 861348051177185715985463)
                    ·
                      rfl

theorem cell22_2516204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 3].length) (baseStart_2516204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2516204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2516204 prefixEnd_2516204 := by exact prefixLift 2516204
  have htrace : WordTrace (prefixWord ++ tailWord_2516204) baseStart_2516204 baseEnd_2516204 := by
    simpa [prefixWord, tailWord_2516204, baseEnd_2516204] using wordTrace_append hprefix tailTrace_2516204
  have hstable : (prefixWord ++ tailWord_2516204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2516204).length < 2 ^ (prefixWord ++ tailWord_2516204).sum := by decide
  have hdescent : baseEnd_2516204 < baseStart_2516204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2516204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2516266 : List Nat := [3, 1, 4, 2, 1, 2, 1, 2, 3, 3]
def baseStart_2516266 : Nat := 118140960795 + 2516266 * 2 ^ 59
def prefixEnd_2516266 : Nat := 4983230072969 + 3 ^ 40 * 2516266 * 2
def baseEnd_2516266 : Nat := 861369275044238220935273

theorem tailTrace_2516266 : CollatzResearch.WordTrace tailWord_2516266 prefixEnd_2516266 861369275044238220935273 := by
  unfold tailWord_2516266
  simp only [CollatzResearch.WordTrace]
  refine ⟨22943940175501375216060163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61183840468003667242827101 22943940175501375216060163)
  ·
    refine ⟨34415910263252062824090245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22943940175501375216060163 34415910263252062824090245)
    ·
      refine ⟨6452983174359761779516921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34415910263252062824090245 6452983174359761779516921)
      ·
        refine ⟨4839737380769821334637691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6452983174359761779516921 4839737380769821334637691)
        ·
          refine ⟨7259606071154732001956537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4839737380769821334637691 7259606071154732001956537)
          ·
            refine ⟨5444704553366049001467403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7259606071154732001956537 5444704553366049001467403)
            ·
              refine ⟨8167056830049073502201105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5444704553366049001467403 8167056830049073502201105)
              ·
                refine ⟨6125292622536805126650829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8167056830049073502201105 6125292622536805126650829)
                ·
                  refine ⟨2296984733451301922494061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6125292622536805126650829 2296984733451301922494061)
                  ·
                    refine ⟨861369275044238220935273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2296984733451301922494061 861369275044238220935273)
                    ·
                      rfl

theorem cell22_2516266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_2516266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2516266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2516266 prefixEnd_2516266 := by exact prefixLift 2516266
  have htrace : WordTrace (prefixWord ++ tailWord_2516266) baseStart_2516266 baseEnd_2516266 := by
    simpa [prefixWord, tailWord_2516266, baseEnd_2516266] using wordTrace_append hprefix tailTrace_2516266
  have hstable : (prefixWord ++ tailWord_2516266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2516266).length < 2 ^ (prefixWord ++ tailWord_2516266).sum := by decide
  have hdescent : baseEnd_2516266 < baseStart_2516266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2516266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2516307 : List Nat := [1, 1, 1, 2, 1, 1, 8, 1, 6]
def baseStart_2516307 : Nat := 118140960795 + 2516307 * 2 ^ 59
def prefixEnd_2516307 : Nat := 4983230072969 + 3 ^ 40 * 2516307 * 2
def baseEnd_2516307 : Nat := 287127770060709260220049

theorem tailTrace_2516307 : CollatzResearch.WordTrace tailWord_2516307 prefixEnd_2516307 287127770060709260220049 := by
  unfold tailWord_2516307
  simp only [CollatzResearch.WordTrace]
  refine ⟨91777256094856964866483175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61184837396571309910988783 91777256094856964866483175)
  ·
    refine ⟨137665884142285447299724763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91777256094856964866483175 137665884142285447299724763)
    ·
      refine ⟨206498826213428170949587145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137665884142285447299724763 206498826213428170949587145)
      ·
        refine ⟨154874119660071128212190359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 206498826213428170949587145 154874119660071128212190359)
        ·
          refine ⟨232311179490106692318285539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154874119660071128212190359 232311179490106692318285539)
          ·
            refine ⟨348466769235160038477428309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 232311179490106692318285539 348466769235160038477428309)
            ·
              refine ⟨4083594951974531700907363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 348466769235160038477428309 4083594951974531700907363)
              ·
                refine ⟨6125392427961797551361045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4083594951974531700907363 6125392427961797551361045)
                ·
                  refine ⟨287127770060709260220049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6125392427961797551361045 287127770060709260220049)
                  ·
                    rfl

theorem cell22_2516307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 1, 6].length) (baseStart_2516307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2516307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2516307 prefixEnd_2516307 := by exact prefixLift 2516307
  have htrace : WordTrace (prefixWord ++ tailWord_2516307) baseStart_2516307 baseEnd_2516307 := by
    simpa [prefixWord, tailWord_2516307, baseEnd_2516307] using wordTrace_append hprefix tailTrace_2516307
  have hstable : (prefixWord ++ tailWord_2516307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2516307).length < 2 ^ (prefixWord ++ tailWord_2516307).sum := by decide
  have hdescent : baseEnd_2516307 < baseStart_2516307 := by decide
  rcases family_descends (prefixWord ++ tailWord_2516307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2516337 : List Nat := [1, 2, 2, 2, 1, 2, 4, 1, 1, 6]
def baseStart_2516337 : Nat := 118140960795 + 2516337 * 2 ^ 59
def prefixEnd_2516337 : Nat := 4983230072969 + 3 ^ 40 * 2516337 * 2
def baseEnd_2516337 : Nat := 861393579795217702410055

theorem tailTrace_2516337 : CollatzResearch.WordTrace tailWord_2516337 prefixEnd_2516337 861393579795217702410055 := by
  unfold tailWord_2516337
  simp only [CollatzResearch.WordTrace]
  refine ⟨91778350284748279990075265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61185566856498853326716843 91778350284748279990075265)
  ·
    refine ⟨68833762713561209992556449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91778350284748279990075265 68833762713561209992556449)
    ·
      refine ⟨51625322035170907494417337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68833762713561209992556449 51625322035170907494417337)
      ·
        refine ⟨38718991526378180620813003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51625322035170907494417337 38718991526378180620813003)
        ·
          refine ⟨58078487289567270931219505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38718991526378180620813003 58078487289567270931219505)
          ·
            refine ⟨43558865467175453198414629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58078487289567270931219505 43558865467175453198414629)
            ·
              refine ⟨8167287275095397474702743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43558865467175453198414629 8167287275095397474702743)
              ·
                refine ⟨12250930912643096212054115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8167287275095397474702743 12250930912643096212054115)
                ·
                  refine ⟨18376396368964644318081173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12250930912643096212054115 18376396368964644318081173)
                  ·
                    refine ⟨861393579795217702410055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18376396368964644318081173 861393579795217702410055)
                    ·
                      rfl

theorem cell22_2516337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 1, 1, 6].length) (baseStart_2516337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2516337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2516337 prefixEnd_2516337 := by exact prefixLift 2516337
  have htrace : WordTrace (prefixWord ++ tailWord_2516337) baseStart_2516337 baseEnd_2516337 := by
    simpa [prefixWord, tailWord_2516337, baseEnd_2516337] using wordTrace_append hprefix tailTrace_2516337
  have hstable : (prefixWord ++ tailWord_2516337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2516337).length < 2 ^ (prefixWord ++ tailWord_2516337).sum := by decide
  have hdescent : baseEnd_2516337 < baseStart_2516337 := by decide
  rcases family_descends (prefixWord ++ tailWord_2516337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2516384 : List Nat := [2, 1, 1, 4, 1, 2, 2, 1, 5, 3]
def baseStart_2516384 : Nat := 118140960795 + 2516384 * 2 ^ 59
def prefixEnd_2516384 : Nat := 4983230072969 + 3 ^ 40 * 2516384 * 2
def baseEnd_2516384 : Nat := 861409668855725246484911

theorem tailTrace_2516384 : CollatzResearch.WordTrace tailWord_2516384 prefixEnd_2516384 861409668855725246484911 := by
  unfold tailWord_2516384
  simp only [CollatzResearch.WordTrace]
  refine ⟨45890032257789003508518103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61186709677052004678024137 45890032257789003508518103)
  ·
    refine ⟨68835048386683505262777155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45890032257789003508518103 68835048386683505262777155)
    ·
      refine ⟨103252572580025257894165733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68835048386683505262777155 103252572580025257894165733)
      ·
        refine ⟨19359857358754735855156075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 103252572580025257894165733 19359857358754735855156075)
        ·
          refine ⟨29039786038132103782734113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19359857358754735855156075 29039786038132103782734113)
          ·
            refine ⟨21779839528599077837050585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29039786038132103782734113 21779839528599077837050585)
            ·
              refine ⟨16334879646449308377787939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21779839528599077837050585 16334879646449308377787939)
              ·
                refine ⟨24502319469673962566681909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16334879646449308377787939 24502319469673962566681909)
                ·
                  refine ⟨2297092450281933990626429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24502319469673962566681909 2297092450281933990626429)
                  ·
                    refine ⟨861409668855725246484911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2297092450281933990626429 861409668855725246484911)
                    ·
                      rfl

theorem cell22_2516384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 5, 3].length) (baseStart_2516384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2516384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2516384 prefixEnd_2516384 := by exact prefixLift 2516384
  have htrace : WordTrace (prefixWord ++ tailWord_2516384) baseStart_2516384 baseEnd_2516384 := by
    simpa [prefixWord, tailWord_2516384, baseEnd_2516384] using wordTrace_append hprefix tailTrace_2516384
  have hstable : (prefixWord ++ tailWord_2516384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2516384).length < 2 ^ (prefixWord ++ tailWord_2516384).sum := by decide
  have hdescent : baseEnd_2516384 < baseStart_2516384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2516384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2516457 : List Nat := [1, 2, 1, 1, 1, 2, 1, 2, 2, 9]
def baseStart_2516457 : Nat := 118140960795 + 2516457 * 2 ^ 59
def prefixEnd_2516457 : Nat := 4983230072969 + 3 ^ 40 * 2516457 * 2
def baseEnd_2516457 : Nat := 861434658247577389409687

theorem tailTrace_2516457 : CollatzResearch.WordTrace tailWord_2516457 prefixEnd_2516457 861434658247577389409687 := by
  unfold tailWord_2516457
  simp only [CollatzResearch.WordTrace]
  refine ⟨91782727044313540484443625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61188484696209026989629083 91782727044313540484443625)
  ·
    refine ⟨68837045283235155363332719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91782727044313540484443625 68837045283235155363332719)
    ·
      refine ⟨103255567924852733044999079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68837045283235155363332719 103255567924852733044999079)
      ·
        refine ⟨154883351887279099567498619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103255567924852733044999079 154883351887279099567498619)
        ·
          refine ⟨232325027830918649351247929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154883351887279099567498619 232325027830918649351247929)
          ·
            refine ⟨174243770873188987013435947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 232325027830918649351247929 174243770873188987013435947)
            ·
              refine ⟨261365656309783480520153921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174243770873188987013435947 261365656309783480520153921)
              ·
                refine ⟨196024242232337610390115441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 261365656309783480520153921 196024242232337610390115441)
                ·
                  refine ⟨147018181674253207792586581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 196024242232337610390115441 147018181674253207792586581)
                  ·
                    refine ⟨861434658247577389409687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 147018181674253207792586581 861434658247577389409687)
                    ·
                      rfl

theorem cell22_2516457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 9].length) (baseStart_2516457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2516457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2516457 prefixEnd_2516457 := by exact prefixLift 2516457
  have htrace : WordTrace (prefixWord ++ tailWord_2516457) baseStart_2516457 baseEnd_2516457 := by
    simpa [prefixWord, tailWord_2516457, baseEnd_2516457] using wordTrace_append hprefix tailTrace_2516457
  have hstable : (prefixWord ++ tailWord_2516457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2516457).length < 2 ^ (prefixWord ++ tailWord_2516457).sum := by decide
  have hdescent : baseEnd_2516457 < baseStart_2516457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2516457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2516476 : List Nat := [2, 2, 2, 1, 2, 1, 4, 4, 4]
def baseStart_2516476 : Nat := 118140960795 + 2516476 * 2 ^ 59
def prefixEnd_2516476 : Nat := 4983230072969 + 3 ^ 40 * 2516476 * 2
def baseEnd_2516476 : Nat := 287147054111955891061543

theorem tailTrace_2516476 : CollatzResearch.WordTrace tailWord_2516476 prefixEnd_2516476 287147054111955891061543 := by
  unfold tailWord_2516476
  simp only [CollatzResearch.WordTrace]
  refine ⟨45891710015622353364692641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61188946687496471152923521 45891710015622353364692641)
  ·
    refine ⟨34418782511716765023519481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45891710015622353364692641 34418782511716765023519481)
    ·
      refine ⟨25814086883787573767639611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34418782511716765023519481 25814086883787573767639611)
      ·
        refine ⟨38721130325681360651459417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25814086883787573767639611 38721130325681360651459417)
        ·
          refine ⟨29040847744261020488594563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38721130325681360651459417 29040847744261020488594563)
          ·
            refine ⟨43561271616391530732891845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29040847744261020488594563 43561271616391530732891845)
            ·
              refine ⟨8167738428073412012417221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43561271616391530732891845 8167738428073412012417221)
              ·
                refine ⟨1531450955263764752328229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8167738428073412012417221 1531450955263764752328229)
                ·
                  refine ⟨287147054111955891061543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1531450955263764752328229 287147054111955891061543)
                  ·
                    rfl

theorem cell22_2516476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 4, 4].length) (baseStart_2516476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2516476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2516476 prefixEnd_2516476 := by exact prefixLift 2516476
  have htrace : WordTrace (prefixWord ++ tailWord_2516476) baseStart_2516476 baseEnd_2516476 := by
    simpa [prefixWord, tailWord_2516476, baseEnd_2516476] using wordTrace_append hprefix tailTrace_2516476
  have hstable : (prefixWord ++ tailWord_2516476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2516476).length < 2 ^ (prefixWord ++ tailWord_2516476).sum := by decide
  have hdescent : baseEnd_2516476 < baseStart_2516476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2516476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2516598 : List Nat := [5, 1, 1, 2, 2, 2, 1, 1, 2, 5]
def baseStart_2516598 : Nat := 118140960795 + 2516598 * 2 ^ 59
def prefixEnd_2516598 : Nat := 4983230072969 + 3 ^ 40 * 2516598 * 2
def baseEnd_2516598 : Nat := 861482925429100021634255

theorem tailTrace_2516598 : CollatzResearch.WordTrace tailWord_2516598 prefixEnd_2516598 861482925429100021634255 := by
  unfold tailWord_2516598
  simp only [CollatzResearch.WordTrace]
  refine ⟨5736741858550170097832903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61191913157868481043550965 5736741858550170097832903)
  ·
    refine ⟨8605112787825255146749355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5736741858550170097832903 8605112787825255146749355)
    ·
      refine ⟨12907669181737882720124033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8605112787825255146749355 12907669181737882720124033)
      ·
        refine ⟨9680751886303412040093025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12907669181737882720124033 9680751886303412040093025)
        ·
          refine ⟨7260563914727559030069769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9680751886303412040093025 7260563914727559030069769)
          ·
            refine ⟨5445422936045669272552327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7260563914727559030069769 5445422936045669272552327)
            ·
              refine ⟨8168134404068503908828491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5445422936045669272552327 8168134404068503908828491)
              ·
                refine ⟨12252201606102755863242737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8168134404068503908828491 12252201606102755863242737)
                ·
                  refine ⟨9189151204577066897432053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12252201606102755863242737 9189151204577066897432053)
                  ·
                    refine ⟨861482925429100021634255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9189151204577066897432053 861482925429100021634255)
                    ·
                      rfl

theorem cell22_2516598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_2516598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2516598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2516598 prefixEnd_2516598 := by exact prefixLift 2516598
  have htrace : WordTrace (prefixWord ++ tailWord_2516598) baseStart_2516598 baseEnd_2516598 := by
    simpa [prefixWord, tailWord_2516598, baseEnd_2516598] using wordTrace_append hprefix tailTrace_2516598
  have hstable : (prefixWord ++ tailWord_2516598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2516598).length < 2 ^ (prefixWord ++ tailWord_2516598).sum := by decide
  have hdescent : baseEnd_2516598 < baseStart_2516598 := by decide
  rcases family_descends (prefixWord ++ tailWord_2516598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2516711 : List Nat := [1, 1, 5, 4, 2, 1, 2, 1, 2, 3]
def baseStart_2516711 : Nat := 118140960795 + 2516711 * 2 ^ 59
def prefixEnd_2516711 : Nat := 4983230072969 + 3 ^ 40 * 2516711 * 2
def baseEnd_2516711 : Nat := 861521607638405393558909

theorem tailTrace_2516711 : CollatzResearch.WordTrace tailWord_2516711 prefixEnd_2516711 861521607638405393558909 := by
  unfold tailWord_2516711
  simp only [CollatzResearch.WordTrace]
  refine ⟨91791991185393341864189987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61194660790262227909459991 91791991185393341864189987)
  ·
    refine ⟨137687986778090012796284981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91791991185393341864189987 137687986778090012796284981)
    ·
      refine ⟨12908248760445938699651717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 137687986778090012796284981 12908248760445938699651717)
      ·
        refine ⟨2420296642583613506184697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12908248760445938699651717 2420296642583613506184697)
        ·
          refine ⟨1815222481937710129638523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2420296642583613506184697 1815222481937710129638523)
          ·
            refine ⟨2722833722906565194457785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1815222481937710129638523 2722833722906565194457785)
            ·
              refine ⟨2042125292179923895843339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2722833722906565194457785 2042125292179923895843339)
              ·
                refine ⟨3063187938269885843765009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2042125292179923895843339 3063187938269885843765009)
                ·
                  refine ⟨2297390953702414382823757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3063187938269885843765009 2297390953702414382823757)
                  ·
                    refine ⟨861521607638405393558909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2297390953702414382823757 861521607638405393558909)
                    ·
                      rfl

theorem cell22_2516711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 2, 1, 2, 3].length) (baseStart_2516711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2516711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2516711 prefixEnd_2516711 := by exact prefixLift 2516711
  have htrace : WordTrace (prefixWord ++ tailWord_2516711) baseStart_2516711 baseEnd_2516711 := by
    simpa [prefixWord, tailWord_2516711, baseEnd_2516711] using wordTrace_append hprefix tailTrace_2516711
  have hstable : (prefixWord ++ tailWord_2516711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2516711).length < 2 ^ (prefixWord ++ tailWord_2516711).sum := by decide
  have hdescent : baseEnd_2516711 < baseStart_2516711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2516711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2516716 : List Nat := [2, 2, 1, 1, 2, 2, 2, 3, 2, 5]
def baseStart_2516716 : Nat := 118140960795 + 2516716 * 2 ^ 59
def prefixEnd_2516716 : Nat := 4983230072969 + 3 ^ 40 * 2516716 * 2
def baseEnd_2516716 : Nat := 861523319240587047183893

theorem tailTrace_2516716 : CollatzResearch.WordTrace tailWord_2516716 prefixEnd_2516716 861523319240587047183893 := by
  unfold tailWord_2516716
  simp only [CollatzResearch.WordTrace]
  refine ⟨45896086775187613859061001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61194782366916818478748001 45896086775187613859061001)
  ·
    refine ⟨34422065081390710394295751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45896086775187613859061001 34422065081390710394295751)
    ·
      refine ⟨51633097622086065591443627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34422065081390710394295751 51633097622086065591443627)
      ·
        refine ⟨77449646433129098387165441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51633097622086065591443627 77449646433129098387165441)
        ·
          refine ⟨58087234824846823790374081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77449646433129098387165441 58087234824846823790374081)
          ·
            refine ⟨43565426118635117842780561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58087234824846823790374081 43565426118635117842780561)
            ·
              refine ⟨32674069588976338382085421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43565426118635117842780561 32674069588976338382085421)
              ·
                refine ⟨12252776095866126893282033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32674069588976338382085421 12252776095866126893282033)
                ·
                  refine ⟨9189582071899595169961525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12252776095866126893282033 9189582071899595169961525)
                  ·
                    refine ⟨861523319240587047183893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9189582071899595169961525 861523319240587047183893)
                    ·
                      rfl

theorem cell22_2516716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 5].length) (baseStart_2516716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2516716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2516716 prefixEnd_2516716 := by exact prefixLift 2516716
  have htrace : WordTrace (prefixWord ++ tailWord_2516716) baseStart_2516716 baseEnd_2516716 := by
    simpa [prefixWord, tailWord_2516716, baseEnd_2516716] using wordTrace_append hprefix tailTrace_2516716
  have hstable : (prefixWord ++ tailWord_2516716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2516716).length < 2 ^ (prefixWord ++ tailWord_2516716).sum := by decide
  have hdescent : baseEnd_2516716 < baseStart_2516716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2516716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2516718 : List Nat := [4, 1, 2, 1, 1, 2, 3, 3, 5]
def baseStart_2516718 : Nat := 118140960795 + 2516718 * 2 ^ 59
def prefixEnd_2516718 : Nat := 4983230072969 + 3 ^ 40 * 2516718 * 2
def baseEnd_2516718 : Nat := 287174667960486569544629

theorem tailTrace_2516718 : CollatzResearch.WordTrace tailWord_2516718 prefixEnd_2516718 287174667960486569544629 := by
  unfold tailWord_2516718
  simp only [CollatzResearch.WordTrace]
  refine ⟨11474030812045997757461851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61194830997578654706463205 11474030812045997757461851)
  ·
    refine ⟨17211046218068996636192777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11474030812045997757461851 17211046218068996636192777)
    ·
      refine ⟨12908284663551747477144583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17211046218068996636192777 12908284663551747477144583)
      ·
        refine ⟨19362426995327621215716875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12908284663551747477144583 19362426995327621215716875)
        ·
          refine ⟨29043640492991431823575313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19362426995327621215716875 29043640492991431823575313)
          ·
            refine ⟨21782730369743573867681485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29043640492991431823575313 21782730369743573867681485)
            ·
              refine ⟨8168523888653840200380557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21782730369743573867681485 8168523888653840200380557)
              ·
                refine ⟨3063196458245190075142709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8168523888653840200380557 3063196458245190075142709)
                ·
                  refine ⟨287174667960486569544629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3063196458245190075142709 287174667960486569544629)
                  ·
                    rfl

theorem cell22_2516718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 3, 5].length) (baseStart_2516718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2516718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2516718 prefixEnd_2516718 := by exact prefixLift 2516718
  have htrace : WordTrace (prefixWord ++ tailWord_2516718) baseStart_2516718 baseEnd_2516718 := by
    simpa [prefixWord, tailWord_2516718, baseEnd_2516718] using wordTrace_append hprefix tailTrace_2516718
  have hstable : (prefixWord ++ tailWord_2516718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2516718).length < 2 ^ (prefixWord ++ tailWord_2516718).sum := by decide
  have hdescent : baseEnd_2516718 < baseStart_2516718 := by decide
  rcases family_descends (prefixWord ++ tailWord_2516718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2516748 : List Nat := [2, 2, 1, 2, 2, 1, 2, 5, 1, 4]
def baseStart_2516748 : Nat := 118140960795 + 2516748 * 2 ^ 59
def prefixEnd_2516748 : Nat := 4983230072969 + 3 ^ 40 * 2516748 * 2
def baseEnd_2516748 : Nat := 861534273494549630383795

theorem tailTrace_2516748 : CollatzResearch.WordTrace tailWord_2516748 prefixEnd_2516748 861534273494549630383795 := by
  unfold tailWord_2516748
  simp only [CollatzResearch.WordTrace]
  refine ⟨45896670343129648591643449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61195560457506198122191265 45896670343129648591643449)
  ·
    refine ⟨34422502757347236443732587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45896670343129648591643449 34422502757347236443732587)
    ·
      refine ⟨51633754136020854665598881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34422502757347236443732587 51633754136020854665598881)
      ·
        refine ⟨38725315602015640999199161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51633754136020854665598881 38725315602015640999199161)
        ·
          refine ⟨29043986701511730749399371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38725315602015640999199161 29043986701511730749399371)
          ·
            refine ⟨43565980052267596124099057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29043986701511730749399371 43565980052267596124099057)
            ·
              refine ⟨32674485039200697093074293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43565980052267596124099057 32674485039200697093074293)
              ·
                refine ⟨3063232972425065352475715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32674485039200697093074293 3063232972425065352475715)
                ·
                  refine ⟨4594849458637598028713573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3063232972425065352475715 4594849458637598028713573)
                  ·
                    refine ⟨861534273494549630383795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4594849458637598028713573 861534273494549630383795)
                    ·
                      rfl

theorem cell22_2516748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 5, 1, 4].length) (baseStart_2516748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2516748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2516748 prefixEnd_2516748 := by exact prefixLift 2516748
  have htrace : WordTrace (prefixWord ++ tailWord_2516748) baseStart_2516748 baseEnd_2516748 := by
    simpa [prefixWord, tailWord_2516748, baseEnd_2516748] using wordTrace_append hprefix tailTrace_2516748
  have hstable : (prefixWord ++ tailWord_2516748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2516748).length < 2 ^ (prefixWord ++ tailWord_2516748).sum := by decide
  have hdescent : baseEnd_2516748 < baseStart_2516748 := by decide
  rcases family_descends (prefixWord ++ tailWord_2516748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2516763 : List Nat := [1, 1, 1, 1, 1, 1, 4, 8, 4]
def baseStart_2516763 : Nat := 118140960795 + 2516763 * 2 ^ 59
def prefixEnd_2516763 : Nat := 4983230072969 + 3 ^ 40 * 2516763 * 2
def baseEnd_2516763 : Nat := 287179802767031530419583

theorem tailTrace_2516763 : CollatzResearch.WordTrace tailWord_2516763 prefixEnd_2516763 287179802767031530419583 := by
  unfold tailWord_2516763
  simp only [CollatzResearch.WordTrace]
  refine ⟨91793887781204954745082943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61195925187469969830055295 91793887781204954745082943)
  ·
    refine ⟨137690831671807432117624415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91793887781204954745082943 137690831671807432117624415)
    ·
      refine ⟨206536247507711148176436623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137690831671807432117624415 206536247507711148176436623)
      ·
        refine ⟨309804371261566722264654935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206536247507711148176436623 309804371261566722264654935)
        ·
          refine ⟨464706556892350083396982403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 309804371261566722264654935 464706556892350083396982403)
          ·
            refine ⟨697059835338525125095473605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 464706556892350083396982403 697059835338525125095473605)
            ·
              refine ⟨130698719125973460955401301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 697059835338525125095473605 130698719125973460955401301)
              ·
                refine ⟨1531625614757501495571109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 130698719125973460955401301 1531625614757501495571109)
                ·
                  refine ⟨287179802767031530419583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1531625614757501495571109 287179802767031530419583)
                  ·
                    rfl

theorem cell22_2516763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 8, 4].length) (baseStart_2516763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2516763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2516763 prefixEnd_2516763 := by exact prefixLift 2516763
  have htrace : WordTrace (prefixWord ++ tailWord_2516763) baseStart_2516763 baseEnd_2516763 := by
    simpa [prefixWord, tailWord_2516763, baseEnd_2516763] using wordTrace_append hprefix tailTrace_2516763
  have hstable : (prefixWord ++ tailWord_2516763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2516763).length < 2 ^ (prefixWord ++ tailWord_2516763).sum := by decide
  have hdescent : baseEnd_2516763 < baseStart_2516763 := by decide
  rcases family_descends (prefixWord ++ tailWord_2516763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2516797 : List Nat := [1, 4, 1, 4, 1, 2, 2, 3, 4]
def baseStart_2516797 : Nat := 118140960795 + 2516797 * 2 ^ 59
def prefixEnd_2516797 : Nat := 4983230072969 + 3 ^ 40 * 2516797 * 2
def baseEnd_2516797 : Nat := 287183682398643278636215

theorem tailTrace_2516797 : CollatzResearch.WordTrace tailWord_2516797 prefixEnd_2516797 287183682398643278636215 := by
  unfold tailWord_2516797
  simp only [CollatzResearch.WordTrace]
  refine ⟨91795127863081778551820645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61196751908721185701213763 91795127863081778551820645)
  ·
    refine ⟨17211586474327833478466371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91795127863081778551820645 17211586474327833478466371)
    ·
      refine ⟨25817379711491750217699557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17211586474327833478466371 25817379711491750217699557)
      ·
        refine ⟨4840758695904703165818667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25817379711491750217699557 4840758695904703165818667)
        ·
          refine ⟨7261138043857054748728001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4840758695904703165818667 7261138043857054748728001)
          ·
            refine ⟨5445853532892791061546001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7261138043857054748728001 5445853532892791061546001)
            ·
              refine ⟨4084390149669593296159501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5445853532892791061546001 4084390149669593296159501)
              ·
                refine ⟨1531646306126097486059813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4084390149669593296159501 1531646306126097486059813)
                ·
                  refine ⟨287183682398643278636215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1531646306126097486059813 287183682398643278636215)
                  ·
                    rfl

theorem cell22_2516797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 3, 4].length) (baseStart_2516797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2516797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2516797 prefixEnd_2516797 := by exact prefixLift 2516797
  have htrace : WordTrace (prefixWord ++ tailWord_2516797) baseStart_2516797 baseEnd_2516797 := by
    simpa [prefixWord, tailWord_2516797, baseEnd_2516797] using wordTrace_append hprefix tailTrace_2516797
  have hstable : (prefixWord ++ tailWord_2516797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2516797).length < 2 ^ (prefixWord ++ tailWord_2516797).sum := by decide
  have hdescent : baseEnd_2516797 < baseStart_2516797 := by decide
  rcases family_descends (prefixWord ++ tailWord_2516797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2516799 : List Nat := [1, 1, 2, 2, 7, 1, 2, 1, 1, 4]
def baseStart_2516799 : Nat := 118140960795 + 2516799 * 2 ^ 59
def prefixEnd_2516799 : Nat := 4983230072969 + 3 ^ 40 * 2516799 * 2
def baseEnd_2516799 : Nat := 861551731836802497358639

theorem tailTrace_2516799 : CollatzResearch.WordTrace tailWord_2516799 prefixEnd_2516799 861551731836802497358639 := by
  unfold tailWord_2516799
  simp only [CollatzResearch.WordTrace]
  refine ⟨91795200809074532893393451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61196800539383021928928967 91795200809074532893393451)
  ·
    refine ⟨137692801213611799340090177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91795200809074532893393451 137692801213611799340090177)
    ·
      refine ⟨103269600910208849505067633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137692801213611799340090177 103269600910208849505067633)
      ·
        refine ⟨77452200682656637128800725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103269600910208849505067633 77452200682656637128800725)
        ·
          refine ⟨1815285953499764932706267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 77452200682656637128800725 1815285953499764932706267)
          ·
            refine ⟨2722928930249647399059401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1815285953499764932706267 2722928930249647399059401)
            ·
              refine ⟨2042196697687235549294551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2722928930249647399059401 2042196697687235549294551)
              ·
                refine ⟨3063295046530853323941827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2042196697687235549294551 3063295046530853323941827)
                ·
                  refine ⟨4594942569796279985912741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3063295046530853323941827 4594942569796279985912741)
                  ·
                    refine ⟨861551731836802497358639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4594942569796279985912741 861551731836802497358639)
                    ·
                      rfl

theorem cell22_2516799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 2, 1, 1, 4].length) (baseStart_2516799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2516799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2516799 prefixEnd_2516799 := by exact prefixLift 2516799
  have htrace : WordTrace (prefixWord ++ tailWord_2516799) baseStart_2516799 baseEnd_2516799 := by
    simpa [prefixWord, tailWord_2516799, baseEnd_2516799] using wordTrace_append hprefix tailTrace_2516799
  have hstable : (prefixWord ++ tailWord_2516799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2516799).length < 2 ^ (prefixWord ++ tailWord_2516799).sum := by decide
  have hdescent : baseEnd_2516799 < baseStart_2516799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2516799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2516840 : List Nat := [2, 1, 4, 2, 1, 1, 1, 4, 3, 3]
def baseStart_2516840 : Nat := 118140960795 + 2516840 * 2 ^ 59
def prefixEnd_2516840 : Nat := 4983230072969 + 3 ^ 40 * 2516840 * 2
def baseEnd_2516840 : Nat := 861565766974692057083513

theorem tailTrace_2516840 : CollatzResearch.WordTrace tailWord_2516840 prefixEnd_2516840 861565766974692057083513 := by
  unfold tailWord_2516840
  simp only [CollatzResearch.WordTrace]
  refine ⟨45898348100962998447817987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61197797467950664597090649 45898348100962998447817987)
  ·
    refine ⟨68847522151444497671726981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45898348100962998447817987 68847522151444497671726981)
    ·
      refine ⟨12908910403395843313448809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68847522151444497671726981 12908910403395843313448809)
      ·
        refine ⟨9681682802546882485086607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12908910403395843313448809 9681682802546882485086607)
        ·
          refine ⟨14522524203820323727629911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9681682802546882485086607 14522524203820323727629911)
          ·
            refine ⟨21783786305730485591444867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14522524203820323727629911 21783786305730485591444867)
            ·
              refine ⟨32675679458595728387167301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21783786305730485591444867 32675679458595728387167301)
              ·
                refine ⟨6126689898486699072593869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32675679458595728387167301 6126689898486699072593869)
                ·
                  refine ⟨2297508711932512152222701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6126689898486699072593869 2297508711932512152222701)
                  ·
                    refine ⟨861565766974692057083513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2297508711932512152222701 861565766974692057083513)
                    ·
                      rfl

theorem cell22_2516840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 4, 3, 3].length) (baseStart_2516840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2516840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2516840 prefixEnd_2516840 := by exact prefixLift 2516840
  have htrace : WordTrace (prefixWord ++ tailWord_2516840) baseStart_2516840 baseEnd_2516840 := by
    simpa [prefixWord, tailWord_2516840, baseEnd_2516840] using wordTrace_append hprefix tailTrace_2516840
  have hstable : (prefixWord ++ tailWord_2516840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2516840).length < 2 ^ (prefixWord ++ tailWord_2516840).sum := by decide
  have hdescent : baseEnd_2516840 < baseStart_2516840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2516840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2516853 : List Nat := [1, 3, 4, 1, 1, 1, 1, 1, 9]
def baseStart_2516853 : Nat := 118140960795 + 2516853 * 2 ^ 59
def prefixEnd_2516853 : Nat := 4983230072969 + 3 ^ 40 * 2516853 * 2
def baseEnd_2516853 : Nat := 287190072380121452169491

theorem tailTrace_2516853 : CollatzResearch.WordTrace tailWord_2516853 prefixEnd_2516853 287190072380121452169491 := by
  unfold tailWord_2516853
  simp only [CollatzResearch.WordTrace]
  refine ⟨91797170350878900115859213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61198113567252600077239475 91797170350878900115859213)
  ·
    refine ⟨34423938881579587543447205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91797170350878900115859213 34423938881579587543447205)
    ·
      refine ⟨6454488540296172664396351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34423938881579587543447205 6454488540296172664396351)
      ·
        refine ⟨9681732810444258996594527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6454488540296172664396351 9681732810444258996594527)
        ·
          refine ⟨14522599215666388494891791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9681732810444258996594527 14522599215666388494891791)
          ·
            refine ⟨21783898823499582742337687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14522599215666388494891791 21783898823499582742337687)
            ·
              refine ⟨32675848235249374113506531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21783898823499582742337687 32675848235249374113506531)
              ·
                refine ⟨49013772352874061170259797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32675848235249374113506531 49013772352874061170259797)
                ·
                  refine ⟨287190072380121452169491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 49013772352874061170259797 287190072380121452169491)
                  ·
                    rfl

theorem cell22_2516853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 9].length) (baseStart_2516853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2516853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2516853 prefixEnd_2516853 := by exact prefixLift 2516853
  have htrace : WordTrace (prefixWord ++ tailWord_2516853) baseStart_2516853 baseEnd_2516853 := by
    simpa [prefixWord, tailWord_2516853, baseEnd_2516853] using wordTrace_append hprefix tailTrace_2516853
  have hstable : (prefixWord ++ tailWord_2516853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2516853).length < 2 ^ (prefixWord ++ tailWord_2516853).sum := by decide
  have hdescent : baseEnd_2516853 < baseStart_2516853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2516853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2516868 : List Nat := [2, 3, 2, 1, 1, 1, 2, 1, 4, 5]
def baseStart_2516868 : Nat := 118140960795 + 2516868 * 2 ^ 59
def prefixEnd_2516868 : Nat := 4983230072969 + 3 ^ 40 * 2516868 * 2
def baseEnd_2516868 : Nat := 861575351946909317383427

theorem tailTrace_2516868 : CollatzResearch.WordTrace tailWord_2516868 prefixEnd_2516868 861575351946909317383427 := by
  unfold tailWord_2516868
  simp only [CollatzResearch.WordTrace]
  refine ⟨45898858722912278838827629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61198478297216371785103505 45898858722912278838827629)
  ·
    refine ⟨17212072021092104564560361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45898858722912278838827629 17212072021092104564560361)
    ·
      refine ⟨12909054015819078423420271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17212072021092104564560361 12909054015819078423420271)
      ·
        refine ⟨19363581023728617635130407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12909054015819078423420271 19363581023728617635130407)
        ·
          refine ⟨29045371535592926452695611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19363581023728617635130407 29045371535592926452695611)
          ·
            refine ⟨43568057303389389679043417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29045371535592926452695611 43568057303389389679043417)
            ·
              refine ⟨32676042977542042259282563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43568057303389389679043417 32676042977542042259282563)
              ·
                refine ⟨49014064466313063388923845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32676042977542042259282563 49014064466313063388923845)
                ·
                  refine ⟨9190137087433699385423221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49014064466313063388923845 9190137087433699385423221)
                  ·
                    refine ⟨861575351946909317383427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9190137087433699385423221 861575351946909317383427)
                    ·
                      rfl

theorem cell22_2516868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_2516868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2516868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2516868 prefixEnd_2516868 := by exact prefixLift 2516868
  have htrace : WordTrace (prefixWord ++ tailWord_2516868) baseStart_2516868 baseEnd_2516868 := by
    simpa [prefixWord, tailWord_2516868, baseEnd_2516868] using wordTrace_append hprefix tailTrace_2516868
  have hstable : (prefixWord ++ tailWord_2516868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2516868).length < 2 ^ (prefixWord ++ tailWord_2516868).sum := by decide
  have hdescent : baseEnd_2516868 < baseStart_2516868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2516868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2516874 : List Nat := [3, 1, 2, 4, 2, 2, 1, 1, 3, 3]
def baseStart_2516874 : Nat := 118140960795 + 2516874 * 2 ^ 59
def prefixEnd_2516874 : Nat := 4983230072969 + 3 ^ 40 * 2516874 * 2
def baseEnd_2516874 : Nat := 861577405869527301733409

theorem tailTrace_2516874 : CollatzResearch.WordTrace tailWord_2516874 prefixEnd_2516874 861577405869527301733409 := by
  unfold tailWord_2516874
  simp only [CollatzResearch.WordTrace]
  refine ⟨22949484070950705175593419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61198624189201880468249117 22949484070950705175593419)
  ·
    refine ⟨34424226106426057763390129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22949484070950705175593419 34424226106426057763390129)
    ·
      refine ⟨25818169579819543322542597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34424226106426057763390129 25818169579819543322542597)
      ·
        refine ⟨4840906796216164372976737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25818169579819543322542597 4840906796216164372976737)
        ·
          refine ⟨3630680097162123279732553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4840906796216164372976737 3630680097162123279732553)
          ·
            refine ⟨2723010072871592459799415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3630680097162123279732553 2723010072871592459799415)
            ·
              refine ⟨4084515109307388689699123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2723010072871592459799415 4084515109307388689699123)
              ·
                refine ⟨6126772663961083034548685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4084515109307388689699123 6126772663961083034548685)
                ·
                  refine ⟨2297539748985406137955757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6126772663961083034548685 2297539748985406137955757)
                  ·
                    refine ⟨861577405869527301733409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2297539748985406137955757 861577405869527301733409)
                    ·
                      rfl

theorem cell22_2516874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 1, 3, 3].length) (baseStart_2516874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2516874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2516874 prefixEnd_2516874 := by exact prefixLift 2516874
  have htrace : WordTrace (prefixWord ++ tailWord_2516874) baseStart_2516874 baseEnd_2516874 := by
    simpa [prefixWord, tailWord_2516874, baseEnd_2516874] using wordTrace_append hprefix tailTrace_2516874
  have hstable : (prefixWord ++ tailWord_2516874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2516874).length < 2 ^ (prefixWord ++ tailWord_2516874).sum := by decide
  have hdescent : baseEnd_2516874 < baseStart_2516874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2516874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2516887 : List Nat := [1, 1, 3, 3, 1, 5, 2, 1, 5]
def baseStart_2516887 : Nat := 118140960795 + 2516887 * 2 ^ 59
def prefixEnd_2516887 : Nat := 4983230072969 + 3 ^ 40 * 2516887 * 2
def baseEnd_2516887 : Nat := 287193952011733200386123

theorem tailTrace_2516887 : CollatzResearch.WordTrace tailWord_2516887 prefixEnd_2516887 287193952011733200386123 := by
  unfold tailWord_2516887
  simp only [CollatzResearch.WordTrace]
  refine ⟨91798410432755723922596915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61198940288503815948397943 91798410432755723922596915)
  ·
    refine ⟨137697615649133585883895373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91798410432755723922596915 137697615649133585883895373)
    ·
      refine ⟨51636605868425094706460765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137697615649133585883895373 51636605868425094706460765)
      ·
        refine ⟨19363727200659410514922787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51636605868425094706460765 19363727200659410514922787)
        ·
          refine ⟨29045590800989115772384181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19363727200659410514922787 29045590800989115772384181)
          ·
            refine ⟨2723024137592729603661017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29045590800989115772384181 2723024137592729603661017)
            ·
              refine ⟨2042268103194547202745763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2723024137592729603661017 2042268103194547202745763)
              ·
                refine ⟨3063402154791820804118645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2042268103194547202745763 3063402154791820804118645)
                ·
                  refine ⟨287193952011733200386123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3063402154791820804118645 287193952011733200386123)
                  ·
                    rfl

theorem cell22_2516887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 2, 1, 5].length) (baseStart_2516887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2516887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2516887 prefixEnd_2516887 := by exact prefixLift 2516887
  have htrace : WordTrace (prefixWord ++ tailWord_2516887) baseStart_2516887 baseEnd_2516887 := by
    simpa [prefixWord, tailWord_2516887, baseEnd_2516887] using wordTrace_append hprefix tailTrace_2516887
  have hstable : (prefixWord ++ tailWord_2516887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2516887).length < 2 ^ (prefixWord ++ tailWord_2516887).sum := by decide
  have hdescent : baseEnd_2516887 < baseStart_2516887 := by decide
  rcases family_descends (prefixWord ++ tailWord_2516887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2516900 : List Nat := [2, 3, 1, 2, 1, 4, 1, 1, 3, 4]
def baseStart_2516900 : Nat := 118140960795 + 2516900 * 2 ^ 59
def prefixEnd_2516900 : Nat := 4983230072969 + 3 ^ 40 * 2516900 * 2
def baseEnd_2516900 : Nat := 861586306200871900583329

theorem tailTrace_2516900 : CollatzResearch.WordTrace tailWord_2516900 prefixEnd_2516900 861586306200871900583329 := by
  unfold tailWord_2516900
  simp only [CollatzResearch.WordTrace]
  refine ⟨45899442290854313571410077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61199256387805751428546769 45899442290854313571410077)
  ·
    refine ⟨17212290859070367589278779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45899442290854313571410077 17212290859070367589278779)
    ·
      refine ⟨25818436288605551383918169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17212290859070367589278779 25818436288605551383918169)
      ·
        refine ⟨19363827216454163537938627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25818436288605551383918169 19363827216454163537938627)
        ·
          refine ⟨29045740824681245306907941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19363827216454163537938627 29045740824681245306907941)
          ·
            refine ⟨5446076404627733495045239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29045740824681245306907941 5446076404627733495045239)
            ·
              refine ⟨8169114606941600242567859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5446076404627733495045239 8169114606941600242567859)
              ·
                refine ⟨12253671910412400363851789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8169114606941600242567859 12253671910412400363851789)
                ·
                  refine ⟨4595126966404650136444421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12253671910412400363851789 4595126966404650136444421)
                  ·
                    refine ⟨861586306200871900583329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4595126966404650136444421 861586306200871900583329)
                    ·
                      rfl

theorem cell22_2516900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 1, 3, 4].length) (baseStart_2516900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2516900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2516900 prefixEnd_2516900 := by exact prefixLift 2516900
  have htrace : WordTrace (prefixWord ++ tailWord_2516900) baseStart_2516900 baseEnd_2516900 := by
    simpa [prefixWord, tailWord_2516900, baseEnd_2516900] using wordTrace_append hprefix tailTrace_2516900
  have hstable : (prefixWord ++ tailWord_2516900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2516900).length < 2 ^ (prefixWord ++ tailWord_2516900).sum := by decide
  have hdescent : baseEnd_2516900 < baseStart_2516900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2516900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2516915 : List Nat := [1, 1, 1, 2, 3, 1, 4, 5, 4]
def baseStart_2516915 : Nat := 118140960795 + 2516915 * 2 ^ 59
def prefixEnd_2516915 : Nat := 4983230072969 + 3 ^ 40 * 2516915 * 2
def baseEnd_2516915 : Nat := 287197147002472287152761

theorem tailTrace_2516915 : CollatzResearch.WordTrace tailWord_2516915 prefixEnd_2516915 287197147002472287152761 := by
  unfold tailWord_2516915
  simp only [CollatzResearch.WordTrace]
  refine ⟨91799431676654284704616199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61199621117769523136410799 91799431676654284704616199)
  ·
    refine ⟨137699147514981427056924299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91799431676654284704616199 137699147514981427056924299)
    ·
      refine ⟨206548721272472140585386449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137699147514981427056924299 206548721272472140585386449)
      ·
        refine ⟨154911540954354105439039837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 206548721272472140585386449 154911540954354105439039837)
        ·
          refine ⟨58091827857882789539639939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 154911540954354105439039837 58091827857882789539639939)
          ·
            refine ⟨87137741786824184309459909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58091827857882789539639939 87137741786824184309459909)
            ·
              refine ⟨16338326585029534558023733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87137741786824184309459909 16338326585029534558023733)
              ·
                refine ⟨1531718117346518864814725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16338326585029534558023733 1531718117346518864814725)
                ·
                  refine ⟨287197147002472287152761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1531718117346518864814725 287197147002472287152761)
                  ·
                    rfl

theorem cell22_2516915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 5, 4].length) (baseStart_2516915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2516915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2516915 prefixEnd_2516915 := by exact prefixLift 2516915
  have htrace : WordTrace (prefixWord ++ tailWord_2516915) baseStart_2516915 baseEnd_2516915 := by
    simpa [prefixWord, tailWord_2516915, baseEnd_2516915] using wordTrace_append hprefix tailTrace_2516915
  have hstable : (prefixWord ++ tailWord_2516915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2516915).length < 2 ^ (prefixWord ++ tailWord_2516915).sum := by decide
  have hdescent : baseEnd_2516915 < baseStart_2516915 := by decide
  rcases family_descends (prefixWord ++ tailWord_2516915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2516975 : List Nat := [1, 1, 2, 1, 4, 2, 1, 2, 5, 3]
def baseStart_2516975 : Nat := 118140960795 + 2516975 * 2 ^ 59
def prefixEnd_2516975 : Nat := 4983230072969 + 3 ^ 40 * 2516975 * 2
def baseEnd_2516975 : Nat := 861611980233596704958099

theorem tailTrace_2516975 : CollatzResearch.WordTrace tailWord_2516975 prefixEnd_2516975 861611980233596704958099 := by
  unfold tailWord_2516975
  simp only [CollatzResearch.WordTrace]
  refine ⟨91801620056436914951800379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61201080037624609967866919 91801620056436914951800379)
  ·
    refine ⟨137702430084655372427700569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91801620056436914951800379 137702430084655372427700569)
    ·
      refine ⟨103276822563491529320775427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137702430084655372427700569 103276822563491529320775427)
      ·
        refine ⟨154915233845237293981163141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103276822563491529320775427 154915233845237293981163141)
        ·
          refine ⟨29046606345981992621468089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 154915233845237293981163141 29046606345981992621468089)
          ·
            refine ⟨21784954759486494466101067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29046606345981992621468089 21784954759486494466101067)
            ·
              refine ⟨32677432139229741699151601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21784954759486494466101067 32677432139229741699151601)
              ·
                refine ⟨24508074104422306274363701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32677432139229741699151601 24508074104422306274363701)
                ·
                  refine ⟨2297631947289591213221597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24508074104422306274363701 2297631947289591213221597)
                  ·
                    refine ⟨861611980233596704958099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2297631947289591213221597 861611980233596704958099)
                    ·
                      rfl

theorem cell22_2516975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 5, 3].length) (baseStart_2516975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2516975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2516975 prefixEnd_2516975 := by exact prefixLift 2516975
  have htrace : WordTrace (prefixWord ++ tailWord_2516975) baseStart_2516975 baseEnd_2516975 := by
    simpa [prefixWord, tailWord_2516975, baseEnd_2516975] using wordTrace_append hprefix tailTrace_2516975
  have hstable : (prefixWord ++ tailWord_2516975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2516975).length < 2 ^ (prefixWord ++ tailWord_2516975).sum := by decide
  have hdescent : baseEnd_2516975 < baseStart_2516975 := by decide
  rcases family_descends (prefixWord ++ tailWord_2516975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2517065 : List Nat := [1, 2, 1, 1, 2, 2, 4, 3, 1, 5]
def baseStart_2517065 : Nat := 118140960795 + 2517065 * 2 ^ 59
def prefixEnd_2517065 : Nat := 4983230072969 + 3 ^ 40 * 2517065 * 2
def baseEnd_2517065 : Nat := 861642789072866470207823

theorem tailTrace_2517065 : CollatzResearch.WordTrace tailWord_2517065 prefixEnd_2517065 861642789072866470207823 := by
  unfold tailWord_2517065
  simp only [CollatzResearch.WordTrace]
  refine ⟨91804902626110860322576649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61203268417407240215051099 91804902626110860322576649)
  ·
    refine ⟨68853676969583145241932487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91804902626110860322576649 68853676969583145241932487)
    ·
      refine ⟨103280515454374717862898731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68853676969583145241932487 103280515454374717862898731)
      ·
        refine ⟨154920773181562076794348097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103280515454374717862898731 154920773181562076794348097)
        ·
          refine ⟨116190579886171557595761073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154920773181562076794348097 116190579886171557595761073)
          ·
            refine ⟨87142934914628668196820805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116190579886171557595761073 87142934914628668196820805)
            ·
              refine ⟨16339300296492875286903901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87142934914628668196820805 16339300296492875286903901)
              ·
                refine ⟨6127237611184828232588963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16339300296492875286903901 6127237611184828232588963)
                ·
                  refine ⟨9190856416777242348883445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6127237611184828232588963 9190856416777242348883445)
                  ·
                    refine ⟨861642789072866470207823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9190856416777242348883445 861642789072866470207823)
                    ·
                      rfl

theorem cell22_2517065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 3, 1, 5].length) (baseStart_2517065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2517065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2517065 prefixEnd_2517065 := by exact prefixLift 2517065
  have htrace : WordTrace (prefixWord ++ tailWord_2517065) baseStart_2517065 baseEnd_2517065 := by
    simpa [prefixWord, tailWord_2517065, baseEnd_2517065] using wordTrace_append hprefix tailTrace_2517065
  have hstable : (prefixWord ++ tailWord_2517065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2517065).length < 2 ^ (prefixWord ++ tailWord_2517065).sum := by decide
  have hdescent : baseEnd_2517065 < baseStart_2517065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2517065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2517127 : List Nat := [1, 1, 4, 2, 1, 1, 3, 1, 5, 3]
def baseStart_2517127 : Nat := 118140960795 + 2517127 * 2 ^ 59
def prefixEnd_2517127 : Nat := 4983230072969 + 3 ^ 40 * 2517127 * 2
def baseEnd_2517127 : Nat := 861664012939918975157633

theorem tailTrace_2517127 : CollatzResearch.WordTrace tailWord_2517127 prefixEnd_2517127 861664012939918975157633 := by
  unfold tailWord_2517127
  simp only [CollatzResearch.WordTrace]
  refine ⟨91807163951886244911333635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61204775967924163274222423 91807163951886244911333635)
  ·
    refine ⟨137710745927829367367000453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91807163951886244911333635 137710745927829367367000453)
    ·
      refine ⟨25820764861468006381312585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 137710745927829367367000453 25820764861468006381312585)
      ·
        refine ⟨19365573646101004785984439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25820764861468006381312585 19365573646101004785984439)
        ·
          refine ⟨29048360469151507178976659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19365573646101004785984439 29048360469151507178976659)
          ·
            refine ⟨43572540703727260768464989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29048360469151507178976659 43572540703727260768464989)
            ·
              refine ⟨16339702763897722788174371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43572540703727260768464989 16339702763897722788174371)
              ·
                refine ⟨24509554145846584182261557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16339702763897722788174371 24509554145846584182261557)
                ·
                  refine ⟨2297770701173117267087021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24509554145846584182261557 2297770701173117267087021)
                  ·
                    refine ⟨861664012939918975157633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2297770701173117267087021 861664012939918975157633)
                    ·
                      rfl

theorem cell22_2517127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 5, 3].length) (baseStart_2517127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2517127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2517127 prefixEnd_2517127 := by exact prefixLift 2517127
  have htrace : WordTrace (prefixWord ++ tailWord_2517127) baseStart_2517127 baseEnd_2517127 := by
    simpa [prefixWord, tailWord_2517127, baseEnd_2517127] using wordTrace_append hprefix tailTrace_2517127
  have hstable : (prefixWord ++ tailWord_2517127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2517127).length < 2 ^ (prefixWord ++ tailWord_2517127).sum := by decide
  have hdescent : baseEnd_2517127 < baseStart_2517127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2517127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2517150 : List Nat := [4, 3, 1, 1, 4, 1, 1, 2, 2, 3]
def baseStart_2517150 : Nat := 118140960795 + 2517150 * 2 ^ 59
def prefixEnd_2517150 : Nat := 4983230072969 + 3 ^ 40 * 2517150 * 2
def baseEnd_2517150 : Nat := 861671886309954581832563

theorem tailTrace_2517150 : CollatzResearch.WordTrace tailWord_2517150 prefixEnd_2517150 861671886309954581832563 := by
  unfold tailWord_2517150
  simp only [CollatzResearch.WordTrace]
  refine ⟨11476000353850364979927613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61205335220535279892947269 11476000353850364979927613)
  ·
    refine ⟨4303500132693886867472855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11476000353850364979927613 4303500132693886867472855)
    ·
      refine ⟨6455250199040830301209283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4303500132693886867472855 6455250199040830301209283)
      ·
        refine ⟨9682875298561245451813925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6455250199040830301209283 9682875298561245451813925)
        ·
          refine ⟨1815539118480233522215111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9682875298561245451813925 1815539118480233522215111)
          ·
            refine ⟨2723308677720350283322667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1815539118480233522215111 2723308677720350283322667)
            ·
              refine ⟨4084963016580525424984001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2723308677720350283322667 4084963016580525424984001)
              ·
                refine ⟨3063722262435394068738001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4084963016580525424984001 3063722262435394068738001)
                ·
                  refine ⟨2297791696826545551553501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3063722262435394068738001 2297791696826545551553501)
                  ·
                    refine ⟨861671886309954581832563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2297791696826545551553501 861671886309954581832563)
                    ·
                      rfl

theorem cell22_2517150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_2517150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2517150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2517150 prefixEnd_2517150 := by exact prefixLift 2517150
  have htrace : WordTrace (prefixWord ++ tailWord_2517150) baseStart_2517150 baseEnd_2517150 := by
    simpa [prefixWord, tailWord_2517150, baseEnd_2517150] using wordTrace_append hprefix tailTrace_2517150
  have hstable : (prefixWord ++ tailWord_2517150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2517150).length < 2 ^ (prefixWord ++ tailWord_2517150).sum := by decide
  have hdescent : baseEnd_2517150 < baseStart_2517150 := by decide
  rcases family_descends (prefixWord ++ tailWord_2517150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2517212 : List Nat := [2, 2, 5, 2, 1, 1, 3, 2, 1, 3]
def baseStart_2517212 : Nat := 118140960795 + 2517212 * 2 ^ 59
def prefixEnd_2517212 : Nat := 4983230072969 + 3 ^ 40 * 2517212 * 2
def baseEnd_2517212 : Nat := 861693110177007086782373

theorem tailTrace_2517212 : CollatzResearch.WordTrace tailWord_2517212 prefixEnd_2517212 861693110177007086782373 := by
  unfold tailWord_2517212
  simp only [CollatzResearch.WordTrace]
  refine ⟨45905132078289152214088945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61206842771052202952118593 45905132078289152214088945)
  ·
    refine ⟨34428849058716864160566709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45905132078289152214088945 34428849058716864160566709)
    ·
      refine ⟨3227704599254706015053129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34428849058716864160566709 3227704599254706015053129)
      ·
        refine ⟨2420778449441029511289847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3227704599254706015053129 2420778449441029511289847)
        ·
          refine ⟨3631167674161544266934771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2420778449441029511289847 3631167674161544266934771)
          ·
            refine ⟨5446751511242316400402157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3631167674161544266934771 5446751511242316400402157)
            ·
              refine ⟨2042531816715868650150809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5446751511242316400402157 2042531816715868650150809)
              ·
                refine ⟨1531898862536901487613107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2042531816715868650150809 1531898862536901487613107)
                ·
                  refine ⟨2297848293805352231419661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1531898862536901487613107 2297848293805352231419661)
                  ·
                    refine ⟨861693110177007086782373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2297848293805352231419661 861693110177007086782373)
                    ·
                      rfl

theorem cell22_2517212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_2517212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2517212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2517212 prefixEnd_2517212 := by exact prefixLift 2517212
  have htrace : WordTrace (prefixWord ++ tailWord_2517212) baseStart_2517212 baseEnd_2517212 := by
    simpa [prefixWord, tailWord_2517212, baseEnd_2517212] using wordTrace_append hprefix tailTrace_2517212
  have hstable : (prefixWord ++ tailWord_2517212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2517212).length < 2 ^ (prefixWord ++ tailWord_2517212).sum := by decide
  have hdescent : baseEnd_2517212 < baseStart_2517212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2517212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2517249 : List Nat := [1, 2, 4, 1, 1, 2, 4, 1, 2, 4]
def baseStart_2517249 : Nat := 118140960795 + 2517249 * 2 ^ 59
def prefixEnd_2517249 : Nat := 4983230072969 + 3 ^ 40 * 2517249 * 2
def baseEnd_2517249 : Nat := 861705776033151323607259

theorem tailTrace_2517249 : CollatzResearch.WordTrace tailWord_2517249 prefixEnd_2517249 861705776033151323607259 := by
  unfold tailWord_2517249
  simp only [CollatzResearch.WordTrace]
  refine ⟨91811613657444259747274801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61207742438296173164849867 91811613657444259747274801)
  ·
    refine ⟨68858710243083194810456101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91811613657444259747274801 68858710243083194810456101)
    ·
      refine ⟨12911008170578099026960519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68858710243083194810456101 12911008170578099026960519)
      ·
        refine ⟨19366512255867148540440779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12911008170578099026960519 19366512255867148540440779)
        ·
          refine ⟨29049768383800722810661169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19366512255867148540440779 29049768383800722810661169)
          ·
            refine ⟨21787326287850542107995877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29049768383800722810661169 21787326287850542107995877)
            ·
              refine ⟨4085123678971976645249227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21787326287850542107995877 4085123678971976645249227)
              ·
                refine ⟨6127685518457964967873841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4085123678971976645249227 6127685518457964967873841)
                ·
                  refine ⟨4595764138843473725905381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6127685518457964967873841 4595764138843473725905381)
                  ·
                    refine ⟨861705776033151323607259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4595764138843473725905381 861705776033151323607259)
                    ·
                      rfl

theorem cell22_2517249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_2517249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2517249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2517249 prefixEnd_2517249 := by exact prefixLift 2517249
  have htrace : WordTrace (prefixWord ++ tailWord_2517249) baseStart_2517249 baseEnd_2517249 := by
    simpa [prefixWord, tailWord_2517249, baseEnd_2517249] using wordTrace_append hprefix tailTrace_2517249
  have hstable : (prefixWord ++ tailWord_2517249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2517249).length < 2 ^ (prefixWord ++ tailWord_2517249).sum := by decide
  have hdescent : baseEnd_2517249 < baseStart_2517249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2517249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2517371 : List Nat := [1, 1, 1, 1, 1, 7, 3, 3, 4]
def baseStart_2517371 : Nat := 118140960795 + 2517371 * 2 ^ 59
def prefixEnd_2517371 : Nat := 4983230072969 + 3 ^ 40 * 2517371 * 2
def baseEnd_2517371 : Nat := 287249179708794557352295

theorem tailTrace_2517371 : CollatzResearch.WordTrace tailWord_2517371 prefixEnd_2517371 287249179708794557352295 := by
  unfold tailWord_2517371
  simp only [CollatzResearch.WordTrace]
  refine ⟨91816063363002274583215967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61210708908668183055477311 91816063363002274583215967)
  ·
    refine ⟨137724095044503411874823951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91816063363002274583215967 137724095044503411874823951)
    ·
      refine ⟨206586142566755117812235927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137724095044503411874823951 206586142566755117812235927)
      ·
        refine ⟨309879213850132676718353891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206586142566755117812235927 309879213850132676718353891)
        ·
          refine ⟨464818820775199015077530837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 309879213850132676718353891 464818820775199015077530837)
          ·
            refine ⟨10894191111918726915879629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 464818820775199015077530837 10894191111918726915879629)
            ·
              refine ⟨4085321666969522593454861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10894191111918726915879629 4085321666969522593454861)
              ·
                refine ⟨1531995625113570972545573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4085321666969522593454861 1531995625113570972545573)
                ·
                  refine ⟨287249179708794557352295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1531995625113570972545573 287249179708794557352295)
                  ·
                    rfl

theorem cell22_2517371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 3, 4].length) (baseStart_2517371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2517371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2517371 prefixEnd_2517371 := by exact prefixLift 2517371
  have htrace : WordTrace (prefixWord ++ tailWord_2517371) baseStart_2517371 baseEnd_2517371 := by
    simpa [prefixWord, tailWord_2517371, baseEnd_2517371] using wordTrace_append hprefix tailTrace_2517371
  have hstable : (prefixWord ++ tailWord_2517371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2517371).length < 2 ^ (prefixWord ++ tailWord_2517371).sum := by decide
  have hdescent : baseEnd_2517371 < baseStart_2517371 := by decide
  rcases family_descends (prefixWord ++ tailWord_2517371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2517388 : List Nat := [2, 2, 1, 2, 1, 5, 3, 2, 4]
def baseStart_2517388 : Nat := 118140960795 + 2517388 * 2 ^ 59
def prefixEnd_2517388 : Nat := 4983230072969 + 3 ^ 40 * 2517388 * 2
def baseEnd_2517388 : Nat := 287251119524600431460611

theorem tailTrace_2517388 : CollatzResearch.WordTrace tailWord_2517388 prefixEnd_2517388 287251119524600431460611 := by
  unfold tailWord_2517388
  simp only [CollatzResearch.WordTrace]
  refine ⟨45908341701970343243292409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61211122269293790991056545 45908341701970343243292409)
  ·
    refine ⟨34431256276477757432469307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45908341701970343243292409 34431256276477757432469307)
    ·
      refine ⟨51646884414716636148703961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34431256276477757432469307 51646884414716636148703961)
      ·
        refine ⟨38735163311037477111527971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51646884414716636148703961 38735163311037477111527971)
        ·
          refine ⟨58102744966556215667291957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38735163311037477111527971 58102744966556215667291957)
          ·
            refine ⟨5447132340614645218808621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58102744966556215667291957 5447132340614645218808621)
            ·
              refine ⟨2042674627730491957053233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5447132340614645218808621 2042674627730491957053233)
              ·
                refine ⟨1532005970797868967789925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2042674627730491957053233 1532005970797868967789925)
                ·
                  refine ⟨287251119524600431460611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1532005970797868967789925 287251119524600431460611)
                  ·
                    rfl

theorem cell22_2517388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 3, 2, 4].length) (baseStart_2517388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2517388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2517388 prefixEnd_2517388 := by exact prefixLift 2517388
  have htrace : WordTrace (prefixWord ++ tailWord_2517388) baseStart_2517388 baseEnd_2517388 := by
    simpa [prefixWord, tailWord_2517388, baseEnd_2517388] using wordTrace_append hprefix tailTrace_2517388
  have hstable : (prefixWord ++ tailWord_2517388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2517388).length < 2 ^ (prefixWord ++ tailWord_2517388).sum := by decide
  have hdescent : baseEnd_2517388 < baseStart_2517388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2517388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2517416 : List Nat := [2, 1, 6, 1, 1, 1, 2, 8]
def baseStart_2517416 : Nat := 118140960795 + 2517416 * 2 ^ 59
def prefixEnd_2517416 : Nat := 4983230072969 + 3 ^ 40 * 2517416 * 2
def baseEnd_2517416 : Nat := 95751438171779839409083

theorem tailTrace_2517416 : CollatzResearch.WordTrace tailWord_2517416 prefixEnd_2517416 95751438171779839409083 := by
  unfold tailWord_2517416
  simp only [CollatzResearch.WordTrace]
  refine ⟨45908852323919623634302051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61211803098559498179069401 45908852323919623634302051)
  ·
    refine ⟨68863278485879435451453077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45908852323919623634302051 68863278485879435451453077)
    ·
      refine ⟨3227966179025598536786863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 68863278485879435451453077 3227966179025598536786863)
      ·
        refine ⟨4841949268538397805180295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3227966179025598536786863 4841949268538397805180295)
        ·
          refine ⟨7262923902807596707770443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4841949268538397805180295 7262923902807596707770443)
          ·
            refine ⟨10894385854211395061655665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7262923902807596707770443 10894385854211395061655665)
            ·
              refine ⟨8170789390658546296241749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10894385854211395061655665 8170789390658546296241749)
              ·
                refine ⟨95751438171779839409083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8170789390658546296241749 95751438171779839409083)
                ·
                  rfl

theorem cell22_2517416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 8].length) (baseStart_2517416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2517416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2517416 prefixEnd_2517416 := by exact prefixLift 2517416
  have htrace : WordTrace (prefixWord ++ tailWord_2517416) baseStart_2517416 baseEnd_2517416 := by
    simpa [prefixWord, tailWord_2517416, baseEnd_2517416] using wordTrace_append hprefix tailTrace_2517416
  have hstable : (prefixWord ++ tailWord_2517416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2517416).length < 2 ^ (prefixWord ++ tailWord_2517416).sum := by decide
  have hdescent : baseEnd_2517416 < baseStart_2517416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2517416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2517461 : List Nat := [1, 3, 2, 3, 1, 2, 2, 3, 5]
def baseStart_2517461 : Nat := 118140960795 + 2517461 * 2 ^ 59
def prefixEnd_2517461 : Nat := 4983230072969 + 3 ^ 40 * 2517461 * 2
def baseEnd_2517461 : Nat := 287259449321884479102203

theorem tailTrace_2517461 : CollatzResearch.WordTrace tailWord_2517461 prefixEnd_2517461 287259449321884479102203 := by
  unfold tailWord_2517461
  simp only [CollatzResearch.WordTrace]
  refine ⟨91819345932676219953992237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61212897288450813302661491 91819345932676219953992237)
  ·
    refine ⟨34432254724753582482747089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91819345932676219953992237 34432254724753582482747089)
    ·
      refine ⟨25824191043565186862060317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34432254724753582482747089 25824191043565186862060317)
      ·
        refine ⟨9684071641336945073272619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25824191043565186862060317 9684071641336945073272619)
        ·
          refine ⟨14526107462005417609908929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9684071641336945073272619 14526107462005417609908929)
          ·
            refine ⟨10894580596504063207431697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14526107462005417609908929 10894580596504063207431697)
            ·
              refine ⟨8170935447378047405573773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10894580596504063207431697 8170935447378047405573773)
              ·
                refine ⟨3064100792766767777090165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8170935447378047405573773 3064100792766767777090165)
                ·
                  refine ⟨287259449321884479102203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3064100792766767777090165 287259449321884479102203)
                  ·
                    rfl

theorem cell22_2517461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 3, 5].length) (baseStart_2517461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2517461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2517461 prefixEnd_2517461 := by exact prefixLift 2517461
  have htrace : WordTrace (prefixWord ++ tailWord_2517461) baseStart_2517461 baseEnd_2517461 := by
    simpa [prefixWord, tailWord_2517461, baseEnd_2517461] using wordTrace_append hprefix tailTrace_2517461
  have hstable : (prefixWord ++ tailWord_2517461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2517461).length < 2 ^ (prefixWord ++ tailWord_2517461).sum := by decide
  have hdescent : baseEnd_2517461 < baseStart_2517461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2517461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2517489 : List Nat := [1, 2, 2, 2, 3, 1, 1, 2, 8]
def baseStart_2517489 : Nat := 118140960795 + 2517489 * 2 ^ 59
def prefixEnd_2517489 : Nat := 4983230072969 + 3 ^ 40 * 2517489 * 2
def baseEnd_2517489 : Nat := 287262644312623565868841

theorem tailTrace_2517489 : CollatzResearch.WordTrace tailWord_2517489 prefixEnd_2517489 287262644312623565868841 := by
  unfold tailWord_2517489
  simp only [CollatzResearch.WordTrace]
  refine ⟨91820367176574780736011521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61213578117716520490674347 91820367176574780736011521)
  ·
    refine ⟨68865275382431085552008641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91820367176574780736011521 68865275382431085552008641)
    ·
      refine ⟨51648956536823314164006481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68865275382431085552008641 51648956536823314164006481)
      ·
        refine ⟨38736717402617485623004861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51648956536823314164006481 38736717402617485623004861)
        ·
          refine ⟨14526269025981557108626823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38736717402617485623004861 14526269025981557108626823)
          ·
            refine ⟨21789403538972335662940235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14526269025981557108626823 21789403538972335662940235)
            ·
              refine ⟨32684105308458503494410353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21789403538972335662940235 32684105308458503494410353)
              ·
                refine ⟨24513078981343877620807765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32684105308458503494410353 24513078981343877620807765)
                ·
                  refine ⟨287262644312623565868841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24513078981343877620807765 287262644312623565868841)
                  ·
                    rfl

theorem cell22_2517489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 8].length) (baseStart_2517489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2517489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2517489 prefixEnd_2517489 := by exact prefixLift 2517489
  have htrace : WordTrace (prefixWord ++ tailWord_2517489) baseStart_2517489 baseEnd_2517489 := by
    simpa [prefixWord, tailWord_2517489, baseEnd_2517489] using wordTrace_append hprefix tailTrace_2517489
  have hstable : (prefixWord ++ tailWord_2517489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2517489).length < 2 ^ (prefixWord ++ tailWord_2517489).sum := by decide
  have hdescent : baseEnd_2517489 < baseStart_2517489 := by decide
  rcases family_descends (prefixWord ++ tailWord_2517489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2517491 : List Nat := [1, 1, 1, 2, 2, 2, 5, 3, 1, 4]
def baseStart_2517491 : Nat := 118140960795 + 2517491 * 2 ^ 59
def prefixEnd_2517491 : Nat := 4983230072969 + 3 ^ 40 * 2517491 * 2
def baseEnd_2517491 : Nat := 861788617578743359056517

theorem tailTrace_2517491 : CollatzResearch.WordTrace tailWord_2517491 prefixEnd_2517491 861788617578743359056517 := by
  unfold tailWord_2517491
  simp only [CollatzResearch.WordTrace]
  refine ⟨91820440122567535077584327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61213626748378356718389551 91820440122567535077584327)
  ·
    refine ⟨137730660183851302616376491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91820440122567535077584327 137730660183851302616376491)
    ·
      refine ⟨206595990275776953924564737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137730660183851302616376491 206595990275776953924564737)
      ·
        refine ⟨154946992706832715443423553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 206595990275776953924564737 154946992706832715443423553)
        ·
          refine ⟨116210244530124536582567665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154946992706832715443423553 116210244530124536582567665)
          ·
            refine ⟨87157683397593402436925749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116210244530124536582567665 87157683397593402436925749)
            ·
              refine ⟨8171032818524381478461789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 87157683397593402436925749 8171032818524381478461789)
              ·
                refine ⟨3064137306946643054423171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8171032818524381478461789 3064137306946643054423171)
                ·
                  refine ⟨4596205960419964581634757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3064137306946643054423171 4596205960419964581634757)
                  ·
                    refine ⟨861788617578743359056517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4596205960419964581634757 861788617578743359056517)
                    ·
                      rfl

theorem cell22_2517491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 3, 1, 4].length) (baseStart_2517491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2517491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2517491 prefixEnd_2517491 := by exact prefixLift 2517491
  have htrace : WordTrace (prefixWord ++ tailWord_2517491) baseStart_2517491 baseEnd_2517491 := by
    simpa [prefixWord, tailWord_2517491, baseEnd_2517491] using wordTrace_append hprefix tailTrace_2517491
  have hstable : (prefixWord ++ tailWord_2517491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2517491).length < 2 ^ (prefixWord ++ tailWord_2517491).sum := by decide
  have hdescent : baseEnd_2517491 < baseStart_2517491 := by decide
  rcases family_descends (prefixWord ++ tailWord_2517491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2517519 : List Nat := [1, 1, 2, 1, 1, 1, 2, 6, 1, 6]
def baseStart_2517519 : Nat := 118140960795 + 2517519 * 2 ^ 59
def prefixEnd_2517519 : Nat := 4983230072969 + 3 ^ 40 * 2517519 * 2
def baseEnd_2517519 : Nat := 861798202550960619356431

theorem tailTrace_2517519 : CollatzResearch.WordTrace tailWord_2517519 prefixEnd_2517519 861798202550960619356431 := by
  unfold tailWord_2517519
  simp only [CollatzResearch.WordTrace]
  refine ⟨91821461366466095859603611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61214307577644063906402407 91821461366466095859603611)
  ·
    refine ⟨137732192049699143789405417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91821461366466095859603611 137732192049699143789405417)
    ·
      refine ⟨103299144037274357842054063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137732192049699143789405417 103299144037274357842054063)
      ·
        refine ⟨154948716055911536763081095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103299144037274357842054063 154948716055911536763081095)
        ·
          refine ⟨232423074083867305144621643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154948716055911536763081095 232423074083867305144621643)
          ·
            refine ⟨348634611125800957716932465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 232423074083867305144621643 348634611125800957716932465)
            ·
              refine ⟨261475958344350718287699349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 348634611125800957716932465 261475958344350718287699349)
              ·
                refine ⟨12256685547391439919735907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 261475958344350718287699349 12256685547391439919735907)
                ·
                  refine ⟨18385028321087159879603861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12256685547391439919735907 18385028321087159879603861)
                  ·
                    refine ⟨861798202550960619356431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18385028321087159879603861 861798202550960619356431)
                    ·
                      rfl

theorem cell22_2517519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 6, 1, 6].length) (baseStart_2517519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2517519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2517519 prefixEnd_2517519 := by exact prefixLift 2517519
  have htrace : WordTrace (prefixWord ++ tailWord_2517519) baseStart_2517519 baseEnd_2517519 := by
    simpa [prefixWord, tailWord_2517519, baseEnd_2517519] using wordTrace_append hprefix tailTrace_2517519
  have hstable : (prefixWord ++ tailWord_2517519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2517519).length < 2 ^ (prefixWord ++ tailWord_2517519).sum := by decide
  have hdescent : baseEnd_2517519 < baseStart_2517519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2517519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2517613 : List Nat := [1, 5, 1, 1, 3, 1, 1, 4, 5]
def baseStart_2517613 : Nat := 118140960795 + 2517613 * 2 ^ 59
def prefixEnd_2517613 : Nat := 4983230072969 + 3 ^ 40 * 2517613 * 2
def baseEnd_2517613 : Nat := 287276793557325235835381

theorem tailTrace_2517613 : CollatzResearch.WordTrace tailWord_2517613 prefixEnd_2517613 287276793557325235835381 := by
  unfold tailWord_2517613
  simp only [CollatzResearch.WordTrace]
  refine ⟨91824889828125549913525493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61216593218750366609016995 91824889828125549913525493)
  ·
    refine ⟨8608583421386770304393015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 91824889828125549913525493 8608583421386770304393015)
    ·
      refine ⟨12912875132080155456589523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8608583421386770304393015 12912875132080155456589523)
      ·
        refine ⟨19369312698120233184884285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12912875132080155456589523 19369312698120233184884285)
        ·
          refine ⟨7263492261795087444331607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19369312698120233184884285 7263492261795087444331607)
          ·
            refine ⟨10895238392692631166497411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7263492261795087444331607 10895238392692631166497411)
            ·
              refine ⟨16342857589038946749746117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10895238392692631166497411 16342857589038946749746117)
              ·
                refine ⟨3064285797944802515577397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16342857589038946749746117 3064285797944802515577397)
                ·
                  refine ⟨287276793557325235835381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3064285797944802515577397 287276793557325235835381)
                  ·
                    rfl

theorem cell22_2517613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 4, 5].length) (baseStart_2517613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2517613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2517613 prefixEnd_2517613 := by exact prefixLift 2517613
  have htrace : WordTrace (prefixWord ++ tailWord_2517613) baseStart_2517613 baseEnd_2517613 := by
    simpa [prefixWord, tailWord_2517613, baseEnd_2517613] using wordTrace_append hprefix tailTrace_2517613
  have hstable : (prefixWord ++ tailWord_2517613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2517613).length < 2 ^ (prefixWord ++ tailWord_2517613).sum := by decide
  have hdescent : baseEnd_2517613 < baseStart_2517613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2517613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2517660 : List Nat := [2, 2, 3, 2, 2, 2, 1, 3, 1, 4]
def baseStart_2517660 : Nat := 118140960795 + 2517660 * 2 ^ 59
def prefixEnd_2517660 : Nat := 4983230072969 + 3 ^ 40 * 2517660 * 2
def baseEnd_2517660 : Nat := 861846469732483251580999

theorem tailTrace_2517660 : CollatzResearch.WordTrace tailWord_2517660 prefixEnd_2517660 861846469732483251580999 := by
  unfold tailWord_2517660
  simp only [CollatzResearch.WordTrace]
  refine ⟨45913302029477638470243217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61217736039303517960324289 45913302029477638470243217)
  ·
    refine ⟨34434976522108228852682413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45913302029477638470243217 34434976522108228852682413)
    ·
      refine ⟨12913116195790585819755905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34434976522108228852682413 12913116195790585819755905)
      ·
        refine ⟨9684837146842939364816929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12913116195790585819755905 9684837146842939364816929)
        ·
          refine ⟨7263627860132204523612697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9684837146842939364816929 7263627860132204523612697)
          ·
            refine ⟨5447720895099153392709523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7263627860132204523612697 5447720895099153392709523)
            ·
              refine ⟨8171581342648730089064285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5447720895099153392709523 8171581342648730089064285)
              ·
                refine ⟨3064343003493273783399107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8171581342648730089064285 3064343003493273783399107)
                ·
                  refine ⟨4596514505239910675098661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3064343003493273783399107 4596514505239910675098661)
                  ·
                    refine ⟨861846469732483251580999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4596514505239910675098661 861846469732483251580999)
                    ·
                      rfl

theorem cell22_2517660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_2517660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2517660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2517660 prefixEnd_2517660 := by exact prefixLift 2517660
  have htrace : WordTrace (prefixWord ++ tailWord_2517660) baseStart_2517660 baseEnd_2517660 := by
    simpa [prefixWord, tailWord_2517660, baseEnd_2517660] using wordTrace_append hprefix tailTrace_2517660
  have hstable : (prefixWord ++ tailWord_2517660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2517660).length < 2 ^ (prefixWord ++ tailWord_2517660).sum := by decide
  have hdescent : baseEnd_2517660 < baseStart_2517660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2517660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2517793 : List Nat := [1, 2, 3, 2, 1, 2, 2, 3, 6]
def baseStart_2517793 : Nat := 118140960795 + 2517793 * 2 ^ 59
def prefixEnd_2517793 : Nat := 4983230072969 + 3 ^ 40 * 2517793 * 2
def baseEnd_2517793 : Nat := 287297332783505079335197

theorem tailTrace_2517793 : CollatzResearch.WordTrace tailWord_2517793 prefixEnd_2517793 287297332783505079335197 := by
  unfold tailWord_2517793
  simp only [CollatzResearch.WordTrace]
  refine ⟨91831454967473440655078033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61220969978315627103385355 91831454967473440655078033)
  ·
    refine ⟨68873591225605080491308525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91831454967473440655078033 68873591225605080491308525)
    ·
      refine ⟨25827596709601905184240697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68873591225605080491308525 25827596709601905184240697)
      ·
        refine ⟨19370697532201428888180523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25827596709601905184240697 19370697532201428888180523)
        ·
          refine ⟨29056046298302143332270785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19370697532201428888180523 29056046298302143332270785)
          ·
            refine ⟨21792034723726607499203089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29056046298302143332270785 21792034723726607499203089)
            ·
              refine ⟨16344026042794955624402317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21792034723726607499203089 16344026042794955624402317)
              ·
                refine ⟨6129009766048108359150869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16344026042794955624402317 6129009766048108359150869)
                ·
                  refine ⟨287297332783505079335197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6129009766048108359150869 287297332783505079335197)
                  ·
                    rfl

theorem cell22_2517793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 3, 6].length) (baseStart_2517793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2517793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2517793 prefixEnd_2517793 := by exact prefixLift 2517793
  have htrace : WordTrace (prefixWord ++ tailWord_2517793) baseStart_2517793 baseEnd_2517793 := by
    simpa [prefixWord, tailWord_2517793, baseEnd_2517793] using wordTrace_append hprefix tailTrace_2517793
  have hstable : (prefixWord ++ tailWord_2517793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2517793).length < 2 ^ (prefixWord ++ tailWord_2517793).sum := by decide
  have hdescent : baseEnd_2517793 < baseStart_2517793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2517793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2517859 : List Nat := [1, 1, 1, 5, 3, 2, 3, 1, 2, 3]
def baseStart_2517859 : Nat := 118140960795 + 2517859 * 2 ^ 59
def prefixEnd_2517859 : Nat := 4983230072969 + 3 ^ 40 * 2517859 * 2
def baseEnd_2517859 : Nat := 861914591499313065855389

theorem tailTrace_2517859 : CollatzResearch.WordTrace tailWord_2517859 prefixEnd_2517859 861914591499313065855389 := by
  unfold tailWord_2517859
  simp only [CollatzResearch.WordTrace]
  refine ⟨91833862185234333926980631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61222574790156222617987087 91833862185234333926980631)
  ·
    refine ⟨137750793277851500890470947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91833862185234333926980631 137750793277851500890470947)
    ·
      refine ⟨206626189916777251335706421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137750793277851500890470947 206626189916777251335706421)
      ·
        refine ⟨19371205304697867312722477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 206626189916777251335706421 19371205304697867312722477)
        ·
          refine ⟨7264201989261700242270929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19371205304697867312722477 7264201989261700242270929)
          ·
            refine ⟨5448151491946275181703197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7264201989261700242270929 5448151491946275181703197)
            ·
              refine ⟨2043056809479853193138699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5448151491946275181703197 2043056809479853193138699)
              ·
                refine ⟨3064585214219779789708049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2043056809479853193138699 3064585214219779789708049)
                ·
                  refine ⟨2298438910664834842281037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3064585214219779789708049 2298438910664834842281037)
                  ·
                    refine ⟨861914591499313065855389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2298438910664834842281037 861914591499313065855389)
                    ·
                      rfl

theorem cell22_2517859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 3, 1, 2, 3].length) (baseStart_2517859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2517859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2517859 prefixEnd_2517859 := by exact prefixLift 2517859
  have htrace : WordTrace (prefixWord ++ tailWord_2517859) baseStart_2517859 baseEnd_2517859 := by
    simpa [prefixWord, tailWord_2517859, baseEnd_2517859] using wordTrace_append hprefix tailTrace_2517859
  have hstable : (prefixWord ++ tailWord_2517859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2517859).length < 2 ^ (prefixWord ++ tailWord_2517859).sum := by decide
  have hdescent : baseEnd_2517859 < baseStart_2517859 := by decide
  rcases family_descends (prefixWord ++ tailWord_2517859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2517883 : List Nat := [1, 1, 1, 1, 1, 5, 3, 2, 7]
def baseStart_2517883 : Nat := 118140960795 + 2517883 * 2 ^ 59
def prefixEnd_2517883 : Nat := 4983230072969 + 3 ^ 40 * 2517883 * 2
def baseEnd_2517883 : Nat := 287307602396595001085105

theorem tailTrace_2517883 : CollatzResearch.WordTrace tailWord_2517883 prefixEnd_2517883 287307602396595001085105 := by
  unfold tailWord_2517883
  simp only [CollatzResearch.WordTrace]
  refine ⟨91834737537147386025854303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61223158358098257350569535 91834737537147386025854303)
  ·
    refine ⟨137752106305721079038781455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91834737537147386025854303 137752106305721079038781455)
    ·
      refine ⟨206628159458581618558172183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137752106305721079038781455 206628159458581618558172183)
      ·
        refine ⟨309942239187872427837258275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206628159458581618558172183 309942239187872427837258275)
        ·
          refine ⟨464913358781808641755887413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 309942239187872427837258275 464913358781808641755887413)
          ·
            refine ⟨43585627385794560164614445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 464913358781808641755887413 43585627385794560164614445)
            ·
              refine ⟨16344610269672960061730417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43585627385794560164614445 16344610269672960061730417)
              ·
                refine ⟨12258457702254720046297813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16344610269672960061730417 12258457702254720046297813)
                ·
                  refine ⟨287307602396595001085105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12258457702254720046297813 287307602396595001085105)
                  ·
                    rfl

theorem cell22_2517883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 2, 7].length) (baseStart_2517883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2517883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2517883 prefixEnd_2517883 := by exact prefixLift 2517883
  have htrace : WordTrace (prefixWord ++ tailWord_2517883) baseStart_2517883 baseEnd_2517883 := by
    simpa [prefixWord, tailWord_2517883, baseEnd_2517883] using wordTrace_append hprefix tailTrace_2517883
  have hstable : (prefixWord ++ tailWord_2517883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2517883).length < 2 ^ (prefixWord ++ tailWord_2517883).sum := by decide
  have hdescent : baseEnd_2517883 < baseStart_2517883 := by decide
  rcases family_descends (prefixWord ++ tailWord_2517883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2517910 : List Nat := [5, 3, 1, 1, 1, 3, 2, 1, 2, 3]
def baseStart_2517910 : Nat := 118140960795 + 2517910 * 2 ^ 59
def prefixEnd_2517910 : Nat := 4983230072969 + 3 ^ 40 * 2517910 * 2
def baseEnd_2517910 : Nat := 861932049841565932830233

theorem tailTrace_2517910 : CollatzResearch.WordTrace tailWord_2517910 prefixEnd_2517910 861932049841565932830233 := by
  unfold tailWord_2517910
  simp only [CollatzResearch.WordTrace]
  refine ⟨5739732644253098102317949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61223814872033046424724789 5739732644253098102317949)
  ·
    refine ⟨2152399741594911788369231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5739732644253098102317949 2152399741594911788369231)
    ·
      refine ⟨3228599612392367682553847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2152399741594911788369231 3228599612392367682553847)
      ·
        refine ⟨4842899418588551523830771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3228599612392367682553847 4842899418588551523830771)
        ·
          refine ⟨7264349127882827285746157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4842899418588551523830771 7264349127882827285746157)
          ·
            refine ⟨2724130922956060232154809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7264349127882827285746157 2724130922956060232154809)
            ·
              refine ⟨2043098192217045174116107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2724130922956060232154809 2043098192217045174116107)
              ·
                refine ⟨3064647288325567761174161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2043098192217045174116107 3064647288325567761174161)
                ·
                  refine ⟨2298485466244175820880621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3064647288325567761174161 2298485466244175820880621)
                  ·
                    refine ⟨861932049841565932830233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2298485466244175820880621 861932049841565932830233)
                    ·
                      rfl

theorem cell22_2517910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_2517910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2517910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2517910 prefixEnd_2517910 := by exact prefixLift 2517910
  have htrace : WordTrace (prefixWord ++ tailWord_2517910) baseStart_2517910 baseEnd_2517910 := by
    simpa [prefixWord, tailWord_2517910, baseEnd_2517910] using wordTrace_append hprefix tailTrace_2517910
  have hstable : (prefixWord ++ tailWord_2517910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2517910).length < 2 ^ (prefixWord ++ tailWord_2517910).sum := by decide
  have hdescent : baseEnd_2517910 < baseStart_2517910 := by decide
  rcases family_descends (prefixWord ++ tailWord_2517910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2517913 : List Nat := [1, 2, 1, 2, 1, 3, 1, 1, 2, 8]
def baseStart_2517913 : Nat := 118140960795 + 2517913 * 2 ^ 59
def prefixEnd_2517913 : Nat := 4983230072969 + 3 ^ 40 * 2517913 * 2
def baseEnd_2517913 : Nat := 861933076802874925005223

theorem tailTrace_2517913 : CollatzResearch.WordTrace tailWord_2517913 prefixEnd_2517913 861933076802874925005223 := by
  unfold tailWord_2517913
  simp only [CollatzResearch.WordTrace]
  refine ⟨91835831727038701149446393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61223887818025800766297595 91835831727038701149446393)
  ·
    refine ⟨68876873795279025862084795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91835831727038701149446393 68876873795279025862084795)
    ·
      refine ⟨103315310692918538793127193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68876873795279025862084795 103315310692918538793127193)
      ·
        refine ⟨77486483019688904094845395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103315310692918538793127193 77486483019688904094845395)
        ·
          refine ⟨116229724529533356142268093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77486483019688904094845395 116229724529533356142268093)
          ·
            refine ⟨43586146698575008553350535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116229724529533356142268093 43586146698575008553350535)
            ·
              refine ⟨65379220047862512830025803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43586146698575008553350535 65379220047862512830025803)
              ·
                refine ⟨98068830071793769245038705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65379220047862512830025803 98068830071793769245038705)
                ·
                  refine ⟨73551622553845326933779029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98068830071793769245038705 73551622553845326933779029)
                  ·
                    refine ⟨861933076802874925005223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 73551622553845326933779029 861933076802874925005223)
                    ·
                      rfl

theorem cell22_2517913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 8].length) (baseStart_2517913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2517913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2517913 prefixEnd_2517913 := by exact prefixLift 2517913
  have htrace : WordTrace (prefixWord ++ tailWord_2517913) baseStart_2517913 baseEnd_2517913 := by
    simpa [prefixWord, tailWord_2517913, baseEnd_2517913] using wordTrace_append hprefix tailTrace_2517913
  have hstable : (prefixWord ++ tailWord_2517913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2517913).length < 2 ^ (prefixWord ++ tailWord_2517913).sum := by decide
  have hdescent : baseEnd_2517913 < baseStart_2517913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2517913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2517977 : List Nat := [1, 2, 1, 2, 5, 2, 2, 1, 1, 5]
def baseStart_2517977 : Nat := 118140960795 + 2517977 * 2 ^ 59
def prefixEnd_2517977 : Nat := 4983230072969 + 3 ^ 40 * 2517977 * 2
def baseEnd_2517977 : Nat := 861954985310800091405027

theorem tailTrace_2517977 : CollatzResearch.WordTrace tailWord_2517977 prefixEnd_2517977 861954985310800091405027 := by
  unfold tailWord_2517977
  simp only [CollatzResearch.WordTrace]
  refine ⟨91838165998806840079776185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61225443999204560053184123 91838165998806840079776185)
  ·
    refine ⟨68878624499105130059832139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91838165998806840079776185 68878624499105130059832139)
    ·
      refine ⟨103317936748657695089748209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68878624499105130059832139 103317936748657695089748209)
      ·
        refine ⟨77488452561493271317311157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103317936748657695089748209 77488452561493271317311157)
        ·
          refine ⟨7264542427639994185997921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 77488452561493271317311157 7264542427639994185997921)
          ·
            refine ⟨5448406820729995639498441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7264542427639994185997921 5448406820729995639498441)
            ·
              refine ⟨4086305115547496729623831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5448406820729995639498441 4086305115547496729623831)
              ·
                refine ⟨6129457673321245094435747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4086305115547496729623831 6129457673321245094435747)
                ·
                  refine ⟨9194186509981867641653621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6129457673321245094435747 9194186509981867641653621)
                  ·
                    refine ⟨861954985310800091405027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9194186509981867641653621 861954985310800091405027)
                    ·
                      rfl

theorem cell22_2517977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 1, 1, 5].length) (baseStart_2517977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2517977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2517977 prefixEnd_2517977 := by exact prefixLift 2517977
  have htrace : WordTrace (prefixWord ++ tailWord_2517977) baseStart_2517977 baseEnd_2517977 := by
    simpa [prefixWord, tailWord_2517977, baseEnd_2517977] using wordTrace_append hprefix tailTrace_2517977
  have hstable : (prefixWord ++ tailWord_2517977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2517977).length < 2 ^ (prefixWord ++ tailWord_2517977).sum := by decide
  have hdescent : baseEnd_2517977 < baseStart_2517977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2517977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2517992 : List Nat := [2, 1, 4, 1, 1, 1, 5, 1, 2, 4]
def baseStart_2517992 : Nat := 118140960795 + 2517992 * 2 ^ 59
def prefixEnd_2517992 : Nat := 4983230072969 + 3 ^ 40 * 2517992 * 2
def baseEnd_2517992 : Nat := 861960120117345052279981

theorem tailTrace_2517992 : CollatzResearch.WordTrace tailWord_2517992 prefixEnd_2517992 861960120117345052279981 := by
  unfold tailWord_2517992
  simp only [CollatzResearch.WordTrace]
  refine ⟨45919356546876248820786115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61225808729168331761048153 45919356546876248820786115)
  ·
    refine ⟨68879034820314373231179173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45919356546876248820786115 68879034820314373231179173)
    ·
      refine ⟨12914819028808944980846095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68879034820314373231179173 12914819028808944980846095)
      ·
        refine ⟨19372228543213417471269143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12914819028808944980846095 19372228543213417471269143)
        ·
          refine ⟨29058342814820126206903715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19372228543213417471269143 29058342814820126206903715)
          ·
            refine ⟨43587514222230189310355573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29058342814820126206903715 43587514222230189310355573)
            ·
              refine ⟨4086329458334080247845835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43587514222230189310355573 4086329458334080247845835)
              ·
                refine ⟨6129494187501120371768753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4086329458334080247845835 6129494187501120371768753)
                ·
                  refine ⟨4597120640625840278826565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6129494187501120371768753 4597120640625840278826565)
                  ·
                    refine ⟨861960120117345052279981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4597120640625840278826565 861960120117345052279981)
                    ·
                      rfl

theorem cell22_2517992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_2517992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2517992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2517992 prefixEnd_2517992 := by exact prefixLift 2517992
  have htrace : WordTrace (prefixWord ++ tailWord_2517992) baseStart_2517992 baseEnd_2517992 := by
    simpa [prefixWord, tailWord_2517992, baseEnd_2517992] using wordTrace_append hprefix tailTrace_2517992
  have hstable : (prefixWord ++ tailWord_2517992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2517992).length < 2 ^ (prefixWord ++ tailWord_2517992).sum := by decide
  have hdescent : baseEnd_2517992 < baseStart_2517992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2517992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2517998 : List Nat := [4, 1, 2, 1, 5, 1, 2, 1, 1, 4]
def baseStart_2517998 : Nat := 118140960795 + 2517998 * 2 ^ 59
def prefixEnd_2517998 : Nat := 4983230072969 + 3 ^ 40 * 2517998 * 2
def baseEnd_2517998 : Nat := 861962174039963036629963

theorem tailTrace_2517998 : CollatzResearch.WordTrace tailWord_2517998 prefixEnd_2517998 861962174039963036629963 := by
  unfold tailWord_2517998
  simp only [CollatzResearch.WordTrace]
  refine ⟨11479866491466345083286331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61225954621153840444193765 11479866491466345083286331)
  ·
    refine ⟨17219799737199517624929497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11479866491466345083286331 17219799737199517624929497)
    ·
      refine ⟨12914849802899638218697123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17219799737199517624929497 12914849802899638218697123)
      ·
        refine ⟨19372274704349457328045685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12914849802899638218697123 19372274704349457328045685)
        ·
          refine ⟨1816150753532761624504283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19372274704349457328045685 1816150753532761624504283)
          ·
            refine ⟨2724226130299142436756425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1816150753532761624504283 2724226130299142436756425)
            ·
              refine ⟨2043169597724356827567319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2724226130299142436756425 2043169597724356827567319)
              ·
                refine ⟨3064754396586535241350979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2043169597724356827567319 3064754396586535241350979)
                ·
                  refine ⟨4597131594879802862026469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3064754396586535241350979 4597131594879802862026469)
                  ·
                    refine ⟨861962174039963036629963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4597131594879802862026469 861962174039963036629963)
                    ·
                      rfl

theorem cell22_2517998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 2, 1, 1, 4].length) (baseStart_2517998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2517998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2517998 prefixEnd_2517998 := by exact prefixLift 2517998
  have htrace : WordTrace (prefixWord ++ tailWord_2517998) baseStart_2517998 baseEnd_2517998 := by
    simpa [prefixWord, tailWord_2517998, baseEnd_2517998] using wordTrace_append hprefix tailTrace_2517998
  have hstable : (prefixWord ++ tailWord_2517998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2517998).length < 2 ^ (prefixWord ++ tailWord_2517998).sum := by decide
  have hdescent : baseEnd_2517998 < baseStart_2517998 := by decide
  rcases family_descends (prefixWord ++ tailWord_2517998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518039 : List Nat := [1, 1, 3, 5, 1, 1, 2, 2, 3, 3]
def baseStart_2518039 : Nat := 118140960795 + 2518039 * 2 ^ 59
def prefixEnd_2518039 : Nat := 4983230072969 + 3 ^ 40 * 2518039 * 2
def baseEnd_2518039 : Nat := 861976209177852596354837

theorem tailTrace_2518039 : CollatzResearch.WordTrace tailWord_2518039 prefixEnd_2518039 861976209177852596354837 := by
  unfold tailWord_2518039
  simp only [CollatzResearch.WordTrace]
  refine ⟨91840427324582224668533171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61226951549721483112355447 91840427324582224668533171)
  ·
    refine ⟨137760640986873337002799757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91840427324582224668533171 137760640986873337002799757)
    ·
      refine ⟨51660240370077501376049909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137760640986873337002799757 51660240370077501376049909)
      ·
        refine ⟨4843147534694765754004679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 51660240370077501376049909 4843147534694765754004679)
        ·
          refine ⟨7264721302042148631007019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4843147534694765754004679 7264721302042148631007019)
          ·
            refine ⟨10897081953063222946510529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7264721302042148631007019 10897081953063222946510529)
            ·
              refine ⟨8172811464797417209882897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10897081953063222946510529 8172811464797417209882897)
              ·
                refine ⟨6129608598598062907412173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8172811464797417209882897 6129608598598062907412173)
                ·
                  refine ⟨2298603224474273590279565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6129608598598062907412173 2298603224474273590279565)
                  ·
                    refine ⟨861976209177852596354837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2298603224474273590279565 861976209177852596354837)
                    ·
                      rfl

theorem cell22_2518039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 2, 3, 3].length) (baseStart_2518039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2518039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2518039 prefixEnd_2518039 := by exact prefixLift 2518039
  have htrace : WordTrace (prefixWord ++ tailWord_2518039) baseStart_2518039 baseEnd_2518039 := by
    simpa [prefixWord, tailWord_2518039, baseEnd_2518039] using wordTrace_append hprefix tailTrace_2518039
  have hstable : (prefixWord ++ tailWord_2518039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518039).length < 2 ^ (prefixWord ++ tailWord_2518039).sum := by decide
  have hdescent : baseEnd_2518039 < baseStart_2518039 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518052 : List Nat := [2, 3, 1, 4, 1, 1, 1, 2, 7]
def baseStart_2518052 : Nat := 118140960795 + 2518052 * 2 ^ 59
def prefixEnd_2518052 : Nat := 4983230072969 + 3 ^ 40 * 2518052 * 2
def baseEnd_2518052 : Nat := 287326886447841631926599

theorem tailTrace_2518052 : CollatzResearch.WordTrace tailWord_2518052 prefixEnd_2518052 287326886447841631926599 := by
  unfold tailWord_2518052
  simp only [CollatzResearch.WordTrace]
  refine ⟨45920450736767563944378205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61227267649023418592504273 45920450736767563944378205)
  ·
    refine ⟨17220169026287836479141827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45920450736767563944378205 17220169026287836479141827)
    ·
      refine ⟨25830253539431754718712741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17220169026287836479141827 25830253539431754718712741)
      ·
        refine ⟨4843172538643454009758639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25830253539431754718712741 4843172538643454009758639)
        ·
          refine ⟨7264758807965181014637959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4843172538643454009758639 7264758807965181014637959)
          ·
            refine ⟨10897138211947771521956939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7264758807965181014637959 10897138211947771521956939)
            ·
              refine ⟨16345707317921657282935409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10897138211947771521956939 16345707317921657282935409)
              ·
                refine ⟨12259280488441242962201557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16345707317921657282935409 12259280488441242962201557)
                ·
                  refine ⟨287326886447841631926599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12259280488441242962201557 287326886447841631926599)
                  ·
                    rfl

theorem cell22_2518052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 2, 7].length) (baseStart_2518052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2518052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2518052 prefixEnd_2518052 := by exact prefixLift 2518052
  have htrace : WordTrace (prefixWord ++ tailWord_2518052) baseStart_2518052 baseEnd_2518052 := by
    simpa [prefixWord, tailWord_2518052, baseEnd_2518052] using wordTrace_append hprefix tailTrace_2518052
  have hstable : (prefixWord ++ tailWord_2518052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518052).length < 2 ^ (prefixWord ++ tailWord_2518052).sum := by decide
  have hdescent : baseEnd_2518052 < baseStart_2518052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518073 : List Nat := [1, 2, 1, 5, 2, 2, 3, 2, 1, 3]
def baseStart_2518073 : Nat := 118140960795 + 2518073 * 2 ^ 59
def prefixEnd_2518073 : Nat := 4983230072969 + 3 ^ 40 * 2518073 * 2
def baseEnd_2518073 : Nat := 861987848072687841004733

theorem tailTrace_2518073 : CollatzResearch.WordTrace tailWord_2518073 prefixEnd_2518073 861987848072687841004733 := by
  unfold tailWord_2518073
  simp only [CollatzResearch.WordTrace]
  refine ⟨91841667406459048475270873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61227778270972698983513915 91841667406459048475270873)
  ·
    refine ⟨68881250554844286356453155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91841667406459048475270873 68881250554844286356453155)
    ·
      refine ⟨103321875832266429534679733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68881250554844286356453155 103321875832266429534679733)
      ·
        refine ⟨9686425859274977768876225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 103321875832266429534679733 9686425859274977768876225)
        ·
          refine ⟨7264819394456233326657169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9686425859274977768876225 7264819394456233326657169)
          ·
            refine ⟨5448614545842174994992877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7264819394456233326657169 5448614545842174994992877)
            ·
              refine ⟨2043230454690815623122329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5448614545842174994992877 2043230454690815623122329)
              ·
                refine ⟨1532422841018111717341747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2043230454690815623122329 1532422841018111717341747)
                ·
                  refine ⟨2298634261527167576012621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1532422841018111717341747 2298634261527167576012621)
                  ·
                    refine ⟨861987848072687841004733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2298634261527167576012621 861987848072687841004733)
                    ·
                      rfl

theorem cell22_2518073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 3, 2, 1, 3].length) (baseStart_2518073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2518073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2518073 prefixEnd_2518073 := by exact prefixLift 2518073
  have htrace : WordTrace (prefixWord ++ tailWord_2518073) baseStart_2518073 baseEnd_2518073 := by
    simpa [prefixWord, tailWord_2518073, baseEnd_2518073] using wordTrace_append hprefix tailTrace_2518073
  have hstable : (prefixWord ++ tailWord_2518073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518073).length < 2 ^ (prefixWord ++ tailWord_2518073).sum := by decide
  have hdescent : baseEnd_2518073 < baseStart_2518073 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518086 : List Nat := [6, 1, 1, 1, 1, 3, 1, 3, 5]
def baseStart_2518086 : Nat := 118140960795 + 2518086 * 2 ^ 59
def prefixEnd_2518086 : Nat := 4983230072969 + 3 ^ 40 * 2518086 * 2
def baseEnd_2518086 : Nat := 287330766079453380143231

theorem tailTrace_2518086 : CollatzResearch.WordTrace tailWord_2518086 prefixEnd_2518086 287330766079453380143231 := by
  unfold tailWord_2518086
  simp only [CollatzResearch.WordTrace]
  refine ⟨2870066923606623490484191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 61228094370274634463662741 2870066923606623490484191)
  ·
    refine ⟨4305100385409935235726287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2870066923606623490484191 4305100385409935235726287)
    ·
      refine ⟨6457650578114902853589431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4305100385409935235726287 6457650578114902853589431)
      ·
        refine ⟨9686475867172354280384147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6457650578114902853589431 9686475867172354280384147)
        ·
          refine ⟨14529713800758531420576221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9686475867172354280384147 14529713800758531420576221)
          ·
            refine ⟨5448642675284449282716083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14529713800758531420576221 5448642675284449282716083)
            ·
              refine ⟨8172964012926673924074125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5448642675284449282716083 8172964012926673924074125)
              ·
                refine ⟨3064861504847502721527797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8172964012926673924074125 3064861504847502721527797)
                ·
                  refine ⟨287330766079453380143231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3064861504847502721527797 287330766079453380143231)
                  ·
                    rfl

theorem cell22_2518086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_2518086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2518086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2518086 prefixEnd_2518086 := by exact prefixLift 2518086
  have htrace : WordTrace (prefixWord ++ tailWord_2518086) baseStart_2518086 baseEnd_2518086 := by
    simpa [prefixWord, tailWord_2518086, baseEnd_2518086] using wordTrace_append hprefix tailTrace_2518086
  have hstable : (prefixWord ++ tailWord_2518086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518086).length < 2 ^ (prefixWord ++ tailWord_2518086).sum := by decide
  have hdescent : baseEnd_2518086 < baseStart_2518086 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518112 : List Nat := [2, 1, 1, 3, 2, 2, 3, 2, 1, 5]
def baseStart_2518112 : Nat := 118140960795 + 2518112 * 2 ^ 59
def prefixEnd_2518112 : Nat := 4983230072969 + 3 ^ 40 * 2518112 * 2
def baseEnd_2518112 : Nat := 862001198569704739279613

theorem tailTrace_2518112 : CollatzResearch.WordTrace tailWord_2518112 prefixEnd_2518112 862001198569704739279613 := by
  unfold tailWord_2518112
  simp only [CollatzResearch.WordTrace]
  refine ⟨45921544926658879067970295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61228726568878505423960393 45921544926658879067970295)
  ·
    refine ⟨68882317389988318601955443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45921544926658879067970295 68882317389988318601955443)
    ·
      refine ⟨103323476084982477902933165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68882317389988318601955443 103323476084982477902933165)
      ·
        refine ⟨38746303531868429213599937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103323476084982477902933165 38746303531868429213599937)
        ·
          refine ⟨29059727648901321910199953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38746303531868429213599937 29059727648901321910199953)
          ·
            refine ⟨21794795736675991432649965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29059727648901321910199953 21794795736675991432649965)
            ·
              refine ⟨8173048401253496787243737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21794795736675991432649965 8173048401253496787243737)
              ·
                refine ⟨6129786300940122590432803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8173048401253496787243737 6129786300940122590432803)
                ·
                  refine ⟨9194679451410183885649205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6129786300940122590432803 9194679451410183885649205)
                  ·
                    refine ⟨862001198569704739279613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9194679451410183885649205 862001198569704739279613)
                    ·
                      rfl

theorem cell22_2518112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 2, 1, 5].length) (baseStart_2518112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2518112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2518112 prefixEnd_2518112 := by exact prefixLift 2518112
  have htrace : WordTrace (prefixWord ++ tailWord_2518112) baseStart_2518112 baseEnd_2518112 := by
    simpa [prefixWord, tailWord_2518112, baseEnd_2518112] using wordTrace_append hprefix tailTrace_2518112
  have hstable : (prefixWord ++ tailWord_2518112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518112).length < 2 ^ (prefixWord ++ tailWord_2518112).sum := by decide
  have hdescent : baseEnd_2518112 < baseStart_2518112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518127 : List Nat := [1, 1, 2, 1, 3, 3, 1, 4, 2, 4]
def baseStart_2518127 : Nat := 118140960795 + 2518127 * 2 ^ 59
def prefixEnd_2518127 : Nat := 4983230072969 + 3 ^ 40 * 2518127 * 2
def baseEnd_2518127 : Nat := 862006333376249700154567

theorem tailTrace_2518127 : CollatzResearch.WordTrace tailWord_2518127 prefixEnd_2518127 862006333376249700154567 := by
  unfold tailWord_2518127
  simp only [CollatzResearch.WordTrace]
  refine ⟨91843636948263415697736635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61229091298842277131824423 91843636948263415697736635)
  ·
    refine ⟨137765455422395123546604953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91843636948263415697736635 137765455422395123546604953)
    ·
      refine ⟨103324091566796342659953715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137765455422395123546604953 103324091566796342659953715)
      ·
        refine ⟨154986137350194513989930573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103324091566796342659953715 154986137350194513989930573)
        ·
          refine ⟨58119801506322942746223965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 154986137350194513989930573 58119801506322942746223965)
          ·
            refine ⟨21794925564871103529833987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58119801506322942746223965 21794925564871103529833987)
            ·
              refine ⟨32692388347306655294750981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21794925564871103529833987 32692388347306655294750981)
              ·
                refine ⟨6129822815119997867765809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32692388347306655294750981 6129822815119997867765809)
                ·
                  refine ⟨4597367111339998400824357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6129822815119997867765809 4597367111339998400824357)
                  ·
                    refine ⟨862006333376249700154567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4597367111339998400824357 862006333376249700154567)
                    ·
                      rfl

theorem cell22_2518127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 4, 2, 4].length) (baseStart_2518127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2518127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2518127 prefixEnd_2518127 := by exact prefixLift 2518127
  have htrace : WordTrace (prefixWord ++ tailWord_2518127) baseStart_2518127 baseEnd_2518127 := by
    simpa [prefixWord, tailWord_2518127, baseEnd_2518127] using wordTrace_append hprefix tailTrace_2518127
  have hstable : (prefixWord ++ tailWord_2518127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518127).length < 2 ^ (prefixWord ++ tailWord_2518127).sum := by decide
  have hdescent : baseEnd_2518127 < baseStart_2518127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518191 : List Nat := [1, 1, 2, 1, 2, 3, 4, 4, 1, 3]
def baseStart_2518191 : Nat := 118140960795 + 2518191 * 2 ^ 59
def prefixEnd_2518191 : Nat := 4983230072969 + 3 ^ 40 * 2518191 * 2
def baseEnd_2518191 : Nat := 862028241884174866554371

theorem tailTrace_2518191 : CollatzResearch.WordTrace tailWord_2518191 prefixEnd_2518191 862028241884174866554371 := by
  unfold tailWord_2518191
  simp only [CollatzResearch.WordTrace]
  refine ⟨91845971220031554628066427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61230647480021036418710951 91845971220031554628066427)
  ·
    refine ⟨137768956830047331942099641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91845971220031554628066427 137768956830047331942099641)
    ·
      refine ⟨103326717622535498956574731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137768956830047331942099641 103326717622535498956574731)
      ·
        refine ⟨154990076433803248434862097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103326717622535498956574731 154990076433803248434862097)
        ·
          refine ⟨116242557325352436326146573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154990076433803248434862097 116242557325352436326146573)
          ·
            refine ⟨43590958997007163622304965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116242557325352436326146573 43590958997007163622304965)
            ·
              refine ⟨8173304811938843179182181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43590958997007163622304965 8173304811938843179182181)
              ·
                refine ⟨1532494652238533096096659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8173304811938843179182181 1532494652238533096096659)
                ·
                  refine ⟨2298741978357799644144989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1532494652238533096096659 2298741978357799644144989)
                  ·
                    refine ⟨862028241884174866554371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2298741978357799644144989 862028241884174866554371)
                    ·
                      rfl

theorem cell22_2518191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 4, 1, 3].length) (baseStart_2518191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2518191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2518191 prefixEnd_2518191 := by exact prefixLift 2518191
  have htrace : WordTrace (prefixWord ++ tailWord_2518191) baseStart_2518191 baseEnd_2518191 := by
    simpa [prefixWord, tailWord_2518191, baseEnd_2518191] using wordTrace_append hprefix tailTrace_2518191
  have hstable : (prefixWord ++ tailWord_2518191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518191).length < 2 ^ (prefixWord ++ tailWord_2518191).sum := by decide
  have hdescent : baseEnd_2518191 < baseStart_2518191 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518210 : List Nat := [3, 5, 1, 1, 2, 2, 2, 6]
def baseStart_2518210 : Nat := 118140960795 + 2518210 * 2 ^ 59
def prefixEnd_2518210 : Nat := 4983230072969 + 3 ^ 40 * 2518210 * 2
def baseEnd_2518210 : Nat := 95781638441385016703257

theorem tailTrace_2518210 : CollatzResearch.WordTrace tailWord_2518210 prefixEnd_2518210 95781638441385016703257 := by
  unfold tailWord_2518210
  simp only [CollatzResearch.WordTrace]
  refine ⟨22961666051740680218252021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61231109471308480582005389 22961666051740680218252021)
  ·
    refine ⟨2152656192350688770461127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22961666051740680218252021 2152656192350688770461127)
    ·
      refine ⟨3228984288526033155691691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2152656192350688770461127 3228984288526033155691691)
      ·
        refine ⟨4843476432789049733537537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3228984288526033155691691 4843476432789049733537537)
        ·
          refine ⟨3632607324591787300153153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4843476432789049733537537 3632607324591787300153153)
          ·
            refine ⟨2724455493443840475114865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3632607324591787300153153 2724455493443840475114865)
            ·
              refine ⟨2043341620082880356336149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2724455493443840475114865 2043341620082880356336149)
              ·
                refine ⟨95781638441385016703257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2043341620082880356336149 95781638441385016703257)
                ·
                  rfl

theorem cell22_2518210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 2, 6].length) (baseStart_2518210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2518210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2518210 prefixEnd_2518210 := by exact prefixLift 2518210
  have htrace : WordTrace (prefixWord ++ tailWord_2518210) baseStart_2518210 baseEnd_2518210 := by
    simpa [prefixWord, tailWord_2518210, baseEnd_2518210] using wordTrace_append hprefix tailTrace_2518210
  have hstable : (prefixWord ++ tailWord_2518210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518210).length < 2 ^ (prefixWord ++ tailWord_2518210).sum := by decide
  have hdescent : baseEnd_2518210 < baseStart_2518210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518217 : List Nat := [1, 2, 1, 1, 2, 1, 1, 2, 7, 4]
def baseStart_2518217 : Nat := 118140960795 + 2518217 * 2 ^ 59
def prefixEnd_2518217 : Nat := 4983230072969 + 3 ^ 40 * 2518217 * 2
def baseEnd_2518217 : Nat := 862037142215519465404291

theorem tailTrace_2518217 : CollatzResearch.WordTrace tailWord_2518217 prefixEnd_2518217 862037142215519465404291 := by
  unfold tailWord_2518217
  simp only [CollatzResearch.WordTrace]
  refine ⟨91846919517937361068512905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61231279678624907379008603 91846919517937361068512905)
  ·
    refine ⟨68885189638453020801384679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91846919517937361068512905 68885189638453020801384679)
    ·
      refine ⟨103327784457679531202077019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68885189638453020801384679 103327784457679531202077019)
      ·
        refine ⟨154991676686519296803115529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103327784457679531202077019 154991676686519296803115529)
        ·
          refine ⟨116243757514889472602336647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154991676686519296803115529 116243757514889472602336647)
          ·
            refine ⟨174365636272334208903504971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116243757514889472602336647 174365636272334208903504971)
            ·
              refine ⟨261548454408501313355257457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174365636272334208903504971 261548454408501313355257457)
              ·
                refine ⟨196161340806375985016443093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 261548454408501313355257457 196161340806375985016443093)
                ·
                  refine ⟨4597531425149437148822885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 196161340806375985016443093 4597531425149437148822885)
                  ·
                    refine ⟨862037142215519465404291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4597531425149437148822885 862037142215519465404291)
                    ·
                      rfl

theorem cell22_2518217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 7, 4].length) (baseStart_2518217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2518217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2518217 prefixEnd_2518217 := by exact prefixLift 2518217
  have htrace : WordTrace (prefixWord ++ tailWord_2518217) baseStart_2518217 baseEnd_2518217 := by
    simpa [prefixWord, tailWord_2518217, baseEnd_2518217] using wordTrace_append hprefix tailTrace_2518217
  have hstable : (prefixWord ++ tailWord_2518217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518217).length < 2 ^ (prefixWord ++ tailWord_2518217).sum := by decide
  have hdescent : baseEnd_2518217 < baseStart_2518217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518268 : List Nat := [2, 2, 2, 1, 5, 2, 1, 2, 1, 4]
def baseStart_2518268 : Nat := 118140960795 + 2518268 * 2 ^ 59
def prefixEnd_2518268 : Nat := 4983230072969 + 3 ^ 40 * 2518268 * 2
def baseEnd_2518268 : Nat := 862054600557772332379135

theorem tailTrace_2518268 : CollatzResearch.WordTrace tailWord_2518268 prefixEnd_2518268 862054600557772332379135 := by
  unfold tailWord_2518268
  simp only [CollatzResearch.WordTrace]
  refine ⟨45924389820376298389309729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61232519760501731185746305 45924389820376298389309729)
  ·
    refine ⟨34443292365282223791982297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45924389820376298389309729 34443292365282223791982297)
    ·
      refine ⟨25832469273961667843986723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34443292365282223791982297 25832469273961667843986723)
      ·
        refine ⟨38748703910942501765980085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25832469273961667843986723 38748703910942501765980085)
        ·
          refine ⟨3632690991650859540560633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38748703910942501765980085 3632690991650859540560633)
          ·
            refine ⟨2724518243738144655420475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3632690991650859540560633 2724518243738144655420475)
            ·
              refine ⟨4086777365607216983130713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2724518243738144655420475 4086777365607216983130713)
              ·
                refine ⟨3065083024205412737348035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4086777365607216983130713 3065083024205412737348035)
                ·
                  refine ⟨4597624536308119106022053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3065083024205412737348035 4597624536308119106022053)
                  ·
                    refine ⟨862054600557772332379135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4597624536308119106022053 862054600557772332379135)
                    ·
                      rfl

theorem cell22_2518268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 2, 1, 4].length) (baseStart_2518268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2518268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2518268 prefixEnd_2518268 := by exact prefixLift 2518268
  have htrace : WordTrace (prefixWord ++ tailWord_2518268) baseStart_2518268 baseEnd_2518268 := by
    simpa [prefixWord, tailWord_2518268, baseEnd_2518268] using wordTrace_append hprefix tailTrace_2518268
  have hstable : (prefixWord ++ tailWord_2518268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518268).length < 2 ^ (prefixWord ++ tailWord_2518268).sum := by decide
  have hdescent : baseEnd_2518268 < baseStart_2518268 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518277 : List Nat := [1, 3, 1, 1, 2, 1, 3, 10]
def baseStart_2518277 : Nat := 118140960795 + 2518277 * 2 ^ 59
def prefixEnd_2518277 : Nat := 4983230072969 + 3 ^ 40 * 2518277 * 2
def baseEnd_2518277 : Nat := 95784186826855478767123

theorem tailTrace_2518277 : CollatzResearch.WordTrace tailWord_2518277 prefixEnd_2518277 95784186826855478767123 := by
  unfold tailWord_2518277
  simp only [CollatzResearch.WordTrace]
  refine ⟨91849107897719991315697085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61232738598479994210464723 91849107897719991315697085)
  ·
    refine ⟨34443415461644996743386407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91849107897719991315697085 34443415461644996743386407)
    ·
      refine ⟨51665123192467495115079611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34443415461644996743386407 51665123192467495115079611)
      ·
        refine ⟨77497684788701242672619417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51665123192467495115079611 77497684788701242672619417)
        ·
          refine ⟨58123263591525932004464563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77497684788701242672619417 58123263591525932004464563)
          ·
            refine ⟨87184895387288898006696845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58123263591525932004464563 87184895387288898006696845)
            ·
              refine ⟨32694335770233336752511317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87184895387288898006696845 32694335770233336752511317)
              ·
                refine ⟨95784186826855478767123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 32694335770233336752511317 95784186826855478767123)
                ·
                  rfl

theorem cell22_2518277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 10].length) (baseStart_2518277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2518277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2518277 prefixEnd_2518277 := by exact prefixLift 2518277
  have htrace : WordTrace (prefixWord ++ tailWord_2518277) baseStart_2518277 baseEnd_2518277 := by
    simpa [prefixWord, tailWord_2518277, baseEnd_2518277] using wordTrace_append hprefix tailTrace_2518277
  have hstable : (prefixWord ++ tailWord_2518277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518277).length < 2 ^ (prefixWord ++ tailWord_2518277).sum := by decide
  have hdescent : baseEnd_2518277 < baseStart_2518277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518298 : List Nat := [3, 1, 1, 3, 3, 2, 2, 2, 2, 3]
def baseStart_2518298 : Nat := 118140960795 + 2518298 * 2 ^ 59
def prefixEnd_2518298 : Nat := 4983230072969 + 3 ^ 40 * 2518298 * 2
def baseEnd_2518298 : Nat := 862064870170862254129043

theorem tailTrace_2518298 : CollatzResearch.WordTrace tailWord_2518298 prefixEnd_2518298 862064870170862254129043 := by
  unfold tailWord_2518298
  simp only [CollatzResearch.WordTrace]
  refine ⟨22962468457660977975552887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61233249220429274601474365 22962468457660977975552887)
  ·
    refine ⟨34443702686491466963329331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22962468457660977975552887 34443702686491466963329331)
    ·
      refine ⟨51665554029737200444993997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34443702686491466963329331 51665554029737200444993997)
      ·
        refine ⟨19374582761151450166872749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51665554029737200444993997 19374582761151450166872749)
        ·
          refine ⟨7265468535431793812577281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19374582761151450166872749 7265468535431793812577281)
          ·
            refine ⟨5449101401573845359432961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7265468535431793812577281 5449101401573845359432961)
            ·
              refine ⟨4086826051180384019574721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5449101401573845359432961 4086826051180384019574721)
              ·
                refine ⟨3065119538385288014681041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4086826051180384019574721 3065119538385288014681041)
                ·
                  refine ⟨2298839653788966011010781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3065119538385288014681041 2298839653788966011010781)
                  ·
                    refine ⟨862064870170862254129043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2298839653788966011010781 862064870170862254129043)
                    ·
                      rfl

theorem cell22_2518298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 2, 2, 3].length) (baseStart_2518298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2518298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2518298 prefixEnd_2518298 := by exact prefixLift 2518298
  have htrace : WordTrace (prefixWord ++ tailWord_2518298) baseStart_2518298 baseEnd_2518298 := by
    simpa [prefixWord, tailWord_2518298, baseEnd_2518298] using wordTrace_append hprefix tailTrace_2518298
  have hstable : (prefixWord ++ tailWord_2518298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518298).length < 2 ^ (prefixWord ++ tailWord_2518298).sum := by decide
  have hdescent : baseEnd_2518298 < baseStart_2518298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518343 : List Nat := [1, 1, 4, 1, 2, 3, 1, 5, 1, 3]
def baseStart_2518343 : Nat := 118140960795 + 2518343 * 2 ^ 59
def prefixEnd_2518343 : Nat := 4983230072969 + 3 ^ 40 * 2518343 * 2
def baseEnd_2518343 : Nat := 862080274590497136753905

theorem tailTrace_2518343 : CollatzResearch.WordTrace tailWord_2518343 prefixEnd_2518343 862080274590497136753905 := by
  unfold tailWord_2518343
  simp only [CollatzResearch.WordTrace]
  refine ⟨91851515115480884587599683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61234343410320589725066455 91851515115480884587599683)
  ·
    refine ⟨137777272673221326881399525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91851515115480884587599683 137777272673221326881399525)
    ·
      refine ⟨25833238626228998790262411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 137777272673221326881399525 25833238626228998790262411)
      ·
        refine ⟨38749857939343498185393617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25833238626228998790262411 38749857939343498185393617)
        ·
          refine ⟨29062393454507623639045213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38749857939343498185393617 29062393454507623639045213)
          ·
            refine ⟨10898397545440358864641955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29062393454507623639045213 10898397545440358864641955)
            ·
              refine ⟨16347596318160538296962933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10898397545440358864641955 16347596318160538296962933)
              ·
                refine ⟨1532587154827550465340275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16347596318160538296962933 1532587154827550465340275)
                ·
                  refine ⟨2298880732241325698010413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1532587154827550465340275 2298880732241325698010413)
                  ·
                    refine ⟨862080274590497136753905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2298880732241325698010413 862080274590497136753905)
                    ·
                      rfl

theorem cell22_2518343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 5, 1, 3].length) (baseStart_2518343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2518343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2518343 prefixEnd_2518343 := by exact prefixLift 2518343
  have htrace : WordTrace (prefixWord ++ tailWord_2518343) baseStart_2518343 baseEnd_2518343 := by
    simpa [prefixWord, tailWord_2518343, baseEnd_2518343] using wordTrace_append hprefix tailTrace_2518343
  have hstable : (prefixWord ++ tailWord_2518343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518343).length < 2 ^ (prefixWord ++ tailWord_2518343).sum := by decide
  have hdescent : baseEnd_2518343 < baseStart_2518343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518349 : List Nat := [1, 6, 1, 3, 2, 1, 1, 2, 2, 3]
def baseStart_2518349 : Nat := 118140960795 + 2518349 * 2 ^ 59
def prefixEnd_2518349 : Nat := 4983230072969 + 3 ^ 40 * 2518349 * 2
def baseEnd_2518349 : Nat := 862082328513115121103887

theorem tailTrace_2518349 : CollatzResearch.WordTrace tailWord_2518349 prefixEnd_2518349 862082328513115121103887 := by
  unfold tailWord_2518349
  simp only [CollatzResearch.WordTrace]
  refine ⟨91851733953459147612318101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61234489302306098408212067 91851733953459147612318101)
  ·
    refine ⟨4305550029068397544327411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 91851733953459147612318101 4305550029068397544327411)
    ·
      refine ⟨6458325043602596316491117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4305550029068397544327411 6458325043602596316491117)
      ·
        refine ⟨2421871891350973618684169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6458325043602596316491117 2421871891350973618684169)
        ·
          refine ⟨1816403918513230214013127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2421871891350973618684169 1816403918513230214013127)
          ·
            refine ⟨2724605877769845321019691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1816403918513230214013127 2724605877769845321019691)
            ·
              refine ⟨4086908816654767981529537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2724605877769845321019691 4086908816654767981529537)
              ·
                refine ⟨3065181612491075986147153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4086908816654767981529537 3065181612491075986147153)
                ·
                  refine ⟨2298886209368306989610365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3065181612491075986147153 2298886209368306989610365)
                  ·
                    refine ⟨862082328513115121103887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2298886209368306989610365 862082328513115121103887)
                    ·
                      rfl

theorem cell22_2518349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_2518349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2518349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2518349 prefixEnd_2518349 := by exact prefixLift 2518349
  have htrace : WordTrace (prefixWord ++ tailWord_2518349) baseStart_2518349 baseEnd_2518349 := by
    simpa [prefixWord, tailWord_2518349, baseEnd_2518349] using wordTrace_append hprefix tailTrace_2518349
  have hstable : (prefixWord ++ tailWord_2518349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518349).length < 2 ^ (prefixWord ++ tailWord_2518349).sum := by decide
  have hdescent : baseEnd_2518349 < baseStart_2518349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518369 : List Nat := [1, 2, 3, 1, 1, 1, 1, 3, 5, 4]
def baseStart_2518369 : Nat := 118140960795 + 2518369 * 2 ^ 59
def prefixEnd_2518369 : Nat := 4983230072969 + 3 ^ 40 * 2518369 * 2
def baseEnd_2518369 : Nat := 862089174921841735603825

theorem tailTrace_2518369 : CollatzResearch.WordTrace tailWord_2518369 prefixEnd_2518369 862089174921841735603825 := by
  unfold tailWord_2518369
  simp only [CollatzResearch.WordTrace]
  refine ⟨91852463413386691028046161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61234975608924460685364107 91852463413386691028046161)
  ·
    refine ⟨68889347560040018271034621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91852463413386691028046161 68889347560040018271034621)
    ·
      refine ⟨25833505335015006851637983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68889347560040018271034621 25833505335015006851637983)
      ·
        refine ⟨38750258002522510277456975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25833505335015006851637983 38750258002522510277456975)
        ·
          refine ⟨58125387003783765416185463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38750258002522510277456975 58125387003783765416185463)
          ·
            refine ⟨87188080505675648124278195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58125387003783765416185463 87188080505675648124278195)
            ·
              refine ⟨130782120758513472186417293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87188080505675648124278195 130782120758513472186417293)
              ·
                refine ⟨49043295284442552069906485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 130782120758513472186417293 49043295284442552069906485)
                ·
                  refine ⟨4597808932916489256553733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49043295284442552069906485 4597808932916489256553733)
                  ·
                    refine ⟨862089174921841735603825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4597808932916489256553733 862089174921841735603825)
                    ·
                      rfl

theorem cell22_2518369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 5, 4].length) (baseStart_2518369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2518369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2518369 prefixEnd_2518369 := by exact prefixLift 2518369
  have htrace : WordTrace (prefixWord ++ tailWord_2518369) baseStart_2518369 baseEnd_2518369 := by
    simpa [prefixWord, tailWord_2518369, baseEnd_2518369] using wordTrace_append hprefix tailTrace_2518369
  have hstable : (prefixWord ++ tailWord_2518369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518369).length < 2 ^ (prefixWord ++ tailWord_2518369).sum := by decide
  have hdescent : baseEnd_2518369 < baseStart_2518369 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518384 : List Nat := [2, 1, 1, 1, 4, 2, 1, 4, 6]
def baseStart_2518384 : Nat := 118140960795 + 2518384 * 2 ^ 59
def prefixEnd_2518384 : Nat := 4983230072969 + 3 ^ 40 * 2518384 * 2
def baseEnd_2518384 : Nat := 287364769909462232159593

theorem tailTrace_2518384 : CollatzResearch.WordTrace tailWord_2518384 prefixEnd_2518384 287364769909462232159593 := by
  unfold tailWord_2518384
  simp only [CollatzResearch.WordTrace]
  refine ⟨45926505254166174294921103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61235340338888232393228137 45926505254166174294921103)
  ·
    refine ⟨68889757881249261442381655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45926505254166174294921103 68889757881249261442381655)
    ·
      refine ⟨103334636821873892163572483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68889757881249261442381655 103334636821873892163572483)
      ·
        refine ⟨155001955232810838245358725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103334636821873892163572483 155001955232810838245358725)
        ·
          refine ⟨29062866606152032171004761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 155001955232810838245358725 29062866606152032171004761)
          ·
            refine ⟨21797149954614024128253571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29062866606152032171004761 21797149954614024128253571)
            ·
              refine ⟨32695724931921036192380357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21797149954614024128253571 32695724931921036192380357)
              ·
                refine ⟨6130448424735194286071317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32695724931921036192380357 6130448424735194286071317)
                ·
                  refine ⟨287364769909462232159593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6130448424735194286071317 287364769909462232159593)
                  ·
                    rfl

theorem cell22_2518384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 4, 6].length) (baseStart_2518384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2518384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2518384 prefixEnd_2518384 := by exact prefixLift 2518384
  have htrace : WordTrace (prefixWord ++ tailWord_2518384) baseStart_2518384 baseEnd_2518384 := by
    simpa [prefixWord, tailWord_2518384, baseEnd_2518384] using wordTrace_append hprefix tailTrace_2518384
  have hstable : (prefixWord ++ tailWord_2518384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518384).length < 2 ^ (prefixWord ++ tailWord_2518384).sum := by decide
  have hdescent : baseEnd_2518384 < baseStart_2518384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518444 : List Nat := [2, 2, 1, 1, 1, 1, 4, 1, 2, 7]
def baseStart_2518444 : Nat := 118140960795 + 2518444 * 2 ^ 59
def prefixEnd_2518444 : Nat := 4983230072969 + 3 ^ 40 * 2518444 * 2
def baseEnd_2518444 : Nat := 862114848954566539978595

theorem tailTrace_2518444 : CollatzResearch.WordTrace tailWord_2518444 prefixEnd_2518444 862114848954566539978595 := by
  unfold tailWord_2518444
  simp only [CollatzResearch.WordTrace]
  refine ⟨45927599444057489418513193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61236799258743319224684257 45927599444057489418513193)
  ·
    refine ⟨34445699583043117063884895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45927599444057489418513193 34445699583043117063884895)
    ·
      refine ⟨51668549374564675595827343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34445699583043117063884895 51668549374564675595827343)
      ·
        refine ⟨77502824061847013393741015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51668549374564675595827343 77502824061847013393741015)
        ·
          refine ⟨116254236092770520090611523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77502824061847013393741015 116254236092770520090611523)
          ·
            refine ⟨174381354139155780135917285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116254236092770520090611523 174381354139155780135917285)
            ·
              refine ⟨32696503901091708775484491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 174381354139155780135917285 32696503901091708775484491)
              ·
                refine ⟨49044755851637563163226737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32696503901091708775484491 49044755851637563163226737)
                ·
                  refine ⟨36783566888728172372420053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49044755851637563163226737 36783566888728172372420053)
                  ·
                    refine ⟨862114848954566539978595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36783566888728172372420053 862114848954566539978595)
                    ·
                      rfl

theorem cell22_2518444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 7].length) (baseStart_2518444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2518444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2518444 prefixEnd_2518444 := by exact prefixLift 2518444
  have htrace : WordTrace (prefixWord ++ tailWord_2518444) baseStart_2518444 baseEnd_2518444 := by
    simpa [prefixWord, tailWord_2518444, baseEnd_2518444] using wordTrace_append hprefix tailTrace_2518444
  have hstable : (prefixWord ++ tailWord_2518444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518444).length < 2 ^ (prefixWord ++ tailWord_2518444).sum := by decide
  have hdescent : baseEnd_2518444 < baseStart_2518444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518476 : List Nat := [2, 2, 1, 4, 2, 1, 1, 1, 2, 6]
def baseStart_2518476 : Nat := 118140960795 + 2518476 * 2 ^ 59
def prefixEnd_2518476 : Nat := 4983230072969 + 3 ^ 40 * 2518476 * 2
def baseEnd_2518476 : Nat := 862125803208529123178497

theorem tailTrace_2518476 : CollatzResearch.WordTrace tailWord_2518476 prefixEnd_2518476 862125803208529123178497 := by
  unfold tailWord_2518476
  simp only [CollatzResearch.WordTrace]
  refine ⟨45928183011999524151095641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61237577349332698868127521 45928183011999524151095641)
  ·
    refine ⟨34446137258999643113321731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45928183011999524151095641 34446137258999643113321731)
    ·
      refine ⟨51669205888499464669982597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34446137258999643113321731 51669205888499464669982597)
      ·
        refine ⟨9687976104093649625621737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51669205888499464669982597 9687976104093649625621737)
        ·
          refine ⟨7265982078070237219216303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9687976104093649625621737 7265982078070237219216303)
          ·
            refine ⟨10898973117105355828824455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7265982078070237219216303 10898973117105355828824455)
            ·
              refine ⟨16348459675658033743236683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10898973117105355828824455 16348459675658033743236683)
              ·
                refine ⟨24522689513487050614855025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16348459675658033743236683 24522689513487050614855025)
                ·
                  refine ⟨18392017135115287961141269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24522689513487050614855025 18392017135115287961141269)
                  ·
                    refine ⟨862125803208529123178497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18392017135115287961141269 862125803208529123178497)
                    ·
                      rfl

theorem cell22_2518476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 2, 6].length) (baseStart_2518476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2518476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2518476 prefixEnd_2518476 := by exact prefixLift 2518476
  have htrace : WordTrace (prefixWord ++ tailWord_2518476) baseStart_2518476 baseEnd_2518476 := by
    simpa [prefixWord, tailWord_2518476, baseEnd_2518476] using wordTrace_append hprefix tailTrace_2518476
  have hstable : (prefixWord ++ tailWord_2518476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518476).length < 2 ^ (prefixWord ++ tailWord_2518476).sum := by decide
  have hdescent : baseEnd_2518476 < baseStart_2518476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518536 : List Nat := [2, 1, 3, 2, 1, 1, 3, 3, 6]
def baseStart_2518536 : Nat := 118140960795 + 2518536 * 2 ^ 59
def prefixEnd_2518536 : Nat := 4983230072969 + 3 ^ 40 * 2518536 * 2
def baseEnd_2518536 : Nat := 287382114144902988892771

theorem tailTrace_2518536 : CollatzResearch.WordTrace tailWord_2518536 prefixEnd_2518536 287382114144902988892771 := by
  unfold tailWord_2518536
  simp only [CollatzResearch.WordTrace]
  refine ⟨45929277201890839274687731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61239036269187785699583641 45929277201890839274687731)
  ·
    refine ⟨68893915802836258912031597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45929277201890839274687731 68893915802836258912031597)
    ·
      refine ⟨25835218426063597092011849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68893915802836258912031597 25835218426063597092011849)
      ·
        refine ⟨19376413819547697819008887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25835218426063597092011849 19376413819547697819008887)
        ·
          refine ⟨29064620729321546728513331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19376413819547697819008887 29064620729321546728513331)
          ·
            refine ⟨43596931093982320092769997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29064620729321546728513331 43596931093982320092769997)
            ·
              refine ⟨16348849160243370034788749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43596931093982320092769997 16348849160243370034788749)
              ·
                refine ⟨6130818435091263763045781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16348849160243370034788749 6130818435091263763045781)
                ·
                  refine ⟨287382114144902988892771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6130818435091263763045781 287382114144902988892771)
                  ·
                    rfl

theorem cell22_2518536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 3, 6].length) (baseStart_2518536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2518536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2518536 prefixEnd_2518536 := by exact prefixLift 2518536
  have htrace : WordTrace (prefixWord ++ tailWord_2518536) baseStart_2518536 baseEnd_2518536 := by
    simpa [prefixWord, tailWord_2518536, baseEnd_2518536] using wordTrace_append hprefix tailTrace_2518536
  have hstable : (prefixWord ++ tailWord_2518536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518536).length < 2 ^ (prefixWord ++ tailWord_2518536).sum := by decide
  have hdescent : baseEnd_2518536 < baseStart_2518536 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518581 : List Nat := [1, 3, 3, 1, 1, 3, 10]
def baseStart_2518581 : Nat := 118140960795 + 2518581 * 2 ^ 59
def prefixEnd_2518581 : Nat := 4983230072969 + 3 ^ 40 * 2518581 * 2
def baseEnd_2518581 : Nat := 31931916550160883307525

theorem tailTrace_2518581 : CollatzResearch.WordTrace tailWord_2518581 prefixEnd_2518581 31931916550160883307525 := by
  unfold tailWord_2518581
  simp only [CollatzResearch.WordTrace]
  refine ⟨91860195688618651234763597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61240130459079100823175731 91860195688618651234763597)
  ·
    refine ⟨34447573383231994213036349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91860195688618651234763597 34447573383231994213036349)
    ·
      refine ⟨12917840018711997829888631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34447573383231994213036349 12917840018711997829888631)
      ·
        refine ⟨19376760028067996744832947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12917840018711997829888631 19376760028067996744832947)
        ·
          refine ⟨29065140042101995117249421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19376760028067996744832947 29065140042101995117249421)
          ·
            refine ⟨10899427515788248168968533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29065140042101995117249421 10899427515788248168968533)
            ·
              refine ⟨31931916550160883307525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10899427515788248168968533 31931916550160883307525)
              ·
                rfl

theorem cell22_2518581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 10].length) (baseStart_2518581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2518581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2518581 prefixEnd_2518581 := by exact prefixLift 2518581
  have htrace : WordTrace (prefixWord ++ tailWord_2518581) baseStart_2518581 baseEnd_2518581 := by
    simpa [prefixWord, tailWord_2518581, baseEnd_2518581] using wordTrace_append hprefix tailTrace_2518581
  have hstable : (prefixWord ++ tailWord_2518581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518581).length < 2 ^ (prefixWord ++ tailWord_2518581).sum := by decide
  have hdescent : baseEnd_2518581 < baseStart_2518581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518583 : List Nat := [1, 1, 3, 1, 2, 5, 1, 2, 2, 4]
def baseStart_2518583 : Nat := 118140960795 + 2518583 * 2 ^ 59
def prefixEnd_2518583 : Nat := 4983230072969 + 3 ^ 40 * 2518583 * 2
def baseEnd_2518583 : Nat := 862162431495216510753169

theorem tailTrace_2518583 : CollatzResearch.WordTrace tailWord_2518583 prefixEnd_2518583 862162431495216510753169 := by
  unfold tailWord_2518583
  simp only [CollatzResearch.WordTrace]
  refine ⟨91860268634611405576336403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61240179089740937050890935 91860268634611405576336403)
  ·
    refine ⟨137790402951917108364504605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91860268634611405576336403 137790402951917108364504605)
    ·
      refine ⟨51671401106968915636689227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137790402951917108364504605 51671401106968915636689227)
      ·
        refine ⟨77507101660453373455033841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51671401106968915636689227 77507101660453373455033841)
        ·
          refine ⟨58130326245340030091275381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77507101660453373455033841 58130326245340030091275381)
          ·
            refine ⟨5449718085500627821057067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58130326245340030091275381 5449718085500627821057067)
            ·
              refine ⟨8174577128250941731585601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5449718085500627821057067 8174577128250941731585601)
              ·
                refine ⟨6130932846188206298689201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8174577128250941731585601 6130932846188206298689201)
                ·
                  refine ⟨4598199634641154724016901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6130932846188206298689201 4598199634641154724016901)
                  ·
                    refine ⟨862162431495216510753169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4598199634641154724016901 862162431495216510753169)
                    ·
                      rfl

theorem cell22_2518583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 2, 2, 4].length) (baseStart_2518583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2518583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2518583 prefixEnd_2518583 := by exact prefixLift 2518583
  have htrace : WordTrace (prefixWord ++ tailWord_2518583) baseStart_2518583 baseEnd_2518583 := by
    simpa [prefixWord, tailWord_2518583, baseEnd_2518583] using wordTrace_append hprefix tailTrace_2518583
  have hstable : (prefixWord ++ tailWord_2518583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518583).length < 2 ^ (prefixWord ++ tailWord_2518583).sum := by decide
  have hdescent : baseEnd_2518583 < baseStart_2518583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518613 : List Nat := [1, 3, 2, 2, 1, 1, 1, 3, 5, 3]
def baseStart_2518613 : Nat := 118140960795 + 2518613 * 2 ^ 59
def prefixEnd_2518613 : Nat := 4983230072969 + 3 ^ 40 * 2518613 * 2
def baseEnd_2518613 : Nat := 862172701108306432503077

theorem tailTrace_2518613 : CollatzResearch.WordTrace tailWord_2518613 prefixEnd_2518613 862172701108306432503077 := by
  unfold tailWord_2518613
  simp only [CollatzResearch.WordTrace]
  refine ⟨91861362824502720699928493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61240908549668480466618995 91861362824502720699928493)
  ·
    refine ⟨34448011059188520262473185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91861362824502720699928493 34448011059188520262473185)
    ·
      refine ⟨25836008294391390196854889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34448011059188520262473185 25836008294391390196854889)
      ·
        refine ⟨19377006220793542647641167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25836008294391390196854889 19377006220793542647641167)
        ·
          refine ⟨29065509331190313971461751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19377006220793542647641167 29065509331190313971461751)
          ·
            refine ⟨43598263996785470957192627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29065509331190313971461751 43598263996785470957192627)
            ·
              refine ⟨65397395995178206435788941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43598263996785470957192627 65397395995178206435788941)
              ·
                refine ⟨24524023498191827413420853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65397395995178206435788941 24524023498191827413420853)
                ·
                  refine ⟨2299127202955483820008205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24524023498191827413420853 2299127202955483820008205)
                  ·
                    refine ⟨862172701108306432503077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2299127202955483820008205 862172701108306432503077)
                    ·
                      rfl

theorem cell22_2518613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 5, 3].length) (baseStart_2518613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2518613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2518613 prefixEnd_2518613 := by exact prefixLift 2518613
  have htrace : WordTrace (prefixWord ++ tailWord_2518613) baseStart_2518613 baseEnd_2518613 := by
    simpa [prefixWord, tailWord_2518613, baseEnd_2518613] using wordTrace_append hprefix tailTrace_2518613
  have hstable : (prefixWord ++ tailWord_2518613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518613).length < 2 ^ (prefixWord ++ tailWord_2518613).sum := by decide
  have hdescent : baseEnd_2518613 < baseStart_2518613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518641 : List Nat := [1, 2, 2, 2, 1, 1, 1, 2, 3, 7]
def baseStart_2518641 : Nat := 118140960795 + 2518641 * 2 ^ 59
def prefixEnd_2518641 : Nat := 4983230072969 + 3 ^ 40 * 2518641 * 2
def baseEnd_2518641 : Nat := 862182286080523692802991

theorem tailTrace_2518641 : CollatzResearch.WordTrace tailWord_2518641 prefixEnd_2518641 862182286080523692802991 := by
  unfold tailWord_2518641
  simp only [CollatzResearch.WordTrace]
  refine ⟨91862384068401281481947777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61241589378934187654631851 91862384068401281481947777)
  ·
    refine ⟨68896788051300961111460833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91862384068401281481947777 68896788051300961111460833)
    ·
      refine ⟨51672591038475720833595625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68896788051300961111460833 51672591038475720833595625)
      ·
        refine ⟨38754443278856790625196719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51672591038475720833595625 38754443278856790625196719)
        ·
          refine ⟨58131664918285185937795079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38754443278856790625196719 58131664918285185937795079)
          ·
            refine ⟨87197497377427778906692619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58131664918285185937795079 87197497377427778906692619)
            ·
              refine ⟨130796246066141668360038929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87197497377427778906692619 130796246066141668360038929)
              ·
                refine ⟨98097184549606251270029197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 130796246066141668360038929 98097184549606251270029197)
                ·
                  refine ⟨36786444206102344226260949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 98097184549606251270029197 36786444206102344226260949)
                  ·
                    refine ⟨862182286080523692802991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36786444206102344226260949 862182286080523692802991)
                    ·
                      rfl

theorem cell22_2518641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 7].length) (baseStart_2518641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2518641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2518641 prefixEnd_2518641 := by exact prefixLift 2518641
  have htrace : WordTrace (prefixWord ++ tailWord_2518641) baseStart_2518641 baseEnd_2518641 := by
    simpa [prefixWord, tailWord_2518641, baseEnd_2518641] using wordTrace_append hprefix tailTrace_2518641
  have hstable : (prefixWord ++ tailWord_2518641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518641).length < 2 ^ (prefixWord ++ tailWord_2518641).sum := by decide
  have hdescent : baseEnd_2518641 < baseStart_2518641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518793 : List Nat := [1, 2, 1, 1, 3, 2, 1, 2, 4, 5]
def baseStart_2518793 : Nat := 118140960795 + 2518793 * 2 ^ 59
def prefixEnd_2518793 : Nat := 4983230072969 + 3 ^ 40 * 2518793 * 2
def baseEnd_2518793 : Nat := 862234318786845963002525

theorem tailTrace_2518793 : CollatzResearch.WordTrace tailWord_2518793 prefixEnd_2518793 862234318786845963002525 := by
  unfold tailWord_2518793
  simp only [CollatzResearch.WordTrace]
  refine ⟨91867927963850611441481033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61245285309233740960987355 91867927963850611441481033)
  ·
    refine ⟨68900945972887958581110775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91867927963850611441481033 68900945972887958581110775)
    ·
      refine ⟨103351418959331937871666163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68900945972887958581110775 103351418959331937871666163)
      ·
        refine ⟨155027128438997906807499245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103351418959331937871666163 155027128438997906807499245)
        ·
          refine ⟨58135173164624215052812217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 155027128438997906807499245 58135173164624215052812217)
          ·
            refine ⟨43601379873468161289609163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58135173164624215052812217 43601379873468161289609163)
            ·
              refine ⟨65402069810202241934413745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43601379873468161289609163 65402069810202241934413745)
              ·
                refine ⟨49051552357651681450810309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65402069810202241934413745 49051552357651681450810309)
                ·
                  refine ⟨9197166067059690272026933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49051552357651681450810309 9197166067059690272026933)
                  ·
                    refine ⟨862234318786845963002525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9197166067059690272026933 862234318786845963002525)
                    ·
                      rfl

theorem cell22_2518793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 4, 5].length) (baseStart_2518793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2518793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2518793 prefixEnd_2518793 := by exact prefixLift 2518793
  have htrace : WordTrace (prefixWord ++ tailWord_2518793) baseStart_2518793 baseEnd_2518793 := by
    simpa [prefixWord, tailWord_2518793, baseEnd_2518793] using wordTrace_append hprefix tailTrace_2518793
  have hstable : (prefixWord ++ tailWord_2518793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518793).length < 2 ^ (prefixWord ++ tailWord_2518793).sum := by decide
  have hdescent : baseEnd_2518793 < baseStart_2518793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518840 : List Nat := [2, 1, 2, 1, 3, 4, 1, 2, 6]
def baseStart_2518840 : Nat := 118140960795 + 2518840 * 2 ^ 59
def prefixEnd_2518840 : Nat := 4983230072969 + 3 ^ 40 * 2518840 * 2
def baseEnd_2518840 : Nat := 287416802615784502359127

theorem tailTrace_2518840 : CollatzResearch.WordTrace tailWord_2518840 prefixEnd_2518840 287416802615784502359127 := by
  unfold tailWord_2518840
  simp only [CollatzResearch.WordTrace]
  refine ⟨45934821097340169234220987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61246428129786892312294649 45934821097340169234220987)
  ·
    refine ⟨68902231646010253851331481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45934821097340169234220987 68902231646010253851331481)
    ·
      refine ⟨51676673734507690388498611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68902231646010253851331481 51676673734507690388498611)
      ·
        refine ⟨77515010601761535582747917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51676673734507690388498611 77515010601761535582747917)
        ·
          refine ⟨29068128975660575843530469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77515010601761535582747917 29068128975660575843530469)
          ·
            refine ⟨5450274182936357970661963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29068128975660575843530469 5450274182936357970661963)
            ·
              refine ⟨8175411274404536955992945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5450274182936357970661963 8175411274404536955992945)
              ·
                refine ⟨6131558455803402716994709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8175411274404536955992945 6131558455803402716994709)
                ·
                  refine ⟨287416802615784502359127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6131558455803402716994709 287416802615784502359127)
                  ·
                    rfl

theorem cell22_2518840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 2, 6].length) (baseStart_2518840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2518840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2518840 prefixEnd_2518840 := by exact prefixLift 2518840
  have htrace : WordTrace (prefixWord ++ tailWord_2518840) baseStart_2518840 baseEnd_2518840 := by
    simpa [prefixWord, tailWord_2518840, baseEnd_2518840] using wordTrace_append hprefix tailTrace_2518840
  have hstable : (prefixWord ++ tailWord_2518840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518840).length < 2 ^ (prefixWord ++ tailWord_2518840).sum := by decide
  have hdescent : baseEnd_2518840 < baseStart_2518840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518855 : List Nat := [1, 1, 4, 1, 2, 1, 4, 2, 1, 5]
def baseStart_2518855 : Nat := 118140960795 + 2518855 * 2 ^ 59
def prefixEnd_2518855 : Nat := 4983230072969 + 3 ^ 40 * 2518855 * 2
def baseEnd_2518855 : Nat := 862255542653898467952335

theorem tailTrace_2518855 : CollatzResearch.WordTrace tailWord_2518855 prefixEnd_2518855 862255542653898467952335 := by
  unfold tailWord_2518855
  simp only [CollatzResearch.WordTrace]
  refine ⟨91870189289625996030238019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61246792859750664020158679 91870189289625996030238019)
  ·
    refine ⟨137805283934438994045357029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91870189289625996030238019 137805283934438994045357029)
    ·
      refine ⟨25838490737707311383504443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 137805283934438994045357029 25838490737707311383504443)
      ·
        refine ⟨38757736106560967075256665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25838490737707311383504443 38757736106560967075256665)
        ·
          refine ⟨29068302079920725306442499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38757736106560967075256665 29068302079920725306442499)
          ·
            refine ⟨43602453119881087959663749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29068302079920725306442499 43602453119881087959663749)
            ·
              refine ⟨8175459959977703992436953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43602453119881087959663749 8175459959977703992436953)
              ·
                refine ⟨6131594969983277994327715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8175459959977703992436953 6131594969983277994327715)
                ·
                  refine ⟨9197392454974916991491573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6131594969983277994327715 9197392454974916991491573)
                  ·
                    refine ⟨862255542653898467952335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9197392454974916991491573 862255542653898467952335)
                    ·
                      rfl

theorem cell22_2518855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 2, 1, 5].length) (baseStart_2518855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2518855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2518855 prefixEnd_2518855 := by exact prefixLift 2518855
  have htrace : WordTrace (prefixWord ++ tailWord_2518855) baseStart_2518855 baseEnd_2518855 := by
    simpa [prefixWord, tailWord_2518855, baseEnd_2518855] using wordTrace_append hprefix tailTrace_2518855
  have hstable : (prefixWord ++ tailWord_2518855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518855).length < 2 ^ (prefixWord ++ tailWord_2518855).sum := by decide
  have hdescent : baseEnd_2518855 < baseStart_2518855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2518857 : List Nat := [1, 2, 1, 1, 2, 4, 4, 3, 4]
def baseStart_2518857 : Nat := 118140960795 + 2518857 * 2 ^ 59
def prefixEnd_2518857 : Nat := 4983230072969 + 3 ^ 40 * 2518857 * 2
def baseEnd_2518857 : Nat := 287418742431590376467443

theorem tailTrace_2518857 : CollatzResearch.WordTrace tailWord_2518857 prefixEnd_2518857 287418742431590376467443 := by
  unfold tailWord_2518857
  simp only [CollatzResearch.WordTrace]
  refine ⟨91870262235618750371810825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61246841490412500247873883 91870262235618750371810825)
  ·
    refine ⟨68902696676714062778858119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91870262235618750371810825 68902696676714062778858119)
    ·
      refine ⟨103354045015071094168287179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68902696676714062778858119 103354045015071094168287179)
      ·
        refine ⟨155031067522606641252430769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103354045015071094168287179 155031067522606641252430769)
        ·
          refine ⟨116273300641954980939323077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155031067522606641252430769 116273300641954980939323077)
          ·
            refine ⟨21801243870366558926123077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 116273300641954980939323077 21801243870366558926123077)
            ·
              refine ⟨4087733225693729798648077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21801243870366558926123077 4087733225693729798648077)
              ·
                refine ⟨1532899959635148674493029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4087733225693729798648077 1532899959635148674493029)
                ·
                  refine ⟨287418742431590376467443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1532899959635148674493029 287418742431590376467443)
                  ·
                    rfl

theorem cell22_2518857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 3, 4].length) (baseStart_2518857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2518857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2518857 prefixEnd_2518857 := by exact prefixLift 2518857
  have htrace : WordTrace (prefixWord ++ tailWord_2518857) baseStart_2518857 baseEnd_2518857 := by
    simpa [prefixWord, tailWord_2518857, baseEnd_2518857] using wordTrace_append hprefix tailTrace_2518857
  have hstable : (prefixWord ++ tailWord_2518857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2518857).length < 2 ^ (prefixWord ++ tailWord_2518857).sum := by decide
  have hdescent : baseEnd_2518857 < baseStart_2518857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2518857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2519007 : List Nat := [1, 1, 2, 3, 4, 1, 1, 3, 1, 5]
def baseStart_2519007 : Nat := 118140960795 + 2519007 * 2 ^ 59
def prefixEnd_2519007 : Nat := 4983230072969 + 3 ^ 40 * 2519007 * 2
def baseEnd_2519007 : Nat := 862307575360220738151869

theorem tailTrace_2519007 : CollatzResearch.WordTrace tailWord_2519007 prefixEnd_2519007 862307575360220738151869 := by
  unfold tailWord_2519007
  simp only [CollatzResearch.WordTrace]
  refine ⟨91875733185075325989771275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61250488790050217326514183 91875733185075325989771275)
  ·
    refine ⟨137813599777612988984656913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91875733185075325989771275 137813599777612988984656913)
    ·
      refine ⟨103360199833209741738492685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137813599777612988984656913 103360199833209741738492685)
      ·
        refine ⟨38760074937453653151934757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103360199833209741738492685 38760074937453653151934757)
        ·
          refine ⟨7267514050772559965987767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38760074937453653151934757 7267514050772559965987767)
          ·
            refine ⟨10901271076158839948981651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7267514050772559965987767 10901271076158839948981651)
            ·
              refine ⟨16351906614238259923472477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10901271076158839948981651 16351906614238259923472477)
              ·
                refine ⟨6131964980339347471302179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16351906614238259923472477 6131964980339347471302179)
                ·
                  refine ⟨9197947470509021206953269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6131964980339347471302179 9197947470509021206953269)
                  ·
                    refine ⟨862307575360220738151869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9197947470509021206953269 862307575360220738151869)
                    ·
                      rfl

theorem cell22_2519007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 3, 1, 5].length) (baseStart_2519007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2519007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2519007 prefixEnd_2519007 := by exact prefixLift 2519007
  have htrace : WordTrace (prefixWord ++ tailWord_2519007) baseStart_2519007 baseEnd_2519007 := by
    simpa [prefixWord, tailWord_2519007, baseEnd_2519007] using wordTrace_append hprefix tailTrace_2519007
  have hstable : (prefixWord ++ tailWord_2519007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2519007).length < 2 ^ (prefixWord ++ tailWord_2519007).sum := by decide
  have hdescent : baseEnd_2519007 < baseStart_2519007 := by decide
  rcases family_descends (prefixWord ++ tailWord_2519007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2519020 : List Nat := [2, 2, 1, 1, 2, 1, 1, 12]
def baseStart_2519020 : Nat := 118140960795 + 2519020 * 2 ^ 59
def prefixEnd_2519020 : Nat := 4983230072969 + 3 ^ 40 * 2519020 * 2
def baseEnd_2519020 : Nat := 95812447280654781952981

theorem tailTrace_2519020 : CollatzResearch.WordTrace tailWord_2519020 prefixEnd_2519020 95812447280654781952981 := by
  unfold tailWord_2519020
  simp only [CollatzResearch.WordTrace]
  refine ⟨45938103667014114604997257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61250804889352152806663009 45938103667014114604997257)
  ·
    refine ⟨34453577750260585953747943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45938103667014114604997257 34453577750260585953747943)
    ·
      refine ⟨51680366625390878930621915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34453577750260585953747943 51680366625390878930621915)
      ·
        refine ⟨77520549938086318395932873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51680366625390878930621915 77520549938086318395932873)
        ·
          refine ⟨58140412453564738796949655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77520549938086318395932873 58140412453564738796949655)
          ·
            refine ⟨87210618680347108195424483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58140412453564738796949655 87210618680347108195424483)
            ·
              refine ⟨130815928020520662293136725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87210618680347108195424483 130815928020520662293136725)
              ·
                refine ⟨95812447280654781952981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 130815928020520662293136725 95812447280654781952981)
                ·
                  rfl

theorem cell22_2519020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 12].length) (baseStart_2519020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2519020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2519020 prefixEnd_2519020 := by exact prefixLift 2519020
  have htrace : WordTrace (prefixWord ++ tailWord_2519020) baseStart_2519020 baseEnd_2519020 := by
    simpa [prefixWord, tailWord_2519020, baseEnd_2519020] using wordTrace_append hprefix tailTrace_2519020
  have hstable : (prefixWord ++ tailWord_2519020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2519020).length < 2 ^ (prefixWord ++ tailWord_2519020).sum := by decide
  have hdescent : baseEnd_2519020 < baseStart_2519020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2519020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2519127 : List Nat := [1, 1, 3, 2, 2, 1, 2, 4, 6]
def baseStart_2519127 : Nat := 118140960795 + 2519127 * 2 ^ 59
def prefixEnd_2519127 : Nat := 4983230072969 + 3 ^ 40 * 2519127 * 2
def baseEnd_2519127 : Nat := 287449551270860141717167

theorem tailTrace_2519127 : CollatzResearch.WordTrace tailWord_2519127 prefixEnd_2519127 287449551270860141717167 := by
  unfold tailWord_2519127
  simp only [CollatzResearch.WordTrace]
  refine ⟨91880109944640586484139635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61253406629760390989426423 91880109944640586484139635)
  ·
    refine ⟨137820164916960879726209453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91880109944640586484139635 137820164916960879726209453)
    ·
      refine ⟨51682561843860329897328545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137820164916960879726209453 51682561843860329897328545)
      ·
        refine ⟨38761921382895247422996409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51682561843860329897328545 38761921382895247422996409)
        ·
          refine ⟨29071441037171435567247307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38761921382895247422996409 29071441037171435567247307)
          ·
            refine ⟨43607161555757153350870961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29071441037171435567247307 43607161555757153350870961)
            ·
              refine ⟨32705371166817865013153221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43607161555757153350870961 32705371166817865013153221)
              ·
                refine ⟨6132257093778349689966229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32705371166817865013153221 6132257093778349689966229)
                ·
                  refine ⟨287449551270860141717167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6132257093778349689966229 287449551270860141717167)
                  ·
                    rfl

theorem cell22_2519127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 4, 6].length) (baseStart_2519127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2519127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2519127 prefixEnd_2519127 := by exact prefixLift 2519127
  have htrace : WordTrace (prefixWord ++ tailWord_2519127) baseStart_2519127 baseEnd_2519127 := by
    simpa [prefixWord, tailWord_2519127, baseEnd_2519127] using wordTrace_append hprefix tailTrace_2519127
  have hstable : (prefixWord ++ tailWord_2519127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2519127).length < 2 ^ (prefixWord ++ tailWord_2519127).sum := by decide
  have hdescent : baseEnd_2519127 < baseStart_2519127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2519127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2519161 : List Nat := [1, 2, 1, 3, 4, 2, 1, 4, 4]
def baseStart_2519161 : Nat := 118140960795 + 2519161 * 2 ^ 59
def prefixEnd_2519161 : Nat := 4983230072969 + 3 ^ 40 * 2519161 * 2
def baseEnd_2519161 : Nat := 287453430902471889933799

theorem tailTrace_2519161 : CollatzResearch.WordTrace tailWord_2519161 prefixEnd_2519161 287453430902471889933799 := by
  unfold tailWord_2519161
  simp only [CollatzResearch.WordTrace]
  refine ⟨91881350026517410290877337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61254233351011606860584891 91881350026517410290877337)
  ·
    refine ⟨68911012519888057718158003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91881350026517410290877337 68911012519888057718158003)
    ·
      refine ⟨103366518779832086577237005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68911012519888057718158003 103366518779832086577237005)
      ·
        refine ⟨38762444542437032466463877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103366518779832086577237005 38762444542437032466463877)
        ·
          refine ⟨7267958351706943587461977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38762444542437032466463877 7267958351706943587461977)
          ·
            refine ⟨5450968763780207690596483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7267958351706943587461977 5450968763780207690596483)
            ·
              refine ⟨8176453145670311535894725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5450968763780207690596483 8176453145670311535894725)
              ·
                refine ⟨1533084964813183412980261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8176453145670311535894725 1533084964813183412980261)
                ·
                  refine ⟨287453430902471889933799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1533084964813183412980261 287453430902471889933799)
                  ·
                    rfl

theorem cell22_2519161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 4, 4].length) (baseStart_2519161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2519161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2519161 prefixEnd_2519161 := by exact prefixLift 2519161
  have htrace : WordTrace (prefixWord ++ tailWord_2519161) baseStart_2519161 baseEnd_2519161 := by
    simpa [prefixWord, tailWord_2519161, baseEnd_2519161] using wordTrace_append hprefix tailTrace_2519161
  have hstable : (prefixWord ++ tailWord_2519161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2519161).length < 2 ^ (prefixWord ++ tailWord_2519161).sum := by decide
  have hdescent : baseEnd_2519161 < baseStart_2519161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2519161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2519176 : List Nat := [2, 1, 3, 4, 1, 2, 2, 1, 1, 5]
def baseStart_2519176 : Nat := 118140960795 + 2519176 * 2 ^ 59
def prefixEnd_2519176 : Nat := 4983230072969 + 3 ^ 40 * 2519176 * 2
def baseEnd_2519176 : Nat := 862365427513960630676351

theorem tailTrace_2519176 : CollatzResearch.WordTrace tailWord_2519176 prefixEnd_2519176 862365427513960630676351 := by
  unfold tailWord_2519176
  simp only [CollatzResearch.WordTrace]
  refine ⟨45940948560731533926336691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61254598080975378568448921 45940948560731533926336691)
  ·
    refine ⟨68911422841097300889505037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45940948560731533926336691 68911422841097300889505037)
    ·
      refine ⟨25841783565411487833564389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68911422841097300889505037 25841783565411487833564389)
      ·
        refine ⟨4845334418514653968793323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25841783565411487833564389 4845334418514653968793323)
        ·
          refine ⟨7268001627771980953189985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4845334418514653968793323 7268001627771980953189985)
          ·
            refine ⟨5451001220828985714892489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7268001627771980953189985 5451001220828985714892489)
            ·
              refine ⟨4088250915621739286169367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5451001220828985714892489 4088250915621739286169367)
              ·
                refine ⟨6132376373432608929254051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4088250915621739286169367 6132376373432608929254051)
                ·
                  refine ⟨9198564560148913393881077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6132376373432608929254051 9198564560148913393881077)
                  ·
                    refine ⟨862365427513960630676351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9198564560148913393881077 862365427513960630676351)
                    ·
                      rfl

theorem cell22_2519176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 1, 1, 5].length) (baseStart_2519176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2519176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2519176 prefixEnd_2519176 := by exact prefixLift 2519176
  have htrace : WordTrace (prefixWord ++ tailWord_2519176) baseStart_2519176 baseEnd_2519176 := by
    simpa [prefixWord, tailWord_2519176, baseEnd_2519176] using wordTrace_append hprefix tailTrace_2519176
  have hstable : (prefixWord ++ tailWord_2519176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2519176).length < 2 ^ (prefixWord ++ tailWord_2519176).sum := by decide
  have hdescent : baseEnd_2519176 < baseStart_2519176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2519176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2519189 : List Nat := [1, 3, 2, 1, 1, 1, 7, 6]
def baseStart_2519189 : Nat := 118140960795 + 2519189 * 2 ^ 59
def prefixEnd_2519189 : Nat := 4983230072969 + 3 ^ 40 * 2519189 * 2
def baseEnd_2519189 : Nat := 95818875297736992233479

theorem tailTrace_2519189 : CollatzResearch.WordTrace tailWord_2519189 prefixEnd_2519189 95818875297736992233479 := by
  unfold tailWord_2519189
  simp only [CollatzResearch.WordTrace]
  refine ⟨91882371270415971072896621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61254914180277314048597747 91882371270415971072896621)
  ·
    refine ⟨34455889226405989152336233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91882371270415971072896621 34455889226405989152336233)
    ·
      refine ⟨25841916919804491864252175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34455889226405989152336233 25841916919804491864252175)
      ·
        refine ⟨38762875379706737796378263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25841916919804491864252175 38762875379706737796378263)
        ·
          refine ⟨58144313069560106694567395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38762875379706737796378263 58144313069560106694567395)
          ·
            refine ⟨87216469604340160041851093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58144313069560106694567395 87216469604340160041851093)
            ·
              refine ⟨2044136006351722500980885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 87216469604340160041851093 2044136006351722500980885)
              ·
                refine ⟨95818875297736992233479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2044136006351722500980885 95818875297736992233479)
                ·
                  rfl

theorem cell22_2519189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 7, 6].length) (baseStart_2519189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2519189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2519189 prefixEnd_2519189 := by exact prefixLift 2519189
  have htrace : WordTrace (prefixWord ++ tailWord_2519189) baseStart_2519189 baseEnd_2519189 := by
    simpa [prefixWord, tailWord_2519189, baseEnd_2519189] using wordTrace_append hprefix tailTrace_2519189
  have hstable : (prefixWord ++ tailWord_2519189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2519189).length < 2 ^ (prefixWord ++ tailWord_2519189).sum := by decide
  have hdescent : baseEnd_2519189 < baseStart_2519189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2519189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2519298 : List Nat := [3, 4, 1, 1, 2, 2, 1, 1, 3, 4]
def baseStart_2519298 : Nat := 118140960795 + 2519298 * 2 ^ 59
def prefixEnd_2519298 : Nat := 4983230072969 + 3 ^ 40 * 2519298 * 2
def baseEnd_2519298 : Nat := 862407190607192979125977

theorem tailTrace_2519298 : CollatzResearch.WordTrace tailWord_2519298 prefixEnd_2519298 862407190607192979125977 := by
  unfold tailWord_2519298
  simp only [CollatzResearch.WordTrace]
  refine ⟨22971586706755270672153637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61257564551347388459076365 22971586706755270672153637)
  ·
    refine ⟨4307172507516613251028807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22971586706755270672153637 4307172507516613251028807)
    ·
      refine ⟨6460758761274919876543211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4307172507516613251028807 6460758761274919876543211)
      ·
        refine ⟨9691138141912379814814817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6460758761274919876543211 9691138141912379814814817)
        ·
          refine ⟨7268353606434284861111113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9691138141912379814814817 7268353606434284861111113)
          ·
            refine ⟨5451265204825713645833335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7268353606434284861111113 5451265204825713645833335)
            ·
              refine ⟨8176897807238570468750003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5451265204825713645833335 8176897807238570468750003)
              ·
                refine ⟨12265346710857855703125005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8176897807238570468750003 12265346710857855703125005)
                ·
                  refine ⟨4599505016571695888671877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12265346710857855703125005 4599505016571695888671877)
                  ·
                    refine ⟨862407190607192979125977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4599505016571695888671877 862407190607192979125977)
                    ·
                      rfl

theorem cell22_2519298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_2519298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2519298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2519298 prefixEnd_2519298 := by exact prefixLift 2519298
  have htrace : WordTrace (prefixWord ++ tailWord_2519298) baseStart_2519298 baseEnd_2519298 := by
    simpa [prefixWord, tailWord_2519298, baseEnd_2519298] using wordTrace_append hprefix tailTrace_2519298
  have hstable : (prefixWord ++ tailWord_2519298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2519298).length < 2 ^ (prefixWord ++ tailWord_2519298).sum := by decide
  have hdescent : baseEnd_2519298 < baseStart_2519298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2519298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2519328 : List Nat := [2, 1, 1, 5, 2, 1, 1, 4, 2, 3]
def baseStart_2519328 : Nat := 118140960795 + 2519328 * 2 ^ 59
def prefixEnd_2519328 : Nat := 4983230072969 + 3 ^ 40 * 2519328 * 2
def baseEnd_2519328 : Nat := 862417460220282900875885

theorem tailTrace_2519328 : CollatzResearch.WordTrace tailWord_2519328 prefixEnd_2519328 862417460220282900875885 := by
  unfold tailWord_2519328
  simp only [CollatzResearch.WordTrace]
  refine ⟨45943720508456198906103319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61258294011274931874804425 45943720508456198906103319)
  ·
    refine ⟨68915580762684298359154979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45943720508456198906103319 68915580762684298359154979)
    ·
      refine ⟨103373371144026447538732469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68915580762684298359154979 103373371144026447538732469)
      ·
        refine ⟨9691253544752479456756169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 103373371144026447538732469 9691253544752479456756169)
        ·
          refine ⟨7268440158564359592567127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9691253544752479456756169 7268440158564359592567127)
          ·
            refine ⟨10902660237846539388850691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7268440158564359592567127 10902660237846539388850691)
            ·
              refine ⟨16353990356769809083276037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10902660237846539388850691 16353990356769809083276037)
              ·
                refine ⟨3066373191894339203114257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16353990356769809083276037 3066373191894339203114257)
                ·
                  refine ⟨2299779893920754402335693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3066373191894339203114257 2299779893920754402335693)
                  ·
                    refine ⟨862417460220282900875885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2299779893920754402335693 862417460220282900875885)
                    ·
                      rfl

theorem cell22_2519328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 4, 2, 3].length) (baseStart_2519328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2519328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2519328 prefixEnd_2519328 := by exact prefixLift 2519328
  have htrace : WordTrace (prefixWord ++ tailWord_2519328) baseStart_2519328 baseEnd_2519328 := by
    simpa [prefixWord, tailWord_2519328, baseEnd_2519328] using wordTrace_append hprefix tailTrace_2519328
  have hstable : (prefixWord ++ tailWord_2519328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2519328).length < 2 ^ (prefixWord ++ tailWord_2519328).sum := by decide
  have hdescent : baseEnd_2519328 < baseStart_2519328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2519328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2519330 : List Nat := [3, 3, 1, 1, 3, 1, 4, 2, 4]
def baseStart_2519330 : Nat := 118140960795 + 2519330 * 2 ^ 59
def prefixEnd_2519330 : Nat := 4983230072969 + 3 ^ 40 * 2519330 * 2
def baseEnd_2519330 : Nat := 287472714953718520775293

theorem tailTrace_2519330 : CollatzResearch.WordTrace tailWord_2519330 prefixEnd_2519330 287472714953718520775293 := by
  unfold tailWord_2519330
  simp only [CollatzResearch.WordTrace]
  refine ⟨22971878490726288038444861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61258342641936768102519629 22971878490726288038444861)
  ·
    refine ⟨8614454434022358014416823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22971878490726288038444861 8614454434022358014416823)
    ·
      refine ⟨12921681651033537021625235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8614454434022358014416823 12921681651033537021625235)
      ·
        refine ⟨19382522476550305532437853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12921681651033537021625235 19382522476550305532437853)
        ·
          refine ⟨7268445928706364574664195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19382522476550305532437853 7268445928706364574664195)
          ·
            refine ⟨10902668893059546861996293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7268445928706364574664195 10902668893059546861996293)
            ·
              refine ⟨2044250417448665036624305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10902668893059546861996293 2044250417448665036624305)
              ·
                refine ⟨1533187813086498777468229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2044250417448665036624305 1533187813086498777468229)
                ·
                  refine ⟨287472714953718520775293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1533187813086498777468229 287472714953718520775293)
                  ·
                    rfl

theorem cell22_2519330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 4, 2, 4].length) (baseStart_2519330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2519330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2519330 prefixEnd_2519330 := by exact prefixLift 2519330
  have htrace : WordTrace (prefixWord ++ tailWord_2519330) baseStart_2519330 baseEnd_2519330 := by
    simpa [prefixWord, tailWord_2519330, baseEnd_2519330] using wordTrace_append hprefix tailTrace_2519330
  have hstable : (prefixWord ++ tailWord_2519330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2519330).length < 2 ^ (prefixWord ++ tailWord_2519330).sum := by decide
  have hdescent : baseEnd_2519330 < baseStart_2519330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2519330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2519358 : List Nat := [4, 2, 1, 2, 1, 3, 3, 6]
def baseStart_2519358 : Nat := 118140960795 + 2519358 * 2 ^ 59
def prefixEnd_2519358 : Nat := 4983230072969 + 3 ^ 40 * 2519358 * 2
def baseEnd_2519358 : Nat := 95825303314819202513977

theorem tailTrace_2519358 : CollatzResearch.WordTrace tailWord_2519358 prefixEnd_2519358 95825303314819202513977 := by
  unfold tailWord_2519358
  simp only [CollatzResearch.WordTrace]
  refine ⟨11486066900850464116974841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61259023471202475290532485 11486066900850464116974841)
  ·
    refine ⟨8614550175637848087731131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11486066900850464116974841 8614550175637848087731131)
    ·
      refine ⟨12921825263456772131596697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8614550175637848087731131 12921825263456772131596697)
      ·
        refine ⟨9691368947592579098697523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12921825263456772131596697 9691368947592579098697523)
        ·
          refine ⟨14537053421388868648046285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9691368947592579098697523 14537053421388868648046285)
          ·
            refine ⟨5451395033020825743017357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14537053421388868648046285 5451395033020825743017357)
            ·
              refine ⟨2044273137382809653631509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5451395033020825743017357 2044273137382809653631509)
              ·
                refine ⟨95825303314819202513977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2044273137382809653631509 95825303314819202513977)
                ·
                  rfl

theorem cell22_2519358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 3, 6].length) (baseStart_2519358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2519358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2519358 prefixEnd_2519358 := by exact prefixLift 2519358
  have htrace : WordTrace (prefixWord ++ tailWord_2519358) baseStart_2519358 baseEnd_2519358 := by
    simpa [prefixWord, tailWord_2519358, baseEnd_2519358] using wordTrace_append hprefix tailTrace_2519358
  have hstable : (prefixWord ++ tailWord_2519358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2519358).length < 2 ^ (prefixWord ++ tailWord_2519358).sum := by decide
  have hdescent : baseEnd_2519358 < baseStart_2519358 := by decide
  rcases family_descends (prefixWord ++ tailWord_2519358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2519369 : List Nat := [1, 2, 1, 1, 2, 3, 1, 4, 7]
def baseStart_2519369 : Nat := 118140960795 + 2519369 * 2 ^ 59
def prefixEnd_2519369 : Nat := 4983230072969 + 3 ^ 40 * 2519369 * 2
def baseEnd_2519369 : Nat := 287477165119390820200253

theorem tailTrace_2519369 : CollatzResearch.WordTrace tailWord_2519369 prefixEnd_2519369 287477165119390820200253 := by
  unfold tailWord_2519369
  simp only [CollatzResearch.WordTrace]
  refine ⟨91888936409763861814449161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61259290939842574542966107 91888936409763861814449161)
  ·
    refine ⟨68916702307322896360836871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91888936409763861814449161 68916702307322896360836871)
    ·
      refine ⟨103375053460984344541255307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68916702307322896360836871 103375053460984344541255307)
      ·
        refine ⟨155062580191476516811882961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103375053460984344541255307 155062580191476516811882961)
        ·
          refine ⟨116296935143607387608912221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155062580191476516811882961 116296935143607387608912221)
          ·
            refine ⟨43611350678852770353342083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116296935143607387608912221 43611350678852770353342083)
            ·
              refine ⟨65417026018279155530013125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43611350678852770353342083 65417026018279155530013125)
              ·
                refine ⟨12265692378427341661877461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65417026018279155530013125 12265692378427341661877461)
                ·
                  refine ⟨287477165119390820200253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12265692378427341661877461 287477165119390820200253)
                  ·
                    rfl

theorem cell22_2519369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 4, 7].length) (baseStart_2519369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2519369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2519369 prefixEnd_2519369 := by exact prefixLift 2519369
  have htrace : WordTrace (prefixWord ++ tailWord_2519369) baseStart_2519369 baseEnd_2519369 := by
    simpa [prefixWord, tailWord_2519369, baseEnd_2519369] using wordTrace_append hprefix tailTrace_2519369
  have hstable : (prefixWord ++ tailWord_2519369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2519369).length < 2 ^ (prefixWord ++ tailWord_2519369).sum := by decide
  have hdescent : baseEnd_2519369 < baseStart_2519369 := by decide
  rcases family_descends (prefixWord ++ tailWord_2519369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2519433 : List Nat := [1, 2, 1, 1, 6, 1, 2, 3, 1, 4]
def baseStart_2519433 : Nat := 118140960795 + 2519433 * 2 ^ 59
def prefixEnd_2519433 : Nat := 4983230072969 + 3 ^ 40 * 2519433 * 2
def baseEnd_2519433 : Nat := 862453403866097627000563

theorem tailTrace_2519433 : CollatzResearch.WordTrace tailWord_2519433 prefixEnd_2519433 862453403866097627000563 := by
  unfold tailWord_2519433
  simp only [CollatzResearch.WordTrace]
  refine ⟨91891270681532000744778953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61260847121021333829852635 91891270681532000744778953)
  ·
    refine ⟨68918453011149000558584215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91891270681532000744778953 68918453011149000558584215)
    ·
      refine ⟨103377679516723500837876323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68918453011149000558584215 103377679516723500837876323)
      ·
        refine ⟨155066519275085251256814485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103377679516723500837876323 155066519275085251256814485)
        ·
          refine ⟨7268743091019621152663179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 155066519275085251256814485 7268743091019621152663179)
          ·
            refine ⟨10903114636529431728994769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7268743091019621152663179 10903114636529431728994769)
            ·
              refine ⟨8177335977397073796746077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10903114636529431728994769 8177335977397073796746077)
              ·
                refine ⟨3066500991523902673779779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8177335977397073796746077 3066500991523902673779779)
                ·
                  refine ⟨4599751487285854010669669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3066500991523902673779779 4599751487285854010669669)
                  ·
                    refine ⟨862453403866097627000563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4599751487285854010669669 862453403866097627000563)
                    ·
                      rfl

theorem cell22_2519433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 3, 1, 4].length) (baseStart_2519433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2519433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2519433 prefixEnd_2519433 := by exact prefixLift 2519433
  have htrace : WordTrace (prefixWord ++ tailWord_2519433) baseStart_2519433 baseEnd_2519433 := by
    simpa [prefixWord, tailWord_2519433, baseEnd_2519433] using wordTrace_append hprefix tailTrace_2519433
  have hstable : (prefixWord ++ tailWord_2519433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2519433).length < 2 ^ (prefixWord ++ tailWord_2519433).sum := by decide
  have hdescent : baseEnd_2519433 < baseStart_2519433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2519433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2519448 : List Nat := [2, 1, 2, 5, 1, 1, 3, 1, 6]
def baseStart_2519448 : Nat := 118140960795 + 2519448 * 2 ^ 59
def prefixEnd_2519448 : Nat := 4983230072969 + 3 ^ 40 * 2519448 * 2
def baseEnd_2519448 : Nat := 287486179557547529291839

theorem tailTrace_2519448 : CollatzResearch.WordTrace tailWord_2519448 prefixEnd_2519448 287486179557547529291839 := by
  unfold tailWord_2519448
  simp only [CollatzResearch.WordTrace]
  refine ⟨45945908888238829153287499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61261211850985105537716665 45945908888238829153287499)
  ·
    refine ⟨68918863332358243729931249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45945908888238829153287499 68918863332358243729931249)
    ·
      refine ⟨51689147499268682797448437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68918863332358243729931249 51689147499268682797448437)
      ·
        refine ⟨4845857578056439012260791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 51689147499268682797448437 4845857578056439012260791)
        ·
          refine ⟨7268786367084658518391187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4845857578056439012260791 7268786367084658518391187)
          ·
            refine ⟨10903179550626987777586781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7268786367084658518391187 10903179550626987777586781)
            ·
              refine ⟨4088692331485120416595043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10903179550626987777586781 4088692331485120416595043)
              ·
                refine ⟨6133038497227680624892565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4088692331485120416595043 6133038497227680624892565)
                ·
                  refine ⟨287486179557547529291839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6133038497227680624892565 287486179557547529291839)
                  ·
                    rfl

theorem cell22_2519448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 1, 6].length) (baseStart_2519448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2519448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2519448 prefixEnd_2519448 := by exact prefixLift 2519448
  have htrace : WordTrace (prefixWord ++ tailWord_2519448) baseStart_2519448 baseEnd_2519448 := by
    simpa [prefixWord, tailWord_2519448, baseEnd_2519448] using wordTrace_append hprefix tailTrace_2519448
  have hstable : (prefixWord ++ tailWord_2519448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2519448).length < 2 ^ (prefixWord ++ tailWord_2519448).sum := by decide
  have hdescent : baseEnd_2519448 < baseStart_2519448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2519448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2519461 : List Nat := [1, 3, 1, 2, 1, 1, 3, 2, 4, 4]
def baseStart_2519461 : Nat := 118140960795 + 2519461 * 2 ^ 59
def prefixEnd_2519461 : Nat := 4983230072969 + 3 ^ 40 * 2519461 * 2
def baseEnd_2519461 : Nat := 862462988838314887300477

theorem tailTrace_2519461 : CollatzResearch.WordTrace tailWord_2519461 prefixEnd_2519461 862462988838314887300477 := by
  unfold tailWord_2519461
  simp only [CollatzResearch.WordTrace]
  refine ⟨91892291925430561526798237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61261527950287041017865491 91892291925430561526798237)
  ·
    refine ⟨34459609472036460572549339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91892291925430561526798237 34459609472036460572549339)
    ·
      refine ⟨51689414208054690858824009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34459609472036460572549339 51689414208054690858824009)
      ·
        refine ⟨38767060656041018144118007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51689414208054690858824009 38767060656041018144118007)
        ·
          refine ⟨58150590984061527216177011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38767060656041018144118007 58150590984061527216177011)
          ·
            refine ⟨87225886476092290824265517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58150590984061527216177011 87225886476092290824265517)
            ·
              refine ⟨32709707428534609059099569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87225886476092290824265517 32709707428534609059099569)
              ·
                refine ⟨24532280571400956794324677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32709707428534609059099569 24532280571400956794324677)
                ·
                  refine ⟨4599802607137679398935877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24532280571400956794324677 4599802607137679398935877)
                  ·
                    refine ⟨862462988838314887300477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4599802607137679398935877 862462988838314887300477)
                    ·
                      rfl

theorem cell22_2519461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 4, 4].length) (baseStart_2519461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2519461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2519461 prefixEnd_2519461 := by exact prefixLift 2519461
  have htrace : WordTrace (prefixWord ++ tailWord_2519461) baseStart_2519461 baseEnd_2519461 := by
    simpa [prefixWord, tailWord_2519461, baseEnd_2519461] using wordTrace_append hprefix tailTrace_2519461
  have hstable : (prefixWord ++ tailWord_2519461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2519461).length < 2 ^ (prefixWord ++ tailWord_2519461).sum := by decide
  have hdescent : baseEnd_2519461 < baseStart_2519461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2519461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2519536 : List Nat := [2, 1, 1, 1, 3, 3, 1, 2, 1, 7]
def baseStart_2519536 : Nat := 118140960795 + 2519536 * 2 ^ 59
def prefixEnd_2519536 : Nat := 4983230072969 + 3 ^ 40 * 2519536 * 2
def baseEnd_2519536 : Nat := 862488662871039691675247

theorem tailTrace_2519536 : CollatzResearch.WordTrace tailWord_2519536 prefixEnd_2519536 862488662871039691675247 := by
  unfold tailWord_2519536
  simp only [CollatzResearch.WordTrace]
  refine ⟨45947513700079424667889231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61263351600105899557185641 45947513700079424667889231)
  ·
    refine ⟨68921270550119137001833847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45947513700079424667889231 68921270550119137001833847)
    ·
      refine ⟨103381905825178705502750771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68921270550119137001833847 103381905825178705502750771)
      ·
        refine ⟨155072858737768058254126157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103381905825178705502750771 155072858737768058254126157)
        ·
          refine ⟨58152322026663021845297309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 155072858737768058254126157 58152322026663021845297309)
          ·
            refine ⟨21807120759998633191986491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58152322026663021845297309 21807120759998633191986491)
            ·
              refine ⟨32710681139997949787979737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21807120759998633191986491 32710681139997949787979737)
              ·
                refine ⟨24533010854998462340984803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32710681139997949787979737 24533010854998462340984803)
                ·
                  refine ⟨36799516282497693511477205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24533010854998462340984803 36799516282497693511477205)
                  ·
                    refine ⟨862488662871039691675247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36799516282497693511477205 862488662871039691675247)
                    ·
                      rfl

theorem cell22_2519536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 1, 7].length) (baseStart_2519536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2519536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2519536 prefixEnd_2519536 := by exact prefixLift 2519536
  have htrace : WordTrace (prefixWord ++ tailWord_2519536) baseStart_2519536 baseEnd_2519536 := by
    simpa [prefixWord, tailWord_2519536, baseEnd_2519536] using wordTrace_append hprefix tailTrace_2519536
  have hstable : (prefixWord ++ tailWord_2519536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2519536).length < 2 ^ (prefixWord ++ tailWord_2519536).sum := by decide
  have hdescent : baseEnd_2519536 < baseStart_2519536 := by decide
  rcases family_descends (prefixWord ++ tailWord_2519536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2519553 : List Nat := [1, 2, 4, 1, 3, 1, 1, 2, 2, 5]
def baseStart_2519553 : Nat := 118140960795 + 2519553 * 2 ^ 59
def prefixEnd_2519553 : Nat := 4983230072969 + 3 ^ 40 * 2519553 * 2
def baseEnd_2519553 : Nat := 862494482318457314000195

theorem tailTrace_2519553 : CollatzResearch.WordTrace tailWord_2519553 prefixEnd_2519553 862494482318457314000195 := by
  unfold tailWord_2519553
  simp only [CollatzResearch.WordTrace]
  refine ⟨91895647441097261239147313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61263764960731507492764875 91895647441097261239147313)
  ·
    refine ⟨68921735580822945929360485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91895647441097261239147313 68921735580822945929360485)
    ·
      refine ⟨12922825421404302361755091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68921735580822945929360485 12922825421404302361755091)
      ·
        refine ⟨19384238132106453542632637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12922825421404302361755091 19384238132106453542632637)
        ·
          refine ⟨7269089299539920078487239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19384238132106453542632637 7269089299539920078487239)
          ·
            refine ⟨10903633949309880117730859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7269089299539920078487239 10903633949309880117730859)
            ·
              refine ⟨16355450923964820176596289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10903633949309880117730859 16355450923964820176596289)
              ·
                refine ⟨12266588192973615132447217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16355450923964820176596289 12266588192973615132447217)
                ·
                  refine ⟨9199941144730211349335413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12266588192973615132447217 9199941144730211349335413)
                  ·
                    refine ⟨862494482318457314000195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9199941144730211349335413 862494482318457314000195)
                    ·
                      rfl

theorem cell22_2519553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_2519553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2519553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2519553 prefixEnd_2519553 := by exact prefixLift 2519553
  have htrace : WordTrace (prefixWord ++ tailWord_2519553) baseStart_2519553 baseEnd_2519553 := by
    simpa [prefixWord, tailWord_2519553, baseEnd_2519553] using wordTrace_append hprefix tailTrace_2519553
  have hstable : (prefixWord ++ tailWord_2519553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2519553).length < 2 ^ (prefixWord ++ tailWord_2519553).sum := by decide
  have hdescent : baseEnd_2519553 < baseStart_2519553 := by decide
  rcases family_descends (prefixWord ++ tailWord_2519553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2519585 : List Nat := [1, 2, 3, 2, 2, 1, 4, 2, 1, 4]
def baseStart_2519585 : Nat := 118140960795 + 2519585 * 2 ^ 59
def prefixEnd_2519585 : Nat := 4983230072969 + 3 ^ 40 * 2519585 * 2
def baseEnd_2519585 : Nat := 862505436572419897200097

theorem tailTrace_2519585 : CollatzResearch.WordTrace tailWord_2519585 prefixEnd_2519585 862505436572419897200097 := by
  unfold tailWord_2519585
  simp only [CollatzResearch.WordTrace]
  refine ⟨91896814576981330704312209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61264543051320887136208139 91896814576981330704312209)
  ·
    refine ⟨68922610932735998028234157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91896814576981330704312209 68922610932735998028234157)
    ·
      refine ⟨25845979099775999260587809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68922610932735998028234157 25845979099775999260587809)
      ·
        refine ⟨19384484324831999445440857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25845979099775999260587809 19384484324831999445440857)
        ·
          refine ⟨14538363243623999584080643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19384484324831999445440857 14538363243623999584080643)
          ·
            refine ⟨21807544865435999376120965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14538363243623999584080643 21807544865435999376120965)
            ·
              refine ⟨4088914662269249883022681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21807544865435999376120965 4088914662269249883022681)
              ·
                refine ⟨3066685996701937412267011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4088914662269249883022681 3066685996701937412267011)
                ·
                  refine ⟨4600028995052906118400517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3066685996701937412267011 4600028995052906118400517)
                  ·
                    refine ⟨862505436572419897200097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4600028995052906118400517 862505436572419897200097)
                    ·
                      rfl

theorem cell22_2519585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 2, 1, 4].length) (baseStart_2519585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2519585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2519585 prefixEnd_2519585 := by exact prefixLift 2519585
  have htrace : WordTrace (prefixWord ++ tailWord_2519585) baseStart_2519585 baseEnd_2519585 := by
    simpa [prefixWord, tailWord_2519585, baseEnd_2519585] using wordTrace_append hprefix tailTrace_2519585
  have hstable : (prefixWord ++ tailWord_2519585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2519585).length < 2 ^ (prefixWord ++ tailWord_2519585).sum := by decide
  have hdescent : baseEnd_2519585 < baseStart_2519585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2519585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2519600 : List Nat := [2, 1, 1, 1, 2, 3, 5, 3, 4]
def baseStart_2519600 : Nat := 118140960795 + 2519600 * 2 ^ 59
def prefixEnd_2519600 : Nat := 4983230072969 + 3 ^ 40 * 2519600 * 2
def baseEnd_2519600 : Nat := 287503523792988286025017

theorem tailTrace_2519600 : CollatzResearch.WordTrace tailWord_2519600 prefixEnd_2519600 287503523792988286025017 := by
  unfold tailWord_2519600
  simp only [CollatzResearch.WordTrace]
  refine ⟨45948680835963494133054127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61264907781284658844072169 45948680835963494133054127)
  ·
    refine ⟨68923021253945241199581191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45948680835963494133054127 68923021253945241199581191)
    ·
      refine ⟨103384531880917861799371787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68923021253945241199581191 103384531880917861799371787)
      ·
        refine ⟨155076797821376792699057681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103384531880917861799371787 155076797821376792699057681)
        ·
          refine ⟨116307598366032594524293261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155076797821376792699057681 116307598366032594524293261)
          ·
            refine ⟨43615349387262222946609973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116307598366032594524293261 43615349387262222946609973)
            ·
              refine ⟨4088939005055833401244685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43615349387262222946609973 4088939005055833401244685)
              ·
                refine ⟨1533352126895937525466757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4088939005055833401244685 1533352126895937525466757)
                ·
                  refine ⟨287503523792988286025017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1533352126895937525466757 287503523792988286025017)
                  ·
                    rfl

theorem cell22_2519600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 3, 4].length) (baseStart_2519600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2519600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2519600 prefixEnd_2519600 := by exact prefixLift 2519600
  have htrace : WordTrace (prefixWord ++ tailWord_2519600) baseStart_2519600 baseEnd_2519600 := by
    simpa [prefixWord, tailWord_2519600, baseEnd_2519600] using wordTrace_append hprefix tailTrace_2519600
  have hstable : (prefixWord ++ tailWord_2519600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2519600).length < 2 ^ (prefixWord ++ tailWord_2519600).sum := by decide
  have hdescent : baseEnd_2519600 < baseStart_2519600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2519600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2519615 : List Nat := [1, 1, 2, 2, 3, 2, 2, 4, 2, 3]
def baseStart_2519615 : Nat := 118140960795 + 2519615 * 2 ^ 59
def prefixEnd_2519615 : Nat := 4983230072969 + 3 ^ 40 * 2519615 * 2
def baseEnd_2519615 : Nat := 862515706185509818950005

theorem tailTrace_2519615 : CollatzResearch.WordTrace tailWord_2519615 prefixEnd_2519615 862515706185509818950005 := by
  unfold tailWord_2519615
  simp only [CollatzResearch.WordTrace]
  refine ⟨91897908766872645827904299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61265272511248430551936199 91897908766872645827904299)
  ·
    refine ⟨137846863150308968741856449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91897908766872645827904299 137846863150308968741856449)
    ·
      refine ⟨103385147362731726556392337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137846863150308968741856449 103385147362731726556392337)
      ·
        refine ⟨77538860522048794917294253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103385147362731726556392337 77538860522048794917294253)
        ·
          refine ⟨29077072695768298093985345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77538860522048794917294253 29077072695768298093985345)
          ·
            refine ⟨21807804521826223570489009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29077072695768298093985345 21807804521826223570489009)
            ·
              refine ⟨16355853391369667677866757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21807804521826223570489009 16355853391369667677866757)
              ·
                refine ⟨3066722510881812689600017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16355853391369667677866757 3066722510881812689600017)
                ·
                  refine ⟨2300041883161359517200013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3066722510881812689600017 2300041883161359517200013)
                  ·
                    refine ⟨862515706185509818950005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2300041883161359517200013 862515706185509818950005)
                    ·
                      rfl

theorem cell22_2519615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 4, 2, 3].length) (baseStart_2519615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2519615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2519615 prefixEnd_2519615 := by exact prefixLift 2519615
  have htrace : WordTrace (prefixWord ++ tailWord_2519615) baseStart_2519615 baseEnd_2519615 := by
    simpa [prefixWord, tailWord_2519615, baseEnd_2519615] using wordTrace_append hprefix tailTrace_2519615
  have hstable : (prefixWord ++ tailWord_2519615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2519615).length < 2 ^ (prefixWord ++ tailWord_2519615).sum := by decide
  have hdescent : baseEnd_2519615 < baseStart_2519615 := by decide
  rcases family_descends (prefixWord ++ tailWord_2519615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2519628 : List Nat := [2, 2, 1, 3, 1, 2, 4, 7]
def baseStart_2519628 : Nat := 118140960795 + 2519628 * 2 ^ 59
def prefixEnd_2519628 : Nat := 4983230072969 + 3 ^ 40 * 2519628 * 2
def baseEnd_2519628 : Nat := 95835572927909124263885

theorem tailTrace_2519628 : CollatzResearch.WordTrace tailWord_2519628 prefixEnd_2519628 95835572927909124263885 := by
  unfold tailWord_2519628
  simp only [CollatzResearch.WordTrace]
  refine ⟨45949191457912774524063769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61265588610550366032085025 45949191457912774524063769)
  ·
    refine ⟨34461893593434580893047827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45949191457912774524063769 34461893593434580893047827)
    ·
      refine ⟨51692840390151871339571741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34461893593434580893047827 51692840390151871339571741)
      ·
        refine ⟨19384815146306951752339403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51692840390151871339571741 19384815146306951752339403)
        ·
          refine ⟨29077222719460427628509105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19384815146306951752339403 29077222719460427628509105)
          ·
            refine ⟨21807917039595320721381829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29077222719460427628509105 21807917039595320721381829)
            ·
              refine ⟨4088984444924122635259093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21807917039595320721381829 4088984444924122635259093)
              ·
                refine ⟨95835572927909124263885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4088984444924122635259093 95835572927909124263885)
                ·
                  rfl

theorem cell22_2519628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 7].length) (baseStart_2519628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2519628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2519628 prefixEnd_2519628 := by exact prefixLift 2519628
  have htrace : WordTrace (prefixWord ++ tailWord_2519628) baseStart_2519628 baseEnd_2519628 := by
    simpa [prefixWord, tailWord_2519628, baseEnd_2519628] using wordTrace_append hprefix tailTrace_2519628
  have hstable : (prefixWord ++ tailWord_2519628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2519628).length < 2 ^ (prefixWord ++ tailWord_2519628).sum := by decide
  have hdescent : baseEnd_2519628 < baseStart_2519628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2519628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2519780 : List Nat := [2, 3, 1, 1, 1, 6, 8]
def baseStart_2519780 : Nat := 118140960795 + 2519780 * 2 ^ 59
def prefixEnd_2519780 : Nat := 4983230072969 + 3 ^ 40 * 2519780 * 2
def baseEnd_2519780 : Nat := 31947118113240903280537

theorem tailTrace_2519780 : CollatzResearch.WordTrace tailWord_2519780 prefixEnd_2519780 31947118113240903280537 := by
  unfold tailWord_2519780
  simp only [CollatzResearch.WordTrace]
  refine ⟨45951963405637439503830397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61269284540849919338440529 45951963405637439503830397)
  ·
    refine ⟨17231986277114039813936399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45951963405637439503830397 17231986277114039813936399)
    ·
      refine ⟨25847979415671059720904599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17231986277114039813936399 25847979415671059720904599)
      ·
        refine ⟨38771969123506589581356899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25847979415671059720904599 38771969123506589581356899)
        ·
          refine ⟨58157953685259884372035349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38771969123506589581356899 58157953685259884372035349)
          ·
            refine ⟨2726154078996557079939157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 58157953685259884372035349 2726154078996557079939157)
            ·
              refine ⟨31947118113240903280537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2726154078996557079939157 31947118113240903280537)
              ·
                rfl

theorem cell22_2519780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 8].length) (baseStart_2519780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2519780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2519780 prefixEnd_2519780 := by exact prefixLift 2519780
  have htrace : WordTrace (prefixWord ++ tailWord_2519780) baseStart_2519780 baseEnd_2519780 := by
    simpa [prefixWord, tailWord_2519780, baseEnd_2519780] using wordTrace_append hprefix tailTrace_2519780
  have hstable : (prefixWord ++ tailWord_2519780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2519780).length < 2 ^ (prefixWord ++ tailWord_2519780).sum := by decide
  have hdescent : baseEnd_2519780 < baseStart_2519780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2519780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2519812 : List Nat := [2, 3, 2, 2, 1, 1, 2, 1, 5, 3]
def baseStart_2519812 : Nat := 118140960795 + 2519812 * 2 ^ 59
def prefixEnd_2519812 : Nat := 4983230072969 + 3 ^ 40 * 2519812 * 2
def baseEnd_2519812 : Nat := 862583143311466971774401

theorem tailTrace_2519812 : CollatzResearch.WordTrace tailWord_2519812 prefixEnd_2519812 862583143311466971774401 := by
  unfold tailWord_2519812
  simp only [CollatzResearch.WordTrace]
  refine ⟨45952546973579474236412845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61270062631439298981883793 45952546973579474236412845)
  ·
    refine ⟨17232205115092302838654817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45952546973579474236412845 17232205115092302838654817)
    ·
      refine ⟨12924153836319227128991113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17232205115092302838654817 12924153836319227128991113)
      ·
        refine ⟨9693115377239420346743335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12924153836319227128991113 9693115377239420346743335)
        ·
          refine ⟨14539673065859130520115003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9693115377239420346743335 14539673065859130520115003)
          ·
            refine ⟨21809509598788695780172505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14539673065859130520115003 21809509598788695780172505)
            ·
              refine ⟨16357132199091521835129379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21809509598788695780172505 16357132199091521835129379)
              ·
                refine ⟨24535698298637282752694069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16357132199091521835129379 24535698298637282752694069)
                ·
                  refine ⟨2300221715497245258065069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24535698298637282752694069 2300221715497245258065069)
                  ·
                    refine ⟨862583143311466971774401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2300221715497245258065069 862583143311466971774401)
                    ·
                      rfl

theorem cell22_2519812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 5, 3].length) (baseStart_2519812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2519812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2519812 prefixEnd_2519812 := by exact prefixLift 2519812
  have htrace : WordTrace (prefixWord ++ tailWord_2519812) baseStart_2519812 baseEnd_2519812 := by
    simpa [prefixWord, tailWord_2519812, baseEnd_2519812] using wordTrace_append hprefix tailTrace_2519812
  have hstable : (prefixWord ++ tailWord_2519812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2519812).length < 2 ^ (prefixWord ++ tailWord_2519812).sum := by decide
  have hdescent : baseEnd_2519812 < baseStart_2519812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2519812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2519829 : List Nat := [1, 3, 2, 1, 2, 2, 2, 5, 1, 3]
def baseStart_2519829 : Nat := 118140960795 + 2519829 * 2 ^ 59
def prefixEnd_2519829 : Nat := 4983230072969 + 3 ^ 40 * 2519829 * 2
def baseEnd_2519829 : Nat := 862588962758884594099349

theorem tailTrace_2519829 : CollatzResearch.WordTrace tailWord_2519829 prefixEnd_2519829 862588962758884594099349 := by
  unfold tailWord_2519829
  simp only [CollatzResearch.WordTrace]
  refine ⟨91905713988097360376194541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61270475992064906917463027 91905713988097360376194541)
  ·
    refine ⟨34464642745536510141072953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91905713988097360376194541 34464642745536510141072953)
    ·
      refine ⟨25848482059152382605804715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34464642745536510141072953 25848482059152382605804715)
      ·
        refine ⟨38772723088728573908707073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25848482059152382605804715 38772723088728573908707073)
        ·
          refine ⟨29079542316546430431530305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38772723088728573908707073 29079542316546430431530305)
          ·
            refine ⟨21809656737409822823647729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29079542316546430431530305 21809656737409822823647729)
            ·
              refine ⟨16357242553057367117735797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21809656737409822823647729 16357242553057367117735797)
              ·
                refine ⟨1533491489349128167287731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16357242553057367117735797 1533491489349128167287731)
                ·
                  refine ⟨2300237234023692250931597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1533491489349128167287731 2300237234023692250931597)
                  ·
                    refine ⟨862588962758884594099349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2300237234023692250931597 862588962758884594099349)
                    ·
                      rfl

theorem cell22_2519829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 5, 1, 3].length) (baseStart_2519829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2519829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2519829 prefixEnd_2519829 := by exact prefixLift 2519829
  have htrace : WordTrace (prefixWord ++ tailWord_2519829) baseStart_2519829 baseEnd_2519829 := by
    simpa [prefixWord, tailWord_2519829, baseEnd_2519829] using wordTrace_append hprefix tailTrace_2519829
  have hstable : (prefixWord ++ tailWord_2519829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2519829).length < 2 ^ (prefixWord ++ tailWord_2519829).sum := by decide
  have hdescent : baseEnd_2519829 < baseStart_2519829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2519829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2519842 : List Nat := [3, 3, 1, 1, 2, 2, 1, 4, 5]
def baseStart_2519842 : Nat := 118140960795 + 2519842 * 2 ^ 59
def prefixEnd_2519842 : Nat := 4983230072969 + 3 ^ 40 * 2519842 * 2
def baseEnd_2519842 : Nat := 287531137641518964508103

theorem tailTrace_2519842 : CollatzResearch.WordTrace tailWord_2519842 prefixEnd_2519842 287531137641518964508103 := by
  unfold tailWord_2519842
  simp only [CollatzResearch.WordTrace]
  refine ⟨22976547034262565899104445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61270792091366842397611853 22976547034262565899104445)
  ·
    refine ⟨8616205137848462212164167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22976547034262565899104445 8616205137848462212164167)
    ·
      refine ⟨12924307706772693318246251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8616205137848462212164167 12924307706772693318246251)
      ·
        refine ⟨19386461560159039977369377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12924307706772693318246251 19386461560159039977369377)
        ·
          refine ⟨14539846170119279983027033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19386461560159039977369377 14539846170119279983027033)
          ·
            refine ⟨10904884627589459987270275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14539846170119279983027033 10904884627589459987270275)
            ·
              refine ⟨16357326941384189980905413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10904884627589459987270275 16357326941384189980905413)
              ·
                refine ⟨3066998801509535621419765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16357326941384189980905413 3066998801509535621419765)
                ·
                  refine ⟨287531137641518964508103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3066998801509535621419765 287531137641518964508103)
                  ·
                    rfl

theorem cell22_2519842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 4, 5].length) (baseStart_2519842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2519842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2519842 prefixEnd_2519842 := by exact prefixLift 2519842
  have htrace : WordTrace (prefixWord ++ tailWord_2519842) baseStart_2519842 baseEnd_2519842 := by
    simpa [prefixWord, tailWord_2519842, baseEnd_2519842] using wordTrace_append hprefix tailTrace_2519842
  have hstable : (prefixWord ++ tailWord_2519842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2519842).length < 2 ^ (prefixWord ++ tailWord_2519842).sum := by decide
  have hdescent : baseEnd_2519842 < baseStart_2519842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2519842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2519889 : List Nat := [1, 2, 2, 1, 6, 1, 1, 3, 1, 4]
def baseStart_2519889 : Nat := 118140960795 + 2519889 * 2 ^ 59
def prefixEnd_2519889 : Nat := 4983230072969 + 3 ^ 40 * 2519889 * 2
def baseEnd_2519889 : Nat := 862609501985064437599165

theorem tailTrace_2519889 : CollatzResearch.WordTrace tailWord_2519889 prefixEnd_2519889 862609501985064437599165 := by
  unfold tailWord_2519889
  simp only [CollatzResearch.WordTrace]
  refine ⟨91907902367879990623378721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61271934911919993748919147 91907902367879990623378721)
  ·
    refine ⟨68930926775909992967534041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91907902367879990623378721 68930926775909992967534041)
    ·
      refine ⟨51698195081932494725650531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68930926775909992967534041 51698195081932494725650531)
      ·
        refine ⟨77547292622898742088475797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51698195081932494725650531 77547292622898742088475797)
        ·
          refine ⟨3635029341698378535397303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 77547292622898742088475797 3635029341698378535397303)
          ·
            refine ⟨5452544012547567803095955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3635029341698378535397303 5452544012547567803095955)
            ·
              refine ⟨8178816018821351704643933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5452544012547567803095955 8178816018821351704643933)
              ·
                refine ⟨3067056007058006889241475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8178816018821351704643933 3067056007058006889241475)
                ·
                  refine ⟨4600584010587010333862213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3067056007058006889241475 4600584010587010333862213)
                  ·
                    refine ⟨862609501985064437599165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4600584010587010333862213 862609501985064437599165)
                    ·
                      rfl

theorem cell22_2519889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 3, 1, 4].length) (baseStart_2519889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2519889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2519889 prefixEnd_2519889 := by exact prefixLift 2519889
  have htrace : WordTrace (prefixWord ++ tailWord_2519889) baseStart_2519889 baseEnd_2519889 := by
    simpa [prefixWord, tailWord_2519889, baseEnd_2519889] using wordTrace_append hprefix tailTrace_2519889
  have hstable : (prefixWord ++ tailWord_2519889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2519889).length < 2 ^ (prefixWord ++ tailWord_2519889).sum := by decide
  have hdescent : baseEnd_2519889 < baseStart_2519889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2519889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2519930 : List Nat := [3, 1, 1, 1, 1, 1, 3, 1, 1, 9]
def baseStart_2519930 : Nat := 118140960795 + 2519930 * 2 ^ 59
def prefixEnd_2519930 : Nat := 4983230072969 + 3 ^ 40 * 2519930 * 2
def baseEnd_2519930 : Nat := 862623537122953997324039

theorem tailTrace_2519930 : CollatzResearch.WordTrace tailWord_2519930 prefixEnd_2519930 862623537122953997324039 := by
  unfold tailWord_2519930
  simp only [CollatzResearch.WordTrace]
  refine ⟨22977349440182863656405311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61272931840487636417080829 22977349440182863656405311)
  ·
    refine ⟨34466024160274295484607967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22977349440182863656405311 34466024160274295484607967)
    ·
      refine ⟨51699036240411443226911951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34466024160274295484607967 51699036240411443226911951)
      ·
        refine ⟨77548554360617164840367927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51699036240411443226911951 77548554360617164840367927)
        ·
          refine ⟨116322831540925747260551891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77548554360617164840367927 116322831540925747260551891)
          ·
            refine ⟨174484247311388620890827837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116322831540925747260551891 174484247311388620890827837)
            ·
              refine ⟨65431592741770732834060439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 174484247311388620890827837 65431592741770732834060439)
              ·
                refine ⟨98147389112656099251090659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65431592741770732834060439 98147389112656099251090659)
                ·
                  refine ⟨147221083668984148876635989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 98147389112656099251090659 147221083668984148876635989)
                  ·
                    refine ⟨862623537122953997324039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 147221083668984148876635989 862623537122953997324039)
                    ·
                      rfl

theorem cell22_2519930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 1, 9].length) (baseStart_2519930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2519930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2519930 prefixEnd_2519930 := by exact prefixLift 2519930
  have htrace : WordTrace (prefixWord ++ tailWord_2519930) baseStart_2519930 baseEnd_2519930 := by
    simpa [prefixWord, tailWord_2519930, baseEnd_2519930] using wordTrace_append hprefix tailTrace_2519930
  have hstable : (prefixWord ++ tailWord_2519930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2519930).length < 2 ^ (prefixWord ++ tailWord_2519930).sum := by decide
  have hdescent : baseEnd_2519930 < baseStart_2519930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2519930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2519947 : List Nat := [1, 1, 1, 1, 4, 2, 2, 2, 5, 3]
def baseStart_2519947 : Nat := 118140960795 + 2519947 * 2 ^ 59
def prefixEnd_2519947 : Nat := 4983230072969 + 3 ^ 40 * 2519947 * 2
def baseEnd_2519947 : Nat := 862629356570371619648987

theorem tailTrace_2519947 : CollatzResearch.WordTrace tailWord_2519947 prefixEnd_2519947 862629356570371619648987 := by
  unfold tailWord_2519947
  simp only [CollatzResearch.WordTrace]
  refine ⟨91910017801669866528990095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61273345201113244352660063 91910017801669866528990095)
  ·
    refine ⟨137865026702504799793485143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91910017801669866528990095 137865026702504799793485143)
    ·
      refine ⟨206797540053757199690227715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137865026702504799793485143 206797540053757199690227715)
      ·
        refine ⟨310196310080635799535341573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206797540053757199690227715 310196310080635799535341573)
        ·
          refine ⟨58161808140119212412876545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 310196310080635799535341573 58161808140119212412876545)
          ·
            refine ⟨43621356105089409309657409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58161808140119212412876545 43621356105089409309657409)
            ·
              refine ⟨32716017078817056982243057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43621356105089409309657409 32716017078817056982243057)
              ·
                refine ⟨24537012809112792736682293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32716017078817056982243057 24537012809112792736682293)
                ·
                  refine ⟨2300344950854324319063965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24537012809112792736682293 2300344950854324319063965)
                  ·
                    refine ⟨862629356570371619648987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2300344950854324319063965 862629356570371619648987)
                    ·
                      rfl

theorem cell22_2519947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 5, 3].length) (baseStart_2519947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2519947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2519947 prefixEnd_2519947 := by exact prefixLift 2519947
  have htrace : WordTrace (prefixWord ++ tailWord_2519947) baseStart_2519947 baseEnd_2519947 := by
    simpa [prefixWord, tailWord_2519947, baseEnd_2519947] using wordTrace_append hprefix tailTrace_2519947
  have hstable : (prefixWord ++ tailWord_2519947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2519947).length < 2 ^ (prefixWord ++ tailWord_2519947).sum := by decide
  have hdescent : baseEnd_2519947 < baseStart_2519947 := by decide
  rcases family_descends (prefixWord ++ tailWord_2519947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2519977 : List Nat := [1, 2, 1, 1, 1, 1, 7, 3, 5]
def baseStart_2519977 : Nat := 118140960795 + 2519977 * 2 ^ 59
def prefixEnd_2519977 : Nat := 4983230072969 + 3 ^ 40 * 2519977 * 2
def baseEnd_2519977 : Nat := 287546542061153847132965

theorem tailTrace_2519977 : CollatzResearch.WordTrace tailWord_2519977 prefixEnd_2519977 287546542061153847132965 := by
  unfold tailWord_2519977
  simp only [CollatzResearch.WordTrace]
  refine ⟨91911111991561181652582185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61274074661040787768388123 91911111991561181652582185)
  ·
    refine ⟨68933333993670886239436639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91911111991561181652582185 68933333993670886239436639)
    ·
      refine ⟨103400000990506329359154959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68933333993670886239436639 103400000990506329359154959)
      ·
        refine ⟨155100001485759494038732439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103400000990506329359154959 155100001485759494038732439)
        ·
          refine ⟨232650002228639241058098659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155100001485759494038732439 232650002228639241058098659)
          ·
            refine ⟨348975003342958861587147989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 232650002228639241058098659 348975003342958861587147989)
            ·
              refine ⟨8179101640850598318448781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 348975003342958861587147989 8179101640850598318448781)
              ·
                refine ⟨3067163115318974369418293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8179101640850598318448781 3067163115318974369418293)
                ·
                  refine ⟨287546542061153847132965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3067163115318974369418293 287546542061153847132965)
                  ·
                    rfl

theorem cell22_2519977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 3, 5].length) (baseStart_2519977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2519977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2519977 prefixEnd_2519977 := by exact prefixLift 2519977
  have htrace : WordTrace (prefixWord ++ tailWord_2519977) baseStart_2519977 baseEnd_2519977 := by
    simpa [prefixWord, tailWord_2519977, baseEnd_2519977] using wordTrace_append hprefix tailTrace_2519977
  have hstable : (prefixWord ++ tailWord_2519977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2519977).length < 2 ^ (prefixWord ++ tailWord_2519977).sum := by decide
  have hdescent : baseEnd_2519977 < baseStart_2519977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2519977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520006 : List Nat := [6, 1, 3, 1, 2, 1, 2, 2, 4]
def baseStart_2520006 : Nat := 118140960795 + 2520006 * 2 ^ 59
def prefixEnd_2520006 : Nat := 4983230072969 + 3 ^ 40 * 2520006 * 2
def baseEnd_2520006 : Nat := 287549851158705044141269

theorem tailTrace_2520006 : CollatzResearch.WordTrace tailWord_2520006 prefixEnd_2520006 287549851158705044141269 := by
  unfold tailWord_2520006
  simp only [CollatzResearch.WordTrace]
  refine ⟨2872255303389253737668371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 61274779805637413070258581 2872255303389253737668371)
  ·
    refine ⟨4308382955083880606502557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2872255303389253737668371 4308382955083880606502557)
    ·
      refine ⟨1615643608156455227438459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4308382955083880606502557 1615643608156455227438459)
      ·
        refine ⟨2423465412234682841157689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1615643608156455227438459 2423465412234682841157689)
        ·
          refine ⟨1817599059176012130868267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2423465412234682841157689 1817599059176012130868267)
          ·
            refine ⟨2726398588764018196302401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1817599059176012130868267 2726398588764018196302401)
            ·
              refine ⟨2044798941573013647226801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2726398588764018196302401 2044798941573013647226801)
              ·
                refine ⟨1533599206179760235420101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2044798941573013647226801 1533599206179760235420101)
                ·
                  refine ⟨287549851158705044141269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1533599206179760235420101 287549851158705044141269)
                  ·
                    rfl

theorem cell22_2520006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_2520006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2520006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2520006 prefixEnd_2520006 := by exact prefixLift 2520006
  have htrace : WordTrace (prefixWord ++ tailWord_2520006) baseStart_2520006 baseEnd_2520006 := by
    simpa [prefixWord, tailWord_2520006, baseEnd_2520006] using wordTrace_append hprefix tailTrace_2520006
  have hstable : (prefixWord ++ tailWord_2520006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520006).length < 2 ^ (prefixWord ++ tailWord_2520006).sum := by decide
  have hdescent : baseEnd_2520006 < baseStart_2520006 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520039 : List Nat := [1, 1, 5, 2, 2, 2, 1, 2, 6]
def baseStart_2520039 : Nat := 118140960795 + 2520039 * 2 ^ 59
def prefixEnd_2520039 : Nat := 4983230072969 + 3 ^ 40 * 2520039 * 2
def baseEnd_2520039 : Nat := 287553616683504682116235

theorem tailTrace_2520039 : CollatzResearch.WordTrace tailWord_2520039 prefixEnd_2520039 287553616683504682116235 := by
  unfold tailWord_2520039
  simp only [CollatzResearch.WordTrace]
  refine ⟨91913373317336566241339171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61275582211557710827559447 91913373317336566241339171)
  ·
    refine ⟨137870059976004849362008757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91913373317336566241339171 137870059976004849362008757)
    ·
      refine ⟨12925318122750454627688321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 137870059976004849362008757 12925318122750454627688321)
      ·
        refine ⟨9693988592062840970766241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12925318122750454627688321 9693988592062840970766241)
        ·
          refine ⟨7270491444047130728074681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9693988592062840970766241 7270491444047130728074681)
          ·
            refine ⟨5452868583035348046056011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7270491444047130728074681 5452868583035348046056011)
            ·
              refine ⟨8179302874553022069084017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5452868583035348046056011 8179302874553022069084017)
              ·
                refine ⟨6134477155914766551813013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8179302874553022069084017 6134477155914766551813013)
                ·
                  refine ⟨287553616683504682116235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6134477155914766551813013 287553616683504682116235)
                  ·
                    rfl

theorem cell22_2520039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 2, 6].length) (baseStart_2520039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2520039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2520039 prefixEnd_2520039 := by exact prefixLift 2520039
  have htrace : WordTrace (prefixWord ++ tailWord_2520039) baseStart_2520039 baseEnd_2520039 := by
    simpa [prefixWord, tailWord_2520039, baseEnd_2520039] using wordTrace_append hprefix tailTrace_2520039
  have hstable : (prefixWord ++ tailWord_2520039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520039).length < 2 ^ (prefixWord ++ tailWord_2520039).sum := by decide
  have hdescent : baseEnd_2520039 < baseStart_2520039 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520088 : List Nat := [2, 1, 2, 3, 2, 3, 3, 1, 2, 3]
def baseStart_2520088 : Nat := 118140960795 + 2520088 * 2 ^ 59
def prefixEnd_2520088 : Nat := 4983230072969 + 3 ^ 40 * 2520088 * 2
def baseEnd_2520088 : Nat := 862677623751894251873555

theorem tailTrace_2520088 : CollatzResearch.WordTrace tailWord_2520088 prefixEnd_2520088 862677623751894251873555 := by
  unfold tailWord_2520088
  simp only [CollatzResearch.WordTrace]
  refine ⟨45957580247079523804936459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61276773662772698406581945 45957580247079523804936459)
  ·
    refine ⟨68936370370619285707404689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45957580247079523804936459 68936370370619285707404689)
    ·
      refine ⟨51702277777964464280553517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68936370370619285707404689 51702277777964464280553517)
      ·
        refine ⟨19388354166736674105207569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51702277777964464280553517 19388354166736674105207569)
        ·
          refine ⟨14541265625052505578905677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19388354166736674105207569 14541265625052505578905677)
          ·
            refine ⟨5452974609394689592089629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14541265625052505578905677 5452974609394689592089629)
            ·
              refine ⟨2044865478523008597033611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5452974609394689592089629 2044865478523008597033611)
              ·
                refine ⟨3067298217784512895550417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2044865478523008597033611 3067298217784512895550417)
                ·
                  refine ⟨2300473663338384671662813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3067298217784512895550417 2300473663338384671662813)
                  ·
                    refine ⟨862677623751894251873555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2300473663338384671662813 862677623751894251873555)
                    ·
                      rfl

theorem cell22_2520088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 3, 1, 2, 3].length) (baseStart_2520088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2520088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2520088 prefixEnd_2520088 := by exact prefixLift 2520088
  have htrace : WordTrace (prefixWord ++ tailWord_2520088) baseStart_2520088 baseEnd_2520088 := by
    simpa [prefixWord, tailWord_2520088, baseEnd_2520088] using wordTrace_append hprefix tailTrace_2520088
  have hstable : (prefixWord ++ tailWord_2520088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520088).length < 2 ^ (prefixWord ++ tailWord_2520088).sum := by decide
  have hdescent : baseEnd_2520088 < baseStart_2520088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520112 : List Nat := [2, 1, 1, 1, 2, 4, 1, 1, 9]
def baseStart_2520112 : Nat := 118140960795 + 2520112 * 2 ^ 59
def prefixEnd_2520112 : Nat := 4983230072969 + 3 ^ 40 * 2520112 * 2
def baseEnd_2520112 : Nat := 287561946480788729757827

theorem tailTrace_2520112 : CollatzResearch.WordTrace tailWord_2520112 prefixEnd_2520112 287561946480788729757827 := by
  unfold tailWord_2520112
  simp only [CollatzResearch.WordTrace]
  refine ⟨45958017923036049854373295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61277357230714733139164393 45958017923036049854373295)
  ·
    refine ⟨68937026884554074781559943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45958017923036049854373295 68937026884554074781559943)
    ·
      refine ⟨103405540326831112172339915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68937026884554074781559943 103405540326831112172339915)
      ·
        refine ⟨155108310490246668258509873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103405540326831112172339915 155108310490246668258509873)
        ·
          refine ⟨116331232867685001193882405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155108310490246668258509873 116331232867685001193882405)
          ·
            refine ⟨21812106162690937723852951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 116331232867685001193882405 21812106162690937723852951)
            ·
              refine ⟨32718159244036406585779427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21812106162690937723852951 32718159244036406585779427)
              ·
                refine ⟨49077238866054609878669141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32718159244036406585779427 49077238866054609878669141)
                ·
                  refine ⟨287561946480788729757827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 49077238866054609878669141 287561946480788729757827)
                  ·
                    rfl

theorem cell22_2520112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 9].length) (baseStart_2520112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2520112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2520112 prefixEnd_2520112 := by exact prefixLift 2520112
  have htrace : WordTrace (prefixWord ++ tailWord_2520112) baseStart_2520112 baseEnd_2520112 := by
    simpa [prefixWord, tailWord_2520112, baseEnd_2520112] using wordTrace_append hprefix tailTrace_2520112
  have hstable : (prefixWord ++ tailWord_2520112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520112).length < 2 ^ (prefixWord ++ tailWord_2520112).sum := by decide
  have hdescent : baseEnd_2520112 < baseStart_2520112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520146 : List Nat := [3, 2, 2, 1, 3, 2, 1, 3, 5]
def baseStart_2520146 : Nat := 118140960795 + 2520146 * 2 ^ 59
def prefixEnd_2520146 : Nat := 4983230072969 + 3 ^ 40 * 2520146 * 2
def baseEnd_2520146 : Nat := 287565826112400477974459

theorem tailTrace_2520146 : CollatzResearch.WordTrace tailWord_2520146 prefixEnd_2520146 287565826112400477974459 := by
  unfold tailWord_2520146
  simp only [CollatzResearch.WordTrace]
  refine ⟨22979318981987230878871073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61278183951965949010322861 22979318981987230878871073)
  ·
    refine ⟨17234489236490423159153305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22979318981987230878871073 17234489236490423159153305)
    ·
      refine ⟨12925866927367817369364979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17234489236490423159153305 12925866927367817369364979)
      ·
        refine ⟨19388800391051726054047469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12925866927367817369364979 19388800391051726054047469)
        ·
          refine ⟨7270800146644397270267801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19388800391051726054047469 7270800146644397270267801)
          ·
            refine ⟨5453100109983297952700851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7270800146644397270267801 5453100109983297952700851)
            ·
              refine ⟨8179650164974946929051277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5453100109983297952700851 8179650164974946929051277)
              ·
                refine ⟨3067368811865605098394229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8179650164974946929051277 3067368811865605098394229)
                ·
                  refine ⟨287565826112400477974459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3067368811865605098394229 287565826112400477974459)
                  ·
                    rfl

theorem cell22_2520146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 3, 5].length) (baseStart_2520146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2520146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2520146 prefixEnd_2520146 := by exact prefixLift 2520146
  have htrace : WordTrace (prefixWord ++ tailWord_2520146) baseStart_2520146 baseEnd_2520146 := by
    simpa [prefixWord, tailWord_2520146, baseEnd_2520146] using wordTrace_append hprefix tailTrace_2520146
  have hstable : (prefixWord ++ tailWord_2520146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520146).length < 2 ^ (prefixWord ++ tailWord_2520146).sum := by decide
  have hdescent : baseEnd_2520146 < baseStart_2520146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520159 : List Nat := [1, 1, 2, 3, 1, 1, 5, 1, 3, 4]
def baseStart_2520159 : Nat := 118140960795 + 2520159 * 2 ^ 59
def prefixEnd_2520159 : Nat := 4983230072969 + 3 ^ 40 * 2520159 * 2
def baseEnd_2520159 : Nat := 862701928502873733348337

theorem tailTrace_2520159 : CollatzResearch.WordTrace tailWord_2520159 prefixEnd_2520159 862701928502873733348337 := by
  unfold tailWord_2520159
  simp only [CollatzResearch.WordTrace]
  refine ⟨91917750076901826735707531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61278500051267884490471687 91917750076901826735707531)
  ·
    refine ⟨137876625115352740103561297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91917750076901826735707531 137876625115352740103561297)
    ·
      refine ⟨103407468836514555077670973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137876625115352740103561297 103407468836514555077670973)
      ·
        refine ⟨38777800813692958154126615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103407468836514555077670973 38777800813692958154126615)
        ·
          refine ⟨58166701220539437231189923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38777800813692958154126615 58166701220539437231189923)
          ·
            refine ⟨87250051830809155846784885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58166701220539437231189923 87250051830809155846784885)
            ·
              refine ⟨8179692359138358360636083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 87250051830809155846784885 8179692359138358360636083)
              ·
                refine ⟨12269538538707537540954125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8179692359138358360636083 12269538538707537540954125)
                ·
                  refine ⟨4601076952015326577857797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12269538538707537540954125 4601076952015326577857797)
                  ·
                    refine ⟨862701928502873733348337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4601076952015326577857797 862701928502873733348337)
                    ·
                      rfl

theorem cell22_2520159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 1, 3, 4].length) (baseStart_2520159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2520159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2520159 prefixEnd_2520159 := by exact prefixLift 2520159
  have htrace : WordTrace (prefixWord ++ tailWord_2520159) baseStart_2520159 baseEnd_2520159 := by
    simpa [prefixWord, tailWord_2520159, baseEnd_2520159] using wordTrace_append hprefix tailTrace_2520159
  have hstable : (prefixWord ++ tailWord_2520159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520159).length < 2 ^ (prefixWord ++ tailWord_2520159).sum := by decide
  have hdescent : baseEnd_2520159 < baseStart_2520159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520189 : List Nat := [1, 4, 1, 1, 3, 1, 1, 2, 3, 5]
def baseStart_2520189 : Nat := 118140960795 + 2520189 * 2 ^ 59
def prefixEnd_2520189 : Nat := 4983230072969 + 3 ^ 40 * 2520189 * 2
def baseEnd_2520189 : Nat := 862712198115963655098245

theorem tailTrace_2520189 : CollatzResearch.WordTrace tailWord_2520189 prefixEnd_2520189 862712198115963655098245 := by
  unfold tailWord_2520189
  simp only [CollatzResearch.WordTrace]
  refine ⟨91918844266793141859299621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61279229511195427906199747 91918844266793141859299621)
  ·
    refine ⟨17234783300023714098618679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91918844266793141859299621 17234783300023714098618679)
    ·
      refine ⟨25852174950035571147928019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17234783300023714098618679 25852174950035571147928019)
      ·
        refine ⟨38778262425053356721892029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25852174950035571147928019 38778262425053356721892029)
        ·
          refine ⟨14541848409395008770709511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38778262425053356721892029 14541848409395008770709511)
          ·
            refine ⟨21812772614092513156064267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14541848409395008770709511 21812772614092513156064267)
            ·
              refine ⟨32719158921138769734096401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21812772614092513156064267 32719158921138769734096401)
              ·
                refine ⟨24539369190854077300572301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32719158921138769734096401 24539369190854077300572301)
                ·
                  refine ⟨9202263446570278987714613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24539369190854077300572301 9202263446570278987714613)
                  ·
                    refine ⟨862712198115963655098245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9202263446570278987714613 862712198115963655098245)
                    ·
                      rfl

theorem cell22_2520189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 3, 5].length) (baseStart_2520189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2520189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2520189 prefixEnd_2520189 := by exact prefixLift 2520189
  have htrace : WordTrace (prefixWord ++ tailWord_2520189) baseStart_2520189 baseEnd_2520189 := by
    simpa [prefixWord, tailWord_2520189, baseEnd_2520189] using wordTrace_append hprefix tailTrace_2520189
  have hstable : (prefixWord ++ tailWord_2520189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520189).length < 2 ^ (prefixWord ++ tailWord_2520189).sum := by decide
  have hdescent : baseEnd_2520189 < baseStart_2520189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520204 : List Nat := [2, 2, 1, 2, 1, 1, 1, 4, 4, 4]
def baseStart_2520204 : Nat := 118140960795 + 2520204 * 2 ^ 59
def prefixEnd_2520204 : Nat := 4983230072969 + 3 ^ 40 * 2520204 * 2
def baseEnd_2520204 : Nat := 862717332922508615973199

theorem tailTrace_2520204 : CollatzResearch.WordTrace tailWord_2520204 prefixEnd_2520204 862717332922508615973199 := by
  unfold tailWord_2520204
  simp only [CollatzResearch.WordTrace]
  refine ⟨45959695680869399710547833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61279594241159199614063777 45959695680869399710547833)
  ·
    refine ⟨34469771760652049782910875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45959695680869399710547833 34469771760652049782910875)
    ·
      refine ⟨51704657640978074674366313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34469771760652049782910875 51704657640978074674366313)
      ·
        refine ⟨38778493230733556005774735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51704657640978074674366313 38778493230733556005774735)
        ·
          refine ⟨58167739846100334008662103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38778493230733556005774735 58167739846100334008662103)
          ·
            refine ⟨87251609769150501012993155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58167739846100334008662103 87251609769150501012993155)
            ·
              refine ⟨130877414653725751519489733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87251609769150501012993155 130877414653725751519489733)
              ·
                refine ⟨24539515247573578409904325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 130877414653725751519489733 24539515247573578409904325)
                ·
                  refine ⟨4601159108920045951857061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24539515247573578409904325 4601159108920045951857061)
                  ·
                    refine ⟨862717332922508615973199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4601159108920045951857061 862717332922508615973199)
                    ·
                      rfl

theorem cell22_2520204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 4, 4].length) (baseStart_2520204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2520204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2520204 prefixEnd_2520204 := by exact prefixLift 2520204
  have htrace : WordTrace (prefixWord ++ tailWord_2520204) baseStart_2520204 baseEnd_2520204 := by
    simpa [prefixWord, tailWord_2520204, baseEnd_2520204] using wordTrace_append hprefix tailTrace_2520204
  have hstable : (prefixWord ++ tailWord_2520204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520204).length < 2 ^ (prefixWord ++ tailWord_2520204).sum := by decide
  have hdescent : baseEnd_2520204 < baseStart_2520204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520206 : List Nat := [4, 1, 1, 3, 2, 1, 1, 3, 1, 5]
def baseStart_2520206 : Nat := 118140960795 + 2520206 * 2 ^ 59
def prefixEnd_2520206 : Nat := 4983230072969 + 3 ^ 40 * 2520206 * 2
def baseEnd_2520206 : Nat := 862718017563381277423193

theorem tailTrace_2520206 : CollatzResearch.WordTrace tailWord_2520206 prefixEnd_2520206 862718017563381277423193 := by
  unfold tailWord_2520206
  simp only [CollatzResearch.WordTrace]
  refine ⟨11489933038466444220333559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61279642871821035841778981 11489933038466444220333559)
  ·
    refine ⟨17234899557699666330500339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11489933038466444220333559 17234899557699666330500339)
    ·
      refine ⟨25852349336549499495750509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17234899557699666330500339 25852349336549499495750509)
      ·
        refine ⟨9694631001206062310906441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25852349336549499495750509 9694631001206062310906441)
        ·
          refine ⟨7270973250904546733179831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9694631001206062310906441 7270973250904546733179831)
          ·
            refine ⟨10906459876356820099769747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7270973250904546733179831 10906459876356820099769747)
            ·
              refine ⟨16359689814535230149654621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10906459876356820099769747 16359689814535230149654621)
              ·
                refine ⟨6134883680450711306120483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16359689814535230149654621 6134883680450711306120483)
                ·
                  refine ⟨9202325520676066959180725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6134883680450711306120483 9202325520676066959180725)
                  ·
                    refine ⟨862718017563381277423193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9202325520676066959180725 862718017563381277423193)
                    ·
                      rfl

theorem cell22_2520206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 3, 1, 5].length) (baseStart_2520206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2520206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2520206 prefixEnd_2520206 := by exact prefixLift 2520206
  have htrace : WordTrace (prefixWord ++ tailWord_2520206) baseStart_2520206 baseEnd_2520206 := by
    simpa [prefixWord, tailWord_2520206, baseEnd_2520206] using wordTrace_append hprefix tailTrace_2520206
  have hstable : (prefixWord ++ tailWord_2520206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520206).length < 2 ^ (prefixWord ++ tailWord_2520206).sum := by decide
  have hdescent : baseEnd_2520206 < baseStart_2520206 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520257 : List Nat := [1, 2, 6, 1, 1, 2, 3, 1, 2, 3]
def baseStart_2520257 : Nat := 118140960795 + 2520257 * 2 ^ 59
def prefixEnd_2520257 : Nat := 4983230072969 + 3 ^ 40 * 2520257 * 2
def baseEnd_2520257 : Nat := 862735475905634144398037

theorem tailTrace_2520257 : CollatzResearch.WordTrace tailWord_2520257 prefixEnd_2520257 862735475905634144398037 := by
  unfold tailWord_2520257
  simp only [CollatzResearch.WordTrace]
  refine ⟨91921324430546789472775025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61280882953697859648516683 91921324430546789472775025)
  ·
    refine ⟨68940993322910092104581269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91921324430546789472775025 68940993322910092104581269)
    ·
      refine ⟨3231609062011410567402247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 68940993322910092104581269 3231609062011410567402247)
      ·
        refine ⟨4847413593017115851103371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3231609062011410567402247 4847413593017115851103371)
        ·
          refine ⟨7271120389525673776655057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4847413593017115851103371 7271120389525673776655057)
          ·
            refine ⟨5453340292144255332491293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7271120389525673776655057 5453340292144255332491293)
            ·
              refine ⟨2045002609554095749684235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5453340292144255332491293 2045002609554095749684235)
              ·
                refine ⟨3067503914331143624526353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2045002609554095749684235 3067503914331143624526353)
                ·
                  refine ⟨2300627935748357718394765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3067503914331143624526353 2300627935748357718394765)
                  ·
                    refine ⟨862735475905634144398037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2300627935748357718394765 862735475905634144398037)
                    ·
                      rfl

theorem cell22_2520257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_2520257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2520257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2520257 prefixEnd_2520257 := by exact prefixLift 2520257
  have htrace : WordTrace (prefixWord ++ tailWord_2520257) baseStart_2520257 baseEnd_2520257 := by
    simpa [prefixWord, tailWord_2520257, baseEnd_2520257] using wordTrace_append hprefix tailTrace_2520257
  have hstable : (prefixWord ++ tailWord_2520257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520257).length < 2 ^ (prefixWord ++ tailWord_2520257).sum := by decide
  have hdescent : baseEnd_2520257 < baseStart_2520257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520270 : List Nat := [4, 1, 1, 1, 6, 1, 2, 6]
def baseStart_2520270 : Nat := 118140960795 + 2520270 * 2 ^ 59
def prefixEnd_2520270 : Nat := 4983230072969 + 3 ^ 40 * 2520270 * 2
def baseEnd_2520270 : Nat := 95859991785700715980333

theorem tailTrace_2520270 : CollatzResearch.WordTrace tailWord_2520270 prefixEnd_2520270 95859991785700715980333 := by
  unfold tailWord_2520270
  simp only [CollatzResearch.WordTrace]
  refine ⟨11490224822437461586624783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61281199052999795128665509 11490224822437461586624783)
  ·
    refine ⟨17235337233656192379937175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11490224822437461586624783 17235337233656192379937175)
    ·
      refine ⟨25853005850484288569905763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17235337233656192379937175 25853005850484288569905763)
      ·
        refine ⟨38779508775726432854858645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25853005850484288569905763 38779508775726432854858645)
        ·
          refine ⟨1817789473862176540071499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 38779508775726432854858645 1817789473862176540071499)
          ·
            refine ⟨2726684210793264810107249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1817789473862176540071499 2726684210793264810107249)
            ·
              refine ⟨2045013158094948607580437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2726684210793264810107249 2045013158094948607580437)
              ·
                refine ⟨95859991785700715980333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2045013158094948607580437 95859991785700715980333)
                ·
                  rfl

theorem cell22_2520270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 2, 6].length) (baseStart_2520270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2520270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2520270 prefixEnd_2520270 := by exact prefixLift 2520270
  have htrace : WordTrace (prefixWord ++ tailWord_2520270) baseStart_2520270 baseEnd_2520270 := by
    simpa [prefixWord, tailWord_2520270, baseEnd_2520270] using wordTrace_append hprefix tailTrace_2520270
  have hstable : (prefixWord ++ tailWord_2520270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520270).length < 2 ^ (prefixWord ++ tailWord_2520270).sum := by decide
  have hdescent : baseEnd_2520270 < baseStart_2520270 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520279 : List Nat := [1, 1, 3, 2, 1, 2, 2, 2, 1, 7]
def baseStart_2520279 : Nat := 118140960795 + 2520279 * 2 ^ 59
def prefixEnd_2520279 : Nat := 4983230072969 + 3 ^ 40 * 2520279 * 2
def baseEnd_2520279 : Nat := 862743006955233420347969

theorem tailTrace_2520279 : CollatzResearch.WordTrace tailWord_2520279 prefixEnd_2520279 862743006955233420347969 := by
  unfold tailWord_2520279
  simp only [CollatzResearch.WordTrace]
  refine ⟨91922126836467087230075891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61281417890978058153383927 91922126836467087230075891)
  ·
    refine ⟨137883190254700630845113837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91922126836467087230075891 137883190254700630845113837)
    ·
      refine ⟨51706196345512736566917689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137883190254700630845113837 51706196345512736566917689)
      ·
        refine ⟨38779647259134552425188267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51706196345512736566917689 38779647259134552425188267)
        ·
          refine ⟨58169470888701828637782401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38779647259134552425188267 58169470888701828637782401)
          ·
            refine ⟨43627103166526371478336801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58169470888701828637782401 43627103166526371478336801)
            ·
              refine ⟨32720327374894778608752601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43627103166526371478336801 32720327374894778608752601)
              ·
                refine ⟨24540245531171083956564451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32720327374894778608752601 24540245531171083956564451)
                ·
                  refine ⟨36810368296756625934846677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24540245531171083956564451 36810368296756625934846677)
                  ·
                    refine ⟨862743006955233420347969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36810368296756625934846677 862743006955233420347969)
                    ·
                      rfl

theorem cell22_2520279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 7].length) (baseStart_2520279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2520279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2520279 prefixEnd_2520279 := by exact prefixLift 2520279
  have htrace : WordTrace (prefixWord ++ tailWord_2520279) baseStart_2520279 baseEnd_2520279 := by
    simpa [prefixWord, tailWord_2520279, baseEnd_2520279] using wordTrace_append hprefix tailTrace_2520279
  have hstable : (prefixWord ++ tailWord_2520279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520279).length < 2 ^ (prefixWord ++ tailWord_2520279).sum := by decide
  have hdescent : baseEnd_2520279 < baseStart_2520279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520308 : List Nat := [2, 6, 1, 2, 2, 1, 2, 1, 2, 3]
def baseStart_2520308 : Nat := 118140960795 + 2520308 * 2 ^ 59
def prefixEnd_2520308 : Nat := 4983230072969 + 3 ^ 40 * 2520308 * 2
def baseEnd_2520308 : Nat := 862752934247887011372881

theorem tailTrace_2520308 : CollatzResearch.WordTrace tailWord_2520308 prefixEnd_2520308 862752934247887011372881 := by
  unfold tailWord_2520308
  simp only [CollatzResearch.WordTrace]
  refine ⟨45961592276681012591440789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61282123035574683455254385 45961592276681012591440789)
  ·
    refine ⟨2154449637969422465223787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 45961592276681012591440789 2154449637969422465223787)
    ·
      refine ⟨3231674456954133697835681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2154449637969422465223787 3231674456954133697835681)
      ·
        refine ⟨2423755842715600273376761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3231674456954133697835681 2423755842715600273376761)
        ·
          refine ⟨1817816882036700205032571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2423755842715600273376761 1817816882036700205032571)
          ·
            refine ⟨2726725323055050307548857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1817816882036700205032571 2726725323055050307548857)
            ·
              refine ⟨2045043992291287730661643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2726725323055050307548857 2045043992291287730661643)
              ·
                refine ⟨3067565988436931595992465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2045043992291287730661643 3067565988436931595992465)
                ·
                  refine ⟨2300674491327698696994349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3067565988436931595992465 2300674491327698696994349)
                  ·
                    refine ⟨862752934247887011372881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2300674491327698696994349 862752934247887011372881)
                    ·
                      rfl

theorem cell22_2520308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_2520308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2520308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2520308 prefixEnd_2520308 := by exact prefixLift 2520308
  have htrace : WordTrace (prefixWord ++ tailWord_2520308) baseStart_2520308 baseEnd_2520308 := by
    simpa [prefixWord, tailWord_2520308, baseEnd_2520308] using wordTrace_append hprefix tailTrace_2520308
  have hstable : (prefixWord ++ tailWord_2520308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520308).length < 2 ^ (prefixWord ++ tailWord_2520308).sum := by decide
  have hdescent : baseEnd_2520308 < baseStart_2520308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520328 : List Nat := [2, 1, 3, 2, 4, 1, 1, 1, 3, 4]
def baseStart_2520328 : Nat := 118140960795 + 2520328 * 2 ^ 59
def prefixEnd_2520328 : Nat := 4983230072969 + 3 ^ 40 * 2520328 * 2
def baseEnd_2520328 : Nat := 862759780656613625872819

theorem tailTrace_2520328 : CollatzResearch.WordTrace tailWord_2520328 prefixEnd_2520328 862759780656613625872819 := by
  unfold tailWord_2520328
  simp only [CollatzResearch.WordTrace]
  refine ⟨45961957006644784299304819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61282609342193045732406425 45961957006644784299304819)
  ·
    refine ⟨68942935509967176448957229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45961957006644784299304819 68942935509967176448957229)
    ·
      refine ⟨25853600816237691168358961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68942935509967176448957229 25853600816237691168358961)
      ·
        refine ⟨19390200612178268376269221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25853600816237691168358961 19390200612178268376269221)
        ·
          refine ⟨3635662614783425320550479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19390200612178268376269221 3635662614783425320550479)
          ·
            refine ⟨5453493922175137980825719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3635662614783425320550479 5453493922175137980825719)
            ·
              refine ⟨8180240883262706971238579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5453493922175137980825719 8180240883262706971238579)
              ·
                refine ⟨12270361324894060456857869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8180240883262706971238579 12270361324894060456857869)
                ·
                  refine ⟨4601385496835272671321701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12270361324894060456857869 4601385496835272671321701)
                  ·
                    refine ⟨862759780656613625872819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4601385496835272671321701 862759780656613625872819)
                    ·
                      rfl

theorem cell22_2520328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 1, 3, 4].length) (baseStart_2520328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2520328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2520328 prefixEnd_2520328 := by exact prefixLift 2520328
  have htrace : WordTrace (prefixWord ++ tailWord_2520328) baseStart_2520328 baseEnd_2520328 := by
    simpa [prefixWord, tailWord_2520328, baseEnd_2520328] using wordTrace_append hprefix tailTrace_2520328
  have hstable : (prefixWord ++ tailWord_2520328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520328).length < 2 ^ (prefixWord ++ tailWord_2520328).sum := by decide
  have hdescent : baseEnd_2520328 < baseStart_2520328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520343 : List Nat := [1, 1, 3, 4, 1, 1, 2, 5, 4]
def baseStart_2520343 : Nat := 118140960795 + 2520343 * 2 ^ 59
def prefixEnd_2520343 : Nat := 4983230072969 + 3 ^ 40 * 2520343 * 2
def baseEnd_2520343 : Nat := 287588305154386195582591

theorem tailTrace_2520343 : CollatzResearch.WordTrace tailWord_2520343 prefixEnd_2520343 287588305154386195582591 := by
  unfold tailWord_2520343
  simp only [CollatzResearch.WordTrace]
  refine ⟨91924461108235226160405683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61282974072156817440270455 91924461108235226160405683)
  ·
    refine ⟨137886691662352839240608525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91924461108235226160405683 137886691662352839240608525)
    ·
      refine ⟨51707509373382314715228197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137886691662352839240608525 51707509373382314715228197)
      ·
        refine ⟨9695158007509184009105287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51707509373382314715228197 9695158007509184009105287)
        ·
          refine ⟨14542737011263776013657931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9695158007509184009105287 14542737011263776013657931)
          ·
            refine ⟨21814105516895664020486897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14542737011263776013657931 21814105516895664020486897)
            ·
              refine ⟨16360579137671748015365173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21814105516895664020486897 16360579137671748015365173)
              ·
                refine ⟨1533804294156726376440485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16360579137671748015365173 1533804294156726376440485)
                ·
                  refine ⟨287588305154386195582591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1533804294156726376440485 287588305154386195582591)
                  ·
                    rfl

theorem cell22_2520343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 5, 4].length) (baseStart_2520343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2520343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2520343 prefixEnd_2520343 := by exact prefixLift 2520343
  have htrace : WordTrace (prefixWord ++ tailWord_2520343) baseStart_2520343 baseEnd_2520343 := by
    simpa [prefixWord, tailWord_2520343, baseEnd_2520343] using wordTrace_append hprefix tailTrace_2520343
  have hstable : (prefixWord ++ tailWord_2520343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520343).length < 2 ^ (prefixWord ++ tailWord_2520343).sum := by decide
  have hdescent : baseEnd_2520343 < baseStart_2520343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520360 : List Nat := [2, 1, 5, 1, 2, 2, 1, 4, 4]
def baseStart_2520360 : Nat := 118140960795 + 2520360 * 2 ^ 59
def prefixEnd_2520360 : Nat := 4983230072969 + 3 ^ 40 * 2520360 * 2
def baseEnd_2520360 : Nat := 287590244970192069690907

theorem tailTrace_2520360 : CollatzResearch.WordTrace tailWord_2520360 prefixEnd_2520360 287590244970192069690907 := by
  unfold tailWord_2520360
  simp only [CollatzResearch.WordTrace]
  refine ⟨45962540574586819031887267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61283387432782425375849689 45962540574586819031887267)
  ·
    refine ⟨68943810861880228547830901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45962540574586819031887267 68943810861880228547830901)
    ·
      refine ⟨6463482268301271426359147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 68943810861880228547830901 6463482268301271426359147)
      ·
        refine ⟨9695223402451907139538721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6463482268301271426359147 9695223402451907139538721)
        ·
          refine ⟨7271417551838930354654041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9695223402451907139538721 7271417551838930354654041)
          ·
            refine ⟨5453563163879197765990531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7271417551838930354654041 5453563163879197765990531)
            ·
              refine ⟨8180344745818796648985797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5453563163879197765990531 8180344745818796648985797)
              ·
                refine ⟨1533814639841024371684837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8180344745818796648985797 1533814639841024371684837)
                ·
                  refine ⟨287590244970192069690907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1533814639841024371684837 287590244970192069690907)
                  ·
                    rfl

theorem cell22_2520360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 4, 4].length) (baseStart_2520360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2520360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2520360 prefixEnd_2520360 := by exact prefixLift 2520360
  have htrace : WordTrace (prefixWord ++ tailWord_2520360) baseStart_2520360 baseEnd_2520360 := by
    simpa [prefixWord, tailWord_2520360, baseEnd_2520360] using wordTrace_append hprefix tailTrace_2520360
  have hstable : (prefixWord ++ tailWord_2520360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520360).length < 2 ^ (prefixWord ++ tailWord_2520360).sum := by decide
  have hdescent : baseEnd_2520360 < baseStart_2520360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520371 : List Nat := [1, 1, 1, 2, 5, 2, 3, 7]
def baseStart_2520371 : Nat := 118140960795 + 2520371 * 2 ^ 59
def prefixEnd_2520371 : Nat := 4983230072969 + 3 ^ 40 * 2520371 * 2
def baseEnd_2520371 : Nat := 95863833381708427449743

theorem tailTrace_2520371 : CollatzResearch.WordTrace tailWord_2520371 prefixEnd_2520371 95863833381708427449743 := by
  unfold tailWord_2520371
  simp only [CollatzResearch.WordTrace]
  refine ⟨91925482352133786942424967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61283654901422524628283311 91925482352133786942424967)
  ·
    refine ⟨137888223528200680413637451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91925482352133786942424967 137888223528200680413637451)
    ·
      refine ⟨206832335292301020620456177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137888223528200680413637451 206832335292301020620456177)
      ·
        refine ⟨155124251469225765465342133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 206832335292301020620456177 155124251469225765465342133)
        ·
          refine ⟨14542898575239915512375825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 155124251469225765465342133 14542898575239915512375825)
          ·
            refine ⟨10907173931429936634281869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14542898575239915512375825 10907173931429936634281869)
            ·
              refine ⟨4090190224286226237855701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10907173931429936634281869 4090190224286226237855701)
              ·
                refine ⟨95863833381708427449743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4090190224286226237855701 95863833381708427449743)
                ·
                  rfl

theorem cell22_2520371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 7].length) (baseStart_2520371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2520371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2520371 prefixEnd_2520371 := by exact prefixLift 2520371
  have htrace : WordTrace (prefixWord ++ tailWord_2520371) baseStart_2520371 baseEnd_2520371 := by
    simpa [prefixWord, tailWord_2520371, baseEnd_2520371] using wordTrace_append hprefix tailTrace_2520371
  have hstable : (prefixWord ++ tailWord_2520371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520371).length < 2 ^ (prefixWord ++ tailWord_2520371).sum := by decide
  have hdescent : baseEnd_2520371 < baseStart_2520371 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520420 : List Nat := [2, 3, 1, 1, 3, 3, 2, 1, 3, 3]
def baseStart_2520420 : Nat := 118140960795 + 2520420 * 2 ^ 59
def prefixEnd_2520420 : Nat := 4983230072969 + 3 ^ 40 * 2520420 * 2
def baseEnd_2520420 : Nat := 862791274136756052572537

theorem tailTrace_2520420 : CollatzResearch.WordTrace tailWord_2520420 prefixEnd_2520420 862791274136756052572537 := by
  unfold tailWord_2520420
  simp only [CollatzResearch.WordTrace]
  refine ⟨45963634764478134155479357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61284846352637512207305809 45963634764478134155479357)
  ·
    refine ⟨17236363036679300308304759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45963634764478134155479357 17236363036679300308304759)
    ·
      refine ⟨25854544555018950462457139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17236363036679300308304759 25854544555018950462457139)
      ·
        refine ⟨38781816832528425693685709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25854544555018950462457139 38781816832528425693685709)
        ·
          refine ⟨14543181312198159635132141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38781816832528425693685709 14543181312198159635132141)
          ·
            refine ⟨5453692992074309863174553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14543181312198159635132141 5453692992074309863174553)
            ·
              refine ⟨4090269744055732397380915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5453692992074309863174553 4090269744055732397380915)
              ·
                refine ⟨6135404616083598596071373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4090269744055732397380915 6135404616083598596071373)
                ·
                  refine ⟨2300776731031349473526765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6135404616083598596071373 2300776731031349473526765)
                  ·
                    refine ⟨862791274136756052572537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2300776731031349473526765 862791274136756052572537)
                    ·
                      rfl

theorem cell22_2520420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 1, 3, 3].length) (baseStart_2520420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2520420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2520420 prefixEnd_2520420 := by exact prefixLift 2520420
  have htrace : WordTrace (prefixWord ++ tailWord_2520420) baseStart_2520420 baseEnd_2520420 := by
    simpa [prefixWord, tailWord_2520420, baseEnd_2520420] using wordTrace_append hprefix tailTrace_2520420
  have hstable : (prefixWord ++ tailWord_2520420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520420).length < 2 ^ (prefixWord ++ tailWord_2520420).sum := by decide
  have hdescent : baseEnd_2520420 < baseStart_2520420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520431 : List Nat := [1, 1, 2, 1, 3, 1, 3, 3, 2, 5]
def baseStart_2520431 : Nat := 118140960795 + 2520431 * 2 ^ 59
def prefixEnd_2520431 : Nat := 4983230072969 + 3 ^ 40 * 2520431 * 2
def baseEnd_2520431 : Nat := 862795039661555690547503

theorem tailTrace_2520431 : CollatzResearch.WordTrace tailWord_2520431 prefixEnd_2520431 862795039661555690547503 := by
  unfold tailWord_2520431
  simp only [CollatzResearch.WordTrace]
  refine ⟨91927670731916417189609147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61285113821277611459739431 91927670731916417189609147)
  ·
    refine ⟨137891506097874625784413721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91927670731916417189609147 137891506097874625784413721)
    ·
      refine ⟨103418629573405969338310291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137891506097874625784413721 103418629573405969338310291)
      ·
        refine ⟨155127944360108954007465437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103418629573405969338310291 155127944360108954007465437)
        ·
          refine ⟨58172979135040857752799539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 155127944360108954007465437 58172979135040857752799539)
          ·
            refine ⟨87259468702561286629199309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58172979135040857752799539 87259468702561286629199309)
            ·
              refine ⟨32722300763460482485949741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87259468702561286629199309 32722300763460482485949741)
              ·
                refine ⟨12270862786297680932231153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32722300763460482485949741 12270862786297680932231153)
                ·
                  refine ⟨9203147089723260699173365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12270862786297680932231153 9203147089723260699173365)
                  ·
                    refine ⟨862795039661555690547503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9203147089723260699173365 862795039661555690547503)
                    ·
                      rfl

theorem cell22_2520431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 3, 2, 5].length) (baseStart_2520431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2520431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2520431 prefixEnd_2520431 := by exact prefixLift 2520431
  have htrace : WordTrace (prefixWord ++ tailWord_2520431) baseStart_2520431 baseEnd_2520431 := by
    simpa [prefixWord, tailWord_2520431, baseEnd_2520431] using wordTrace_append hprefix tailTrace_2520431
  have hstable : (prefixWord ++ tailWord_2520431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520431).length < 2 ^ (prefixWord ++ tailWord_2520431).sum := by decide
  have hdescent : baseEnd_2520431 < baseStart_2520431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520450 : List Nat := [3, 4, 2, 1, 1, 1, 1, 2, 7]
def baseStart_2520450 : Nat := 118140960795 + 2520450 * 2 ^ 59
def prefixEnd_2520450 : Nat := 4983230072969 + 3 ^ 40 * 2520450 * 2
def baseEnd_2520450 : Nat := 287600514583281991440815

theorem tailTrace_2520450 : CollatzResearch.WordTrace tailWord_2520450 prefixEnd_2520450 287600514583281991440815 := by
  unfold tailWord_2520450
  simp only [CollatzResearch.WordTrace]
  refine ⟨22982090929711895858637701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61285575812565055623033869 22982090929711895858637701)
  ·
    refine ⟨4309142049320980473494569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22982090929711895858637701 4309142049320980473494569)
    ·
      refine ⟨3231856536990735355120927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4309142049320980473494569 3231856536990735355120927)
      ·
        refine ⟨4847784805486103032681391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3231856536990735355120927 4847784805486103032681391)
        ·
          refine ⟨7271677208229154549022087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4847784805486103032681391 7271677208229154549022087)
          ·
            refine ⟨10907515812343731823533131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7271677208229154549022087 10907515812343731823533131)
            ·
              refine ⟨16361273718515597735299697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10907515812343731823533131 16361273718515597735299697)
              ·
                refine ⟨12270955288886698301474773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16361273718515597735299697 12270955288886698301474773)
                ·
                  refine ⟨287600514583281991440815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12270955288886698301474773 287600514583281991440815)
                  ·
                    rfl

theorem cell22_2520450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_2520450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2520450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2520450 prefixEnd_2520450 := by exact prefixLift 2520450
  have htrace : WordTrace (prefixWord ++ tailWord_2520450) baseStart_2520450 baseEnd_2520450 := by
    simpa [prefixWord, tailWord_2520450, baseEnd_2520450] using wordTrace_append hprefix tailTrace_2520450
  have hstable : (prefixWord ++ tailWord_2520450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520450).length < 2 ^ (prefixWord ++ tailWord_2520450).sum := by decide
  have hdescent : baseEnd_2520450 < baseStart_2520450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520557 : List Nat := [1, 5, 1, 3, 2, 1, 3, 6]
def baseStart_2520557 : Nat := 118140960795 + 2520557 * 2 ^ 59
def prefixEnd_2520557 : Nat := 4983230072969 + 3 ^ 40 * 2520557 * 2
def baseEnd_2520557 : Nat := 95870908004059262433013

theorem tailTrace_2520557 : CollatzResearch.WordTrace tailWord_2520557 prefixEnd_2520557 95870908004059262433013 := by
  unfold tailWord_2520557
  simp only [CollatzResearch.WordTrace]
  refine ⟨91932266329459940708695925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61288177552973293805797283 91932266329459940708695925)
  ·
    refine ⟨8618649968386869441440243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 91932266329459940708695925 8618649968386869441440243)
    ·
      refine ⟨12927974952580304162160365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8618649968386869441440243 12927974952580304162160365)
      ·
        refine ⟨4847990607217614060810137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12927974952580304162160365 4847990607217614060810137)
        ·
          refine ⟨3635992955413210545607603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4847990607217614060810137 3635992955413210545607603)
          ·
            refine ⟨5453989433119815818411405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3635992955413210545607603 5453989433119815818411405)
            ·
              refine ⟨2045246037419930931904277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5453989433119815818411405 2045246037419930931904277)
              ·
                refine ⟨95870908004059262433013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2045246037419930931904277 95870908004059262433013)
                ·
                  rfl

theorem cell22_2520557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 3, 6].length) (baseStart_2520557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2520557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2520557 prefixEnd_2520557 := by exact prefixLift 2520557
  have htrace : WordTrace (prefixWord ++ tailWord_2520557) baseStart_2520557 baseEnd_2520557 := by
    simpa [prefixWord, tailWord_2520557, baseEnd_2520557] using wordTrace_append hprefix tailTrace_2520557
  have hstable : (prefixWord ++ tailWord_2520557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520557).length < 2 ^ (prefixWord ++ tailWord_2520557).sum := by decide
  have hdescent : baseEnd_2520557 < baseStart_2520557 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520572 : List Nat := [2, 2, 2, 1, 2, 1, 3, 5, 1, 3]
def baseStart_2520572 : Nat := 118140960795 + 2520572 * 2 ^ 59
def prefixEnd_2520572 : Nat := 4983230072969 + 3 ^ 40 * 2520572 * 2
def baseEnd_2520572 : Nat := 862843306843078322772071

theorem tailTrace_2520572 : CollatzResearch.WordTrace tailWord_2520572 prefixEnd_2520572 862843306843078322772071 := by
  unfold tailWord_2520572
  simp only [CollatzResearch.WordTrace]
  refine ⟨45966406712202799135245985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61288542282937065513661313 45966406712202799135245985)
  ·
    refine ⟨34474805034152099351434489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45966406712202799135245985 34474805034152099351434489)
    ·
      refine ⟨25856103775614074513575867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34474805034152099351434489 25856103775614074513575867)
      ·
        refine ⟨38784155663421111770363801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25856103775614074513575867 38784155663421111770363801)
        ·
          refine ⟨29088116747565833827772851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38784155663421111770363801 29088116747565833827772851)
          ·
            refine ⟨43632175121348750741659277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29088116747565833827772851 43632175121348750741659277)
            ·
              refine ⟨16362065670505781528122229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43632175121348750741659277 16362065670505781528122229)
              ·
                refine ⟨1533943656609917018261459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16362065670505781528122229 1533943656609917018261459)
                ·
                  refine ⟨2300915484914875527392189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1533943656609917018261459 2300915484914875527392189)
                  ·
                    refine ⟨862843306843078322772071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2300915484914875527392189 862843306843078322772071)
                    ·
                      rfl

theorem cell22_2520572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 5, 1, 3].length) (baseStart_2520572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2520572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2520572 prefixEnd_2520572 := by exact prefixLift 2520572
  have htrace : WordTrace (prefixWord ++ tailWord_2520572) baseStart_2520572 baseEnd_2520572 := by
    simpa [prefixWord, tailWord_2520572, baseEnd_2520572] using wordTrace_append hprefix tailTrace_2520572
  have hstable : (prefixWord ++ tailWord_2520572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520572).length < 2 ^ (prefixWord ++ tailWord_2520572).sum := by decide
  have hdescent : baseEnd_2520572 < baseStart_2520572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520645 : List Nat := [1, 3, 1, 1, 1, 4, 1, 3, 4, 3]
def baseStart_2520645 : Nat := 118140960795 + 2520645 * 2 ^ 59
def prefixEnd_2520645 : Nat := 4983230072969 + 3 ^ 40 * 2520645 * 2
def baseEnd_2520645 : Nat := 862868296234930465696847

theorem tailTrace_2520645 : CollatzResearch.WordTrace tailWord_2520645 prefixEnd_2520645 862868296234930465696847 := by
  unfold tailWord_2520645
  simp only [CollatzResearch.WordTrace]
  refine ⟨91935475953141131737899389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61290317302094087825266259 91935475953141131737899389)
  ·
    refine ⟨34475803482427924401712271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91935475953141131737899389 34475803482427924401712271)
    ·
      refine ⟨51713705223641886602568407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34475803482427924401712271 51713705223641886602568407)
      ·
        refine ⟨77570557835462829903852611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51713705223641886602568407 77570557835462829903852611)
        ·
          refine ⟨116355836753194244855778917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77570557835462829903852611 116355836753194244855778917)
          ·
            refine ⟨21816719391223920910458547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 116355836753194244855778917 21816719391223920910458547)
            ·
              refine ⟨32725079086835881365687821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21816719391223920910458547 32725079086835881365687821)
              ·
                refine ⟨12271904657563455512132933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32725079086835881365687821 12271904657563455512132933)
                ·
                  refine ⟨2300982123293147908524925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12271904657563455512132933 2300982123293147908524925)
                  ·
                    refine ⟨862868296234930465696847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2300982123293147908524925 862868296234930465696847)
                    ·
                      rfl

theorem cell22_2520645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 3, 4, 3].length) (baseStart_2520645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2520645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2520645 prefixEnd_2520645 := by exact prefixLift 2520645
  have htrace : WordTrace (prefixWord ++ tailWord_2520645) baseStart_2520645 baseEnd_2520645 := by
    simpa [prefixWord, tailWord_2520645, baseEnd_2520645] using wordTrace_append hprefix tailTrace_2520645
  have hstable : (prefixWord ++ tailWord_2520645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520645).length < 2 ^ (prefixWord ++ tailWord_2520645).sum := by decide
  have hdescent : baseEnd_2520645 < baseStart_2520645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520647 : List Nat := [1, 1, 4, 1, 5, 2, 1, 1, 6]
def baseStart_2520647 : Nat := 118140960795 + 2520647 * 2 ^ 59
def prefixEnd_2520647 : Nat := 4983230072969 + 3 ^ 40 * 2520647 * 2
def baseEnd_2520647 : Nat := 287622993625267709048947

theorem tailTrace_2520647 : CollatzResearch.WordTrace tailWord_2520647 prefixEnd_2520647 287622993625267709048947 := by
  unfold tailWord_2520647
  simp only [CollatzResearch.WordTrace]
  refine ⟨91935548899133886079472195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61290365932755924052981463 91935548899133886079472195)
  ·
    refine ⟨137903323348700829119208293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91935548899133886079472195 137903323348700829119208293)
    ·
      refine ⟨25856873127881405459851555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 137903323348700829119208293 25856873127881405459851555)
      ·
        refine ⟨38785309691822108189777333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25856873127881405459851555 38785309691822108189777333)
        ·
          refine ⟨3636122783608322642791625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38785309691822108189777333 3636122783608322642791625)
          ·
            refine ⟨2727092087706241982093719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3636122783608322642791625 2727092087706241982093719)
            ·
              refine ⟨4090638131559362973140579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2727092087706241982093719 4090638131559362973140579)
              ·
                refine ⟨6135957197339044459710869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4090638131559362973140579 6135957197339044459710869)
                ·
                  refine ⟨287622993625267709048947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6135957197339044459710869 287622993625267709048947)
                  ·
                    rfl

theorem cell22_2520647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 1, 6].length) (baseStart_2520647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2520647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2520647 prefixEnd_2520647 := by exact prefixLift 2520647
  have htrace : WordTrace (prefixWord ++ tailWord_2520647) baseStart_2520647 baseEnd_2520647 := by
    simpa [prefixWord, tailWord_2520647, baseEnd_2520647] using wordTrace_append hprefix tailTrace_2520647
  have hstable : (prefixWord ++ tailWord_2520647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520647).length < 2 ^ (prefixWord ++ tailWord_2520647).sum := by decide
  have hdescent : baseEnd_2520647 < baseStart_2520647 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520660 : List Nat := [2, 4, 1, 1, 1, 2, 1, 2, 4, 4]
def baseStart_2520660 : Nat := 118140960795 + 2520660 * 2 ^ 59
def prefixEnd_2520660 : Nat := 4983230072969 + 3 ^ 40 * 2520660 * 2
def baseEnd_2520660 : Nat := 862873431041475426571801

theorem tailTrace_2520660 : CollatzResearch.WordTrace tailWord_2520660 prefixEnd_2520660 862873431041475426571801 := by
  unfold tailWord_2520660
  simp only [CollatzResearch.WordTrace]
  refine ⟨45968011524043394649847717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61290682032057859533130289 45968011524043394649847717)
  ·
    refine ⟨8619002160758136496846447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45968011524043394649847717 8619002160758136496846447)
    ·
      refine ⟨12928503241137204745269671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8619002160758136496846447 12928503241137204745269671)
      ·
        refine ⟨19392754861705807117904507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12928503241137204745269671 19392754861705807117904507)
        ·
          refine ⟨29089132292558710676856761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19392754861705807117904507 29089132292558710676856761)
          ·
            refine ⟨21816849219419033007642571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29089132292558710676856761 21816849219419033007642571)
            ·
              refine ⟨32725273829128549511463857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21816849219419033007642571 32725273829128549511463857)
              ·
                refine ⟨24543955371846412133597893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32725273829128549511463857 24543955371846412133597893)
                ·
                  refine ⟨4601991632221202275049605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24543955371846412133597893 4601991632221202275049605)
                  ·
                    refine ⟨862873431041475426571801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4601991632221202275049605 862873431041475426571801)
                    ·
                      rfl

theorem cell22_2520660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_2520660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2520660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2520660 prefixEnd_2520660 := by exact prefixLift 2520660
  have htrace : WordTrace (prefixWord ++ tailWord_2520660) baseStart_2520660 baseEnd_2520660 := by
    simpa [prefixWord, tailWord_2520660, baseEnd_2520660] using wordTrace_append hprefix tailTrace_2520660
  have hstable : (prefixWord ++ tailWord_2520660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520660).length < 2 ^ (prefixWord ++ tailWord_2520660).sum := by decide
  have hdescent : baseEnd_2520660 < baseStart_2520660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520677 : List Nat := [1, 3, 1, 3, 3, 2, 2, 1, 2, 4]
def baseStart_2520677 : Nat := 118140960795 + 2520677 * 2 ^ 59
def prefixEnd_2520677 : Nat := 4983230072969 + 3 ^ 40 * 2520677 * 2
def baseEnd_2520677 : Nat := 862879250488893048896749

theorem tailTrace_2520677 : CollatzResearch.WordTrace tailWord_2520677 prefixEnd_2520677 862879250488893048896749 := by
  unfold tailWord_2520677
  simp only [CollatzResearch.WordTrace]
  refine ⟨91936643089025201203064285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61291095392683467468709523 91936643089025201203064285)
  ·
    refine ⟨34476241158384450451149107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91936643089025201203064285 34476241158384450451149107)
    ·
      refine ⟨51714361737576675676723661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34476241158384450451149107 51714361737576675676723661)
      ·
        refine ⟨19392885651591253378771373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51714361737576675676723661 19392885651591253378771373)
        ·
          refine ⟨7272332119346720017039265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19392885651591253378771373 7272332119346720017039265)
          ·
            refine ⟨5454249089510040012779449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7272332119346720017039265 5454249089510040012779449)
            ·
              refine ⟨4090686817132530009584587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5454249089510040012779449 4090686817132530009584587)
              ·
                refine ⟨6136030225698795014376881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4090686817132530009584587 6136030225698795014376881)
                ·
                  refine ⟨4602022669274096260782661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6136030225698795014376881 4602022669274096260782661)
                  ·
                    refine ⟨862879250488893048896749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4602022669274096260782661 862879250488893048896749)
                    ·
                      rfl

theorem cell22_2520677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 1, 2, 4].length) (baseStart_2520677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2520677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2520677 prefixEnd_2520677 := by exact prefixLift 2520677
  have htrace : WordTrace (prefixWord ++ tailWord_2520677) baseStart_2520677 baseEnd_2520677 := by
    simpa [prefixWord, tailWord_2520677, baseEnd_2520677] using wordTrace_append hprefix tailTrace_2520677
  have hstable : (prefixWord ++ tailWord_2520677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520677).length < 2 ^ (prefixWord ++ tailWord_2520677).sum := by decide
  have hdescent : baseEnd_2520677 < baseStart_2520677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520703 : List Nat := [1, 1, 2, 2, 1, 1, 1, 2, 11]
def baseStart_2520703 : Nat := 118140960795 + 2520703 * 2 ^ 59
def prefixEnd_2520703 : Nat := 4983230072969 + 3 ^ 40 * 2520703 * 2
def baseEnd_2520703 : Nat := 287629383606745882582223

theorem tailTrace_2520703 : CollatzResearch.WordTrace tailWord_2520703 prefixEnd_2520703 287629383606745882582223 := by
  unfold tailWord_2520703
  simp only [CollatzResearch.WordTrace]
  refine ⟨91937591386931007643510763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61291727591287338429007175 91937591386931007643510763)
  ·
    refine ⟨137906387080396511465266145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91937591386931007643510763 137906387080396511465266145)
    ·
      refine ⟨103429790310297383598949609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137906387080396511465266145 103429790310297383598949609)
      ·
        refine ⟨77572342732723037699212207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103429790310297383598949609 77572342732723037699212207)
        ·
          refine ⟨116358514099084556548818311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77572342732723037699212207 116358514099084556548818311)
          ·
            refine ⟨174537771148626834823227467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116358514099084556548818311 174537771148626834823227467)
            ·
              refine ⟨261806656722940252234841201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174537771148626834823227467 261806656722940252234841201)
              ·
                refine ⟨196354992542205189176130901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 261806656722940252234841201 196354992542205189176130901)
                ·
                  refine ⟨287629383606745882582223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 196354992542205189176130901 287629383606745882582223)
                  ·
                    rfl

theorem cell22_2520703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 11].length) (baseStart_2520703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2520703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2520703 prefixEnd_2520703 := by exact prefixLift 2520703
  have htrace : WordTrace (prefixWord ++ tailWord_2520703) baseStart_2520703 baseEnd_2520703 := by
    simpa [prefixWord, tailWord_2520703, baseEnd_2520703] using wordTrace_append hprefix tailTrace_2520703
  have hstable : (prefixWord ++ tailWord_2520703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520703).length < 2 ^ (prefixWord ++ tailWord_2520703).sum := by decide
  have hdescent : baseEnd_2520703 < baseStart_2520703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520705 : List Nat := [1, 2, 4, 2, 1, 2, 1, 1, 2, 6]
def baseStart_2520705 : Nat := 118140960795 + 2520705 * 2 ^ 59
def prefixEnd_2520705 : Nat := 4983230072969 + 3 ^ 40 * 2520705 * 2
def baseEnd_2520705 : Nat := 862888835461110309196663

theorem tailTrace_2520705 : CollatzResearch.WordTrace tailWord_2520705 prefixEnd_2520705 862888835461110309196663 := by
  unfold tailWord_2520705
  simp only [CollatzResearch.WordTrace]
  refine ⟨91937664332923761985083569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61291776221949174656722379 91937664332923761985083569)
  ·
    refine ⟨68953248249692821488812677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91937664332923761985083569 68953248249692821488812677)
    ·
      refine ⟨12928734046817404029152377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68953248249692821488812677 12928734046817404029152377)
      ·
        refine ⟨9696550535113053021864283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12928734046817404029152377 9696550535113053021864283)
        ·
          refine ⟨14544825802669579532796425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9696550535113053021864283 14544825802669579532796425)
          ·
            refine ⟨10908619352002184649597319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14544825802669579532796425 10908619352002184649597319)
            ·
              refine ⟨16362929028003276974395979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10908619352002184649597319 16362929028003276974395979)
              ·
                refine ⟨24544393542004915461593969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16362929028003276974395979 24544393542004915461593969)
                ·
                  refine ⟨18408295156503686596195477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24544393542004915461593969 18408295156503686596195477)
                  ·
                    refine ⟨862888835461110309196663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18408295156503686596195477 862888835461110309196663)
                    ·
                      rfl

theorem cell22_2520705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_2520705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2520705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2520705 prefixEnd_2520705 := by exact prefixLift 2520705
  have htrace : WordTrace (prefixWord ++ tailWord_2520705) baseStart_2520705 baseEnd_2520705 := by
    simpa [prefixWord, tailWord_2520705, baseEnd_2520705] using wordTrace_append hprefix tailTrace_2520705
  have hstable : (prefixWord ++ tailWord_2520705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520705).length < 2 ^ (prefixWord ++ tailWord_2520705).sum := by decide
  have hdescent : baseEnd_2520705 < baseStart_2520705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520758 : List Nat := [5, 1, 3, 1, 1, 1, 2, 4, 1, 3]
def baseStart_2520758 : Nat := 118140960795 + 2520758 * 2 ^ 59
def prefixEnd_2520758 : Nat := 4983230072969 + 3 ^ 40 * 2520758 * 2
def baseEnd_2520758 : Nat := 862906978444235837621501

theorem tailTrace_2520758 : CollatzResearch.WordTrace tailWord_2520758 prefixEnd_2520758 862906978444235837621501 := by
  unfold tailWord_2520758
  simp only [CollatzResearch.WordTrace]
  refine ⟨5746224837608234502297683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61293064934487834691175285 5746224837608234502297683)
  ·
    refine ⟨8619337256412351753446525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5746224837608234502297683 8619337256412351753446525)
    ·
      refine ⟨3232251471154631907542447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8619337256412351753446525 3232251471154631907542447)
      ·
        refine ⟨4848377206731947861313671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3232251471154631907542447 4848377206731947861313671)
        ·
          refine ⟨7272565810097921791970507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4848377206731947861313671 7272565810097921791970507)
          ·
            refine ⟨10908848715146882687955761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7272565810097921791970507 10908848715146882687955761)
            ·
              refine ⟨8181636536360162015966821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10908848715146882687955761 8181636536360162015966821)
              ·
                refine ⟨1534056850567530377993779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8181636536360162015966821 1534056850567530377993779)
                ·
                  refine ⟨2301085275851295566990669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1534056850567530377993779 2301085275851295566990669)
                  ·
                    refine ⟨862906978444235837621501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2301085275851295566990669 862906978444235837621501)
                    ·
                      rfl

theorem cell22_2520758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_2520758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2520758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2520758 prefixEnd_2520758 := by exact prefixLift 2520758
  have htrace : WordTrace (prefixWord ++ tailWord_2520758) baseStart_2520758 baseEnd_2520758 := by
    simpa [prefixWord, tailWord_2520758, baseEnd_2520758] using wordTrace_append hprefix tailTrace_2520758
  have hstable : (prefixWord ++ tailWord_2520758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520758).length < 2 ^ (prefixWord ++ tailWord_2520758).sum := by decide
  have hdescent : baseEnd_2520758 < baseStart_2520758 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520810 : List Nat := [3, 1, 3, 1, 1, 1, 12]
def baseStart_2520810 : Nat := 118140960795 + 2520810 * 2 ^ 59
def prefixEnd_2520810 : Nat := 4983230072969 + 3 ^ 40 * 2520810 * 2
def baseEnd_2520810 : Nat := 31960177003960186493383

theorem tailTrace_2520810 : CollatzResearch.WordTrace tailWord_2520810 prefixEnd_2520810 31960177003960186493383 := by
  unfold tailWord_2520810
  simp only [CollatzResearch.WordTrace]
  refine ⟨22985373499385841229413971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61294329331695576611770589 22985373499385841229413971)
  ·
    refine ⟨34478060249078761844120957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22985373499385841229413971 34478060249078761844120957)
    ·
      refine ⟨12929272593404535691545359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34478060249078761844120957 12929272593404535691545359)
      ·
        refine ⟨19393908890106803537318039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12929272593404535691545359 19393908890106803537318039)
        ·
          refine ⟨29090863335160205305977059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19393908890106803537318039 29090863335160205305977059)
          ·
            refine ⟨43636295002740307958965589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29090863335160205305977059 43636295002740307958965589)
            ·
              refine ⟨31960177003960186493383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 43636295002740307958965589 31960177003960186493383)
              ·
                rfl

theorem cell22_2520810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 12].length) (baseStart_2520810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2520810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2520810 prefixEnd_2520810 := by exact prefixLift 2520810
  have htrace : WordTrace (prefixWord ++ tailWord_2520810) baseStart_2520810 baseEnd_2520810 := by
    simpa [prefixWord, tailWord_2520810, baseEnd_2520810] using wordTrace_append hprefix tailTrace_2520810
  have hstable : (prefixWord ++ tailWord_2520810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520810).length < 2 ^ (prefixWord ++ tailWord_2520810).sum := by decide
  have hdescent : baseEnd_2520810 < baseStart_2520810 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520814 : List Nat := [4, 1, 2, 1, 1, 2, 2, 4, 2, 3]
def baseStart_2520814 : Nat := 118140960795 + 2520814 * 2 ^ 59
def prefixEnd_2520814 : Nat := 4983230072969 + 3 ^ 40 * 2520814 * 2
def baseEnd_2520814 : Nat := 862926148388670358221329

theorem tailTrace_2520814 : CollatzResearch.WordTrace tailWord_2520814 prefixEnd_2520814 862926148388670358221329 := by
  unfold tailWord_2520814
  simp only [CollatzResearch.WordTrace]
  refine ⟨11492704986191109200100187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61294426593019249067200997 11492704986191109200100187)
  ·
    refine ⟨17239057479286663800150281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11492704986191109200100187 17239057479286663800150281)
    ·
      refine ⟨12929293109464997850112711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17239057479286663800150281 12929293109464997850112711)
      ·
        refine ⟨19393939664197496775169067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12929293109464997850112711 19393939664197496775169067)
        ·
          refine ⟨29090909496296245162753601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19393939664197496775169067 29090909496296245162753601)
          ·
            refine ⟨21818182122222183872065201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29090909496296245162753601 21818182122222183872065201)
            ·
              refine ⟨16363636591666637904048901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21818182122222183872065201 16363636591666637904048901)
              ·
                refine ⟨3068181860937494607009169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16363636591666637904048901 3068181860937494607009169)
                ·
                  refine ⟨2301136395703120955256877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3068181860937494607009169 2301136395703120955256877)
                  ·
                    refine ⟨862926148388670358221329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2301136395703120955256877 862926148388670358221329)
                    ·
                      rfl

theorem cell22_2520814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 4, 2, 3].length) (baseStart_2520814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2520814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2520814 prefixEnd_2520814 := by exact prefixLift 2520814
  have htrace : WordTrace (prefixWord ++ tailWord_2520814) baseStart_2520814 baseEnd_2520814 := by
    simpa [prefixWord, tailWord_2520814, baseEnd_2520814] using wordTrace_append hprefix tailTrace_2520814
  have hstable : (prefixWord ++ tailWord_2520814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520814).length < 2 ^ (prefixWord ++ tailWord_2520814).sum := by decide
  have hdescent : baseEnd_2520814 < baseStart_2520814 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520876 : List Nat := [2, 2, 1, 1, 1, 6, 1, 4, 1, 3]
def baseStart_2520876 : Nat := 118140960795 + 2520876 * 2 ^ 59
def prefixEnd_2520876 : Nat := 4983230072969 + 3 ^ 40 * 2520876 * 2
def baseEnd_2520876 : Nat := 862947372255722863171139

theorem tailTrace_2520876 : CollatzResearch.WordTrace tailWord_2520876 prefixEnd_2520876 862947372255722863171139 := by
  unfold tailWord_2520876
  simp only [CollatzResearch.WordTrace]
  refine ⟨45971950607652129094779241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61295934143536172126372321 45971950607652129094779241)
  ·
    refine ⟨34478962955739096821084431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45971950607652129094779241 34478962955739096821084431)
    ·
      refine ⟨51718444433608645231626647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34478962955739096821084431 51718444433608645231626647)
      ·
        refine ⟨77577666650412967847439971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51718444433608645231626647 77577666650412967847439971)
        ·
          refine ⟨116366499975619451771159957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77577666650412967847439971 116366499975619451771159957)
          ·
            refine ⟨5454679686357161801773123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 116366499975619451771159957 5454679686357161801773123)
            ·
              refine ⟨8182019529535742702659685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5454679686357161801773123 8182019529535742702659685)
              ·
                refine ⟨1534128661787951756748691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8182019529535742702659685 1534128661787951756748691)
                ·
                  refine ⟨2301192992681927635123037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1534128661787951756748691 2301192992681927635123037)
                  ·
                    refine ⟨862947372255722863171139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2301192992681927635123037 862947372255722863171139)
                    ·
                      rfl

theorem cell22_2520876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 4, 1, 3].length) (baseStart_2520876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2520876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2520876 prefixEnd_2520876 := by exact prefixLift 2520876
  have htrace : WordTrace (prefixWord ++ tailWord_2520876) baseStart_2520876 baseEnd_2520876 := by
    simpa [prefixWord, tailWord_2520876, baseEnd_2520876] using wordTrace_append hprefix tailTrace_2520876
  have hstable : (prefixWord ++ tailWord_2520876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520876).length < 2 ^ (prefixWord ++ tailWord_2520876).sum := by decide
  have hdescent : baseEnd_2520876 < baseStart_2520876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520968 : List Nat := [2, 1, 3, 3, 3, 2, 1, 3, 4]
def baseStart_2520968 : Nat := 118140960795 + 2520968 * 2 ^ 59
def prefixEnd_2520968 : Nat := 4983230072969 + 3 ^ 40 * 2520968 * 2
def baseEnd_2520968 : Nat := 287659621911955096623619

theorem tailTrace_2520968 : CollatzResearch.WordTrace tailWord_2520968 prefixEnd_2520968 287659621911955096623619 := by
  unfold tailWord_2520968
  simp only [CollatzResearch.WordTrace]
  refine ⟨45973628365485478950953779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61298171153980638601271705 45973628365485478950953779)
  ·
    refine ⟨68960442548228218426430669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45973628365485478950953779 68960442548228218426430669)
    ·
      refine ⟨25860165955585581909911501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68960442548228218426430669 25860165955585581909911501)
      ·
        refine ⟨9697562233344593216216813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25860165955585581909911501 9697562233344593216216813)
        ·
          refine ⟨3636585837504222456081305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9697562233344593216216813 3636585837504222456081305)
          ·
            refine ⟨2727439378128166842060979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3636585837504222456081305 2727439378128166842060979)
            ·
              refine ⟨4091159067192250263091469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2727439378128166842060979 4091159067192250263091469)
              ·
                refine ⟨1534184650197093848659301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4091159067192250263091469 1534184650197093848659301)
                ·
                  refine ⟨287659621911955096623619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1534184650197093848659301 287659621911955096623619)
                  ·
                    rfl

theorem cell22_2520968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 3, 4].length) (baseStart_2520968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2520968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2520968 prefixEnd_2520968 := by exact prefixLift 2520968
  have htrace : WordTrace (prefixWord ++ tailWord_2520968) baseStart_2520968 baseEnd_2520968 := by
    simpa [prefixWord, tailWord_2520968, baseEnd_2520968] using wordTrace_append hprefix tailTrace_2520968
  have hstable : (prefixWord ++ tailWord_2520968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520968).length < 2 ^ (prefixWord ++ tailWord_2520968).sum := by decide
  have hdescent : baseEnd_2520968 < baseStart_2520968 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2520992 : List Nat := [2, 1, 1, 4, 1, 1, 1, 3, 2, 6]
def baseStart_2520992 : Nat := 118140960795 + 2520992 * 2 ^ 59
def prefixEnd_2520992 : Nat := 4983230072969 + 3 ^ 40 * 2520992 * 2
def baseEnd_2520992 : Nat := 862987081426337227270783

theorem tailTrace_2520992 : CollatzResearch.WordTrace tailWord_2520992 prefixEnd_2520992 862987081426337227270783 := by
  unfold tailWord_2520992
  simp only [CollatzResearch.WordTrace]
  refine ⟨45974066041442005000390615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61298754721922673333854153 45974066041442005000390615)
  ·
    refine ⟨68961099062163007500585923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45974066041442005000390615 68961099062163007500585923)
    ·
      refine ⟨103441648593244511250878885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68961099062163007500585923 103441648593244511250878885)
      ·
        refine ⟨19395309111233345859539791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 103441648593244511250878885 19395309111233345859539791)
        ·
          refine ⟨29092963666850018789309687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19395309111233345859539791 29092963666850018789309687)
          ·
            refine ⟨43639445500275028183964531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29092963666850018789309687 43639445500275028183964531)
            ·
              refine ⟨65459168250412542275946797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43639445500275028183964531 65459168250412542275946797)
              ·
                refine ⟨24547188093904703353480049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65459168250412542275946797 24547188093904703353480049)
                ·
                  refine ⟨18410391070428527515110037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24547188093904703353480049 18410391070428527515110037)
                  ·
                    refine ⟨862987081426337227270783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18410391070428527515110037 862987081426337227270783)
                    ·
                      rfl

theorem cell22_2520992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 2, 6].length) (baseStart_2520992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2520992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2520992 prefixEnd_2520992 := by exact prefixLift 2520992
  have htrace : WordTrace (prefixWord ++ tailWord_2520992) baseStart_2520992 baseEnd_2520992 := by
    simpa [prefixWord, tailWord_2520992, baseEnd_2520992] using wordTrace_append hprefix tailTrace_2520992
  have hstable : (prefixWord ++ tailWord_2520992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2520992).length < 2 ^ (prefixWord ++ tailWord_2520992).sum := by decide
  have hdescent : baseEnd_2520992 < baseStart_2520992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2520992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2521000 : List Nat := [2, 1, 6, 2, 1, 1, 1, 3, 2, 3]
def baseStart_2521000 : Nat := 118140960795 + 2521000 * 2 ^ 59
def prefixEnd_2521000 : Nat := 4983230072969 + 3 ^ 40 * 2521000 * 2
def baseEnd_2521000 : Nat := 862989819989827873070759

theorem tailTrace_2521000 : CollatzResearch.WordTrace tailWord_2521000 prefixEnd_2521000 862989819989827873070759 := by
  unfold tailWord_2521000
  simp only [CollatzResearch.WordTrace]
  refine ⟨45974211933427513683536227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61298949244570018244714969 45974211933427513683536227)
  ·
    refine ⟨68961317900141270525304341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45974211933427513683536227 68961317900141270525304341)
    ·
      refine ⟨3232561776569122055873641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 68961317900141270525304341 3232561776569122055873641)
      ·
        refine ⟨2424421332426841541905231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3232561776569122055873641 2424421332426841541905231)
        ·
          refine ⟨3636631998640262312857847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2424421332426841541905231 3636631998640262312857847)
          ·
            refine ⟨5454947997960393469286771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3636631998640262312857847 5454947997960393469286771)
            ·
              refine ⟨8182421996940590203930157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5454947997960393469286771 8182421996940590203930157)
              ·
                refine ⟨3068408248852721326473809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8182421996940590203930157 3068408248852721326473809)
                ·
                  refine ⟨2301306186639540994855357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3068408248852721326473809 2301306186639540994855357)
                  ·
                    refine ⟨862989819989827873070759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2301306186639540994855357 862989819989827873070759)
                    ·
                      rfl

theorem cell22_2521000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_2521000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2521000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2521000 prefixEnd_2521000 := by exact prefixLift 2521000
  have htrace : WordTrace (prefixWord ++ tailWord_2521000) baseStart_2521000 baseEnd_2521000 := by
    simpa [prefixWord, tailWord_2521000, baseEnd_2521000] using wordTrace_append hprefix tailTrace_2521000
  have hstable : (prefixWord ++ tailWord_2521000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2521000).length < 2 ^ (prefixWord ++ tailWord_2521000).sum := by decide
  have hdescent : baseEnd_2521000 < baseStart_2521000 := by decide
  rcases family_descends (prefixWord ++ tailWord_2521000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2521045 : List Nat := [1, 3, 2, 3, 2, 1, 4, 2, 1, 3]
def baseStart_2521045 : Nat := 118140960795 + 2521045 * 2 ^ 59
def prefixEnd_2521045 : Nat := 4983230072969 + 3 ^ 40 * 2521045 * 2
def baseEnd_2521045 : Nat := 863005224409462755695621

theorem tailTrace_2521045 : CollatzResearch.WordTrace tailWord_2521045 prefixEnd_2521045 863005224409462755695621 := by
  unfold tailWord_2521045
  simp only [CollatzResearch.WordTrace]
  refine ⟨91950065151692000052460589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61300043434461333368307059 91950065151692000052460589)
  ·
    refine ⟨34481274431884500019672721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91950065151692000052460589 34481274431884500019672721)
    ·
      refine ⟨25860955823913375014754541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34481274431884500019672721 25860955823913375014754541)
      ·
        refine ⟨9697858433967515630532953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25860955823913375014754541 9697858433967515630532953)
        ·
          refine ⟨7273393825475636722899715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9697858433967515630532953 7273393825475636722899715)
          ·
            refine ⟨10910090738213455084349573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7273393825475636722899715 10910090738213455084349573)
            ·
              refine ⟨2045642013415022828315545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10910090738213455084349573 2045642013415022828315545)
              ·
                refine ⟨1534231510061267121236659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2045642013415022828315545 1534231510061267121236659)
                ·
                  refine ⟨2301347265091900681854989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1534231510061267121236659 2301347265091900681854989)
                  ·
                    refine ⟨863005224409462755695621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2301347265091900681854989 863005224409462755695621)
                    ·
                      rfl

theorem cell22_2521045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 4, 2, 1, 3].length) (baseStart_2521045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2521045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2521045 prefixEnd_2521045 := by exact prefixLift 2521045
  have htrace : WordTrace (prefixWord ++ tailWord_2521045) baseStart_2521045 baseEnd_2521045 := by
    simpa [prefixWord, tailWord_2521045, baseEnd_2521045] using wordTrace_append hprefix tailTrace_2521045
  have hstable : (prefixWord ++ tailWord_2521045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2521045).length < 2 ^ (prefixWord ++ tailWord_2521045).sum := by decide
  have hdescent : baseEnd_2521045 < baseStart_2521045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2521045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2521084 : List Nat := [2, 2, 2, 1, 2, 2, 1, 4, 1, 5]
def baseStart_2521084 : Nat := 118140960795 + 2521084 * 2 ^ 59
def prefixEnd_2521084 : Nat := 4983230072969 + 3 ^ 40 * 2521084 * 2
def baseEnd_2521084 : Nat := 863018574906479653970501

theorem tailTrace_2521084 : CollatzResearch.WordTrace tailWord_2521084 prefixEnd_2521084 863018574906479653970501 := by
  unfold tailWord_2521084
  simp only [CollatzResearch.WordTrace]
  refine ⟨45975743799275354856565153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61300991732367139808753537 45975743799275354856565153)
  ·
    refine ⟨34481807849456516142423865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45975743799275354856565153 34481807849456516142423865)
    ·
      refine ⟨25861355887092387106817899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34481807849456516142423865 25861355887092387106817899)
      ·
        refine ⟨38792033830638580660226849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25861355887092387106817899 38792033830638580660226849)
        ·
          refine ⟨29094025372978935495170137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38792033830638580660226849 29094025372978935495170137)
          ·
            refine ⟨21820519029734201621377603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29094025372978935495170137 21820519029734201621377603)
            ·
              refine ⟨32730778544601302432066405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21820519029734201621377603 32730778544601302432066405)
              ·
                refine ⟨6137020977112744206012451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32730778544601302432066405 6137020977112744206012451)
                ·
                  refine ⟨9205531465669116309018677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6137020977112744206012451 9205531465669116309018677)
                  ·
                    refine ⟨863018574906479653970501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9205531465669116309018677 863018574906479653970501)
                    ·
                      rfl

theorem cell22_2521084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 4, 1, 5].length) (baseStart_2521084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2521084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2521084 prefixEnd_2521084 := by exact prefixLift 2521084
  have htrace : WordTrace (prefixWord ++ tailWord_2521084) baseStart_2521084 baseEnd_2521084 := by
    simpa [prefixWord, tailWord_2521084, baseEnd_2521084] using wordTrace_append hprefix tailTrace_2521084
  have hstable : (prefixWord ++ tailWord_2521084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2521084).length < 2 ^ (prefixWord ++ tailWord_2521084).sum := by decide
  have hdescent : baseEnd_2521084 < baseStart_2521084 := by decide
  rcases family_descends (prefixWord ++ tailWord_2521084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2521099 : List Nat := [1, 1, 1, 1, 6, 1, 2, 1, 4, 4]
def baseStart_2521099 : Nat := 118140960795 + 2521099 * 2 ^ 59
def prefixEnd_2521099 : Nat := 4983230072969 + 3 ^ 40 * 2521099 * 2
def baseEnd_2521099 : Nat := 863023709713024614845455

theorem tailTrace_2521099 : CollatzResearch.WordTrace tailWord_2521099 prefixEnd_2521099 863023709713024614845455 := by
  unfold tailWord_2521099
  simp only [CollatzResearch.WordTrace]
  refine ⟨91952034693496367274926351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61301356462330911516617567 91952034693496367274926351)
  ·
    refine ⟨137928052040244550912389527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91952034693496367274926351 137928052040244550912389527)
    ·
      refine ⟨206892078060366826368584291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137928052040244550912389527 206892078060366826368584291)
      ·
        refine ⟨310338117090550239552876437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206892078060366826368584291 310338117090550239552876437)
        ·
          refine ⟨14547099238619542479041083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 310338117090550239552876437 14547099238619542479041083)
          ·
            refine ⟨21820648857929313718561625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14547099238619542479041083 21820648857929313718561625)
            ·
              refine ⟨16365486643446985288921219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21820648857929313718561625 16365486643446985288921219)
              ·
                refine ⟨24548229965170477933381829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16365486643446985288921219 24548229965170477933381829)
                ·
                  refine ⟨4602793118469464612509093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24548229965170477933381829 4602793118469464612509093)
                  ·
                    refine ⟨863023709713024614845455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4602793118469464612509093 863023709713024614845455)
                    ·
                      rfl

theorem cell22_2521099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 4, 4].length) (baseStart_2521099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2521099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2521099 prefixEnd_2521099 := by exact prefixLift 2521099
  have htrace : WordTrace (prefixWord ++ tailWord_2521099) baseStart_2521099 baseEnd_2521099 := by
    simpa [prefixWord, tailWord_2521099, baseEnd_2521099] using wordTrace_append hprefix tailTrace_2521099
  have hstable : (prefixWord ++ tailWord_2521099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2521099).length < 2 ^ (prefixWord ++ tailWord_2521099).sum := by decide
  have hdescent : baseEnd_2521099 < baseStart_2521099 := by decide
  rcases family_descends (prefixWord ++ tailWord_2521099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2521159 : List Nat := [1, 1, 4, 1, 3, 1, 1, 3, 7]
def baseStart_2521159 : Nat := 118140960795 + 2521159 * 2 ^ 59
def prefixEnd_2521159 : Nat := 4983230072969 + 3 ^ 40 * 2521159 * 2
def baseEnd_2521159 : Nat := 287681416313068152781757

theorem tailTrace_2521159 : CollatzResearch.WordTrace tailWord_2521159 prefixEnd_2521159 287681416313068152781757 := by
  unfold tailWord_2521159
  simp only [CollatzResearch.WordTrace]
  refine ⟨91954223073278997522110531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61302815382185998348073687 91954223073278997522110531)
  ·
    refine ⟨137931334609918496283165797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91954223073278997522110531 137931334609918496283165797)
    ·
      refine ⟨25862125239359718053093587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 137931334609918496283165797 25862125239359718053093587)
      ·
        refine ⟨38793187859039577079640381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25862125239359718053093587 38793187859039577079640381)
        ·
          refine ⟨14547445447139841404865143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38793187859039577079640381 14547445447139841404865143)
          ·
            refine ⟨21821168170709762107297715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14547445447139841404865143 21821168170709762107297715)
            ·
              refine ⟨32731752256064643160946573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21821168170709762107297715 32731752256064643160946573)
              ·
                refine ⟨12274407096024241185354965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32731752256064643160946573 12274407096024241185354965)
                ·
                  refine ⟨287681416313068152781757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12274407096024241185354965 287681416313068152781757)
                  ·
                    rfl

theorem cell22_2521159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 3, 7].length) (baseStart_2521159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2521159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2521159 prefixEnd_2521159 := by exact prefixLift 2521159
  have htrace : WordTrace (prefixWord ++ tailWord_2521159) baseStart_2521159 baseEnd_2521159 := by
    simpa [prefixWord, tailWord_2521159, baseEnd_2521159] using wordTrace_append hprefix tailTrace_2521159
  have hstable : (prefixWord ++ tailWord_2521159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2521159).length < 2 ^ (prefixWord ++ tailWord_2521159).sum := by decide
  have hdescent : baseEnd_2521159 < baseStart_2521159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2521159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2521176 : List Nat := [2, 1, 2, 2, 1, 5, 1, 3, 5]
def baseStart_2521176 : Nat := 118140960795 + 2521176 * 2 ^ 59
def prefixEnd_2521176 : Nat := 4983230072969 + 3 ^ 40 * 2521176 * 2
def baseEnd_2521176 : Nat := 287683356128874026890073

theorem tailTrace_2521176 : CollatzResearch.WordTrace tailWord_2521176 prefixEnd_2521176 287683356128874026890073 := by
  unfold tailWord_2521176
  simp only [CollatzResearch.WordTrace]
  refine ⟨45977421557108704712739691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61303228742811606283652921 45977421557108704712739691)
  ·
    refine ⟨68966132335663057069109537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45977421557108704712739691 68966132335663057069109537)
    ·
      refine ⟨51724599251747292801832153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68966132335663057069109537 51724599251747292801832153)
      ·
        refine ⟨38793449438810469601374115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51724599251747292801832153 38793449438810469601374115)
        ·
          refine ⟨58190174158215704402061173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38793449438810469601374115 58190174158215704402061173)
          ·
            refine ⟨5455328827332722287693235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58190174158215704402061173 5455328827332722287693235)
            ·
              refine ⟨8182993240999083431539853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5455328827332722287693235 8182993240999083431539853)
              ·
                refine ⟨3068622465374656286827445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8182993240999083431539853 3068622465374656286827445)
                ·
                  refine ⟨287683356128874026890073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3068622465374656286827445 287683356128874026890073)
                  ·
                    rfl

theorem cell22_2521176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 3, 5].length) (baseStart_2521176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2521176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2521176 prefixEnd_2521176 := by exact prefixLift 2521176
  have htrace : WordTrace (prefixWord ++ tailWord_2521176) baseStart_2521176 baseEnd_2521176 := by
    simpa [prefixWord, tailWord_2521176, baseEnd_2521176] using wordTrace_append hprefix tailTrace_2521176
  have hstable : (prefixWord ++ tailWord_2521176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2521176).length < 2 ^ (prefixWord ++ tailWord_2521176).sum := by decide
  have hdescent : baseEnd_2521176 < baseStart_2521176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2521176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2521356 : List Nat := [2, 2, 1, 2, 2, 2, 2, 1, 8]
def baseStart_2521356 : Nat := 118140960795 + 2521356 * 2 ^ 59
def prefixEnd_2521356 : Nat := 4983230072969 + 3 ^ 40 * 2521356 * 2
def baseEnd_2521356 : Nat := 287703895355053870389889

theorem tailTrace_2521356 : CollatzResearch.WordTrace tailWord_2521356 prefixEnd_2521356 287703895355053870389889 := by
  unfold tailWord_2521356
  simp only [CollatzResearch.WordTrace]
  refine ⟨45980704126782650083515961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61307605502376866778021281 45980704126782650083515961)
  ·
    refine ⟨34485528095086987562636971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45980704126782650083515961 34485528095086987562636971)
    ·
      refine ⟨51728292142630481343955457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34485528095086987562636971 51728292142630481343955457)
      ·
        refine ⟨38796219106972861007966593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51728292142630481343955457 38796219106972861007966593)
        ·
          refine ⟨29097164330229645755974945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38796219106972861007966593 29097164330229645755974945)
          ·
            refine ⟨21822873247672234316981209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29097164330229645755974945 21822873247672234316981209)
            ·
              refine ⟨16367154935754175737735907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21822873247672234316981209 16367154935754175737735907)
              ·
                refine ⟨24550732403631263606603861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16367154935754175737735907 24550732403631263606603861)
                ·
                  refine ⟨287703895355053870389889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24550732403631263606603861 287703895355053870389889)
                  ·
                    rfl

theorem cell22_2521356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 8].length) (baseStart_2521356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2521356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2521356 prefixEnd_2521356 := by exact prefixLift 2521356
  have htrace : WordTrace (prefixWord ++ tailWord_2521356) baseStart_2521356 baseEnd_2521356 := by
    simpa [prefixWord, tailWord_2521356, baseEnd_2521356] using wordTrace_append hprefix tailTrace_2521356
  have hstable : (prefixWord ++ tailWord_2521356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2521356).length < 2 ^ (prefixWord ++ tailWord_2521356).sum := by decide
  have hdescent : baseEnd_2521356 < baseStart_2521356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2521356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2521358 : List Nat := [4, 1, 1, 2, 1, 2, 3, 1, 3, 4]
def baseStart_2521358 : Nat := 118140960795 + 2521358 * 2 ^ 59
def prefixEnd_2521358 : Nat := 4983230072969 + 3 ^ 40 * 2521358 * 2
def baseEnd_2521358 : Nat := 863112370706034272619661

theorem tailTrace_2521358 : CollatzResearch.WordTrace tailWord_2521358 prefixEnd_2521358 863112370706034272619661 := by
  unfold tailWord_2521358
  simp only [CollatzResearch.WordTrace]
  refine ⟨11495185149944756813575591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61307654133038703005736485 11495185149944756813575591)
  ·
    refine ⟨17242777724917135220363387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11495185149944756813575591 17242777724917135220363387)
    ·
      refine ⟨25864166587375702830545081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17242777724917135220363387 25864166587375702830545081)
      ·
        refine ⟨19398124940531777122908811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25864166587375702830545081 19398124940531777122908811)
        ·
          refine ⟨29097187410797665684363217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19398124940531777122908811 29097187410797665684363217)
          ·
            refine ⟨21822890558098249263272413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29097187410797665684363217 21822890558098249263272413)
            ·
              refine ⟨8183583959286843473727155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21822890558098249263272413 8183583959286843473727155)
              ·
                refine ⟨12275375938930265210590733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8183583959286843473727155 12275375938930265210590733)
                ·
                  refine ⟨4603265977098849453971525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12275375938930265210590733 4603265977098849453971525)
                  ·
                    refine ⟨863112370706034272619661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4603265977098849453971525 863112370706034272619661)
                    ·
                      rfl

theorem cell22_2521358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 1, 3, 4].length) (baseStart_2521358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2521358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2521358 prefixEnd_2521358 := by exact prefixLift 2521358
  have htrace : WordTrace (prefixWord ++ tailWord_2521358) baseStart_2521358 baseEnd_2521358 := by
    simpa [prefixWord, tailWord_2521358, baseEnd_2521358] using wordTrace_append hprefix tailTrace_2521358
  have hstable : (prefixWord ++ tailWord_2521358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2521358).length < 2 ^ (prefixWord ++ tailWord_2521358).sum := by decide
  have hdescent : baseEnd_2521358 < baseStart_2521358 := by decide
  rcases family_descends (prefixWord ++ tailWord_2521358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2521371 : List Nat := [1, 1, 1, 1, 1, 1, 7, 1, 3, 5]
def baseStart_2521371 : Nat := 118140960795 + 2521371 * 2 ^ 59
def prefixEnd_2521371 : Nat := 4983230072969 + 3 ^ 40 * 2521371 * 2
def baseEnd_2521371 : Nat := 863116820871706572044621

theorem tailTrace_2521371 : CollatzResearch.WordTrace tailWord_2521371 prefixEnd_2521371 863116820871706572044621 := by
  unfold tailWord_2521371
  simp only [CollatzResearch.WordTrace]
  refine ⟨91961955348510957728827967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61307970232340638485885311 91961955348510957728827967)
  ·
    refine ⟨137942933022766436593241951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91961955348510957728827967 137942933022766436593241951)
    ·
      refine ⟨206914399534149654889862927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137942933022766436593241951 206914399534149654889862927)
      ·
        refine ⟨310371599301224482334794391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206914399534149654889862927 310371599301224482334794391)
        ·
          refine ⟨465557398951836723502191587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 310371599301224482334794391 465557398951836723502191587)
          ·
            refine ⟨698336098427755085253287381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 465557398951836723502191587 698336098427755085253287381)
            ·
              refine ⟨16367252306900509810623923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 698336098427755085253287381 16367252306900509810623923)
              ·
                refine ⟨24550878460350764715935885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16367252306900509810623923 24550878460350764715935885)
                ·
                  refine ⟨9206579422631536768475957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24550878460350764715935885 9206579422631536768475957)
                  ·
                    refine ⟨863116820871706572044621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9206579422631536768475957 863116820871706572044621)
                    ·
                      rfl

theorem cell22_2521371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 3, 5].length) (baseStart_2521371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2521371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2521371 prefixEnd_2521371 := by exact prefixLift 2521371
  have htrace : WordTrace (prefixWord ++ tailWord_2521371) baseStart_2521371 baseEnd_2521371 := by
    simpa [prefixWord, tailWord_2521371, baseEnd_2521371] using wordTrace_append hprefix tailTrace_2521371
  have hstable : (prefixWord ++ tailWord_2521371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2521371).length < 2 ^ (prefixWord ++ tailWord_2521371).sum := by decide
  have hdescent : baseEnd_2521371 < baseStart_2521371 := by decide
  rcases family_descends (prefixWord ++ tailWord_2521371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2521388 : List Nat := [2, 2, 1, 1, 1, 3, 2, 3, 4, 3]
def baseStart_2521388 : Nat := 118140960795 + 2521388 * 2 ^ 59
def prefixEnd_2521388 : Nat := 4983230072969 + 3 ^ 40 * 2521388 * 2
def baseEnd_2521388 : Nat := 863122640319124194369569

theorem tailTrace_2521388 : CollatzResearch.WordTrace tailWord_2521388 prefixEnd_2521388 863122640319124194369569 := by
  unfold tailWord_2521388
  simp only [CollatzResearch.WordTrace]
  refine ⟨45981287694724684816098409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61308383592966246421464545 45981287694724684816098409)
  ·
    refine ⟨34485965771043513612073807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45981287694724684816098409 34485965771043513612073807)
    ·
      refine ⟨51728948656565270418110711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34485965771043513612073807 51728948656565270418110711)
      ·
        refine ⟨77593422984847905627166067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51728948656565270418110711 77593422984847905627166067)
        ·
          refine ⟨116390134477271858440749101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77593422984847905627166067 116390134477271858440749101)
          ·
            refine ⟨43646300428976946915280913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116390134477271858440749101 43646300428976946915280913)
            ·
              refine ⟨32734725321732710186460685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43646300428976946915280913 32734725321732710186460685)
              ·
                refine ⟨12275521995649766319922757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32734725321732710186460685 12275521995649766319922757)
                ·
                  refine ⟨2301660374184331184985517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12275521995649766319922757 2301660374184331184985517)
                  ·
                    refine ⟨863122640319124194369569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2301660374184331184985517 863122640319124194369569)
                    ·
                      rfl

theorem cell22_2521388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 3].length) (baseStart_2521388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2521388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2521388 prefixEnd_2521388 := by exact prefixLift 2521388
  have htrace : WordTrace (prefixWord ++ tailWord_2521388) baseStart_2521388 baseEnd_2521388 := by
    simpa [prefixWord, tailWord_2521388, baseEnd_2521388] using wordTrace_append hprefix tailTrace_2521388
  have hstable : (prefixWord ++ tailWord_2521388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2521388).length < 2 ^ (prefixWord ++ tailWord_2521388).sum := by decide
  have hdescent : baseEnd_2521388 < baseStart_2521388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2521388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2521433 : List Nat := [1, 2, 1, 2, 2, 2, 1, 1, 7, 3]
def baseStart_2521433 : Nat := 118140960795 + 2521433 * 2 ^ 59
def prefixEnd_2521433 : Nat := 4983230072969 + 3 ^ 40 * 2521433 * 2
def baseEnd_2521433 : Nat := 863138044738759076994431

theorem tailTrace_2521433 : CollatzResearch.WordTrace tailWord_2521433 prefixEnd_2521433 863138044738759076994431 := by
  unfold tailWord_2521433
  simp only [CollatzResearch.WordTrace]
  refine ⟨91964216674286342317584953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61309477782857561545056635 91964216674286342317584953)
  ·
    refine ⟨68973162505714756738188715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91964216674286342317584953 68973162505714756738188715)
    ·
      refine ⟨103459743758572135107283073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68973162505714756738188715 103459743758572135107283073)
      ·
        refine ⟨77594807818929101330462305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103459743758572135107283073 77594807818929101330462305)
        ·
          refine ⟨58196105864196825997846729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77594807818929101330462305 58196105864196825997846729)
          ·
            refine ⟨43647079398147619498385047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58196105864196825997846729 43647079398147619498385047)
            ·
              refine ⟨65470619097221429247577571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43647079398147619498385047 65470619097221429247577571)
              ·
                refine ⟨98205928645832143871366357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65470619097221429247577571 98205928645832143871366357)
                ·
                  refine ⟨2301701452636690871985149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 98205928645832143871366357 2301701452636690871985149)
                  ·
                    refine ⟨863138044738759076994431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2301701452636690871985149 863138044738759076994431)
                    ·
                      rfl

theorem cell22_2521433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 7, 3].length) (baseStart_2521433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2521433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2521433 prefixEnd_2521433 := by exact prefixLift 2521433
  have htrace : WordTrace (prefixWord ++ tailWord_2521433) baseStart_2521433 baseEnd_2521433 := by
    simpa [prefixWord, tailWord_2521433, baseEnd_2521433] using wordTrace_append hprefix tailTrace_2521433
  have hstable : (prefixWord ++ tailWord_2521433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2521433).length < 2 ^ (prefixWord ++ tailWord_2521433).sum := by decide
  have hdescent : baseEnd_2521433 < baseStart_2521433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2521433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2521484 : List Nat := [2, 2, 1, 2, 1, 6, 1, 3, 1, 3]
def baseStart_2521484 : Nat := 118140960795 + 2521484 * 2 ^ 59
def prefixEnd_2521484 : Nat := 4983230072969 + 3 ^ 40 * 2521484 * 2
def baseEnd_2521484 : Nat := 863155503081011943969275

theorem tailTrace_2521484 : CollatzResearch.WordTrace tailWord_2521484 prefixEnd_2521484 863155503081011943969275 := by
  unfold tailWord_2521484
  simp only [CollatzResearch.WordTrace]
  refine ⟨45983038398550789013845753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61310717864734385351794337 45983038398550789013845753)
  ·
    refine ⟨34487278798913091760384315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45983038398550789013845753 34487278798913091760384315)
    ·
      refine ⟨51730918198369637640576473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34487278798913091760384315 51730918198369637640576473)
      ·
        refine ⟨38798188648777228230432355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51730918198369637640576473 38798188648777228230432355)
        ·
          refine ⟨58197282973165842345648533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38798188648777228230432355 58197282973165842345648533)
          ·
            refine ⟨2727997639367148859952275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 58197282973165842345648533 2727997639367148859952275)
            ·
              refine ⟨4091996459050723289928413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2727997639367148859952275 4091996459050723289928413)
              ·
                refine ⟨1534498672144021233723155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4091996459050723289928413 1534498672144021233723155)
                ·
                  refine ⟨2301748008216031850584733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1534498672144021233723155 2301748008216031850584733)
                  ·
                    refine ⟨863155503081011943969275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2301748008216031850584733 863155503081011943969275)
                    ·
                      rfl

theorem cell22_2521484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 3, 1, 3].length) (baseStart_2521484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2521484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2521484 prefixEnd_2521484 := by exact prefixLift 2521484
  have htrace : WordTrace (prefixWord ++ tailWord_2521484) baseStart_2521484 baseEnd_2521484 := by
    simpa [prefixWord, tailWord_2521484, baseEnd_2521484] using wordTrace_append hprefix tailTrace_2521484
  have hstable : (prefixWord ++ tailWord_2521484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2521484).length < 2 ^ (prefixWord ++ tailWord_2521484).sum := by decide
  have hdescent : baseEnd_2521484 < baseStart_2521484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2521484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2521493 : List Nat := [1, 3, 2, 1, 1, 2, 1, 2, 5, 4]
def baseStart_2521493 : Nat := 118140960795 + 2521493 * 2 ^ 59
def prefixEnd_2521493 : Nat := 4983230072969 + 3 ^ 40 * 2521493 * 2
def baseEnd_2521493 : Nat := 863158583964938920494247

theorem tailTrace_2521493 : CollatzResearch.WordTrace tailWord_2521493 prefixEnd_2521493 863158583964938920494247 := by
  unfold tailWord_2521493
  simp only [CollatzResearch.WordTrace]
  refine ⟨91966405054068972564769133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61310936702712648376512755 91966405054068972564769133)
  ·
    refine ⟨34487401895275864711788425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91966405054068972564769133 34487401895275864711788425)
    ·
      refine ⟨25865551421456898533841319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34487401895275864711788425 25865551421456898533841319)
      ·
        refine ⟨38798327132185347800761979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25865551421456898533841319 38798327132185347800761979)
        ·
          refine ⟨58197490698278021701142969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38798327132185347800761979 58197490698278021701142969)
          ·
            refine ⟨43648118023708516275857227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58197490698278021701142969 43648118023708516275857227)
            ·
              refine ⟨65472177035562774413785841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43648118023708516275857227 65472177035562774413785841)
              ·
                refine ⟨49104132776672080810339381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65472177035562774413785841 49104132776672080810339381)
                ·
                  refine ⟨4603512447813007575969317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49104132776672080810339381 4603512447813007575969317)
                  ·
                    refine ⟨863158583964938920494247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4603512447813007575969317 863158583964938920494247)
                    ·
                      rfl

theorem cell22_2521493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 5, 4].length) (baseStart_2521493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2521493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2521493 prefixEnd_2521493 := by exact prefixLift 2521493
  have htrace : WordTrace (prefixWord ++ tailWord_2521493) baseStart_2521493 baseEnd_2521493 := by
    simpa [prefixWord, tailWord_2521493, baseEnd_2521493] using wordTrace_append hprefix tailTrace_2521493
  have hstable : (prefixWord ++ tailWord_2521493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2521493).length < 2 ^ (prefixWord ++ tailWord_2521493).sum := by decide
  have hdescent : baseEnd_2521493 < baseStart_2521493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2521493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2521501 : List Nat := [1, 4, 2, 1, 4, 1, 3, 2, 1, 3]
def baseStart_2521501 : Nat := 118140960795 + 2521501 * 2 ^ 59
def prefixEnd_2521501 : Nat := 4983230072969 + 3 ^ 40 * 2521501 * 2
def baseEnd_2521501 : Nat := 863161322528429566294223

theorem tailTrace_2521501 : CollatzResearch.WordTrace tailWord_2521501 prefixEnd_2521501 863161322528429566294223 := by
  unfold tailWord_2521501
  simp only [CollatzResearch.WordTrace]
  refine ⟨91966696838039989931060357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61311131225359993287373571 91966696838039989931060357)
  ·
    refine ⟨17243755657132498112073817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91966696838039989931060357 17243755657132498112073817)
    ·
      refine ⟨12932816742849373584055363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17243755657132498112073817 12932816742849373584055363)
      ·
        refine ⟨19399225114274060376083045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12932816742849373584055363 19399225114274060376083045)
        ·
          refine ⟨3637354708926386320515571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19399225114274060376083045 3637354708926386320515571)
          ·
            refine ⟨5456032063389579480773357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3637354708926386320515571 5456032063389579480773357)
            ·
              refine ⟨2046012023771092305290009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5456032063389579480773357 2046012023771092305290009)
              ·
                refine ⟨1534509017828319228967507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2046012023771092305290009 1534509017828319228967507)
                ·
                  refine ⟨2301763526742478843451261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1534509017828319228967507 2301763526742478843451261)
                  ·
                    refine ⟨863161322528429566294223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2301763526742478843451261 863161322528429566294223)
                    ·
                      rfl

theorem cell22_2521501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 3, 2, 1, 3].length) (baseStart_2521501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2521501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2521501 prefixEnd_2521501 := by exact prefixLift 2521501
  have htrace : WordTrace (prefixWord ++ tailWord_2521501) baseStart_2521501 baseEnd_2521501 := by
    simpa [prefixWord, tailWord_2521501, baseEnd_2521501] using wordTrace_append hprefix tailTrace_2521501
  have hstable : (prefixWord ++ tailWord_2521501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2521501).length < 2 ^ (prefixWord ++ tailWord_2521501).sum := by decide
  have hdescent : baseEnd_2521501 < baseStart_2521501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2521501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2521527 : List Nat := [1, 1, 3, 1, 3, 5, 1, 2, 1, 4]
def baseStart_2521527 : Nat := 118140960795 + 2521527 * 2 ^ 59
def prefixEnd_2521527 : Nat := 4983230072969 + 3 ^ 40 * 2521527 * 2
def baseEnd_2521527 : Nat := 863170222859774165144143

theorem tailTrace_2521527 : CollatzResearch.WordTrace tailWord_2521527 prefixEnd_2521527 863170222859774165144143 := by
  unfold tailWord_2521527
  simp only [CollatzResearch.WordTrace]
  refine ⟨91967645135945796371506835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61311763423963864247671223 91967645135945796371506835)
  ·
    refine ⟨137951467703918694557260253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91967645135945796371506835 137951467703918694557260253)
    ·
      refine ⟨51731800388969510458972595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137951467703918694557260253 51731800388969510458972595)
      ·
        refine ⟨77597700583454265688458893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51731800388969510458972595 77597700583454265688458893)
        ·
          refine ⟨29099137718795349633172085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77597700583454265688458893 29099137718795349633172085)
          ·
            refine ⟨2728044161137064028109883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29099137718795349633172085 2728044161137064028109883)
            ·
              refine ⟨4092066241705596042164825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2728044161137064028109883 4092066241705596042164825)
              ·
                refine ⟨3069049681279197031623619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4092066241705596042164825 3069049681279197031623619)
                ·
                  refine ⟨4603574521918795547435429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3069049681279197031623619 4603574521918795547435429)
                  ·
                    refine ⟨863170222859774165144143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4603574521918795547435429 863170222859774165144143)
                    ·
                      rfl

theorem cell22_2521527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 2, 1, 4].length) (baseStart_2521527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2521527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2521527 prefixEnd_2521527 := by exact prefixLift 2521527
  have htrace : WordTrace (prefixWord ++ tailWord_2521527) baseStart_2521527 baseEnd_2521527 := by
    simpa [prefixWord, tailWord_2521527, baseEnd_2521527] using wordTrace_append hprefix tailTrace_2521527
  have hstable : (prefixWord ++ tailWord_2521527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2521527).length < 2 ^ (prefixWord ++ tailWord_2521527).sum := by decide
  have hdescent : baseEnd_2521527 < baseStart_2521527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2521527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2521557 : List Nat := [1, 3, 2, 3, 1, 2, 1, 4, 2, 3]
def baseStart_2521557 : Nat := 118140960795 + 2521557 * 2 ^ 59
def prefixEnd_2521557 : Nat := 4983230072969 + 3 ^ 40 * 2521557 * 2
def baseEnd_2521557 : Nat := 863180492472864086894051

theorem tailTrace_2521557 : CollatzResearch.WordTrace tailWord_2521557 prefixEnd_2521557 863180492472864086894051 := by
  unfold tailWord_2521557
  simp only [CollatzResearch.WordTrace]
  refine ⟨91968739325837111495098925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61312492883891407663399283 91968739325837111495098925)
  ·
    refine ⟨34488277247188916810662097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91968739325837111495098925 34488277247188916810662097)
    ·
      refine ⟨25866207935391687607996573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34488277247188916810662097 25866207935391687607996573)
      ·
        refine ⟨9699827975771882852998715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25866207935391687607996573 9699827975771882852998715)
        ·
          refine ⟨14549741963657824279498073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9699827975771882852998715 14549741963657824279498073)
          ·
            refine ⟨10912306472743368209623555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14549741963657824279498073 10912306472743368209623555)
            ·
              refine ⟨16368459709115052314435333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10912306472743368209623555 16368459709115052314435333)
              ·
                refine ⟨3069086195459072308956625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16368459709115052314435333 3069086195459072308956625)
                ·
                  refine ⟨2301814646594304231717469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3069086195459072308956625 2301814646594304231717469)
                  ·
                    refine ⟨863180492472864086894051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2301814646594304231717469 863180492472864086894051)
                    ·
                      rfl

theorem cell22_2521557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 4, 2, 3].length) (baseStart_2521557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2521557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2521557 prefixEnd_2521557 := by exact prefixLift 2521557
  have htrace : WordTrace (prefixWord ++ tailWord_2521557) baseStart_2521557 baseEnd_2521557 := by
    simpa [prefixWord, tailWord_2521557, baseEnd_2521557] using wordTrace_append hprefix tailTrace_2521557
  have hstable : (prefixWord ++ tailWord_2521557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2521557).length < 2 ^ (prefixWord ++ tailWord_2521557).sum := by decide
  have hdescent : baseEnd_2521557 < baseStart_2521557 := by decide
  rcases family_descends (prefixWord ++ tailWord_2521557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2521583 : List Nat := [1, 1, 2, 1, 4, 1, 1, 1, 4, 6]
def baseStart_2521583 : Nat := 118140960795 + 2521583 * 2 ^ 59
def prefixEnd_2521583 : Nat := 4983230072969 + 3 ^ 40 * 2521583 * 2
def baseEnd_2521583 : Nat := 863189392804208685743971

theorem tailTrace_2521583 : CollatzResearch.WordTrace tailWord_2521583 prefixEnd_2521583 863189392804208685743971 := by
  unfold tailWord_2521583
  simp only [CollatzResearch.WordTrace]
  refine ⟨91969687623742917935545403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61313125082495278623696935 91969687623742917935545403)
  ·
    refine ⟨137954531435614376903318105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91969687623742917935545403 137954531435614376903318105)
    ·
      refine ⟨103465898576710782677488579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137954531435614376903318105 103465898576710782677488579)
      ·
        refine ⟨155198847865066174016232869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103465898576710782677488579 155198847865066174016232869)
        ·
          refine ⟨29099783974699907628043663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 155198847865066174016232869 29099783974699907628043663)
          ·
            refine ⟨43649675962049861442065495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29099783974699907628043663 43649675962049861442065495)
            ·
              refine ⟨65474513943074792163098243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43649675962049861442065495 65474513943074792163098243)
              ·
                refine ⟨98211770914612188244647365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65474513943074792163098243 98211770914612188244647365)
                ·
                  refine ⟨18414707046489785295871381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 98211770914612188244647365 18414707046489785295871381)
                  ·
                    refine ⟨863189392804208685743971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18414707046489785295871381 863189392804208685743971)
                    ·
                      rfl

theorem cell22_2521583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 4, 6].length) (baseStart_2521583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2521583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2521583 prefixEnd_2521583 := by exact prefixLift 2521583
  have htrace : WordTrace (prefixWord ++ tailWord_2521583) baseStart_2521583 baseEnd_2521583 := by
    simpa [prefixWord, tailWord_2521583, baseEnd_2521583] using wordTrace_append hprefix tailTrace_2521583
  have hstable : (prefixWord ++ tailWord_2521583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2521583).length < 2 ^ (prefixWord ++ tailWord_2521583).sum := by decide
  have hdescent : baseEnd_2521583 < baseStart_2521583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2521583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2521670 : List Nat := [6, 1, 1, 1, 2, 2, 3, 2, 1, 3]
def baseStart_2521670 : Nat := 118140960795 + 2521670 * 2 ^ 59
def prefixEnd_2521670 : Nat := 4983230072969 + 3 ^ 40 * 2521670 * 2
def baseEnd_2521670 : Nat := 863219174682169458818705

theorem tailTrace_2521670 : CollatzResearch.WordTrace tailWord_2521670 prefixEnd_2521670 863219174682169458818705 := by
  unfold tailWord_2521670
  simp only [CollatzResearch.WordTrace]
  refine ⟨2874151899200866618561327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 61315240516285154529308309 2874151899200866618561327)
  ·
    refine ⟨4311227848801299927841991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2874151899200866618561327 4311227848801299927841991)
    ·
      refine ⟨6466841773201949891762987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4311227848801299927841991 6466841773201949891762987)
      ·
        refine ⟨9700262659802924837644481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6466841773201949891762987 9700262659802924837644481)
        ·
          refine ⟨7275196994852193628233361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9700262659802924837644481 7275196994852193628233361)
          ·
            refine ⟨5456397746139145221175021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7275196994852193628233361 5456397746139145221175021)
            ·
              refine ⟨2046149154802179457940633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5456397746139145221175021 2046149154802179457940633)
              ·
                refine ⟨1534611866101634593455475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2046149154802179457940633 1534611866101634593455475)
                ·
                  refine ⟨2301917799152451890183213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1534611866101634593455475 2301917799152451890183213)
                  ·
                    refine ⟨863219174682169458818705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2301917799152451890183213 863219174682169458818705)
                    ·
                      rfl

theorem cell22_2521670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_2521670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2521670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2521670 prefixEnd_2521670 := by exact prefixLift 2521670
  have htrace : WordTrace (prefixWord ++ tailWord_2521670) baseStart_2521670 baseEnd_2521670 := by
    simpa [prefixWord, tailWord_2521670, baseEnd_2521670] using wordTrace_append hprefix tailTrace_2521670
  have hstable : (prefixWord ++ tailWord_2521670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2521670).length < 2 ^ (prefixWord ++ tailWord_2521670).sum := by decide
  have hdescent : baseEnd_2521670 < baseStart_2521670 := by decide
  rcases family_descends (prefixWord ++ tailWord_2521670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2521735 : List Nat := [1, 1, 4, 2, 1, 2, 1, 1, 1, 8]
def baseStart_2521735 : Nat := 118140960795 + 2521735 * 2 ^ 59
def prefixEnd_2521735 : Nat := 4983230072969 + 3 ^ 40 * 2521735 * 2
def baseEnd_2521735 : Nat := 863241425510530955943505

theorem tailTrace_2521735 : CollatzResearch.WordTrace tailWord_2521735 prefixEnd_2521735 863241425510530955943505 := by
  unfold tailWord_2521735
  simp only [CollatzResearch.WordTrace]
  refine ⟨91975231519192247895078659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61316821012794831930052439 91975231519192247895078659)
  ·
    refine ⟨137962847278788371842617989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91975231519192247895078659 137962847278788371842617989)
    ·
      refine ⟨25868033864772819720490873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 137962847278788371842617989 25868033864772819720490873)
      ·
        refine ⟨19401025398579614790368155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25868033864772819720490873 19401025398579614790368155)
        ·
          refine ⟨29101538097869422185552233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19401025398579614790368155 29101538097869422185552233)
          ·
            refine ⟨21826153573402066639164175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29101538097869422185552233 21826153573402066639164175)
            ·
              refine ⟨32739230360103099958746263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21826153573402066639164175 32739230360103099958746263)
              ·
                refine ⟨49108845540154649938119395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32739230360103099958746263 49108845540154649938119395)
                ·
                  refine ⟨73663268310231974907179093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49108845540154649938119395 73663268310231974907179093)
                  ·
                    refine ⟨863241425510530955943505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 73663268310231974907179093 863241425510530955943505)
                    ·
                      rfl

theorem cell22_2521735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 8].length) (baseStart_2521735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2521735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2521735 prefixEnd_2521735 := by exact prefixLift 2521735
  have htrace : WordTrace (prefixWord ++ tailWord_2521735) baseStart_2521735 baseEnd_2521735 := by
    simpa [prefixWord, tailWord_2521735, baseEnd_2521735] using wordTrace_append hprefix tailTrace_2521735
  have hstable : (prefixWord ++ tailWord_2521735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2521735).length < 2 ^ (prefixWord ++ tailWord_2521735).sum := by decide
  have hdescent : baseEnd_2521735 < baseStart_2521735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2521735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2521737 : List Nat := [1, 2, 1, 1, 4, 1, 1, 5, 3, 3]
def baseStart_2521737 : Nat := 118140960795 + 2521737 * 2 ^ 59
def prefixEnd_2521737 : Nat := 4983230072969 + 3 ^ 40 * 2521737 * 2
def baseEnd_2521737 : Nat := 863242110151403617393499

theorem tailTrace_2521737 : CollatzResearch.WordTrace tailWord_2521737 prefixEnd_2521737 863242110151403617393499 := by
  unfold tailWord_2521737
  simp only [CollatzResearch.WordTrace]
  refine ⟨91975304465185002236651465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61316869643456668157767643 91975304465185002236651465)
  ·
    refine ⟨68981478348888751677488599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91975304465185002236651465 68981478348888751677488599)
    ·
      refine ⟨103472217523333127516232899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68981478348888751677488599 103472217523333127516232899)
      ·
        refine ⟨155208326284999691274349349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103472217523333127516232899 155208326284999691274349349)
        ·
          refine ⟨29101561178437442113940503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 155208326284999691274349349 29101561178437442113940503)
          ·
            refine ⟨43652341767656163170910755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29101561178437442113940503 43652341767656163170910755)
            ·
              refine ⟨65478512651484244756366133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43652341767656163170910755 65478512651484244756366133)
              ·
                refine ⟨6138610561076647945909325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 65478512651484244756366133 6138610561076647945909325)
                ·
                  refine ⟨2301978960403742979715997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6138610561076647945909325 2301978960403742979715997)
                  ·
                    refine ⟨863242110151403617393499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2301978960403742979715997 863242110151403617393499)
                    ·
                      rfl

theorem cell22_2521737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 5, 3, 3].length) (baseStart_2521737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2521737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2521737 prefixEnd_2521737 := by exact prefixLift 2521737
  have htrace : WordTrace (prefixWord ++ tailWord_2521737) baseStart_2521737 baseEnd_2521737 := by
    simpa [prefixWord, tailWord_2521737, baseEnd_2521737] using wordTrace_append hprefix tailTrace_2521737
  have hstable : (prefixWord ++ tailWord_2521737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2521737).length < 2 ^ (prefixWord ++ tailWord_2521737).sum := by decide
  have hdescent : baseEnd_2521737 < baseStart_2521737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2521737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2521765 : List Nat := [1, 3, 1, 2, 1, 2, 1, 1, 3, 7]
def baseStart_2521765 : Nat := 118140960795 + 2521765 * 2 ^ 59
def prefixEnd_2521765 : Nat := 4983230072969 + 3 ^ 40 * 2521765 * 2
def baseEnd_2521765 : Nat := 863251695123620877693413

theorem tailTrace_2521765 : CollatzResearch.WordTrace tailWord_2521765 prefixEnd_2521765 863251695123620877693413 := by
  unfold tailWord_2521765
  simp only [CollatzResearch.WordTrace]
  refine ⟨91976325709083563018670749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61317550472722375345780499 91976325709083563018670749)
  ·
    refine ⟨34491122140906336132001531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91976325709083563018670749 34491122140906336132001531)
    ·
      refine ⟨51736683211359504198002297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34491122140906336132001531 51736683211359504198002297)
      ·
        refine ⟨38802512408519628148501723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51736683211359504198002297 38802512408519628148501723)
        ·
          refine ⟨58203768612779442222752585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38802512408519628148501723 58203768612779442222752585)
          ·
            refine ⟨43652826459584581667064439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58203768612779442222752585 43652826459584581667064439)
            ·
              refine ⟨65479239689376872500596659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43652826459584581667064439 65479239689376872500596659)
              ·
                refine ⟨98218859534065308750894989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65479239689376872500596659 98218859534065308750894989)
                ·
                  refine ⟨36832072325274490781585621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 98218859534065308750894989 36832072325274490781585621)
                  ·
                    refine ⟨863251695123620877693413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36832072325274490781585621 863251695123620877693413)
                    ·
                      rfl

theorem cell22_2521765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 7].length) (baseStart_2521765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2521765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2521765 prefixEnd_2521765 := by exact prefixLift 2521765
  have htrace : WordTrace (prefixWord ++ tailWord_2521765) baseStart_2521765 baseEnd_2521765 := by
    simpa [prefixWord, tailWord_2521765, baseEnd_2521765] using wordTrace_append hprefix tailTrace_2521765
  have hstable : (prefixWord ++ tailWord_2521765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2521765).length < 2 ^ (prefixWord ++ tailWord_2521765).sum := by decide
  have hdescent : baseEnd_2521765 < baseStart_2521765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2521765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2521908 : List Nat := [2, 5, 1, 1, 4, 1, 1, 7]
def baseStart_2521908 : Nat := 118140960795 + 2521908 * 2 ^ 59
def prefixEnd_2521908 : Nat := 4983230072969 + 3 ^ 40 * 2521908 * 2
def baseEnd_2521908 : Nat := 95922294105112907929775

theorem tailTrace_2521908 : CollatzResearch.WordTrace tailWord_2521908 prefixEnd_2521908 95922294105112907929775 := by
  unfold tailWord_2521908
  simp only [CollatzResearch.WordTrace]
  refine ⟨45990770673782749220563189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61321027565043665627417585 45990770673782749220563189)
  ·
    refine ⟨4311634750667132739427799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45990770673782749220563189 4311634750667132739427799)
    ·
      refine ⟨6467452126000699109141699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4311634750667132739427799 6467452126000699109141699)
      ·
        refine ⟨9701178189001048663712549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6467452126000699109141699 9701178189001048663712549)
        ·
          refine ⟨1818970910437696624446103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9701178189001048663712549 1818970910437696624446103)
          ·
            refine ⟨2728456365656544936669155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1818970910437696624446103 2728456365656544936669155)
            ·
              refine ⟨4092684548484817405003733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2728456365656544936669155 4092684548484817405003733)
              ·
                refine ⟨95922294105112907929775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4092684548484817405003733 95922294105112907929775)
                ·
                  rfl

theorem cell22_2521908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 7].length) (baseStart_2521908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2521908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2521908 prefixEnd_2521908 := by exact prefixLift 2521908
  have htrace : WordTrace (prefixWord ++ tailWord_2521908) baseStart_2521908 baseEnd_2521908 := by
    simpa [prefixWord, tailWord_2521908, baseEnd_2521908] using wordTrace_append hprefix tailTrace_2521908
  have hstable : (prefixWord ++ tailWord_2521908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2521908).length < 2 ^ (prefixWord ++ tailWord_2521908).sum := by decide
  have hdescent : baseEnd_2521908 < baseStart_2521908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2521908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2521919 : List Nat := [1, 1, 2, 2, 5, 1, 2, 3, 5]
def baseStart_2521919 : Nat := 118140960795 + 2521919 * 2 ^ 59
def prefixEnd_2521919 : Nat := 4983230072969 + 3 ^ 40 * 2521919 * 2
def baseEnd_2521919 : Nat := 287768137490271936447647

theorem tailTrace_2521919 : CollatzResearch.WordTrace tailWord_2521919 prefixEnd_2521919 287768137490271936447647 := by
  unfold tailWord_2521919
  simp only [CollatzResearch.WordTrace]
  refine ⟨91981942550525647319776811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61321295033683764879851207 91981942550525647319776811)
  ·
    refine ⟨137972913825788470979665217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91981942550525647319776811 137972913825788470979665217)
    ·
      refine ⟨103479685369341353234748913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137972913825788470979665217 103479685369341353234748913)
      ·
        refine ⟨77609764027006014926061685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103479685369341353234748913 77609764027006014926061685)
        ·
          refine ⟨7275915377531813899318283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 77609764027006014926061685 7275915377531813899318283)
          ·
            refine ⟨10913873066297720848977425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7275915377531813899318283 10913873066297720848977425)
            ·
              refine ⟨8185404799723290636733069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10913873066297720848977425 8185404799723290636733069)
              ·
                refine ⟨3069526799896233988774901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8185404799723290636733069 3069526799896233988774901)
                ·
                  refine ⟨287768137490271936447647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3069526799896233988774901 287768137490271936447647)
                  ·
                    rfl

theorem cell22_2521919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 3, 5].length) (baseStart_2521919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2521919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2521919 prefixEnd_2521919 := by exact prefixLift 2521919
  have htrace : WordTrace (prefixWord ++ tailWord_2521919) baseStart_2521919 baseEnd_2521919 := by
    simpa [prefixWord, tailWord_2521919, baseEnd_2521919] using wordTrace_append hprefix tailTrace_2521919
  have hstable : (prefixWord ++ tailWord_2521919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2521919).length < 2 ^ (prefixWord ++ tailWord_2521919).sum := by decide
  have hdescent : baseEnd_2521919 < baseStart_2521919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2521919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2521940 : List Nat := [2, 4, 1, 1, 4, 1, 2, 3, 1, 3]
def baseStart_2521940 : Nat := 118140960795 + 2521940 * 2 ^ 59
def prefixEnd_2521940 : Nat := 4983230072969 + 3 ^ 40 * 2521940 * 2
def baseEnd_2521940 : Nat := 863311601199978754567877

theorem tailTrace_2521940 : CollatzResearch.WordTrace tailWord_2521940 prefixEnd_2521940 863311601199978754567877 := by
  unfold tailWord_2521940
  simp only [CollatzResearch.WordTrace]
  refine ⟨45991354241724783953145637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61321805655633045270860849 45991354241724783953145637)
  ·
    refine ⟨8623378920323396991214807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45991354241724783953145637 8623378920323396991214807)
    ·
      refine ⟨12935068380485095486822211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8623378920323396991214807 12935068380485095486822211)
      ·
        refine ⟨19402602570727643230233317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12935068380485095486822211 19402602570727643230233317)
        ·
          refine ⟨3637987982011433105668747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19402602570727643230233317 3637987982011433105668747)
          ·
            refine ⟨5456981973017149658503121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3637987982011433105668747 5456981973017149658503121)
            ·
              refine ⟨4092736479762862243877341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5456981973017149658503121 4092736479762862243877341)
              ·
                refine ⟨1534776179911073341454003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4092736479762862243877341 1534776179911073341454003)
                ·
                  refine ⟨2302164269866610012181005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1534776179911073341454003 2302164269866610012181005)
                  ·
                    refine ⟨863311601199978754567877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2302164269866610012181005 863311601199978754567877)
                    ·
                      rfl

theorem cell22_2521940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 3, 1, 3].length) (baseStart_2521940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2521940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2521940 prefixEnd_2521940 := by exact prefixLift 2521940
  have htrace : WordTrace (prefixWord ++ tailWord_2521940) baseStart_2521940 baseEnd_2521940 := by
    simpa [prefixWord, tailWord_2521940, baseEnd_2521940] using wordTrace_append hprefix tailTrace_2521940
  have hstable : (prefixWord ++ tailWord_2521940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2521940).length < 2 ^ (prefixWord ++ tailWord_2521940).sum := by decide
  have hdescent : baseEnd_2521940 < baseStart_2521940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2521940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2521964 : List Nat := [2, 2, 1, 1, 4, 1, 4, 1, 6]
def baseStart_2521964 : Nat := 118140960795 + 2521964 * 2 ^ 59
def prefixEnd_2521964 : Nat := 4983230072969 + 3 ^ 40 * 2521964 * 2
def baseEnd_2521964 : Nat := 287773272296816897322601

theorem tailTrace_2521964 : CollatzResearch.WordTrace tailWord_2521964 prefixEnd_2521964 287773272296816897322601 := by
  unfold tailWord_2521964
  simp only [CollatzResearch.WordTrace]
  refine ⟨45991791917681310002582473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61322389223575080003443297 45991791917681310002582473)
  ·
    refine ⟨34493843938260982501936855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45991791917681310002582473 34493843938260982501936855)
    ·
      refine ⟨51740765907391473752905283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34493843938260982501936855 51740765907391473752905283)
      ·
        refine ⟨77611148861087210629357925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51740765907391473752905283 77611148861087210629357925)
        ·
          refine ⟨14552090411453851993004611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77611148861087210629357925 14552090411453851993004611)
          ·
            refine ⟨21828135617180777989506917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14552090411453851993004611 21828135617180777989506917)
            ·
              refine ⟨4092775428221395873032547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21828135617180777989506917 4092775428221395873032547)
              ·
                refine ⟨6139163142332093809548821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4092775428221395873032547 6139163142332093809548821)
                ·
                  refine ⟨287773272296816897322601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6139163142332093809548821 287773272296816897322601)
                  ·
                    rfl

theorem cell22_2521964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 6].length) (baseStart_2521964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2521964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2521964 prefixEnd_2521964 := by exact prefixLift 2521964
  have htrace : WordTrace (prefixWord ++ tailWord_2521964) baseStart_2521964 baseEnd_2521964 := by
    simpa [prefixWord, tailWord_2521964, baseEnd_2521964] using wordTrace_append hprefix tailTrace_2521964
  have hstable : (prefixWord ++ tailWord_2521964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2521964).length < 2 ^ (prefixWord ++ tailWord_2521964).sum := by decide
  have hdescent : baseEnd_2521964 < baseStart_2521964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2521964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2521979 : List Nat := [1, 1, 1, 1, 1, 5, 5, 1, 1, 5]
def baseStart_2521979 : Nat := 118140960795 + 2521979 * 2 ^ 59
def prefixEnd_2521979 : Nat := 4983230072969 + 3 ^ 40 * 2521979 * 2
def baseEnd_2521979 : Nat := 863324951696995652842757

theorem tailTrace_2521979 : CollatzResearch.WordTrace tailWord_2521979 prefixEnd_2521979 863324951696995652842757 := by
  unfold tailWord_2521979
  simp only [CollatzResearch.WordTrace]
  refine ⟨91984130930308277566960991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61322753953538851711307327 91984130930308277566960991)
  ·
    refine ⟨137976196395462416350441487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91984130930308277566960991 137976196395462416350441487)
    ·
      refine ⟨206964294593193624525662231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137976196395462416350441487 206964294593193624525662231)
      ·
        refine ⟨310446441889790436788493347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206964294593193624525662231 310446441889790436788493347)
        ·
          refine ⟨465669662834685655182740021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 310446441889790436788493347 465669662834685655182740021)
          ·
            refine ⟨43656530890751780173381877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 465669662834685655182740021 43656530890751780173381877)
            ·
              refine ⟨4092799771007979391254551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43656530890751780173381877 4092799771007979391254551)
              ·
                refine ⟨6139199656511969086881827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4092799771007979391254551 6139199656511969086881827)
                ·
                  refine ⟨9208799484767953630322741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6139199656511969086881827 9208799484767953630322741)
                  ·
                    refine ⟨863324951696995652842757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9208799484767953630322741 863324951696995652842757)
                    ·
                      rfl

theorem cell22_2521979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 1, 1, 5].length) (baseStart_2521979 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2521979 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2521979 prefixEnd_2521979 := by exact prefixLift 2521979
  have htrace : WordTrace (prefixWord ++ tailWord_2521979) baseStart_2521979 baseEnd_2521979 := by
    simpa [prefixWord, tailWord_2521979, baseEnd_2521979] using wordTrace_append hprefix tailTrace_2521979
  have hstable : (prefixWord ++ tailWord_2521979).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2521979).length < 2 ^ (prefixWord ++ tailWord_2521979).sum := by decide
  have hdescent : baseEnd_2521979 < baseStart_2521979 := by decide
  rcases family_descends (prefixWord ++ tailWord_2521979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2522058 : List Nat := [3, 1, 2, 1, 2, 1, 1, 7, 1, 3]
def baseStart_2522058 : Nat := 118140960795 + 2522058 * 2 ^ 59
def prefixEnd_2522058 : Nat := 4983230072969 + 3 ^ 40 * 2522058 * 2
def baseEnd_2522058 : Nat := 863351995011465780117515

theorem tailTrace_2522058 : CollatzResearch.WordTrace tailWord_2522058 prefixEnd_2522058 863351995011465780117515 := by
  unfold tailWord_2522058
  simp only [CollatzResearch.WordTrace]
  refine ⟨22996753074255518514771707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61324674864681382706057885 22996753074255518514771707)
  ·
    refine ⟨34495129611383277772157561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22996753074255518514771707 34495129611383277772157561)
    ·
      refine ⟨25871347208537458329118171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34495129611383277772157561 25871347208537458329118171)
      ·
        refine ⟨38807020812806187493677257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25871347208537458329118171 38807020812806187493677257)
        ·
          refine ⟨29105265609604640620257943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38807020812806187493677257 29105265609604640620257943)
          ·
            refine ⟨43657898414406960930386915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29105265609604640620257943 43657898414406960930386915)
            ·
              refine ⟨65486847621610441395580373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43657898414406960930386915 65486847621610441395580373)
              ·
                refine ⟨1534847991131494720208915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 65486847621610441395580373 1534847991131494720208915)
                ·
                  refine ⟨2302271986697242080313373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1534847991131494720208915 2302271986697242080313373)
                  ·
                    refine ⟨863351995011465780117515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2302271986697242080313373 863351995011465780117515)
                    ·
                      rfl

theorem cell22_2522058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 7, 1, 3].length) (baseStart_2522058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2522058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2522058 prefixEnd_2522058 := by exact prefixLift 2522058
  have htrace : WordTrace (prefixWord ++ tailWord_2522058) baseStart_2522058 baseEnd_2522058 := by
    simpa [prefixWord, tailWord_2522058, baseEnd_2522058] using wordTrace_append hprefix tailTrace_2522058
  have hstable : (prefixWord ++ tailWord_2522058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2522058).length < 2 ^ (prefixWord ++ tailWord_2522058).sum := by decide
  have hdescent : baseEnd_2522058 < baseStart_2522058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2522058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2522133 : List Nat := [1, 3, 2, 1, 4, 1, 2, 4, 4]
def baseStart_2522133 : Nat := 118140960795 + 2522133 * 2 ^ 59
def prefixEnd_2522133 : Nat := 4983230072969 + 3 ^ 40 * 2522133 * 2
def baseEnd_2522133 : Nat := 287792556348063528164095

theorem tailTrace_2522133 : CollatzResearch.WordTrace tailWord_2522133 prefixEnd_2522133 287792556348063528164095 := by
  unfold tailWord_2522133
  simp only [CollatzResearch.WordTrace]
  refine ⟨91989747771750361868067053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61326498514500241245378035 91989747771750361868067053)
  ·
    refine ⟨34496155414406385700525145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91989747771750361868067053 34496155414406385700525145)
    ·
      refine ⟨25872116560804789275393859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34496155414406385700525145 25872116560804789275393859)
      ·
        refine ⟨38808174841207183913090789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25872116560804789275393859 38808174841207183913090789)
        ·
          refine ⟨7276532782726346983704523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38808174841207183913090789 7276532782726346983704523)
          ·
            refine ⟨10914799174089520475556785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7276532782726346983704523 10914799174089520475556785)
            ·
              refine ⟨8186099380567140356667589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10914799174089520475556785 8186099380567140356667589)
              ·
                refine ⟨1534893633856338816875173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8186099380567140356667589 1534893633856338816875173)
                ·
                  refine ⟨287792556348063528164095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1534893633856338816875173 287792556348063528164095)
                  ·
                    rfl

theorem cell22_2522133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 4, 4].length) (baseStart_2522133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2522133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2522133 prefixEnd_2522133 := by exact prefixLift 2522133
  have htrace : WordTrace (prefixWord ++ tailWord_2522133) baseStart_2522133 baseEnd_2522133 := by
    simpa [prefixWord, tailWord_2522133, baseEnd_2522133] using wordTrace_append hprefix tailTrace_2522133
  have hstable : (prefixWord ++ tailWord_2522133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2522133).length < 2 ^ (prefixWord ++ tailWord_2522133).sum := by decide
  have hdescent : baseEnd_2522133 < baseStart_2522133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2522133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2522146 : List Nat := [3, 3, 1, 1, 1, 3, 1, 2, 1, 6]
def baseStart_2522146 : Nat := 118140960795 + 2522146 * 2 ^ 59
def prefixEnd_2522146 : Nat := 4983230072969 + 3 ^ 40 * 2522146 * 2
def baseEnd_2522146 : Nat := 863382119209862883917245

theorem tailTrace_2522146 : CollatzResearch.WordTrace tailWord_2522146 prefixEnd_2522146 863382119209862883917245 := by
  unfold tailWord_2522146
  simp only [CollatzResearch.WordTrace]
  refine ⟨22997555480175816272072573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61326814613802176725526861 22997555480175816272072573)
  ·
    refine ⟨8624083305065931102027215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22997555480175816272072573 8624083305065931102027215)
    ·
      refine ⟨12936124957598896653040823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8624083305065931102027215 12936124957598896653040823)
      ·
        refine ⟨19404187436398344979561235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12936124957598896653040823 19404187436398344979561235)
        ·
          refine ⟨29106281154597517469341853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19404187436398344979561235 29106281154597517469341853)
          ·
            refine ⟨10914855432974069051003195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29106281154597517469341853 10914855432974069051003195)
            ·
              refine ⟨16372283149461103576504793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10914855432974069051003195 16372283149461103576504793)
              ·
                refine ⟨12279212362095827682378595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16372283149461103576504793 12279212362095827682378595)
                ·
                  refine ⟨18418818543143741523567893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12279212362095827682378595 18418818543143741523567893)
                  ·
                    refine ⟨863382119209862883917245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18418818543143741523567893 863382119209862883917245)
                    ·
                      rfl

theorem cell22_2522146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_2522146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2522146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2522146 prefixEnd_2522146 := by exact prefixLift 2522146
  have htrace : WordTrace (prefixWord ++ tailWord_2522146) baseStart_2522146 baseEnd_2522146 := by
    simpa [prefixWord, tailWord_2522146, baseEnd_2522146] using wordTrace_append hprefix tailTrace_2522146
  have hstable : (prefixWord ++ tailWord_2522146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2522146).length < 2 ^ (prefixWord ++ tailWord_2522146).sum := by decide
  have hdescent : baseEnd_2522146 < baseStart_2522146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2522146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2522148 : List Nat := [2, 3, 1, 4, 1, 1, 3, 1, 1, 5]
def baseStart_2522148 : Nat := 118140960795 + 2522148 * 2 ^ 59
def prefixEnd_2522148 : Nat := 4983230072969 + 3 ^ 40 * 2522148 * 2
def baseEnd_2522148 : Nat := 863382803850735545367239

theorem tailTrace_2522148 : CollatzResearch.WordTrace tailWord_2522148 prefixEnd_2522148 863382803850735545367239 := by
  unfold tailWord_2522148
  simp only [CollatzResearch.WordTrace]
  refine ⟨45995147433348009714931549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61326863244464012953242065 45995147433348009714931549)
  ·
    refine ⟨17248180287505503643099331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45995147433348009714931549 17248180287505503643099331)
    ·
      refine ⟨25872270431258255464648997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17248180287505503643099331 25872270431258255464648997)
      ·
        refine ⟨4851050705860922899621687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25872270431258255464648997 4851050705860922899621687)
        ·
          refine ⟨7276576058791384349432531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4851050705860922899621687 7276576058791384349432531)
          ·
            refine ⟨10914864088187076524148797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7276576058791384349432531 10914864088187076524148797)
            ·
              refine ⟨4093074033070153696555799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10914864088187076524148797 4093074033070153696555799)
              ·
                refine ⟨6139611049605230544833699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4093074033070153696555799 6139611049605230544833699)
                ·
                  refine ⟨9209416574407845817250549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6139611049605230544833699 9209416574407845817250549)
                  ·
                    refine ⟨863382803850735545367239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9209416574407845817250549 863382803850735545367239)
                    ·
                      rfl

theorem cell22_2522148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 1, 1, 5].length) (baseStart_2522148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2522148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2522148 prefixEnd_2522148 := by exact prefixLift 2522148
  have htrace : WordTrace (prefixWord ++ tailWord_2522148) baseStart_2522148 baseEnd_2522148 := by
    simpa [prefixWord, tailWord_2522148, baseEnd_2522148] using wordTrace_append hprefix tailTrace_2522148
  have hstable : (prefixWord ++ tailWord_2522148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2522148).length < 2 ^ (prefixWord ++ tailWord_2522148).sum := by decide
  have hdescent : baseEnd_2522148 < baseStart_2522148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2522148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2522193 : List Nat := [1, 2, 2, 1, 3, 1, 5, 1, 3, 3]
def baseStart_2522193 : Nat := 118140960795 + 2522193 * 2 ^ 59
def prefixEnd_2522193 : Nat := 4983230072969 + 3 ^ 40 * 2522193 * 2
def baseEnd_2522193 : Nat := 863398208270370427992101

theorem tailTrace_2522193 : CollatzResearch.WordTrace tailWord_2522193 prefixEnd_2522193 863398208270370427992101 := by
  unfold tailWord_2522193
  simp only [CollatzResearch.WordTrace]
  refine ⟨91991936151532992115251233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61327957434355328076834155 91991936151532992115251233)
  ·
    refine ⟨68993952113649744086438425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91991936151532992115251233 68993952113649744086438425)
    ·
      refine ⟨51745464085237308064828819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68993952113649744086438425 51745464085237308064828819)
      ·
        refine ⟨77618196127855962097243229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51745464085237308064828819 77618196127855962097243229)
        ·
          refine ⟨29106823547945985786466211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77618196127855962097243229 29106823547945985786466211)
          ·
            refine ⟨43660235321918978679699317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29106823547945985786466211 43660235321918978679699317)
            ·
              refine ⟨4093147061429904251221811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43660235321918978679699317 4093147061429904251221811)
              ·
                refine ⟨6139720592144856376832717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4093147061429904251221811 6139720592144856376832717)
                ·
                  refine ⟨2302395222054321141312269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6139720592144856376832717 2302395222054321141312269)
                  ·
                    refine ⟨863398208270370427992101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2302395222054321141312269 863398208270370427992101)
                    ·
                      rfl

theorem cell22_2522193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 1, 3, 3].length) (baseStart_2522193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2522193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2522193 prefixEnd_2522193 := by exact prefixLift 2522193
  have htrace : WordTrace (prefixWord ++ tailWord_2522193) baseStart_2522193 baseEnd_2522193 := by
    simpa [prefixWord, tailWord_2522193, baseEnd_2522193] using wordTrace_append hprefix tailTrace_2522193
  have hstable : (prefixWord ++ tailWord_2522193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2522193).length < 2 ^ (prefixWord ++ tailWord_2522193).sum := by decide
  have hdescent : baseEnd_2522193 < baseStart_2522193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2522193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2522244 : List Nat := [2, 3, 2, 1, 2, 4, 2, 2, 1, 3]
def baseStart_2522244 : Nat := 118140960795 + 2522244 * 2 ^ 59
def prefixEnd_2522244 : Nat := 4983230072969 + 3 ^ 40 * 2522244 * 2
def baseEnd_2522244 : Nat := 863415666612623294966945

theorem tailTrace_2522244 : CollatzResearch.WordTrace tailWord_2522244 prefixEnd_2522244 863415666612623294966945 := by
  unfold tailWord_2522244
  simp only [CollatzResearch.WordTrace]
  refine ⟨45996898137174113912678893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61329197516232151883571857 45996898137174113912678893)
  ·
    refine ⟨17248836801440292717254585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45996898137174113912678893 17248836801440292717254585)
    ·
      refine ⟨12936627601080219537940939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17248836801440292717254585 12936627601080219537940939)
      ·
        refine ⟨19404941401620329306911409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12936627601080219537940939 19404941401620329306911409)
        ·
          refine ⟨14553706051215246980183557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19404941401620329306911409 14553706051215246980183557)
          ·
            refine ⟨2728819884602858808784417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14553706051215246980183557 2728819884602858808784417)
            ·
              refine ⟨2046614913452144106588313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2728819884602858808784417 2046614913452144106588313)
              ·
                refine ⟨1534961185089108079941235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2046614913452144106588313 1534961185089108079941235)
                ·
                  refine ⟨2302441777633662119911853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1534961185089108079941235 2302441777633662119911853)
                  ·
                    refine ⟨863415666612623294966945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2302441777633662119911853 863415666612623294966945)
                    ·
                      rfl

theorem cell22_2522244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 2, 2, 1, 3].length) (baseStart_2522244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2522244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2522244 prefixEnd_2522244 := by exact prefixLift 2522244
  have htrace : WordTrace (prefixWord ++ tailWord_2522244) baseStart_2522244 baseEnd_2522244 := by
    simpa [prefixWord, tailWord_2522244, baseEnd_2522244] using wordTrace_append hprefix tailTrace_2522244
  have hstable : (prefixWord ++ tailWord_2522244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2522244).length < 2 ^ (prefixWord ++ tailWord_2522244).sum := by decide
  have hdescent : baseEnd_2522244 < baseStart_2522244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2522244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2522268 : List Nat := [2, 2, 3, 2, 1, 3, 1, 2, 6]
def baseStart_2522268 : Nat := 118140960795 + 2522268 * 2 ^ 59
def prefixEnd_2522268 : Nat := 4983230072969 + 3 ^ 40 * 2522268 * 2
def baseEnd_2522268 : Nat := 287807960767698410788957

theorem tailTrace_2522268 : CollatzResearch.WordTrace tailWord_2522268 prefixEnd_2522268 287807960767698410788957 := by
  unfold tailWord_2522268
  simp only [CollatzResearch.WordTrace]
  refine ⟨45997335813130639962115729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61329781084174186616154305 45997335813130639962115729)
  ·
    refine ⟨34498001859847979971586797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45997335813130639962115729 34498001859847979971586797)
    ·
      refine ⟨12936750697442992489345049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34498001859847979971586797 12936750697442992489345049)
      ·
        refine ⟨9702563023082244367008787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12936750697442992489345049 9702563023082244367008787)
        ·
          refine ⟨14553844534623366550513181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9702563023082244367008787 14553844534623366550513181)
          ·
            refine ⟨5457691700483762456442443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14553844534623366550513181 5457691700483762456442443)
            ·
              refine ⟨8186537550725643684663665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5457691700483762456442443 8186537550725643684663665)
              ·
                refine ⟨6139903163044232763497749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8186537550725643684663665 6139903163044232763497749)
                ·
                  refine ⟨287807960767698410788957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6139903163044232763497749 287807960767698410788957)
                  ·
                    rfl

theorem cell22_2522268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 2, 6].length) (baseStart_2522268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2522268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2522268 prefixEnd_2522268 := by exact prefixLift 2522268
  have htrace : WordTrace (prefixWord ++ tailWord_2522268) baseStart_2522268 baseEnd_2522268 := by
    simpa [prefixWord, tailWord_2522268, baseEnd_2522268] using wordTrace_append hprefix tailTrace_2522268
  have hstable : (prefixWord ++ tailWord_2522268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2522268).length < 2 ^ (prefixWord ++ tailWord_2522268).sum := by decide
  have hdescent : baseEnd_2522268 < baseStart_2522268 := by decide
  rcases family_descends (prefixWord ++ tailWord_2522268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2522270 : List Nat := [4, 3, 1, 1, 2, 1, 2, 1, 3, 4]
def baseStart_2522270 : Nat := 118140960795 + 2522270 * 2 ^ 59
def prefixEnd_2522270 : Nat := 4983230072969 + 3 ^ 40 * 2522270 * 2
def baseEnd_2522270 : Nat := 863424566943967893816865

theorem tailTrace_2522270 : CollatzResearch.WordTrace tailWord_2522270 prefixEnd_2522270 863424566943967893816865 := by
  unfold tailWord_2522270
  simp only [CollatzResearch.WordTrace]
  refine ⟨11499343071531754283225533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61329829714836022843869509 11499343071531754283225533)
  ·
    refine ⟨4312253651824407856209575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11499343071531754283225533 4312253651824407856209575)
    ·
      refine ⟨6468380477736611784314363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4312253651824407856209575 6468380477736611784314363)
      ·
        refine ⟨9702570716604917676471545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6468380477736611784314363 9702570716604917676471545)
        ·
          refine ⟨7276928037453688257353659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9702570716604917676471545 7276928037453688257353659)
          ·
            refine ⟨10915392056180532386030489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7276928037453688257353659 10915392056180532386030489)
            ·
              refine ⟨8186544042135399289522867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10915392056180532386030489 8186544042135399289522867)
              ·
                refine ⟨12279816063203098934284301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8186544042135399289522867 12279816063203098934284301)
                ·
                  refine ⟨4604931023701162100356613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12279816063203098934284301 4604931023701162100356613)
                  ·
                    refine ⟨863424566943967893816865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4604931023701162100356613 863424566943967893816865)
                    ·
                      rfl

theorem cell22_2522270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_2522270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2522270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2522270 prefixEnd_2522270 := by exact prefixLift 2522270
  have htrace : WordTrace (prefixWord ++ tailWord_2522270) baseStart_2522270 baseEnd_2522270 := by
    simpa [prefixWord, tailWord_2522270, baseEnd_2522270] using wordTrace_append hprefix tailTrace_2522270
  have hstable : (prefixWord ++ tailWord_2522270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2522270).length < 2 ^ (prefixWord ++ tailWord_2522270).sum := by decide
  have hdescent : baseEnd_2522270 < baseStart_2522270 := by decide
  rcases family_descends (prefixWord ++ tailWord_2522270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2522281 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 8, 4]
def baseStart_2522281 : Nat := 118140960795 + 2522281 * 2 ^ 59
def prefixEnd_2522281 : Nat := 4983230072969 + 3 ^ 40 * 2522281 * 2
def baseEnd_2522281 : Nat := 863428332468767531791831

theorem tailTrace_2522281 : CollatzResearch.WordTrace tailWord_2522281 prefixEnd_2522281 863428332468767531791831 := by
  unfold tailWord_2522281
  simp only [CollatzResearch.WordTrace]
  refine ⟨91995145775214183144454697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61330097183476122096303131 91995145775214183144454697)
  ·
    refine ⟨68996359331410637358341023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91995145775214183144454697 68996359331410637358341023)
    ·
      refine ⟨103494538997115956037511535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68996359331410637358341023 103494538997115956037511535)
      ·
        refine ⟨155241808495673934056267303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103494538997115956037511535 155241808495673934056267303)
        ·
          refine ⟨232862712743510901084400955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155241808495673934056267303 232862712743510901084400955)
          ·
            refine ⟨349294069115266351626601433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 232862712743510901084400955 349294069115266351626601433)
            ·
              refine ⟨261970551836449763719951075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 349294069115266351626601433 261970551836449763719951075)
              ·
                refine ⟨392955827754674645579926613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 261970551836449763719951075 392955827754674645579926613)
                ·
                  refine ⟨4604951106500093502889765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 392955827754674645579926613 4604951106500093502889765)
                  ·
                    refine ⟨863428332468767531791831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4604951106500093502889765 863428332468767531791831)
                    ·
                      rfl

theorem cell22_2522281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 8, 4].length) (baseStart_2522281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2522281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2522281 prefixEnd_2522281 := by exact prefixLift 2522281
  have htrace : WordTrace (prefixWord ++ tailWord_2522281) baseStart_2522281 baseEnd_2522281 := by
    simpa [prefixWord, tailWord_2522281, baseEnd_2522281] using wordTrace_append hprefix tailTrace_2522281
  have hstable : (prefixWord ++ tailWord_2522281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2522281).length < 2 ^ (prefixWord ++ tailWord_2522281).sum := by decide
  have hdescent : baseEnd_2522281 < baseStart_2522281 := by decide
  rcases family_descends (prefixWord ++ tailWord_2522281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2522300 : List Nat := [2, 2, 2, 3, 2, 2, 1, 1, 4, 3]
def baseStart_2522300 : Nat := 118140960795 + 2522300 * 2 ^ 59
def prefixEnd_2522300 : Nat := 4983230072969 + 3 ^ 40 * 2522300 * 2
def baseEnd_2522300 : Nat := 863434836557057815566773

theorem tailTrace_2522300 : CollatzResearch.WordTrace tailWord_2522300 prefixEnd_2522300 863434836557057815566773 := by
  unfold tailWord_2522300
  simp only [CollatzResearch.WordTrace]
  refine ⟨45997919381072674694698177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61330559174763566259597569 45997919381072674694698177)
  ·
    refine ⟨34498439535804506021023633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45997919381072674694698177 34498439535804506021023633)
    ·
      refine ⟨25873829651853379515767725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34498439535804506021023633 25873829651853379515767725)
      ·
        refine ⟨9702686119445017318412897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25873829651853379515767725 9702686119445017318412897)
        ·
          refine ⟨7277014589583762988809673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9702686119445017318412897 7277014589583762988809673)
          ·
            refine ⟨5457760942187822241607255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7277014589583762988809673 5457760942187822241607255)
            ·
              refine ⟨8186641413281733362410883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5457760942187822241607255 8186641413281733362410883)
              ·
                refine ⟨12279962119922600043616325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8186641413281733362410883 12279962119922600043616325)
                ·
                  refine ⟨2302492897485487508178061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12279962119922600043616325 2302492897485487508178061)
                  ·
                    refine ⟨863434836557057815566773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2302492897485487508178061 863434836557057815566773)
                    ·
                      rfl

theorem cell22_2522300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 1, 4, 3].length) (baseStart_2522300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2522300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2522300 prefixEnd_2522300 := by exact prefixLift 2522300
  have htrace : WordTrace (prefixWord ++ tailWord_2522300) baseStart_2522300 baseEnd_2522300 := by
    simpa [prefixWord, tailWord_2522300, baseEnd_2522300] using wordTrace_append hprefix tailTrace_2522300
  have hstable : (prefixWord ++ tailWord_2522300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2522300).length < 2 ^ (prefixWord ++ tailWord_2522300).sum := by decide
  have hdescent : baseEnd_2522300 < baseStart_2522300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2522300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2522413 : List Nat := [1, 5, 3, 1, 1, 3, 2, 2, 1, 3]
def baseStart_2522413 : Nat := 118140960795 + 2522413 * 2 ^ 59
def prefixEnd_2522413 : Nat := 4983230072969 + 3 ^ 40 * 2522413 * 2
def baseEnd_2522413 : Nat := 863473518766363187491427

theorem tailTrace_2522413 : CollatzResearch.WordTrace tailWord_2522413 prefixEnd_2522413 863473518766363187491427 := by
  unfold tailWord_2522413
  simp only [CollatzResearch.WordTrace]
  refine ⟨91999960210735969688259893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61333306807157313125506595 91999960210735969688259893)
  ·
    refine ⟨8624996269756497158274365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 91999960210735969688259893 8624996269756497158274365)
    ·
      refine ⟨3234373601158686434352887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8624996269756497158274365 3234373601158686434352887)
      ·
        refine ⟨4851560401738029651529331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3234373601158686434352887 4851560401738029651529331)
        ·
          refine ⟨7277340602607044477293997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4851560401738029651529331 7277340602607044477293997)
          ·
            refine ⟨2729002725977641678985249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7277340602607044477293997 2729002725977641678985249)
            ·
              refine ⟨2046752044483231259238937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2729002725977641678985249 2046752044483231259238937)
              ·
                refine ⟨1535064033362423444429203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2046752044483231259238937 1535064033362423444429203)
                ·
                  refine ⟨2302596050043635166643805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1535064033362423444429203 2302596050043635166643805)
                  ·
                    refine ⟨863473518766363187491427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2302596050043635166643805 863473518766363187491427)
                    ·
                      rfl

theorem cell22_2522413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_2522413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2522413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2522413 prefixEnd_2522413 := by exact prefixLift 2522413
  have htrace : WordTrace (prefixWord ++ tailWord_2522413) baseStart_2522413 baseEnd_2522413 := by
    simpa [prefixWord, tailWord_2522413, baseEnd_2522413] using wordTrace_append hprefix tailTrace_2522413
  have hstable : (prefixWord ++ tailWord_2522413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2522413).length < 2 ^ (prefixWord ++ tailWord_2522413).sum := by decide
  have hdescent : baseEnd_2522413 < baseStart_2522413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2522413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2522420 : List Nat := [2, 5, 1, 1, 1, 1, 2, 3, 6]
def baseStart_2522420 : Nat := 118140960795 + 2522420 * 2 ^ 59
def prefixEnd_2522420 : Nat := 4983230072969 + 3 ^ 40 * 2522420 * 2
def baseEnd_2522420 : Nat := 287825305003139167522135

theorem tailTrace_2522420 : CollatzResearch.WordTrace tailWord_2522420 prefixEnd_2522420 287825305003139167522135 := by
  unfold tailWord_2522420
  simp only [CollatzResearch.WordTrace]
  refine ⟨46000107760855304941882357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61333477014473739922509809 46000107760855304941882357)
  ·
    refine ⟨4312510102580184838301471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46000107760855304941882357 4312510102580184838301471)
    ·
      refine ⟨6468765153870277257452207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4312510102580184838301471 6468765153870277257452207)
      ·
        refine ⟨9703147730805415886178311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6468765153870277257452207 9703147730805415886178311)
        ·
          refine ⟨14554721596208123829267467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9703147730805415886178311 14554721596208123829267467)
          ·
            refine ⟨21832082394312185743901201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14554721596208123829267467 21832082394312185743901201)
            ·
              refine ⟨16374061795734139307925901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21832082394312185743901201 16374061795734139307925901)
              ·
                refine ⟨6140273173400302240472213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16374061795734139307925901 6140273173400302240472213)
                ·
                  refine ⟨287825305003139167522135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6140273173400302240472213 287825305003139167522135)
                  ·
                    rfl

theorem cell22_2522420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_2522420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2522420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2522420 prefixEnd_2522420 := by exact prefixLift 2522420
  have htrace : WordTrace (prefixWord ++ tailWord_2522420) baseStart_2522420 baseEnd_2522420 := by
    simpa [prefixWord, tailWord_2522420, baseEnd_2522420] using wordTrace_append hprefix tailTrace_2522420
  have hstable : (prefixWord ++ tailWord_2522420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2522420).length < 2 ^ (prefixWord ++ tailWord_2522420).sum := by decide
  have hdescent : baseEnd_2522420 < baseStart_2522420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2522420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2522570 : List Nat := [3, 1, 2, 1, 2, 3, 1, 1, 3, 5]
def baseStart_2522570 : Nat := 118140960795 + 2522570 * 2 ^ 59
def prefixEnd_2522570 : Nat := 4983230072969 + 3 ^ 40 * 2522570 * 2
def baseEnd_2522570 : Nat := 863527263074867111315945

theorem tailTrace_2522570 : CollatzResearch.WordTrace tailWord_2522570 prefixEnd_2522570 863527263074867111315945 := by
  unfold tailWord_2522570
  simp only [CollatzResearch.WordTrace]
  refine ⟨23001421617791796375431291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61337124314111457001150109 23001421617791796375431291)
  ·
    refine ⟨34502132426687694563146937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23001421617791796375431291 34502132426687694563146937)
    ·
      refine ⟨25876599320015770922360203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34502132426687694563146937 25876599320015770922360203)
      ·
        refine ⟨38814898980023656383540305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25876599320015770922360203 38814898980023656383540305)
        ·
          refine ⟨29111174235017742287655229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38814898980023656383540305 29111174235017742287655229)
          ·
            refine ⟨10916690338131653357870711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29111174235017742287655229 10916690338131653357870711)
            ·
              refine ⟨16375035507197480036806067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10916690338131653357870711 16375035507197480036806067)
              ·
                refine ⟨24562553260796220055209101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16375035507197480036806067 24562553260796220055209101)
                ·
                  refine ⟨9210957472798582520703413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24562553260796220055209101 9210957472798582520703413)
                  ·
                    refine ⟨863527263074867111315945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9210957472798582520703413 863527263074867111315945)
                    ·
                      rfl

theorem cell22_2522570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 3, 5].length) (baseStart_2522570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2522570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2522570 prefixEnd_2522570 := by exact prefixLift 2522570
  have htrace : WordTrace (prefixWord ++ tailWord_2522570) baseStart_2522570 baseEnd_2522570 := by
    simpa [prefixWord, tailWord_2522570, baseEnd_2522570] using wordTrace_append hprefix tailTrace_2522570
  have hstable : (prefixWord ++ tailWord_2522570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2522570).length < 2 ^ (prefixWord ++ tailWord_2522570).sum := by decide
  have hdescent : baseEnd_2522570 < baseStart_2522570 := by decide
  rcases family_descends (prefixWord ++ tailWord_2522570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2522589 : List Nat := [1, 4, 3, 1, 1, 3, 1, 4, 4]
def baseStart_2522589 : Nat := 118140960795 + 2522589 * 2 ^ 59
def prefixEnd_2522589 : Nat := 4983230072969 + 3 ^ 40 * 2522589 * 2
def baseEnd_2522589 : Nat := 287844589054385798363629

theorem tailTrace_2522589 : CollatzResearch.WordTrace tailWord_2522589 prefixEnd_2522589 287844589054385798363629 := by
  unfold tailWord_2522589
  simp only [CollatzResearch.WordTrace]
  refine ⟨92006379458098351746666821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61337586305398901164444547 92006379458098351746666821)
  ·
    refine ⟨17251196148393440952500029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92006379458098351746666821 17251196148393440952500029)
    ·
      refine ⟨6469198555647540357187511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17251196148393440952500029 6469198555647540357187511)
      ·
        refine ⟨9703797833471310535781267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6469198555647540357187511 9703797833471310535781267)
        ·
          refine ⟨14555696750206965803671901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9703797833471310535781267 14555696750206965803671901)
          ·
            refine ⟨5458386281327612176376963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14555696750206965803671901 5458386281327612176376963)
            ·
              refine ⟨8187579421991418264565445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5458386281327612176376963 8187579421991418264565445)
              ·
                refine ⟨1535171141623390924606021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8187579421991418264565445 1535171141623390924606021)
                ·
                  refine ⟨287844589054385798363629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1535171141623390924606021 287844589054385798363629)
                  ·
                    rfl

theorem cell22_2522589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 4, 4].length) (baseStart_2522589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2522589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2522589 prefixEnd_2522589 := by exact prefixLift 2522589
  have htrace : WordTrace (prefixWord ++ tailWord_2522589) baseStart_2522589 baseEnd_2522589 := by
    simpa [prefixWord, tailWord_2522589, baseEnd_2522589] using wordTrace_append hprefix tailTrace_2522589
  have hstable : (prefixWord ++ tailWord_2522589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2522589).length < 2 ^ (prefixWord ++ tailWord_2522589).sum := by decide
  have hdescent : baseEnd_2522589 < baseStart_2522589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2522589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2522638 : List Nat := [4, 1, 1, 2, 5, 1, 1, 2, 2, 3]
def baseStart_2522638 : Nat := 118140960795 + 2522638 * 2 ^ 59
def prefixEnd_2522638 : Nat := 4983230072969 + 3 ^ 40 * 2522638 * 2
def baseEnd_2522638 : Nat := 863550540864537600615737

theorem tailTrace_2522638 : CollatzResearch.WordTrace tailWord_2522638 prefixEnd_2522638 863550540864537600615737 := by
  unfold tailWord_2522638
  simp only [CollatzResearch.WordTrace]
  refine ⟨11501020829365104139400071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61338777756613888743467045 11501020829365104139400071)
  ·
    refine ⟨17251531244047656209100107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11501020829365104139400071 17251531244047656209100107)
    ·
      refine ⟨25877296866071484313650161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17251531244047656209100107 25877296866071484313650161)
      ·
        refine ⟨19407972649553613235237621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25877296866071484313650161 19407972649553613235237621)
        ·
          refine ⟨1819497435895651240803527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19407972649553613235237621 1819497435895651240803527)
          ·
            refine ⟨2729246153843476861205291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1819497435895651240803527 2729246153843476861205291)
            ·
              refine ⟨4093869230765215291807937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2729246153843476861205291 4093869230765215291807937)
              ·
                refine ⟨3070401923073911468855953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4093869230765215291807937 3070401923073911468855953)
                ·
                  refine ⟨2302801442305433601641965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3070401923073911468855953 2302801442305433601641965)
                  ·
                    refine ⟨863550540864537600615737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2302801442305433601641965 863550540864537600615737)
                    ·
                      rfl

theorem cell22_2522638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 2, 2, 3].length) (baseStart_2522638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2522638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2522638 prefixEnd_2522638 := by exact prefixLift 2522638
  have htrace : WordTrace (prefixWord ++ tailWord_2522638) baseStart_2522638 baseEnd_2522638 := by
    simpa [prefixWord, tailWord_2522638, baseEnd_2522638] using wordTrace_append hprefix tailTrace_2522638
  have hstable : (prefixWord ++ tailWord_2522638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2522638).length < 2 ^ (prefixWord ++ tailWord_2522638).sum := by decide
  have hdescent : baseEnd_2522638 < baseStart_2522638 := by decide
  rcases family_descends (prefixWord ++ tailWord_2522638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2522784 : List Nat := [2, 1, 1, 4, 3, 1, 1, 1, 5, 3]
def baseStart_2522784 : Nat := 118140960795 + 2522784 * 2 ^ 59
def prefixEnd_2522784 : Nat := 4983230072969 + 3 ^ 40 * 2522784 * 2
def baseEnd_2522784 : Nat := 863600519648241886465289

theorem tailTrace_2522784 : CollatzResearch.WordTrace tailWord_2522784 prefixEnd_2522784 863600519648241886465289 := by
  unfold tailWord_2522784
  simp only [CollatzResearch.WordTrace]
  refine ⟨46006745846195950025007703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61342327794927933366676937 46006745846195950025007703)
  ·
    refine ⟨69010118769293925037511555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46006745846195950025007703 69010118769293925037511555)
    ·
      refine ⟨103515178153940887556267333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69010118769293925037511555 103515178153940887556267333)
      ·
        refine ⟨19409095903863916416800125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 103515178153940887556267333 19409095903863916416800125)
        ·
          refine ⟨7278410963948968656300047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19409095903863916416800125 7278410963948968656300047)
          ·
            refine ⟨10917616445923452984450071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7278410963948968656300047 10917616445923452984450071)
            ·
              refine ⟨16376424668885179476675107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10917616445923452984450071 16376424668885179476675107)
              ·
                refine ⟨24564637003327769215012661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16376424668885179476675107 24564637003327769215012661)
                ·
                  refine ⟨2302934719061978363907437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24564637003327769215012661 2302934719061978363907437)
                  ·
                    refine ⟨863600519648241886465289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2302934719061978363907437 863600519648241886465289)
                    ·
                      rfl

theorem cell22_2522784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 5, 3].length) (baseStart_2522784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2522784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2522784 prefixEnd_2522784 := by exact prefixLift 2522784
  have htrace : WordTrace (prefixWord ++ tailWord_2522784) baseStart_2522784 baseEnd_2522784 := by
    simpa [prefixWord, tailWord_2522784, baseEnd_2522784] using wordTrace_append hprefix tailTrace_2522784
  have hstable : (prefixWord ++ tailWord_2522784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2522784).length < 2 ^ (prefixWord ++ tailWord_2522784).sum := by decide
  have hdescent : baseEnd_2522784 < baseStart_2522784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2522784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2522814 : List Nat := [4, 2, 1, 1, 2, 3, 1, 1, 7]
def baseStart_2522814 : Nat := 118140960795 + 2522814 * 2 ^ 59
def prefixEnd_2522814 : Nat := 4983230072969 + 3 ^ 40 * 2522814 * 2
def baseEnd_2522814 : Nat := 287870263087110602738399

theorem tailTrace_2522814 : CollatzResearch.WordTrace tailWord_2522814 prefixEnd_2522814 287870263087110602738399 := by
  unfold tailWord_2522814
  simp only [CollatzResearch.WordTrace]
  refine ⟨11501823235285401896700937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61343057254855476782404997 11501823235285401896700937)
  ·
    refine ⟨8626367426464051422525703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11501823235285401896700937 8626367426464051422525703)
    ·
      refine ⟨12939551139696077133788555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8626367426464051422525703 12939551139696077133788555)
      ·
        refine ⟨19409326709544115700682833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12939551139696077133788555 19409326709544115700682833)
        ·
          refine ⟨14556995032158086775512125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19409326709544115700682833 14556995032158086775512125)
          ·
            refine ⟨5458873137059282540817047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14556995032158086775512125 5458873137059282540817047)
            ·
              refine ⟨8188309705588923811225571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5458873137059282540817047 8188309705588923811225571)
              ·
                refine ⟨12282464558383385716838357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8188309705588923811225571 12282464558383385716838357)
                ·
                  refine ⟨287870263087110602738399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12282464558383385716838357 287870263087110602738399)
                  ·
                    rfl

theorem cell22_2522814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 1, 7].length) (baseStart_2522814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2522814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2522814 prefixEnd_2522814 := by exact prefixLift 2522814
  have htrace : WordTrace (prefixWord ++ tailWord_2522814) baseStart_2522814 baseEnd_2522814 := by
    simpa [prefixWord, tailWord_2522814, baseEnd_2522814] using wordTrace_append hprefix tailTrace_2522814
  have hstable : (prefixWord ++ tailWord_2522814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2522814).length < 2 ^ (prefixWord ++ tailWord_2522814).sum := by decide
  have hdescent : baseEnd_2522814 < baseStart_2522814 := by decide
  rcases family_descends (prefixWord ++ tailWord_2522814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2522827 : List Nat := [1, 1, 1, 1, 3, 2, 1, 3, 5, 4]
def baseStart_2522827 : Nat := 118140960795 + 2522827 * 2 ^ 59
def prefixEnd_2522827 : Nat := 4983230072969 + 3 ^ 40 * 2522827 * 2
def baseEnd_2522827 : Nat := 863615239427004107640157

theorem tailTrace_2522827 : CollatzResearch.WordTrace tailWord_2522827 prefixEnd_2522827 863615239427004107640157 := by
  unfold tailWord_2522827
  simp only [CollatzResearch.WordTrace]
  refine ⟨92015060031236118393830735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61343373354157412262553823 92015060031236118393830735)
  ·
    refine ⟨138022590046854177590746103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92015060031236118393830735 138022590046854177590746103)
    ·
      refine ⟨207033885070281266386119155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138022590046854177590746103 207033885070281266386119155)
      ·
        refine ⟨310550827605421899579178733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207033885070281266386119155 310550827605421899579178733)
        ·
          refine ⟨116456560352033212342192025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 310550827605421899579178733 116456560352033212342192025)
          ·
            refine ⟨87342420264024909256644019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116456560352033212342192025 87342420264024909256644019)
            ·
              refine ⟨131013630396037363884966029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87342420264024909256644019 131013630396037363884966029)
              ·
                refine ⟨49130111398514011456862261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 131013630396037363884966029 49130111398514011456862261)
                ·
                  refine ⟨4605947943610688574080837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49130111398514011456862261 4605947943610688574080837)
                  ·
                    refine ⟨863615239427004107640157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4605947943610688574080837 863615239427004107640157)
                    ·
                      rfl

theorem cell22_2522827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 5, 4].length) (baseStart_2522827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2522827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2522827 prefixEnd_2522827 := by exact prefixLift 2522827
  have htrace : WordTrace (prefixWord ++ tailWord_2522827) baseStart_2522827 baseEnd_2522827 := by
    simpa [prefixWord, tailWord_2522827, baseEnd_2522827] using wordTrace_append hprefix tailTrace_2522827
  have hstable : (prefixWord ++ tailWord_2522827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2522827).length < 2 ^ (prefixWord ++ tailWord_2522827).sum := by decide
  have hdescent : baseEnd_2522827 < baseStart_2522827 := by decide
  rcases family_descends (prefixWord ++ tailWord_2522827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2522857 : List Nat := [1, 2, 1, 1, 1, 2, 3, 3, 3, 5]
def baseStart_2522857 : Nat := 118140960795 + 2522857 * 2 ^ 59
def prefixEnd_2522857 : Nat := 4983230072969 + 3 ^ 40 * 2522857 * 2
def baseEnd_2522857 : Nat := 863625509040094029390065

theorem tailTrace_2522857 : CollatzResearch.WordTrace tailWord_2522857 prefixEnd_2522857 863625509040094029390065 := by
  unfold tailWord_2522857
  simp only [CollatzResearch.WordTrace]
  refine ⟨92016154221127433517422825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61344102814084955678281883 92016154221127433517422825)
  ·
    refine ⟨69012115665845575138067119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92016154221127433517422825 69012115665845575138067119)
    ·
      refine ⟨103518173498768362707100679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69012115665845575138067119 103518173498768362707100679)
      ·
        refine ⟨155277260248152544060651019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103518173498768362707100679 155277260248152544060651019)
        ·
          refine ⟨232915890372228816090976529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155277260248152544060651019 232915890372228816090976529)
          ·
            refine ⟨174686917779171612068232397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 232915890372228816090976529 174686917779171612068232397)
            ·
              refine ⟨65507594167189354525587149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 174686917779171612068232397 65507594167189354525587149)
              ·
                refine ⟨24565347812696007947095181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65507594167189354525587149 24565347812696007947095181)
                ·
                  refine ⟨9212005429761002980160693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24565347812696007947095181 9212005429761002980160693)
                  ·
                    refine ⟨863625509040094029390065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9212005429761002980160693 863625509040094029390065)
                    ·
                      rfl

theorem cell22_2522857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 3, 5].length) (baseStart_2522857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2522857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2522857 prefixEnd_2522857 := by exact prefixLift 2522857
  have htrace : WordTrace (prefixWord ++ tailWord_2522857) baseStart_2522857 baseEnd_2522857 := by
    simpa [prefixWord, tailWord_2522857, baseEnd_2522857] using wordTrace_append hprefix tailTrace_2522857
  have hstable : (prefixWord ++ tailWord_2522857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2522857).length < 2 ^ (prefixWord ++ tailWord_2522857).sum := by decide
  have hdescent : baseEnd_2522857 < baseStart_2522857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2522857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2522861 : List Nat := [1, 5, 1, 2, 1, 2, 2, 3, 1, 4]
def baseStart_2522861 : Nat := 118140960795 + 2522861 * 2 ^ 59
def prefixEnd_2522861 : Nat := 4983230072969 + 3 ^ 40 * 2522861 * 2
def baseEnd_2522861 : Nat := 863626878321839352290053

theorem tailTrace_2522861 : CollatzResearch.WordTrace tailWord_2522861 prefixEnd_2522861 863626878321839352290053 := by
  unfold tailWord_2522861
  simp only [CollatzResearch.WordTrace]
  refine ⟨92016300113112942200568437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61344200075408628133712291 92016300113112942200568437)
  ·
    refine ⟨8626528135604338331303291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 92016300113112942200568437 8626528135604338331303291)
    ·
      refine ⟨12939792203406507496954937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8626528135604338331303291 12939792203406507496954937)
      ·
        refine ⟨9704844152554880622716203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12939792203406507496954937 9704844152554880622716203)
        ·
          refine ⟨14557266228832320934074305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9704844152554880622716203 14557266228832320934074305)
          ·
            refine ⟨10917949671624240700555729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14557266228832320934074305 10917949671624240700555729)
            ·
              refine ⟨8188462253718180525416797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10917949671624240700555729 8188462253718180525416797)
              ·
                refine ⟨3070673345144317697031299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8188462253718180525416797 3070673345144317697031299)
                ·
                  refine ⟨4606010017716476545546949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3070673345144317697031299 4606010017716476545546949)
                  ·
                    refine ⟨863626878321839352290053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4606010017716476545546949 863626878321839352290053)
                    ·
                      rfl

theorem cell22_2522861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_2522861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2522861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2522861 prefixEnd_2522861 := by exact prefixLift 2522861
  have htrace : WordTrace (prefixWord ++ tailWord_2522861) baseStart_2522861 baseEnd_2522861 := by
    simpa [prefixWord, tailWord_2522861, baseEnd_2522861] using wordTrace_append hprefix tailTrace_2522861
  have hstable : (prefixWord ++ tailWord_2522861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2522861).length < 2 ^ (prefixWord ++ tailWord_2522861).sum := by decide
  have hdescent : baseEnd_2522861 < baseStart_2522861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2522861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2522872 : List Nat := [2, 1, 2, 1, 1, 2, 2, 2, 3, 6]
def baseStart_2522872 : Nat := 118140960795 + 2522872 * 2 ^ 59
def prefixEnd_2522872 : Nat := 4983230072969 + 3 ^ 40 * 2522872 * 2
def baseEnd_2522872 : Nat := 863630643846638990265019

theorem tailTrace_2522872 : CollatzResearch.WordTrace tailWord_2522872 prefixEnd_2522872 863630643846638990265019 := by
  unfold tailWord_2522872
  simp only [CollatzResearch.WordTrace]
  refine ⟨46008350658036545539609435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61344467544048727386145913 46008350658036545539609435)
  ·
    refine ⟨69012525987054818309414153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46008350658036545539609435 69012525987054818309414153)
    ·
      refine ⟨51759394490291113732060615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69012525987054818309414153 51759394490291113732060615)
      ·
        refine ⟨77639091735436670598090923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51759394490291113732060615 77639091735436670598090923)
        ·
          refine ⟨116458637603155005897136385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77639091735436670598090923 116458637603155005897136385)
          ·
            refine ⟨87343978202366254422852289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116458637603155005897136385 87343978202366254422852289)
            ·
              refine ⟨65507983651774690817139217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87343978202366254422852289 65507983651774690817139217)
              ·
                refine ⟨49130987738831018112854413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65507983651774690817139217 49130987738831018112854413)
                ·
                  refine ⟨18424120402061631792320405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49130987738831018112854413 18424120402061631792320405)
                  ·
                    refine ⟨863630643846638990265019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18424120402061631792320405 863630643846638990265019)
                    ·
                      rfl

theorem cell22_2522872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 3, 6].length) (baseStart_2522872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2522872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2522872 prefixEnd_2522872 := by exact prefixLift 2522872
  have htrace : WordTrace (prefixWord ++ tailWord_2522872) baseStart_2522872 baseEnd_2522872 := by
    simpa [prefixWord, tailWord_2522872, baseEnd_2522872] using wordTrace_append hprefix tailTrace_2522872
  have hstable : (prefixWord ++ tailWord_2522872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2522872).length < 2 ^ (prefixWord ++ tailWord_2522872).sum := by decide
  have hdescent : baseEnd_2522872 < baseStart_2522872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2522872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2522906 : List Nat := [3, 1, 1, 3, 2, 3, 2, 1, 2, 4]
def baseStart_2522906 : Nat := 118140960795 + 2522906 * 2 ^ 59
def prefixEnd_2522906 : Nat := 4983230072969 + 3 ^ 40 * 2522906 * 2
def baseEnd_2522906 : Nat := 863642282741474234914915

theorem tailTrace_2522906 : CollatzResearch.WordTrace tailWord_2522906 prefixEnd_2522906 863642282741474234914915 := by
  unfold tailWord_2522906
  simp only [CollatzResearch.WordTrace]
  refine ⟨23004485349487478721489143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61345294265299943257304381 23004485349487478721489143)
  ·
    refine ⟨34506728024231218082233715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23004485349487478721489143 34506728024231218082233715)
    ·
      refine ⟨51760092036346827123350573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34506728024231218082233715 51760092036346827123350573)
      ·
        refine ⟨19410034513630060171256465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51760092036346827123350573 19410034513630060171256465)
        ·
          refine ⟨14557525885222545128442349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19410034513630060171256465 14557525885222545128442349)
          ·
            refine ⟨5459072206958454423165881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14557525885222545128442349 5459072206958454423165881)
            ·
              refine ⟨4094304155218840817374411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5459072206958454423165881 4094304155218840817374411)
              ·
                refine ⟨6141456232828261226061617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4094304155218840817374411 6141456232828261226061617)
                ·
                  refine ⟨4606092174621195919546213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6141456232828261226061617 4606092174621195919546213)
                  ·
                    refine ⟨863642282741474234914915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4606092174621195919546213 863642282741474234914915)
                    ·
                      rfl

theorem cell22_2522906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 1, 2, 4].length) (baseStart_2522906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2522906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2522906 prefixEnd_2522906 := by exact prefixLift 2522906
  have htrace : WordTrace (prefixWord ++ tailWord_2522906) baseStart_2522906 baseEnd_2522906 := by
    simpa [prefixWord, tailWord_2522906, baseEnd_2522906] using wordTrace_append hprefix tailTrace_2522906
  have hstable : (prefixWord ++ tailWord_2522906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2522906).length < 2 ^ (prefixWord ++ tailWord_2522906).sum := by decide
  have hdescent : baseEnd_2522906 < baseStart_2522906 := by decide
  rcases family_descends (prefixWord ++ tailWord_2522906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2522949 : List Nat := [1, 3, 1, 1, 1, 2, 3, 5, 5]
def baseStart_2522949 : Nat := 118140960795 + 2522949 * 2 ^ 59
def prefixEnd_2522949 : Nat := 4983230072969 + 3 ^ 40 * 2522949 * 2
def baseEnd_2522949 : Nat := 287885667506745485363261

theorem tailTrace_2522949 : CollatzResearch.WordTrace tailWord_2522949 prefixEnd_2522949 287885667506745485363261 := by
  unfold tailWord_2522949
  simp only [CollatzResearch.WordTrace]
  refine ⟨92019509736794133229771901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61346339824529422153181267 92019509736794133229771901)
  ·
    refine ⟨34507316151297799961164463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92019509736794133229771901 34507316151297799961164463)
    ·
      refine ⟨51760974226946699941746695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34507316151297799961164463 51760974226946699941746695)
      ·
        refine ⟨77641461340420049912620043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51760974226946699941746695 77641461340420049912620043)
        ·
          refine ⟨116462192010630074868930065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77641461340420049912620043 116462192010630074868930065)
          ·
            refine ⟨87346644007972556151697549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116462192010630074868930065 87346644007972556151697549)
            ·
              refine ⟨32754991502989708556886581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87346644007972556151697549 32754991502989708556886581)
              ·
                refine ⟨3070780453405285177208117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32754991502989708556886581 3070780453405285177208117)
                ·
                  refine ⟨287885667506745485363261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3070780453405285177208117 287885667506745485363261)
                  ·
                    rfl

theorem cell22_2522949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 5, 5].length) (baseStart_2522949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2522949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2522949 prefixEnd_2522949 := by exact prefixLift 2522949
  have htrace : WordTrace (prefixWord ++ tailWord_2522949) baseStart_2522949 baseEnd_2522949 := by
    simpa [prefixWord, tailWord_2522949, baseEnd_2522949] using wordTrace_append hprefix tailTrace_2522949
  have hstable : (prefixWord ++ tailWord_2522949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2522949).length < 2 ^ (prefixWord ++ tailWord_2522949).sum := by decide
  have hdescent : baseEnd_2522949 < baseStart_2522949 := by decide
  rcases family_descends (prefixWord ++ tailWord_2522949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2523071 : List Nat := [1, 1, 2, 2, 2, 1, 4, 1, 5, 3]
def baseStart_2523071 : Nat := 118140960795 + 2523071 * 2 ^ 59
def prefixEnd_2523071 : Nat := 4983230072969 + 3 ^ 40 * 2523071 * 2
def baseEnd_2523071 : Nat := 863698765613468804539409

theorem tailTrace_2523071 : CollatzResearch.WordTrace tailWord_2523071 prefixEnd_2523071 863698765613468804539409 := by
  unfold tailWord_2523071
  simp only [CollatzResearch.WordTrace]
  refine ⟨92023959442352148065713067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61349306294901432043808711 92023959442352148065713067)
  ·
    refine ⟨138035939163528222098569601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92023959442352148065713067 138035939163528222098569601)
    ·
      refine ⟨103526954372646166573927201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138035939163528222098569601 103526954372646166573927201)
      ·
        refine ⟨77645215779484624930445401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103526954372646166573927201 77645215779484624930445401)
        ·
          refine ⟨58233911834613468697834051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77645215779484624930445401 58233911834613468697834051)
          ·
            refine ⟨87350867751920203046751077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58233911834613468697834051 87350867751920203046751077)
            ·
              refine ⟨16378287703485038071265827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87350867751920203046751077 16378287703485038071265827)
              ·
                refine ⟨24567431555227557106898741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16378287703485038071265827 24567431555227557106898741)
                ·
                  refine ⟨2303196708302583478771757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24567431555227557106898741 2303196708302583478771757)
                  ·
                    refine ⟨863698765613468804539409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2303196708302583478771757 863698765613468804539409)
                    ·
                      rfl

theorem cell22_2523071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 5, 3].length) (baseStart_2523071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2523071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2523071 prefixEnd_2523071 := by exact prefixLift 2523071
  have htrace : WordTrace (prefixWord ++ tailWord_2523071) baseStart_2523071 baseEnd_2523071 := by
    simpa [prefixWord, tailWord_2523071, baseEnd_2523071] using wordTrace_append hprefix tailTrace_2523071
  have hstable : (prefixWord ++ tailWord_2523071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2523071).length < 2 ^ (prefixWord ++ tailWord_2523071).sum := by decide
  have hdescent : baseEnd_2523071 < baseStart_2523071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2523071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2523118 : List Nat := [4, 1, 2, 1, 3, 1, 2, 3, 5]
def baseStart_2523118 : Nat := 118140960795 + 2523118 * 2 ^ 59
def prefixEnd_2523118 : Nat := 4983230072969 + 3 ^ 40 * 2523118 * 2
def baseEnd_2523118 : Nat := 287904951557992116204755

theorem tailTrace_2523118 : CollatzResearch.WordTrace tailWord_2523118 prefixEnd_2523118 287904951557992116204755 := by
  unfold tailWord_2523118
  simp only [CollatzResearch.WordTrace]
  refine ⟨11503209209147734386584251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61350449115454583395116005 11503209209147734386584251)
  ·
    refine ⟨17254813813721601579876377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11503209209147734386584251 17254813813721601579876377)
    ·
      refine ⟨12941110360291201184907283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17254813813721601579876377 12941110360291201184907283)
      ·
        refine ⟨19411665540436801777360925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12941110360291201184907283 19411665540436801777360925)
        ·
          refine ⟨7279374577663800666510347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19411665540436801777360925 7279374577663800666510347)
          ·
            refine ⟨10919061866495700999765521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7279374577663800666510347 10919061866495700999765521)
            ·
              refine ⟨8189296399871775749824141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10919061866495700999765521 8189296399871775749824141)
              ·
                refine ⟨3070986149951915906184053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8189296399871775749824141 3070986149951915906184053)
                ·
                  refine ⟨287904951557992116204755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3070986149951915906184053 287904951557992116204755)
                  ·
                    rfl

theorem cell22_2523118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 3, 5].length) (baseStart_2523118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2523118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2523118 prefixEnd_2523118 := by exact prefixLift 2523118
  have htrace : WordTrace (prefixWord ++ tailWord_2523118) baseStart_2523118 baseEnd_2523118 := by
    simpa [prefixWord, tailWord_2523118, baseEnd_2523118] using wordTrace_append hprefix tailTrace_2523118
  have hstable : (prefixWord ++ tailWord_2523118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2523118).length < 2 ^ (prefixWord ++ tailWord_2523118).sum := by decide
  have hdescent : baseEnd_2523118 < baseStart_2523118 := by decide
  rcases family_descends (prefixWord ++ tailWord_2523118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2523131 : List Nat := [1, 1, 1, 1, 1, 3, 6, 1, 3, 4]
def baseStart_2523131 : Nat := 118140960795 + 2523131 * 2 ^ 59
def prefixEnd_2523131 : Nat := 4983230072969 + 3 ^ 40 * 2523131 * 2
def baseEnd_2523131 : Nat := 863719304839648648039225

theorem tailTrace_2523131 : CollatzResearch.WordTrace tailWord_2523131 prefixEnd_2523131 863719304839648648039225 := by
  unfold tailWord_2523131
  simp only [CollatzResearch.WordTrace]
  refine ⟨92026147822134778312897247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61350765214756518875264831 92026147822134778312897247)
  ·
    refine ⟨138039221733202167469345871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92026147822134778312897247 138039221733202167469345871)
    ·
      refine ⟨207058832599803251204018807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138039221733202167469345871 207058832599803251204018807)
      ·
        refine ⟨310588248899704876806028211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207058832599803251204018807 310588248899704876806028211)
        ·
          refine ⟨465882373349557315209042317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 310588248899704876806028211 465882373349557315209042317)
          ·
            refine ⟨174705890006083993203390869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 465882373349557315209042317 174705890006083993203390869)
            ·
              refine ⟨8189338594035187181408947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 174705890006083993203390869 8189338594035187181408947)
              ·
                refine ⟨12284007891052780772113421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8189338594035187181408947 12284007891052780772113421)
                ·
                  refine ⟨4606502959144792789542533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12284007891052780772113421 4606502959144792789542533)
                  ·
                    refine ⟨863719304839648648039225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4606502959144792789542533 863719304839648648039225)
                    ·
                      rfl

theorem cell22_2523131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 1, 3, 4].length) (baseStart_2523131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2523131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2523131 prefixEnd_2523131 := by exact prefixLift 2523131
  have htrace : WordTrace (prefixWord ++ tailWord_2523131) baseStart_2523131 baseEnd_2523131 := by
    simpa [prefixWord, tailWord_2523131, baseEnd_2523131] using wordTrace_append hprefix tailTrace_2523131
  have hstable : (prefixWord ++ tailWord_2523131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2523131).length < 2 ^ (prefixWord ++ tailWord_2523131).sum := by decide
  have hdescent : baseEnd_2523131 < baseStart_2523131 := by decide
  rcases family_descends (prefixWord ++ tailWord_2523131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2523148 : List Nat := [2, 2, 1, 2, 3, 1, 3, 3, 1, 4]
def baseStart_2523148 : Nat := 118140960795 + 2523148 * 2 ^ 59
def prefixEnd_2523148 : Nat := 4983230072969 + 3 ^ 40 * 2523148 * 2
def baseEnd_2523148 : Nat := 863725124287066270364173

theorem tailTrace_2523148 : CollatzResearch.WordTrace tailWord_2523148 prefixEnd_2523148 863725124287066270364173 := by
  unfold tailWord_2523148
  simp only [CollatzResearch.WordTrace]
  refine ⟨46013383931536595108133049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61351178575382126810844065 46013383931536595108133049)
  ·
    refine ⟨34510037948652446331099787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46013383931536595108133049 34510037948652446331099787)
    ·
      refine ⟨51765056922978669496649681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34510037948652446331099787 51765056922978669496649681)
      ·
        refine ⟨38823792692234002122487261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51765056922978669496649681 38823792692234002122487261)
        ·
          refine ⟨14558922259587750795932723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38823792692234002122487261 14558922259587750795932723)
          ·
            refine ⟨21838383389381626193899085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14558922259587750795932723 21838383389381626193899085)
            ·
              refine ⟨8189393771018109822712157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21838383389381626193899085 8189393771018109822712157)
              ·
                refine ⟨3071022664131791183517059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8189393771018109822712157 3071022664131791183517059)
                ·
                  refine ⟨4606533996197686775275589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3071022664131791183517059 4606533996197686775275589)
                  ·
                    refine ⟨863725124287066270364173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4606533996197686775275589 863725124287066270364173)
                    ·
                      rfl

theorem cell22_2523148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 3, 1, 4].length) (baseStart_2523148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2523148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2523148 prefixEnd_2523148 := by exact prefixLift 2523148
  have htrace : WordTrace (prefixWord ++ tailWord_2523148) baseStart_2523148 baseEnd_2523148 := by
    simpa [prefixWord, tailWord_2523148, baseEnd_2523148] using wordTrace_append hprefix tailTrace_2523148
  have hstable : (prefixWord ++ tailWord_2523148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2523148).length < 2 ^ (prefixWord ++ tailWord_2523148).sum := by decide
  have hdescent : baseEnd_2523148 < baseStart_2523148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2523148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2523229 : List Nat := [1, 4, 4, 1, 1, 1, 4, 1, 2, 3]
def baseStart_2523229 : Nat := 118140960795 + 2523229 * 2 ^ 59
def prefixEnd_2523229 : Nat := 4983230072969 + 3 ^ 40 * 2523229 * 2
def baseEnd_2523229 : Nat := 863752852242409059088925

theorem tailTrace_2523229 : CollatzResearch.WordTrace tailWord_2523229 prefixEnd_2523229 863752852242409059088925 := by
  unfold tailWord_2523229
  simp only [CollatzResearch.WordTrace]
  refine ⟨92029722175779741049964741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61353148117186494033309827 92029722175779741049964741)
  ·
    refine ⟨17255572907958701446868389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92029722175779741049964741 17255572907958701446868389)
    ·
      refine ⟨3235419920242256521287823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17255572907958701446868389 3235419920242256521287823)
      ·
        refine ⟨4853129880363384781931735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3235419920242256521287823 4853129880363384781931735)
        ·
          refine ⟨7279694820545077172897603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4853129880363384781931735 7279694820545077172897603)
          ·
            refine ⟨10919542230817615759346405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7279694820545077172897603 10919542230817615759346405)
            ·
              refine ⟨2047414168278302954877451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10919542230817615759346405 2047414168278302954877451)
              ·
                refine ⟨3071121252417454432316177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2047414168278302954877451 3071121252417454432316177)
                ·
                  refine ⟨2303340939313090824237133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3071121252417454432316177 2303340939313090824237133)
                  ·
                    refine ⟨863752852242409059088925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2303340939313090824237133 863752852242409059088925)
                    ·
                      rfl

theorem cell22_2523229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_2523229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2523229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2523229 prefixEnd_2523229 := by exact prefixLift 2523229
  have htrace : WordTrace (prefixWord ++ tailWord_2523229) baseStart_2523229 baseEnd_2523229 := by
    simpa [prefixWord, tailWord_2523229, baseEnd_2523229] using wordTrace_append hprefix tailTrace_2523229
  have hstable : (prefixWord ++ tailWord_2523229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2523229).length < 2 ^ (prefixWord ++ tailWord_2523229).sum := by decide
  have hdescent : baseEnd_2523229 < baseStart_2523229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2523229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2523268 : List Nat := [2, 3, 2, 1, 2, 1, 2, 2, 2, 5]
def baseStart_2523268 : Nat := 118140960795 + 2523268 * 2 ^ 59
def prefixEnd_2523268 : Nat := 4983230072969 + 3 ^ 40 * 2523268 * 2
def baseEnd_2523268 : Nat := 863766202739425957363805

theorem tailTrace_2523268 : CollatzResearch.WordTrace tailWord_2523268 prefixEnd_2523268 863766202739425957363805 := by
  unfold tailWord_2523268
  simp only [CollatzResearch.WordTrace]
  refine ⟨46015572311319225355317229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61354096415092300473756305 46015572311319225355317229)
  ·
    refine ⟨17255839616744709508243961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46015572311319225355317229 17255839616744709508243961)
    ·
      refine ⟨12941879712558532131182971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17255839616744709508243961 12941879712558532131182971)
      ·
        refine ⟨19412819568837798196774457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12941879712558532131182971 19412819568837798196774457)
        ·
          refine ⟨14559614676628348647580843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19412819568837798196774457 14559614676628348647580843)
          ·
            refine ⟨21839422014942522971371265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14559614676628348647580843 21839422014942522971371265)
            ·
              refine ⟨16379566511206892228528449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21839422014942522971371265 16379566511206892228528449)
              ·
                refine ⟨12284674883405169171396337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16379566511206892228528449 12284674883405169171396337)
                ·
                  refine ⟨9213506162553876878547253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12284674883405169171396337 9213506162553876878547253)
                  ·
                    refine ⟨863766202739425957363805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9213506162553876878547253 863766202739425957363805)
                    ·
                      rfl

theorem cell22_2523268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_2523268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2523268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2523268 prefixEnd_2523268 := by exact prefixLift 2523268
  have htrace : WordTrace (prefixWord ++ tailWord_2523268) baseStart_2523268 baseEnd_2523268 := by
    simpa [prefixWord, tailWord_2523268, baseEnd_2523268] using wordTrace_append hprefix tailTrace_2523268
  have hstable : (prefixWord ++ tailWord_2523268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2523268).length < 2 ^ (prefixWord ++ tailWord_2523268).sum := by decide
  have hdescent : baseEnd_2523268 < baseStart_2523268 := by decide
  rcases family_descends (prefixWord ++ tailWord_2523268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2523274 : List Nat := [3, 1, 2, 3, 1, 2, 4, 2, 1, 3]
def baseStart_2523274 : Nat := 118140960795 + 2523274 * 2 ^ 59
def prefixEnd_2523274 : Nat := 4983230072969 + 3 ^ 40 * 2523274 * 2
def baseEnd_2523274 : Nat := 863768256662043941713787

theorem tailTrace_2523274 : CollatzResearch.WordTrace tailWord_2523274 prefixEnd_2523274 863768256662043941713787 := by
  unfold tailWord_2523274
  simp only [CollatzResearch.WordTrace]
  refine ⟨23007840865154178433838219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61354242307077809156901917 23007840865154178433838219)
  ·
    refine ⟨34511761297731267650757329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23007840865154178433838219 34511761297731267650757329)
    ·
      refine ⟨25883820973298450738067997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34511761297731267650757329 25883820973298450738067997)
      ·
        refine ⟨9706432864986919026775499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25883820973298450738067997 9706432864986919026775499)
        ·
          refine ⟨14559649297480378540163249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9706432864986919026775499 14559649297480378540163249)
          ·
            refine ⟨10919736973110283905122437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14559649297480378540163249 10919736973110283905122437)
            ·
              refine ⟨2047450682458178232210457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10919736973110283905122437 2047450682458178232210457)
              ·
                refine ⟨1535588011843633674157843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2047450682458178232210457 1535588011843633674157843)
                ·
                  refine ⟨2303382017765450511236765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1535588011843633674157843 2303382017765450511236765)
                  ·
                    refine ⟨863768256662043941713787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2303382017765450511236765 863768256662043941713787)
                    ·
                      rfl

theorem cell22_2523274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 4, 2, 1, 3].length) (baseStart_2523274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2523274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2523274 prefixEnd_2523274 := by exact prefixLift 2523274
  have htrace : WordTrace (prefixWord ++ tailWord_2523274) baseStart_2523274 baseEnd_2523274 := by
    simpa [prefixWord, tailWord_2523274, baseEnd_2523274] using wordTrace_append hprefix tailTrace_2523274
  have hstable : (prefixWord ++ tailWord_2523274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2523274).length < 2 ^ (prefixWord ++ tailWord_2523274).sum := by decide
  have hdescent : baseEnd_2523274 < baseStart_2523274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2523274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2523281 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 12]
def baseStart_2523281 : Nat := 118140960795 + 2523281 * 2 ^ 59
def prefixEnd_2523281 : Nat := 4983230072969 + 3 ^ 40 * 2523281 * 2
def baseEnd_2523281 : Nat := 287923550968366085596255

theorem tailTrace_2523281 : CollatzResearch.WordTrace tailWord_2523281 prefixEnd_2523281 287923550968366085596255 := by
  unfold tailWord_2523281
  simp only [CollatzResearch.WordTrace]
  refine ⟨92031618771591353930857697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61354412514394235953905131 92031618771591353930857697)
  ·
    refine ⟨69023714078693515448143273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92031618771591353930857697 69023714078693515448143273)
    ·
      refine ⟨51767785559020136586107455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69023714078693515448143273 51767785559020136586107455)
      ·
        refine ⟨77651678338530204879161183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51767785559020136586107455 77651678338530204879161183)
        ·
          refine ⟨116477517507795307318741775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77651678338530204879161183 116477517507795307318741775)
          ·
            refine ⟨174716276261692960978112663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116477517507795307318741775 174716276261692960978112663)
            ·
              refine ⟨262074414392539441467168995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174716276261692960978112663 262074414392539441467168995)
              ·
                refine ⟨393111621588809162200753493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 262074414392539441467168995 393111621588809162200753493)
                ·
                  refine ⟨287923550968366085596255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 393111621588809162200753493 287923550968366085596255)
                  ·
                    rfl

theorem cell22_2523281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 12].length) (baseStart_2523281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2523281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2523281 prefixEnd_2523281 := by exact prefixLift 2523281
  have htrace : WordTrace (prefixWord ++ tailWord_2523281) baseStart_2523281 baseEnd_2523281 := by
    simpa [prefixWord, tailWord_2523281, baseEnd_2523281] using wordTrace_append hprefix tailTrace_2523281
  have hstable : (prefixWord ++ tailWord_2523281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2523281).length < 2 ^ (prefixWord ++ tailWord_2523281).sum := by decide
  have hdescent : baseEnd_2523281 < baseStart_2523281 := by decide
  rcases family_descends (prefixWord ++ tailWord_2523281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2523332 : List Nat := [2, 3, 3, 1, 2, 1, 2, 4, 4]
def baseStart_2523332 : Nat := 118140960795 + 2523332 * 2 ^ 59
def prefixEnd_2523332 : Nat := 4983230072969 + 3 ^ 40 * 2523332 * 2
def baseEnd_2523332 : Nat := 287929370415783707921203

theorem tailTrace_2523332 : CollatzResearch.WordTrace tailWord_2523332 prefixEnd_2523332 287929370415783707921203 := by
  unfold tailWord_2523332
  simp only [CollatzResearch.WordTrace]
  refine ⟨46016739447203294820482125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61355652596271059760642833 46016739447203294820482125)
  ·
    refine ⟨17256277292701235557680797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46016739447203294820482125 17256277292701235557680797)
    ·
      refine ⟨6471103984762963334130299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17256277292701235557680797 6471103984762963334130299)
      ·
        refine ⟨9706655977144445001195449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6471103984762963334130299 9706655977144445001195449)
        ·
          refine ⟨7279991982858333750896587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9706655977144445001195449 7279991982858333750896587)
          ·
            refine ⟨10919987974287500626344881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7279991982858333750896587 10919987974287500626344881)
            ·
              refine ⟨8189990980715625469758661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10919987974287500626344881 8189990980715625469758661)
              ·
                refine ⟨1535623308884179775579749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8189990980715625469758661 1535623308884179775579749)
                ·
                  refine ⟨287929370415783707921203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1535623308884179775579749 287929370415783707921203)
                  ·
                    rfl

theorem cell22_2523332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 4, 4].length) (baseStart_2523332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2523332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2523332 prefixEnd_2523332 := by exact prefixLift 2523332
  have htrace : WordTrace (prefixWord ++ tailWord_2523332) baseStart_2523332 baseEnd_2523332 := by
    simpa [prefixWord, tailWord_2523332, baseEnd_2523332] using wordTrace_append hprefix tailTrace_2523332
  have hstable : (prefixWord ++ tailWord_2523332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2523332).length < 2 ^ (prefixWord ++ tailWord_2523332).sum := by decide
  have hdescent : baseEnd_2523332 < baseStart_2523332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2523332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2523390 : List Nat := [4, 2, 2, 1, 1, 1, 2, 1, 2, 6]
def baseStart_2523390 : Nat := 118140960795 + 2523390 * 2 ^ 59
def prefixEnd_2523390 : Nat := 4983230072969 + 3 ^ 40 * 2523390 * 2
def baseEnd_2523390 : Nat := 863807965832658305813431

theorem tailTrace_2523390 : CollatzResearch.WordTrace tailWord_2523390 prefixEnd_2523390 863807965832658305813431 := by
  unfold tailWord_2523390
  simp only [CollatzResearch.WordTrace]
  refine ⟨11504449291024558193321953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61357062885464310364383749 11504449291024558193321953)
  ·
    refine ⟨8628336968268418644991465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11504449291024558193321953 8628336968268418644991465)
    ·
      refine ⟨6471252726201313983743599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8628336968268418644991465 6471252726201313983743599)
      ·
        refine ⟨9706879089301970975615399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6471252726201313983743599 9706879089301970975615399)
        ·
          refine ⟨14560318633952956463423099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9706879089301970975615399 14560318633952956463423099)
          ·
            refine ⟨21840477950929434695134649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14560318633952956463423099 21840477950929434695134649)
            ·
              refine ⟨16380358463197076021350987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21840477950929434695134649 16380358463197076021350987)
              ·
                refine ⟨24570537694795614032026481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16380358463197076021350987 24570537694795614032026481)
                ·
                  refine ⟨18427903271096710524019861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24570537694795614032026481 18427903271096710524019861)
                  ·
                    refine ⟨863807965832658305813431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18427903271096710524019861 863807965832658305813431)
                    ·
                      rfl

theorem cell22_2523390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_2523390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2523390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2523390 prefixEnd_2523390 := by exact prefixLift 2523390
  have htrace : WordTrace (prefixWord ++ tailWord_2523390) baseStart_2523390 baseEnd_2523390 := by
    simpa [prefixWord, tailWord_2523390, baseEnd_2523390] using wordTrace_append hprefix tailTrace_2523390
  have hstable : (prefixWord ++ tailWord_2523390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2523390).length < 2 ^ (prefixWord ++ tailWord_2523390).sum := by decide
  have hdescent : baseEnd_2523390 < baseStart_2523390 := by decide
  rcases family_descends (prefixWord ++ tailWord_2523390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2523392 : List Nat := [2, 1, 1, 2, 1, 1, 4, 6, 1, 3]
def baseStart_2523392 : Nat := 118140960795 + 2523392 * 2 ^ 59
def prefixEnd_2523392 : Nat := 4983230072969 + 3 ^ 40 * 2523392 * 2
def baseEnd_2523392 : Nat := 863808650473530967263425

theorem tailTrace_2523392 : CollatzResearch.WordTrace tailWord_2523392 prefixEnd_2523392 863808650473530967263425 := by
  unfold tailWord_2523392
  simp only [CollatzResearch.WordTrace]
  refine ⟨46017833637094609944074215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61357111516126146592098953 46017833637094609944074215)
  ·
    refine ⟨69026750455641914916111323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46017833637094609944074215 69026750455641914916111323)
    ·
      refine ⟨103540125683462872374166985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69026750455641914916111323 103540125683462872374166985)
      ·
        refine ⟨77655094262597154280625239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103540125683462872374166985 77655094262597154280625239)
        ·
          refine ⟨116482641393895731420937859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77655094262597154280625239 116482641393895731420937859)
          ·
            refine ⟨174723962090843597131406789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116482641393895731420937859 174723962090843597131406789)
            ·
              refine ⟨32760742892033174462138773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 174723962090843597131406789 32760742892033174462138773)
              ·
                refine ⟨1535659823064055052912755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 32760742892033174462138773 1535659823064055052912755)
                ·
                  refine ⟨2303489734596082579369133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1535659823064055052912755 2303489734596082579369133)
                  ·
                    refine ⟨863808650473530967263425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2303489734596082579369133 863808650473530967263425)
                    ·
                      rfl

theorem cell22_2523392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 6, 1, 3].length) (baseStart_2523392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2523392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2523392 prefixEnd_2523392 := by exact prefixLift 2523392
  have htrace : WordTrace (prefixWord ++ tailWord_2523392) baseStart_2523392 baseEnd_2523392 := by
    simpa [prefixWord, tailWord_2523392, baseEnd_2523392] using wordTrace_append hprefix tailTrace_2523392
  have hstable : (prefixWord ++ tailWord_2523392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2523392).length < 2 ^ (prefixWord ++ tailWord_2523392).sum := by decide
  have hdescent : baseEnd_2523392 < baseStart_2523392 := by decide
  rcases family_descends (prefixWord ++ tailWord_2523392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2523403 : List Nat := [1, 1, 1, 1, 5, 2, 2, 1, 1, 7]
def baseStart_2523403 : Nat := 118140960795 + 2523403 * 2 ^ 59
def prefixEnd_2523403 : Nat := 4983230072969 + 3 ^ 40 * 2523403 * 2
def baseEnd_2523403 : Nat := 863812415998330605238391

theorem tailTrace_2523403 : CollatzResearch.WordTrace tailWord_2523403 prefixEnd_2523403 863812415998330605238391 := by
  unfold tailWord_2523403
  simp only [CollatzResearch.WordTrace]
  refine ⟨92036068477149368766798863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61357378984766245844532575 92036068477149368766798863)
  ·
    refine ⟨138054102715724053150198295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92036068477149368766798863 138054102715724053150198295)
    ·
      refine ⟨207081154073586079725297443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138054102715724053150198295 207081154073586079725297443)
      ·
        refine ⟨310621731110379119587946165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207081154073586079725297443 310621731110379119587946165)
        ·
          refine ⟨29120787291598042461369953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 310621731110379119587946165 29120787291598042461369953)
          ·
            refine ⟨21840590468698531846027465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29120787291598042461369953 21840590468698531846027465)
            ·
              refine ⟨16380442851523898884520599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21840590468698531846027465 16380442851523898884520599)
              ·
                refine ⟨24570664277285848326780899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16380442851523898884520599 24570664277285848326780899)
                ·
                  refine ⟨36855996415928772490171349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24570664277285848326780899 36855996415928772490171349)
                  ·
                    refine ⟨863812415998330605238391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36855996415928772490171349 863812415998330605238391)
                    ·
                      rfl

theorem cell22_2523403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 7].length) (baseStart_2523403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2523403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2523403 prefixEnd_2523403 := by exact prefixLift 2523403
  have htrace : WordTrace (prefixWord ++ tailWord_2523403) baseStart_2523403 baseEnd_2523403 := by
    simpa [prefixWord, tailWord_2523403, baseEnd_2523403] using wordTrace_append hprefix tailTrace_2523403
  have hstable : (prefixWord ++ tailWord_2523403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2523403).length < 2 ^ (prefixWord ++ tailWord_2523403).sum := by decide
  have hdescent : baseEnd_2523403 < baseStart_2523403 := by decide
  rcases family_descends (prefixWord ++ tailWord_2523403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2523465 : List Nat := [1, 2, 1, 1, 2, 3, 1, 2, 6, 3]
def baseStart_2523465 : Nat := 118140960795 + 2523465 * 2 ^ 59
def prefixEnd_2523465 : Nat := 4983230072969 + 3 ^ 40 * 2523465 * 2
def baseEnd_2523465 : Nat := 863833639865383110188201

theorem tailTrace_2523465 : CollatzResearch.WordTrace tailWord_2523465 prefixEnd_2523465 863833639865383110188201 := by
  unfold tailWord_2523465
  simp only [CollatzResearch.WordTrace]
  refine ⟨92038329802924753355555849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61358886535283168903703899 92038329802924753355555849)
  ·
    refine ⟨69028747352193565016666887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92038329802924753355555849 69028747352193565016666887)
    ·
      refine ⟨103543121028290347525000331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69028747352193565016666887 103543121028290347525000331)
      ·
        refine ⟨155314681542435521287500497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103543121028290347525000331 155314681542435521287500497)
        ·
          refine ⟨116486011156826640965625373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155314681542435521287500497 116486011156826640965625373)
          ·
            refine ⟨43682254183809990362109515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116486011156826640965625373 43682254183809990362109515)
            ·
              refine ⟨65523381275714985543164273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43682254183809990362109515 65523381275714985543164273)
              ·
                refine ⟨49142535956786239157373205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65523381275714985543164273 49142535956786239157373205)
                ·
                  refine ⟨2303556372974354960501869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 49142535956786239157373205 2303556372974354960501869)
                  ·
                    refine ⟨863833639865383110188201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2303556372974354960501869 863833639865383110188201)
                    ·
                      rfl

theorem cell22_2523465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 6, 3].length) (baseStart_2523465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2523465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2523465 prefixEnd_2523465 := by exact prefixLift 2523465
  have htrace : WordTrace (prefixWord ++ tailWord_2523465) baseStart_2523465 baseEnd_2523465 := by
    simpa [prefixWord, tailWord_2523465, baseEnd_2523465] using wordTrace_append hprefix tailTrace_2523465
  have hstable : (prefixWord ++ tailWord_2523465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2523465).length < 2 ^ (prefixWord ++ tailWord_2523465).sum := by decide
  have hdescent : baseEnd_2523465 < baseStart_2523465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2523465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2523480 : List Nat := [2, 1, 2, 2, 1, 1, 2, 5, 2, 4]
def baseStart_2523480 : Nat := 118140960795 + 2523480 * 2 ^ 59
def prefixEnd_2523480 : Nat := 4983230072969 + 3 ^ 40 * 2523480 * 2
def baseEnd_2523480 : Nat := 863838774671928071063155

theorem tailTrace_2523480 : CollatzResearch.WordTrace tailWord_2523480 prefixEnd_2523480 863838774671928071063155 := by
  unfold tailWord_2523480
  simp only [CollatzResearch.WordTrace]
  refine ⟨46019438448935205458675947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61359251265246940611567929 46019438448935205458675947)
  ·
    refine ⟨69029157673402808188013921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46019438448935205458675947 69029157673402808188013921)
    ·
      refine ⟨51771868255052106141010441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69029157673402808188013921 51771868255052106141010441)
      ·
        refine ⟨38828901191289079605757831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51771868255052106141010441 38828901191289079605757831)
        ·
          refine ⟨58243351786933619408636747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38828901191289079605757831 58243351786933619408636747)
          ·
            refine ⟨87365027680400429112955121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58243351786933619408636747 87365027680400429112955121)
            ·
              refine ⟨65523770760300321834716341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87365027680400429112955121 65523770760300321834716341)
              ·
                refine ⟨6142853508778155172004657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 65523770760300321834716341 6142853508778155172004657)
                ·
                  refine ⟨4607140131583616379003493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6142853508778155172004657 4607140131583616379003493)
                  ·
                    refine ⟨863838774671928071063155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4607140131583616379003493 863838774671928071063155)
                    ·
                      rfl

theorem cell22_2523480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 5, 2, 4].length) (baseStart_2523480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2523480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2523480 prefixEnd_2523480 := by exact prefixLift 2523480
  have htrace : WordTrace (prefixWord ++ tailWord_2523480) baseStart_2523480 baseEnd_2523480 := by
    simpa [prefixWord, tailWord_2523480, baseEnd_2523480] using wordTrace_append hprefix tailTrace_2523480
  have hstable : (prefixWord ++ tailWord_2523480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2523480).length < 2 ^ (prefixWord ++ tailWord_2523480).sum := by decide
  have hdescent : baseEnd_2523480 < baseStart_2523480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2523480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2523495 : List Nat := [1, 1, 5, 1, 3, 2, 9]
def baseStart_2523495 : Nat := 118140960795 + 2523495 * 2 ^ 59
def prefixEnd_2523495 : Nat := 4983230072969 + 3 ^ 40 * 2523495 * 2
def baseEnd_2523495 : Nat := 31994218869573075256967

theorem tailTrace_2523495 : CollatzResearch.WordTrace tailWord_2523495 prefixEnd_2523495 31994218869573075256967 := by
  unfold tailWord_2523495
  simp only [CollatzResearch.WordTrace]
  refine ⟨92039423992816068479147939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61359615995210712319431959 92039423992816068479147939)
  ·
    refine ⟨138059135989224102718721909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92039423992816068479147939 138059135989224102718721909)
    ·
      refine ⟨12943043998989759629880179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 138059135989224102718721909 12943043998989759629880179)
      ·
        refine ⟨19414565998484639444820269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12943043998989759629880179 19414565998484639444820269)
        ·
          refine ⟨7280462249431739791807601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19414565998484639444820269 7280462249431739791807601)
          ·
            refine ⟨5460346687073804843855701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7280462249431739791807601 5460346687073804843855701)
            ·
              refine ⟨31994218869573075256967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5460346687073804843855701 31994218869573075256967)
              ·
                rfl

theorem cell22_2523495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 9].length) (baseStart_2523495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2523495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2523495 prefixEnd_2523495 := by exact prefixLift 2523495
  have htrace : WordTrace (prefixWord ++ tailWord_2523495) baseStart_2523495 baseEnd_2523495 := by
    simpa [prefixWord, tailWord_2523495, baseEnd_2523495] using wordTrace_append hprefix tailTrace_2523495
  have hstable : (prefixWord ++ tailWord_2523495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2523495).length < 2 ^ (prefixWord ++ tailWord_2523495).sum := by decide
  have hdescent : baseEnd_2523495 < baseStart_2523495 := by decide
  rcases family_descends (prefixWord ++ tailWord_2523495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2523527 : List Nat := [1, 1, 4, 2, 2, 1, 1, 4, 3, 3]
def baseStart_2523527 : Nat := 118140960795 + 2523527 * 2 ^ 59
def prefixEnd_2523527 : Nat := 4983230072969 + 3 ^ 40 * 2523527 * 2
def baseEnd_2523527 : Nat := 863854863732435615138011

theorem tailTrace_2523527 : CollatzResearch.WordTrace tailWord_2523527 prefixEnd_2523527 863854863732435615138011 := by
  unfold tailWord_2523527
  simp only [CollatzResearch.WordTrace]
  refine ⟨92040591128700137944312835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61360394085800091962875223 92040591128700137944312835)
  ·
    refine ⟨138060886693050206916469253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92040591128700137944312835 138060886693050206916469253)
    ·
      refine ⟨25886416254946913796837985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 138060886693050206916469253 25886416254946913796837985)
      ·
        refine ⟨19414812191210185347628489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25886416254946913796837985 19414812191210185347628489)
        ·
          refine ⟨14561109143407639010721367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19414812191210185347628489 14561109143407639010721367)
          ·
            refine ⟨21841663715111458516082051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14561109143407639010721367 21841663715111458516082051)
            ·
              refine ⟨32762495572667187774123077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21841663715111458516082051 32762495572667187774123077)
              ·
                refine ⟨6142967919875097707648077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32762495572667187774123077 6142967919875097707648077)
                ·
                  refine ⟨2303612969953161640368029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6142967919875097707648077 2303612969953161640368029)
                  ·
                    refine ⟨863854863732435615138011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2303612969953161640368029 863854863732435615138011)
                    ·
                      rfl

theorem cell22_2523527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 4, 3, 3].length) (baseStart_2523527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2523527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2523527 prefixEnd_2523527 := by exact prefixLift 2523527
  have htrace : WordTrace (prefixWord ++ tailWord_2523527) baseStart_2523527 baseEnd_2523527 := by
    simpa [prefixWord, tailWord_2523527, baseEnd_2523527] using wordTrace_append hprefix tailTrace_2523527
  have hstable : (prefixWord ++ tailWord_2523527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2523527).length < 2 ^ (prefixWord ++ tailWord_2523527).sum := by decide
  have hdescent : baseEnd_2523527 < baseStart_2523527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2523527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2523647 : List Nat := [1, 1, 2, 2, 1, 2, 7, 6]
def baseStart_2523647 : Nat := 118140960795 + 2523647 * 2 ^ 59
def prefixEnd_2523647 : Nat := 4983230072969 + 3 ^ 40 * 2523647 * 2
def baseEnd_2523647 : Nat := 95988438020532811348627

theorem tailTrace_2523647 : CollatzResearch.WordTrace tailWord_2523647 prefixEnd_2523647 95988438020532811348627 := by
  unfold tailWord_2523647
  simp only [CollatzResearch.WordTrace]
  refine ⟨92044967888265398438681195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61363311925510265625787463 92044967888265398438681195)
  ·
    refine ⟨138067451832398097658021793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92044967888265398438681195 138067451832398097658021793)
    ·
      refine ⟨103550588874298573243516345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138067451832398097658021793 103550588874298573243516345)
      ·
        refine ⟨77662941655723929932637259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103550588874298573243516345 77662941655723929932637259)
        ·
          refine ⟨116494412483585894898955889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77662941655723929932637259 116494412483585894898955889)
          ·
            refine ⟨87370809362689421174216917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116494412483585894898955889 87370809362689421174216917)
            ·
              refine ⟨2047753344438033308770709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 87370809362689421174216917 2047753344438033308770709)
              ·
                refine ⟨95988438020532811348627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2047753344438033308770709 95988438020532811348627)
                ·
                  rfl

theorem cell22_2523647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 7, 6].length) (baseStart_2523647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2523647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2523647 prefixEnd_2523647 := by exact prefixLift 2523647
  have htrace : WordTrace (prefixWord ++ tailWord_2523647) baseStart_2523647 baseEnd_2523647 := by
    simpa [prefixWord, tailWord_2523647, baseEnd_2523647] using wordTrace_append hprefix tailTrace_2523647
  have hstable : (prefixWord ++ tailWord_2523647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2523647).length < 2 ^ (prefixWord ++ tailWord_2523647).sum := by decide
  have hdescent : baseEnd_2523647 < baseStart_2523647 := by decide
  rcases family_descends (prefixWord ++ tailWord_2523647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2523649 : List Nat := [1, 2, 4, 1, 3, 1, 3, 1, 2, 4]
def baseStart_2523649 : Nat := 118140960795 + 2523649 * 2 ^ 59
def prefixEnd_2523649 : Nat := 4983230072969 + 3 ^ 40 * 2523649 * 2
def baseEnd_2523649 : Nat := 863896626825667963587637

theorem tailTrace_2523649 : CollatzResearch.WordTrace tailWord_2523649 prefixEnd_2523649 863896626825667963587637 := by
  unfold tailWord_2523649
  simp only [CollatzResearch.WordTrace]
  refine ⟨92045040834258152780254001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61363360556172101853502667 92045040834258152780254001)
  ·
    refine ⟨69033780625693614585190501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92045040834258152780254001 69033780625693614585190501)
    ·
      refine ⟨12943833867317552734723219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69033780625693614585190501 12943833867317552734723219)
      ·
        refine ⟨19415750800976329102084829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12943833867317552734723219 19415750800976329102084829)
        ·
          refine ⟨7280906550366123413281811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19415750800976329102084829 7280906550366123413281811)
          ·
            refine ⟨10921359825549185119922717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7280906550366123413281811 10921359825549185119922717)
            ·
              refine ⟨4095509934580944419971019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10921359825549185119922717 4095509934580944419971019)
              ·
                refine ⟨6143264901871416629956529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4095509934580944419971019 6143264901871416629956529)
                ·
                  refine ⟨4607448676403562472467397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6143264901871416629956529 4607448676403562472467397)
                  ·
                    refine ⟨863896626825667963587637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4607448676403562472467397 863896626825667963587637)
                    ·
                      rfl

theorem cell22_2523649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_2523649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2523649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2523649 prefixEnd_2523649 := by exact prefixLift 2523649
  have htrace : WordTrace (prefixWord ++ tailWord_2523649) baseStart_2523649 baseEnd_2523649 := by
    simpa [prefixWord, tailWord_2523649, baseEnd_2523649] using wordTrace_append hprefix tailTrace_2523649
  have hstable : (prefixWord ++ tailWord_2523649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2523649).length < 2 ^ (prefixWord ++ tailWord_2523649).sum := by decide
  have hdescent : baseEnd_2523649 < baseStart_2523649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2523649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2523668 : List Nat := [2, 4, 3, 1, 1, 1, 3, 2, 2, 3]
def baseStart_2523668 : Nat := 118140960795 + 2523668 * 2 ^ 59
def prefixEnd_2523668 : Nat := 4983230072969 + 3 ^ 40 * 2523668 * 2
def baseEnd_2523668 : Nat := 863903130913958247362579

theorem tailTrace_2523668 : CollatzResearch.WordTrace tailWord_2523668 prefixEnd_2523668 863903130913958247362579 := by
  unfold tailWord_2523668
  simp only [CollatzResearch.WordTrace]
  refine ⟨46022866910594659512597829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61363822547459546016797105 46022866910594659512597829)
  ·
    refine ⟨8629287545736498658612093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46022866910594659512597829 8629287545736498658612093)
    ·
      refine ⟨3235982829651186996979535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8629287545736498658612093 3235982829651186996979535)
      ·
        refine ⟨4853974244476780495469303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3235982829651186996979535 4853974244476780495469303)
        ·
          refine ⟨7280961366715170743203955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4853974244476780495469303 7280961366715170743203955)
          ·
            refine ⟨10921442050072756114805933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7280961366715170743203955 10921442050072756114805933)
            ·
              refine ⟨4095540768777283543052225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10921442050072756114805933 4095540768777283543052225)
              ·
                refine ⟨3071655576582962657289169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4095540768777283543052225 3071655576582962657289169)
                ·
                  refine ⟨2303741682437221992966877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3071655576582962657289169 2303741682437221992966877)
                  ·
                    refine ⟨863903130913958247362579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2303741682437221992966877 863903130913958247362579)
                    ·
                      rfl

theorem cell22_2523668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_2523668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2523668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2523668 prefixEnd_2523668 := by exact prefixLift 2523668
  have htrace : WordTrace (prefixWord ++ tailWord_2523668) baseStart_2523668 baseEnd_2523668 := by
    simpa [prefixWord, tailWord_2523668, baseEnd_2523668] using wordTrace_append hprefix tailTrace_2523668
  have hstable : (prefixWord ++ tailWord_2523668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2523668).length < 2 ^ (prefixWord ++ tailWord_2523668).sum := by decide
  have hdescent : baseEnd_2523668 < baseStart_2523668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2523668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2523692 : List Nat := [2, 2, 1, 1, 1, 2, 1, 7, 5]
def baseStart_2523692 : Nat := 118140960795 + 2523692 * 2 ^ 59
def prefixEnd_2523692 : Nat := 4983230072969 + 3 ^ 40 * 2523692 * 2
def baseEnd_2523692 : Nat := 287970448868143394920835

theorem tailTrace_2523692 : CollatzResearch.WordTrace tailWord_2523692 prefixEnd_2523692 287970448868143394920835 := by
  unfold tailWord_2523692
  simp only [CollatzResearch.WordTrace]
  refine ⟨46023304586551185562034665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61364406115401580749379553 46023304586551185562034665)
  ·
    refine ⟨34517478439913389171525999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46023304586551185562034665 34517478439913389171525999)
    ·
      refine ⟨51776217659870083757288999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34517478439913389171525999 51776217659870083757288999)
      ·
        refine ⟨77664326489805125635933499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51776217659870083757288999 77664326489805125635933499)
        ·
          refine ⟨116496489734707688453900249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77664326489805125635933499 116496489734707688453900249)
          ·
            refine ⟨87372367301030766340425187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116496489734707688453900249 87372367301030766340425187)
            ·
              refine ⟨131058550951546149510637781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87372367301030766340425187 131058550951546149510637781)
              ·
                refine ⟨3071684787926862879155573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 131058550951546149510637781 3071684787926862879155573)
                ·
                  refine ⟨287970448868143394920835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3071684787926862879155573 287970448868143394920835)
                  ·
                    rfl

theorem cell22_2523692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 5].length) (baseStart_2523692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2523692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2523692 prefixEnd_2523692 := by exact prefixLift 2523692
  have htrace : WordTrace (prefixWord ++ tailWord_2523692) baseStart_2523692 baseEnd_2523692 := by
    simpa [prefixWord, tailWord_2523692, baseEnd_2523692] using wordTrace_append hprefix tailTrace_2523692
  have hstable : (prefixWord ++ tailWord_2523692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2523692).length < 2 ^ (prefixWord ++ tailWord_2523692).sum := by decide
  have hdescent : baseEnd_2523692 < baseStart_2523692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2523692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2523713 : List Nat := [1, 2, 5, 1, 1, 2, 3, 3, 1, 3]
def baseStart_2523713 : Nat := 118140960795 + 2523713 * 2 ^ 59
def prefixEnd_2523713 : Nat := 4983230072969 + 3 ^ 40 * 2523713 * 2
def baseEnd_2523713 : Nat := 863918535333593129987441

theorem tailTrace_2523713 : CollatzResearch.WordTrace tailWord_2523713 prefixEnd_2523713 863918535333593129987441 := by
  unfold tailWord_2523713
  simp only [CollatzResearch.WordTrace]
  refine ⟨92047375106026291710583793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61364916737350861140389195 92047375106026291710583793)
  ·
    refine ⟨69035531329519718782937845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92047375106026291710583793 69035531329519718782937845)
    ·
      refine ⟨6472081062142473635900423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 69035531329519718782937845 6472081062142473635900423)
      ·
        refine ⟨9708121593213710453850635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6472081062142473635900423 9708121593213710453850635)
        ·
          refine ⟨14562182389820565680775953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9708121593213710453850635 14562182389820565680775953)
          ·
            refine ⟨10921636792365424260581965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14562182389820565680775953 10921636792365424260581965)
            ·
              refine ⟨4095613797137034097718237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10921636792365424260581965 4095613797137034097718237)
              ·
                refine ⟨1535855173926387786644339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4095613797137034097718237 1535855173926387786644339)
                ·
                  refine ⟨2303782760889581679966509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1535855173926387786644339 2303782760889581679966509)
                  ·
                    refine ⟨863918535333593129987441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2303782760889581679966509 863918535333593129987441)
                    ·
                      rfl

theorem cell22_2523713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_2523713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2523713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2523713 prefixEnd_2523713 := by exact prefixLift 2523713
  have htrace : WordTrace (prefixWord ++ tailWord_2523713) baseStart_2523713 baseEnd_2523713 := by
    simpa [prefixWord, tailWord_2523713, baseEnd_2523713] using wordTrace_append hprefix tailTrace_2523713
  have hstable : (prefixWord ++ tailWord_2523713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2523713).length < 2 ^ (prefixWord ++ tailWord_2523713).sum := by decide
  have hdescent : baseEnd_2523713 < baseStart_2523713 := by decide
  rcases family_descends (prefixWord ++ tailWord_2523713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2523767 : List Nat := [1, 1, 3, 1, 1, 3, 2, 3, 1, 6]
def baseStart_2523767 : Nat := 118140960795 + 2523767 * 2 ^ 59
def prefixEnd_2523767 : Nat := 4983230072969 + 3 ^ 40 * 2523767 * 2
def baseEnd_2523767 : Nat := 863937020637154989137275

theorem tailTrace_2523767 : CollatzResearch.WordTrace tailWord_2523767 prefixEnd_2523767 863937020637154989137275 := by
  unfold tailWord_2523767
  simp only [CollatzResearch.WordTrace]
  refine ⟨92049344647830658933049555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61366229765220439288699703 92049344647830658933049555)
  ·
    refine ⟨138074016971745988399574333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92049344647830658933049555 138074016971745988399574333)
    ·
      refine ⟨51777756364404745649840375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138074016971745988399574333 51777756364404745649840375)
      ·
        refine ⟨77666634546607118474760563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51777756364404745649840375 77666634546607118474760563)
        ·
          refine ⟨116499951819910677712140845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77666634546607118474760563 116499951819910677712140845)
          ·
            refine ⟨43687481932466504142052817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116499951819910677712140845 43687481932466504142052817)
            ·
              refine ⟨32765611449349878106539613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43687481932466504142052817 32765611449349878106539613)
              ·
                refine ⟨12287104293506204289952355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32765611449349878106539613 12287104293506204289952355)
                ·
                  refine ⟨18430656440259306434928533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12287104293506204289952355 18430656440259306434928533)
                  ·
                    refine ⟨863937020637154989137275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18430656440259306434928533 863937020637154989137275)
                    ·
                      rfl

theorem cell22_2523767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 3, 1, 6].length) (baseStart_2523767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2523767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2523767 prefixEnd_2523767 := by exact prefixLift 2523767
  have htrace : WordTrace (prefixWord ++ tailWord_2523767) baseStart_2523767 baseEnd_2523767 := by
    simpa [prefixWord, tailWord_2523767, baseEnd_2523767] using wordTrace_append hprefix tailTrace_2523767
  have hstable : (prefixWord ++ tailWord_2523767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2523767).length < 2 ^ (prefixWord ++ tailWord_2523767).sum := by decide
  have hdescent : baseEnd_2523767 < baseStart_2523767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2523767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2523769 : List Nat := [1, 2, 1, 3, 3, 3, 1, 2, 1, 5]
def baseStart_2523769 : Nat := 118140960795 + 2523769 * 2 ^ 59
def prefixEnd_2523769 : Nat := 4983230072969 + 3 ^ 40 * 2523769 * 2
def baseEnd_2523769 : Nat := 863937705278027650587269

theorem tailTrace_2523769 : CollatzResearch.WordTrace tailWord_2523769 prefixEnd_2523769 863937705278027650587269 := by
  unfold tailWord_2523769
  simp only [CollatzResearch.WordTrace]
  refine ⟨92049417593823413274622361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61366278395882275516414907 92049417593823413274622361)
  ·
    refine ⟨69037063195367559955966771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92049417593823413274622361 69037063195367559955966771)
    ·
      refine ⟨103555594793051339933950157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69037063195367559955966771 103555594793051339933950157)
      ·
        refine ⟨38833348047394252475231309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103555594793051339933950157 38833348047394252475231309)
        ·
          refine ⟨14562505517772844678211741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38833348047394252475231309 14562505517772844678211741)
          ·
            refine ⟨5460939569164816754329403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14562505517772844678211741 5460939569164816754329403)
            ·
              refine ⟨8191409353747225131494105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5460939569164816754329403 8191409353747225131494105)
              ·
                refine ⟨6143557015310418848620579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8191409353747225131494105 6143557015310418848620579)
                ·
                  refine ⟨9215335522965628272930869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6143557015310418848620579 9215335522965628272930869)
                  ·
                    refine ⟨863937705278027650587269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9215335522965628272930869 863937705278027650587269)
                    ·
                      rfl

theorem cell22_2523769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 2, 1, 5].length) (baseStart_2523769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2523769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2523769 prefixEnd_2523769 := by exact prefixLift 2523769
  have htrace : WordTrace (prefixWord ++ tailWord_2523769) baseStart_2523769 baseEnd_2523769 := by
    simpa [prefixWord, tailWord_2523769, baseEnd_2523769] using wordTrace_append hprefix tailTrace_2523769
  have hstable : (prefixWord ++ tailWord_2523769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2523769).length < 2 ^ (prefixWord ++ tailWord_2523769).sum := by decide
  have hdescent : baseEnd_2523769 < baseStart_2523769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2523769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2523773 : List Nat := [1, 4, 1, 1, 5, 1, 3, 1, 1, 4]
def baseStart_2523773 : Nat := 118140960795 + 2523773 * 2 ^ 59
def prefixEnd_2523773 : Nat := 4983230072969 + 3 ^ 40 * 2523773 * 2
def baseEnd_2523773 : Nat := 863939074559772973487257

theorem tailTrace_2523773 : CollatzResearch.WordTrace tailWord_2523773 prefixEnd_2523773 863939074559772973487257 := by
  unfold tailWord_2523773
  simp only [CollatzResearch.WordTrace]
  refine ⟨92049563485808921957767973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61366375657205947971845315 92049563485808921957767973)
  ·
    refine ⟨17259293153589172867081495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92049563485808921957767973 17259293153589172867081495)
    ·
      refine ⟨25888939730383759300622243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17259293153589172867081495 25888939730383759300622243)
      ·
        refine ⟨38833409595575638950933365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25888939730383759300622243 38833409595575638950933365)
        ·
          refine ⟨3640632149585216151650003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38833409595575638950933365 3640632149585216151650003)
          ·
            refine ⟨5460948224377824227475005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3640632149585216151650003 5460948224377824227475005)
            ·
              refine ⟨2047855584141684085303127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5460948224377824227475005 2047855584141684085303127)
              ·
                refine ⟨3071783376212526127954691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2047855584141684085303127 3071783376212526127954691)
                ·
                  refine ⟨4607675064318789191932037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3071783376212526127954691 4607675064318789191932037)
                  ·
                    refine ⟨863939074559772973487257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4607675064318789191932037 863939074559772973487257)
                    ·
                      rfl

theorem cell22_2523773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 3, 1, 1, 4].length) (baseStart_2523773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2523773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2523773 prefixEnd_2523773 := by exact prefixLift 2523773
  have htrace : WordTrace (prefixWord ++ tailWord_2523773) baseStart_2523773 baseEnd_2523773 := by
    simpa [prefixWord, tailWord_2523773, baseEnd_2523773] using wordTrace_append hprefix tailTrace_2523773
  have hstable : (prefixWord ++ tailWord_2523773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2523773).length < 2 ^ (prefixWord ++ tailWord_2523773).sum := by decide
  have hdescent : baseEnd_2523773 < baseStart_2523773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2523773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2523797 : List Nat := [1, 3, 2, 1, 1, 1, 1, 1, 4, 7]
def baseStart_2523797 : Nat := 118140960795 + 2523797 * 2 ^ 59
def prefixEnd_2523797 : Nat := 4983230072969 + 3 ^ 40 * 2523797 * 2
def baseEnd_2523797 : Nat := 863947290250244910887183

theorem tailTrace_2523797 : CollatzResearch.WordTrace tailWord_2523797 prefixEnd_2523797 863947290250244910887183 := by
  unfold tailWord_2523797
  simp only [CollatzResearch.WordTrace]
  refine ⟨92050438837721974056641645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61366959225147982704427763 92050438837721974056641645)
  ·
    refine ⟨34518914564145740271240617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92050438837721974056641645 34518914564145740271240617)
    ·
      refine ⟨25889185923109305203430463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34518914564145740271240617 25889185923109305203430463)
      ·
        refine ⟨38833778884663957805145695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25889185923109305203430463 38833778884663957805145695)
        ·
          refine ⟨58250668326995936707718543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38833778884663957805145695 58250668326995936707718543)
          ·
            refine ⟨87376002490493905061577815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58250668326995936707718543 87376002490493905061577815)
            ·
              refine ⟨131064003735740857592366723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87376002490493905061577815 131064003735740857592366723)
              ·
                refine ⟨196596005603611286388550085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131064003735740857592366723 196596005603611286388550085)
                ·
                  refine ⟨36861751050677116197853141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 196596005603611286388550085 36861751050677116197853141)
                  ·
                    refine ⟨863947290250244910887183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36861751050677116197853141 863947290250244910887183)
                    ·
                      rfl

theorem cell22_2523797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 7].length) (baseStart_2523797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2523797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2523797 prefixEnd_2523797 := by exact prefixLift 2523797
  have htrace : WordTrace (prefixWord ++ tailWord_2523797) baseStart_2523797 baseEnd_2523797 := by
    simpa [prefixWord, tailWord_2523797, baseEnd_2523797] using wordTrace_append hprefix tailTrace_2523797
  have hstable : (prefixWord ++ tailWord_2523797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2523797).length < 2 ^ (prefixWord ++ tailWord_2523797).sum := by decide
  have hdescent : baseEnd_2523797 < baseStart_2523797 := by decide
  rcases family_descends (prefixWord ++ tailWord_2523797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2523818 : List Nat := [3, 1, 5, 2, 1, 1, 1, 1, 1, 6]
def baseStart_2523818 : Nat := 118140960795 + 2523818 * 2 ^ 59
def prefixEnd_2523818 : Nat := 4983230072969 + 3 ^ 40 * 2523818 * 2
def baseEnd_2523818 : Nat := 863954478979407856112119

theorem tailTrace_2523818 : CollatzResearch.WordTrace tailWord_2523818 prefixEnd_2523818 863954478979407856112119 := by
  unfold tailWord_2523818
  simp only [CollatzResearch.WordTrace]
  refine ⟨23012801192661473660789027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61367469847097263095437405 23012801192661473660789027)
  ·
    refine ⟨34519201788992210491183541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23012801192661473660789027 34519201788992210491183541)
    ·
      refine ⟨3236175167718019733548457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34519201788992210491183541 3236175167718019733548457)
      ·
        refine ⟨2427131375788514800161343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3236175167718019733548457 2427131375788514800161343)
        ·
          refine ⟨3640697063682772200242015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2427131375788514800161343 3640697063682772200242015)
          ·
            refine ⟨5461045595524158300363023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3640697063682772200242015 5461045595524158300363023)
            ·
              refine ⟨8191568393286237450544535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5461045595524158300363023 8191568393286237450544535)
              ·
                refine ⟨12287352589929356175816803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8191568393286237450544535 12287352589929356175816803)
                ·
                  refine ⟨18431028884894034263725205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12287352589929356175816803 18431028884894034263725205)
                  ·
                    refine ⟨863954478979407856112119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18431028884894034263725205 863954478979407856112119)
                    ·
                      rfl

theorem cell22_2523818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_2523818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2523818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2523818 prefixEnd_2523818 := by exact prefixLift 2523818
  have htrace : WordTrace (prefixWord ++ tailWord_2523818) baseStart_2523818 baseEnd_2523818 := by
    simpa [prefixWord, tailWord_2523818, baseEnd_2523818] using wordTrace_append hprefix tailTrace_2523818
  have hstable : (prefixWord ++ tailWord_2523818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2523818).length < 2 ^ (prefixWord ++ tailWord_2523818).sum := by decide
  have hdescent : baseEnd_2523818 < baseStart_2523818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2523818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2523848 : List Nat := [2, 1, 3, 1, 2, 3, 2, 4, 1, 3]
def baseStart_2523848 : Nat := 118140960795 + 2523848 * 2 ^ 59
def prefixEnd_2523848 : Nat := 4983230072969 + 3 ^ 40 * 2523848 * 2
def baseEnd_2523848 : Nat := 863964748592497777862027

theorem tailTrace_2523848 : CollatzResearch.WordTrace tailWord_2523848 prefixEnd_2523848 863964748592497777862027 := by
  unfold tailWord_2523848
  simp only [CollatzResearch.WordTrace]
  refine ⟨46026149480268604883374099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61368199307024806511165465 46026149480268604883374099)
  ·
    refine ⟨69039224220402907325061149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46026149480268604883374099 69039224220402907325061149)
    ·
      refine ⟨25889709082651090246897931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69039224220402907325061149 25889709082651090246897931)
      ·
        refine ⟨38834563623976635370346897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25889709082651090246897931 38834563623976635370346897)
        ·
          refine ⟨29125922717982476527760173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38834563623976635370346897 29125922717982476527760173)
          ·
            refine ⟨10922221019243428697910065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29125922717982476527760173 10922221019243428697910065)
            ·
              refine ⟨8191665764432571523432549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10922221019243428697910065 8191665764432571523432549)
              ·
                refine ⟨1535937330831107160643603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8191665764432571523432549 1535937330831107160643603)
                ·
                  refine ⟨2303905996246660740965405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1535937330831107160643603 2303905996246660740965405)
                  ·
                    refine ⟨863964748592497777862027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2303905996246660740965405 863964748592497777862027)
                    ·
                      rfl

theorem cell22_2523848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 4, 1, 3].length) (baseStart_2523848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2523848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2523848 prefixEnd_2523848 := by exact prefixLift 2523848
  have htrace : WordTrace (prefixWord ++ tailWord_2523848) baseStart_2523848 baseEnd_2523848 := by
    simpa [prefixWord, tailWord_2523848, baseEnd_2523848] using wordTrace_append hprefix tailTrace_2523848
  have hstable : (prefixWord ++ tailWord_2523848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2523848).length < 2 ^ (prefixWord ++ tailWord_2523848).sum := by decide
  have hdescent : baseEnd_2523848 < baseStart_2523848 := by decide
  rcases family_descends (prefixWord ++ tailWord_2523848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2523919 : List Nat := [1, 1, 2, 1, 1, 1, 5, 2, 4, 4]
def baseStart_2523919 : Nat := 118140960795 + 2523919 * 2 ^ 59
def prefixEnd_2523919 : Nat := 4983230072969 + 3 ^ 40 * 2523919 * 2
def baseEnd_2523919 : Nat := 863989053343477259336809

theorem tailTrace_2523919 : CollatzResearch.WordTrace tailWord_2523919 prefixEnd_2523919 863989053343477259336809 := by
  unfold tailWord_2523919
  simp only [CollatzResearch.WordTrace]
  refine ⟨92054888543279988892582811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61369925695519992595055207 92054888543279988892582811)
  ·
    refine ⟨138082332814919983338874217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92054888543279988892582811 138082332814919983338874217)
    ·
      refine ⟨103561749611189987504155663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138082332814919983338874217 103561749611189987504155663)
      ·
        refine ⟨155342624416784981256233495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103561749611189987504155663 155342624416784981256233495)
        ·
          refine ⟨233013936625177471884350243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155342624416784981256233495 233013936625177471884350243)
          ·
            refine ⟨349520904937766207826525365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233013936625177471884350243 349520904937766207826525365)
            ·
              refine ⟨32767584837915581983736753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 349520904937766207826525365 32767584837915581983736753)
              ·
                refine ⟨24575688628436686487802565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32767584837915581983736753 24575688628436686487802565)
                ·
                  refine ⟨4607941617831878716462981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24575688628436686487802565 4607941617831878716462981)
                  ·
                    refine ⟨863989053343477259336809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4607941617831878716462981 863989053343477259336809)
                    ·
                      rfl

theorem cell22_2523919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 4, 4].length) (baseStart_2523919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2523919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2523919 prefixEnd_2523919 := by exact prefixLift 2523919
  have htrace : WordTrace (prefixWord ++ tailWord_2523919) baseStart_2523919 baseEnd_2523919 := by
    simpa [prefixWord, tailWord_2523919, baseEnd_2523919] using wordTrace_append hprefix tailTrace_2523919
  have hstable : (prefixWord ++ tailWord_2523919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2523919).length < 2 ^ (prefixWord ++ tailWord_2523919).sum := by decide
  have hdescent : baseEnd_2523919 < baseStart_2523919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2523919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2523936 : List Nat := [2, 1, 1, 5, 1, 2, 1, 3, 2, 4]
def baseStart_2523936 : Nat := 118140960795 + 2523936 * 2 ^ 59
def prefixEnd_2523936 : Nat := 4983230072969 + 3 ^ 40 * 2523936 * 2
def baseEnd_2523936 : Nat := 863994872790894881661757

theorem tailTrace_2523936 : CollatzResearch.WordTrace tailWord_2523936 prefixEnd_2523936 863994872790894881661757 := by
  unfold tailWord_2523936
  simp only [CollatzResearch.WordTrace]
  refine ⟨46027754292109200397975831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61370339056145600530634441 46027754292109200397975831)
  ·
    refine ⟨69041631438163800596963747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46027754292109200397975831 69041631438163800596963747)
    ·
      refine ⟨103562447157245700895445621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69041631438163800596963747 103562447157245700895445621)
      ·
        refine ⟨9708979420991784458948027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 103562447157245700895445621 9708979420991784458948027)
        ·
          refine ⟨14563469131487676688422041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9708979420991784458948027 14563469131487676688422041)
          ·
            refine ⟨10922601848615757516316531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14563469131487676688422041 10922601848615757516316531)
            ·
              refine ⟨16383902772923636274474797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10922601848615757516316531 16383902772923636274474797)
              ·
                refine ⟨6143963539846363602928049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16383902772923636274474797 6143963539846363602928049)
                ·
                  refine ⟨4607972654884772702196037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6143963539846363602928049 4607972654884772702196037)
                  ·
                    refine ⟨863994872790894881661757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4607972654884772702196037 863994872790894881661757)
                    ·
                      rfl

theorem cell22_2523936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 3, 2, 4].length) (baseStart_2523936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2523936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2523936 prefixEnd_2523936 := by exact prefixLift 2523936
  have htrace : WordTrace (prefixWord ++ tailWord_2523936) baseStart_2523936 baseEnd_2523936 := by
    simpa [prefixWord, tailWord_2523936, baseEnd_2523936] using wordTrace_append hprefix tailTrace_2523936
  have hstable : (prefixWord ++ tailWord_2523936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2523936).length < 2 ^ (prefixWord ++ tailWord_2523936).sum := by decide
  have hdescent : baseEnd_2523936 < baseStart_2523936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2523936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2524000 : List Nat := [2, 1, 1, 3, 3, 1, 4, 3, 1, 3]
def baseStart_2524000 : Nat := 118140960795 + 2524000 * 2 ^ 59
def prefixEnd_2524000 : Nat := 4983230072969 + 3 ^ 40 * 2524000 * 2
def baseEnd_2524000 : Nat := 864016781298820048061561

theorem tailTrace_2524000 : CollatzResearch.WordTrace tailWord_2524000 prefixEnd_2524000 864016781298820048061561 := by
  unfold tailWord_2524000
  simp only [CollatzResearch.WordTrace]
  refine ⟨46028921427993269863140727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61371895237324359817520969 46028921427993269863140727)
  ·
    refine ⟨69043382141989904794711091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46028921427993269863140727 69043382141989904794711091)
    ·
      refine ⟨103565073212984857192066637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69043382141989904794711091 103565073212984857192066637)
      ·
        refine ⟨38836902454869321447024989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103565073212984857192066637 38836902454869321447024989)
        ·
          refine ⟨14563838420575995542634371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38836902454869321447024989 14563838420575995542634371)
          ·
            refine ⟨21845757630863993313951557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14563838420575995542634371 21845757630863993313951557)
            ·
              refine ⟨4096079555786998746365917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21845757630863993313951557 4096079555786998746365917)
              ·
                refine ⟨1536029833420124529887219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4096079555786998746365917 1536029833420124529887219)
                ·
                  refine ⟨2304044750130186794830829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1536029833420124529887219 2304044750130186794830829)
                  ·
                    refine ⟨864016781298820048061561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2304044750130186794830829 864016781298820048061561)
                    ·
                      rfl

theorem cell22_2524000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 3, 1, 3].length) (baseStart_2524000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2524000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2524000 prefixEnd_2524000 := by exact prefixLift 2524000
  have htrace : WordTrace (prefixWord ++ tailWord_2524000) baseStart_2524000 baseEnd_2524000 := by
    simpa [prefixWord, tailWord_2524000, baseEnd_2524000] using wordTrace_append hprefix tailTrace_2524000
  have hstable : (prefixWord ++ tailWord_2524000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2524000).length < 2 ^ (prefixWord ++ tailWord_2524000).sum := by decide
  have hdescent : baseEnd_2524000 < baseStart_2524000 := by decide
  rcases family_descends (prefixWord ++ tailWord_2524000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2524041 : List Nat := [1, 2, 1, 1, 5, 2, 2, 2, 6]
def baseStart_2524041 : Nat := 118140960795 + 2524041 * 2 ^ 59
def prefixEnd_2524041 : Nat := 4983230072969 + 3 ^ 40 * 2524041 * 2
def baseEnd_2524041 : Nat := 288010272145569869262145

theorem tailTrace_2524041 : CollatzResearch.WordTrace tailWord_2524041 prefixEnd_2524041 288010272145569869262145 := by
  unfold tailWord_2524041
  simp only [CollatzResearch.WordTrace]
  refine ⟨92059338248838003728523977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61372892165892002485682651 92059338248838003728523977)
  ·
    refine ⟨69044503686628502796392983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92059338248838003728523977 69044503686628502796392983)
    ·
      refine ⟨103566755529942754194589475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69044503686628502796392983 103566755529942754194589475)
      ·
        refine ⟨155350133294914131291884213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103566755529942754194589475 155350133294914131291884213)
        ·
          refine ⟨14564074996398199808614145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 155350133294914131291884213 14564074996398199808614145)
          ·
            refine ⟨10923056247298649856460609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14564074996398199808614145 10923056247298649856460609)
            ·
              refine ⟨8192292185473987392345457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10923056247298649856460609 8192292185473987392345457)
              ·
                refine ⟨6144219139105490544259093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8192292185473987392345457 6144219139105490544259093)
                ·
                  refine ⟨288010272145569869262145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6144219139105490544259093 288010272145569869262145)
                  ·
                    rfl

theorem cell22_2524041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 2, 6].length) (baseStart_2524041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2524041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2524041 prefixEnd_2524041 := by exact prefixLift 2524041
  have htrace : WordTrace (prefixWord ++ tailWord_2524041) baseStart_2524041 baseEnd_2524041 := by
    simpa [prefixWord, tailWord_2524041, baseEnd_2524041] using wordTrace_append hprefix tailTrace_2524041
  have hstable : (prefixWord ++ tailWord_2524041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2524041).length < 2 ^ (prefixWord ++ tailWord_2524041).sum := by decide
  have hdescent : baseEnd_2524041 < baseStart_2524041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2524041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2524073 : List Nat := [1, 2, 1, 1, 1, 1, 6, 4, 2, 3]
def baseStart_2524073 : Nat := 118140960795 + 2524073 * 2 ^ 59
def prefixEnd_2524073 : Nat := 4983230072969 + 3 ^ 40 * 2524073 * 2
def baseEnd_2524073 : Nat := 864041770690672190986337

theorem tailTrace_2524073 : CollatzResearch.WordTrace tailWord_2524073 prefixEnd_2524073 864041770690672190986337 := by
  unfold tailWord_2524073
  simp only [CollatzResearch.WordTrace]
  refine ⟨92060505384722073193688873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61373670256481382129125915 92060505384722073193688873)
  ·
    refine ⟨69045379038541554895266655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92060505384722073193688873 69045379038541554895266655)
    ·
      refine ⟨103568068557812332342899983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69045379038541554895266655 103568068557812332342899983)
      ·
        refine ⟨155352102836718498514349975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103568068557812332342899983 155352102836718498514349975)
        ·
          refine ⟨233028154255077747771524963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155352102836718498514349975 233028154255077747771524963)
          ·
            refine ⟨349542231382616621657287445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233028154255077747771524963 349542231382616621657287445)
            ·
              refine ⟨16384792096060154140185349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 349542231382616621657287445 16384792096060154140185349)
              ·
                refine ⟨3072148518011278901284753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16384792096060154140185349 3072148518011278901284753)
                ·
                  refine ⟨2304111388508459175963565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3072148518011278901284753 2304111388508459175963565)
                  ·
                    refine ⟨864041770690672190986337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2304111388508459175963565 864041770690672190986337)
                    ·
                      rfl

theorem cell22_2524073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 4, 2, 3].length) (baseStart_2524073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2524073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2524073 prefixEnd_2524073 := by exact prefixLift 2524073
  have htrace : WordTrace (prefixWord ++ tailWord_2524073) baseStart_2524073 baseEnd_2524073 := by
    simpa [prefixWord, tailWord_2524073, baseEnd_2524073] using wordTrace_append hprefix tailTrace_2524073
  have hstable : (prefixWord ++ tailWord_2524073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2524073).length < 2 ^ (prefixWord ++ tailWord_2524073).sum := by decide
  have hdescent : baseEnd_2524073 < baseStart_2524073 := by decide
  rcases family_descends (prefixWord ++ tailWord_2524073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2524193 : List Nat := [1, 2, 3, 2, 3, 1, 1, 3, 6]
def baseStart_2524193 : Nat := 118140960795 + 2524193 * 2 ^ 59
def prefixEnd_2524193 : Nat := 4983230072969 + 3 ^ 40 * 2524193 * 2
def baseEnd_2524193 : Nat := 288027616381010625995323

theorem tailTrace_2524193 : CollatzResearch.WordTrace tailWord_2524193 prefixEnd_2524193 288027616381010625995323 := by
  unfold tailWord_2524193
  simp only [CollatzResearch.WordTrace]
  refine ⟨92064882144287333688057233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61376588096191555792038155 92064882144287333688057233)
  ·
    refine ⟨69048661608215500266042925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92064882144287333688057233 69048661608215500266042925)
    ·
      refine ⟨25893248103080812599766097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69048661608215500266042925 25893248103080812599766097)
      ·
        refine ⟨19419936077310609449824573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25893248103080812599766097 19419936077310609449824573)
        ·
          refine ⟨7282476028991478543684215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19419936077310609449824573 7282476028991478543684215)
          ·
            refine ⟨10923714043487217815526323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7282476028991478543684215 10923714043487217815526323)
            ·
              refine ⟨16385571065230826723289485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10923714043487217815526323 16385571065230826723289485)
              ·
                refine ⟨6144589149461560021233557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16385571065230826723289485 6144589149461560021233557)
                ·
                  refine ⟨288027616381010625995323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6144589149461560021233557 288027616381010625995323)
                  ·
                    rfl

theorem cell22_2524193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 3, 6].length) (baseStart_2524193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2524193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2524193 prefixEnd_2524193 := by exact prefixLift 2524193
  have htrace : WordTrace (prefixWord ++ tailWord_2524193) baseStart_2524193 baseEnd_2524193 := by
    simpa [prefixWord, tailWord_2524193, baseEnd_2524193] using wordTrace_append hprefix tailTrace_2524193
  have hstable : (prefixWord ++ tailWord_2524193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2524193).length < 2 ^ (prefixWord ++ tailWord_2524193).sum := by decide
  have hdescent : baseEnd_2524193 < baseStart_2524193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2524193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2524212 : List Nat := [2, 5, 1, 2, 1, 1, 1, 4, 1, 4]
def baseStart_2524212 : Nat := 118140960795 + 2524212 * 2 ^ 59
def prefixEnd_2524212 : Nat := 4983230072969 + 3 ^ 40 * 2524212 * 2
def baseEnd_2524212 : Nat := 864089353231322161760911

theorem tailTrace_2524212 : CollatzResearch.WordTrace tailWord_2524212 prefixEnd_2524212 864089353231322161760911 := by
  unfold tailWord_2524212
  simp only [CollatzResearch.WordTrace]
  refine ⟨46032787565609249966499445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61377050087478999955332593 46032787565609249966499445)
  ·
    refine ⟨4315573834275867184359323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46032787565609249966499445 4315573834275867184359323)
    ·
      refine ⟨6473360751413800776538985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4315573834275867184359323 6473360751413800776538985)
      ·
        refine ⟨4855020563560350582404239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6473360751413800776538985 4855020563560350582404239)
        ·
          refine ⟨7282530845340525873606359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4855020563560350582404239 7282530845340525873606359)
          ·
            refine ⟨10923796268010788810409539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7282530845340525873606359 10923796268010788810409539)
            ·
              refine ⟨16385694402016183215614309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10923796268010788810409539 16385694402016183215614309)
              ·
                refine ⟨3072317700378034352927683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16385694402016183215614309 3072317700378034352927683)
                ·
                  refine ⟨4608476550567051529391525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3072317700378034352927683 4608476550567051529391525)
                  ·
                    refine ⟨864089353231322161760911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4608476550567051529391525 864089353231322161760911)
                    ·
                      rfl

theorem cell22_2524212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_2524212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2524212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2524212 prefixEnd_2524212 := by exact prefixLift 2524212
  have htrace : WordTrace (prefixWord ++ tailWord_2524212) baseStart_2524212 baseEnd_2524212 := by
    simpa [prefixWord, tailWord_2524212, baseEnd_2524212] using wordTrace_append hprefix tailTrace_2524212
  have hstable : (prefixWord ++ tailWord_2524212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2524212).length < 2 ^ (prefixWord ++ tailWord_2524212).sum := by decide
  have hdescent : baseEnd_2524212 < baseStart_2524212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2524212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2524223 : List Nat := [1, 1, 2, 2, 3, 1, 1, 5, 2, 4]
def baseStart_2524223 : Nat := 118140960795 + 2524223 * 2 ^ 59
def prefixEnd_2524223 : Nat := 4983230072969 + 3 ^ 40 * 2524223 * 2
def baseEnd_2524223 : Nat := 864093118756121799735877

theorem tailTrace_2524223 : CollatzResearch.WordTrace tailWord_2524223 prefixEnd_2524223 864093118756121799735877 := by
  unfold tailWord_2524223
  simp only [CollatzResearch.WordTrace]
  refine ⟨92065976334178648811649323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61377317556119099207766215 92065976334178648811649323)
  ·
    refine ⟨138098964501267973217473985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92065976334178648811649323 138098964501267973217473985)
    ·
      refine ⟨103574223375950979913105489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138098964501267973217473985 103574223375950979913105489)
      ·
        refine ⟨77680667531963234934829117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103574223375950979913105489 77680667531963234934829117)
        ·
          refine ⟨29130250324486213100560919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77680667531963234934829117 29130250324486213100560919)
          ·
            refine ⟨43695375486729319650841379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29130250324486213100560919 43695375486729319650841379)
            ·
              refine ⟨65543063230093979476262069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43695375486729319650841379 65543063230093979476262069)
              ·
                refine ⟨6144662177821310575899569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 65543063230093979476262069 6144662177821310575899569)
                ·
                  refine ⟨4608496633365982931924677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6144662177821310575899569 4608496633365982931924677)
                  ·
                    refine ⟨864093118756121799735877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4608496633365982931924677 864093118756121799735877)
                    ·
                      rfl

theorem cell22_2524223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 5, 2, 4].length) (baseStart_2524223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2524223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2524223 prefixEnd_2524223 := by exact prefixLift 2524223
  have htrace : WordTrace (prefixWord ++ tailWord_2524223) baseStart_2524223 baseEnd_2524223 := by
    simpa [prefixWord, tailWord_2524223, baseEnd_2524223] using wordTrace_append hprefix tailTrace_2524223
  have hstable : (prefixWord ++ tailWord_2524223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2524223).length < 2 ^ (prefixWord ++ tailWord_2524223).sum := by decide
  have hdescent : baseEnd_2524223 < baseStart_2524223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2524223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2524362 : List Nat := [3, 1, 2, 1, 3, 2, 2, 4, 4]
def baseStart_2524362 : Nat := 118140960795 + 2524362 * 2 ^ 59
def prefixEnd_2524362 : Nat := 4983230072969 + 3 ^ 40 * 2524362 * 2
def baseEnd_2524362 : Nat := 288046900432257256836817

theorem tailTrace_2524362 : CollatzResearch.WordTrace tailWord_2524362 prefixEnd_2524362 288046900432257256836817 := by
  unfold tailWord_2524362
  simp only [CollatzResearch.WordTrace]
  refine ⟨23017761520168768887739835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61380697387116717033972893 23017761520168768887739835)
  ·
    refine ⟨34526642280253153331609753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23017761520168768887739835 34526642280253153331609753)
    ·
      refine ⟨25894981710189864998707315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34526642280253153331609753 25894981710189864998707315)
      ·
        refine ⟨38842472565284797498060973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25894981710189864998707315 38842472565284797498060973)
        ·
          refine ⟨14565927211981799061772865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38842472565284797498060973 14565927211981799061772865)
          ·
            refine ⟨10924445408986349296329649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14565927211981799061772865 10924445408986349296329649)
            ·
              refine ⟨8193334056739761972247237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10924445408986349296329649 8193334056739761972247237)
              ·
                refine ⟨1536250135638705369796357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8193334056739761972247237 1536250135638705369796357)
                ·
                  refine ⟨288046900432257256836817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1536250135638705369796357 288046900432257256836817)
                  ·
                    rfl

theorem cell22_2524362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 4, 4].length) (baseStart_2524362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2524362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2524362 prefixEnd_2524362 := by exact prefixLift 2524362
  have htrace : WordTrace (prefixWord ++ tailWord_2524362) baseStart_2524362 baseEnd_2524362 := by
    simpa [prefixWord, tailWord_2524362, baseEnd_2524362] using wordTrace_append hprefix tailTrace_2524362
  have hstable : (prefixWord ++ tailWord_2524362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2524362).length < 2 ^ (prefixWord ++ tailWord_2524362).sum := by decide
  have hdescent : baseEnd_2524362 < baseStart_2524362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2524362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2524480 : List Nat := [2, 1, 1, 2, 2, 1, 4, 3, 6]
def baseStart_2524480 : Nat := 118140960795 + 2524480 * 2 ^ 59
def prefixEnd_2524480 : Nat := 4983230072969 + 3 ^ 40 * 2524480 * 2
def baseEnd_2524480 : Nat := 288060365036086265353363

theorem tailTrace_2524480 : CollatzResearch.WordTrace tailWord_2524480 prefixEnd_2524480 288060365036086265353363 := by
  unfold tailWord_2524480
  simp only [CollatzResearch.WordTrace]
  refine ⟨46037674947123790851877447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61383566596165054469169929 46037674947123790851877447)
  ·
    refine ⟨69056512420685686277816171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46037674947123790851877447 69056512420685686277816171)
    ·
      refine ⟨103584768631028529416724257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69056512420685686277816171 103584768631028529416724257)
      ·
        refine ⟨77688576473271397062543193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103584768631028529416724257 77688576473271397062543193)
        ·
          refine ⟨58266432354953547796907395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77688576473271397062543193 58266432354953547796907395)
          ·
            refine ⟨87399648532430321695361093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58266432354953547796907395 87399648532430321695361093)
            ·
              refine ⟨16387434099830685317880205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87399648532430321695361093 16387434099830685317880205)
              ·
                refine ⟨6145287787436506994205077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16387434099830685317880205 6145287787436506994205077)
                ·
                  refine ⟨288060365036086265353363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6145287787436506994205077 288060365036086265353363)
                  ·
                    rfl

theorem cell22_2524480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 3, 6].length) (baseStart_2524480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2524480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2524480 prefixEnd_2524480 := by exact prefixLift 2524480
  have htrace : WordTrace (prefixWord ++ tailWord_2524480) baseStart_2524480 baseEnd_2524480 := by
    simpa [prefixWord, tailWord_2524480, baseEnd_2524480] using wordTrace_append hprefix tailTrace_2524480
  have hstable : (prefixWord ++ tailWord_2524480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2524480).length < 2 ^ (prefixWord ++ tailWord_2524480).sum := by decide
  have hdescent : baseEnd_2524480 < baseStart_2524480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2524480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2524484 : List Nat := [2, 3, 4, 1, 1, 2, 1, 1, 2, 5]
def baseStart_2524484 : Nat := 118140960795 + 2524484 * 2 ^ 59
def prefixEnd_2524484 : Nat := 4983230072969 + 3 ^ 40 * 2524484 * 2
def baseEnd_2524484 : Nat := 864182464390004118960077

theorem tailTrace_2524484 : CollatzResearch.WordTrace tailWord_2524484 prefixEnd_2524484 864182464390004118960077 := by
  unfold tailWord_2524484
  simp only [CollatzResearch.WordTrace]
  refine ⟨46037747893116545193450253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61383663857488726924600337 46037747893116545193450253)
  ·
    refine ⟨17264155459918704447543845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46037747893116545193450253 17264155459918704447543845)
    ·
      refine ⟨3237029148734757083914471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17264155459918704447543845 3237029148734757083914471)
      ·
        refine ⟨4855543723102135625871707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3237029148734757083914471 4855543723102135625871707)
        ·
          refine ⟨7283315584653203438807561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4855543723102135625871707 7283315584653203438807561)
          ·
            refine ⟨5462486688489902579105671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7283315584653203438807561 5462486688489902579105671)
            ·
              refine ⟨8193730032734853868658507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5462486688489902579105671 8193730032734853868658507)
              ·
                refine ⟨12290595049102280802987761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8193730032734853868658507 12290595049102280802987761)
                ·
                  refine ⟨9217946286826710602240821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12290595049102280802987761 9217946286826710602240821)
                  ·
                    refine ⟨864182464390004118960077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9217946286826710602240821 864182464390004118960077)
                    ·
                      rfl

theorem cell22_2524484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_2524484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2524484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2524484 prefixEnd_2524484 := by exact prefixLift 2524484
  have htrace : WordTrace (prefixWord ++ tailWord_2524484) baseStart_2524484 baseEnd_2524484 := by
    simpa [prefixWord, tailWord_2524484, baseEnd_2524484] using wordTrace_append hprefix tailTrace_2524484
  have hstable : (prefixWord ++ tailWord_2524484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2524484).length < 2 ^ (prefixWord ++ tailWord_2524484).sum := by decide
  have hdescent : baseEnd_2524484 < baseStart_2524484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2524484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2524512 : List Nat := [2, 1, 1, 3, 4, 1, 2, 2, 1, 5]
def baseStart_2524512 : Nat := 118140960795 + 2524512 * 2 ^ 59
def prefixEnd_2524512 : Nat := 4983230072969 + 3 ^ 40 * 2524512 * 2
def baseEnd_2524512 : Nat := 864192049362221379259991

theorem tailTrace_2524512 : CollatzResearch.WordTrace tailWord_2524512 prefixEnd_2524512 864192049362221379259991 := by
  unfold tailWord_2524512
  simp only [CollatzResearch.WordTrace]
  refine ⟨46038258515065825584459895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61384344686754434112613193 46038258515065825584459895)
  ·
    refine ⟨69057387772598738376689843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46038258515065825584459895 69057387772598738376689843)
    ·
      refine ⟨103586081658898107565034765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69057387772598738376689843 103586081658898107565034765)
      ·
        refine ⟨38844780622086790336888037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103586081658898107565034765 38844780622086790336888037)
        ·
          refine ⟨7283396366641273188166507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38844780622086790336888037 7283396366641273188166507)
          ·
            refine ⟨10925094549961909782249761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7283396366641273188166507 10925094549961909782249761)
            ·
              refine ⟨8193820912471432336687321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10925094549961909782249761 8193820912471432336687321)
              ·
                refine ⟨6145365684353574252515491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8193820912471432336687321 6145365684353574252515491)
                ·
                  refine ⟨9218048526530361378773237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6145365684353574252515491 9218048526530361378773237)
                  ·
                    refine ⟨864192049362221379259991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9218048526530361378773237 864192049362221379259991)
                    ·
                      rfl

theorem cell22_2524512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 2, 1, 5].length) (baseStart_2524512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2524512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2524512 prefixEnd_2524512 := by exact prefixLift 2524512
  have htrace : WordTrace (prefixWord ++ tailWord_2524512) baseStart_2524512 baseEnd_2524512 := by
    simpa [prefixWord, tailWord_2524512, baseEnd_2524512] using wordTrace_append hprefix tailTrace_2524512
  have hstable : (prefixWord ++ tailWord_2524512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2524512).length < 2 ^ (prefixWord ++ tailWord_2524512).sum := by decide
  have hdescent : baseEnd_2524512 < baseStart_2524512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2524512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2524516 : List Nat := [2, 3, 1, 1, 3, 4, 2, 1, 1, 4]
def baseStart_2524516 : Nat := 118140960795 + 2524516 * 2 ^ 59
def prefixEnd_2524516 : Nat := 4983230072969 + 3 ^ 40 * 2524516 * 2
def baseEnd_2524516 : Nat := 864193418643966702159979

theorem tailTrace_2524516 : CollatzResearch.WordTrace tailWord_2524516 prefixEnd_2524516 864193418643966702159979 := by
  unfold tailWord_2524516
  simp only [CollatzResearch.WordTrace]
  refine ⟨46038331461058579926032701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61384441948078106568043601 46038331461058579926032701)
  ·
    refine ⟨17264374297896967472262263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46038331461058579926032701 17264374297896967472262263)
    ·
      refine ⟨25896561446845451208393395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17264374297896967472262263 25896561446845451208393395)
      ·
        refine ⟨38844842170268176812590093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25896561446845451208393395 38844842170268176812590093)
        ·
          refine ⟨14566815813850566304721285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38844842170268176812590093 14566815813850566304721285)
          ·
            refine ⟨2731277965096981182135241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14566815813850566304721285 2731277965096981182135241)
            ·
              refine ⟨2048458473822735886601431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2731277965096981182135241 2048458473822735886601431)
              ·
                refine ⟨3072687710734103829902147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2048458473822735886601431 3072687710734103829902147)
                ·
                  refine ⟨4609031566101155744853221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3072687710734103829902147 4609031566101155744853221)
                  ·
                    refine ⟨864193418643966702159979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4609031566101155744853221 864193418643966702159979)
                    ·
                      rfl

theorem cell22_2524516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 2, 1, 1, 4].length) (baseStart_2524516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2524516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2524516 prefixEnd_2524516 := by exact prefixLift 2524516
  have htrace : WordTrace (prefixWord ++ tailWord_2524516) baseStart_2524516 baseEnd_2524516 := by
    simpa [prefixWord, tailWord_2524516, baseEnd_2524516] using wordTrace_append hprefix tailTrace_2524516
  have hstable : (prefixWord ++ tailWord_2524516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2524516).length < 2 ^ (prefixWord ++ tailWord_2524516).sum := by decide
  have hdescent : baseEnd_2524516 < baseStart_2524516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2524516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2524529 : List Nat := [1, 2, 2, 2, 1, 2, 5, 2, 2, 3]
def baseStart_2524529 : Nat := 118140960795 + 2524529 * 2 ^ 59
def prefixEnd_2524529 : Nat := 4983230072969 + 3 ^ 40 * 2524529 * 2
def baseEnd_2524529 : Nat := 864197868809639001584939

theorem tailTrace_2524529 : CollatzResearch.WordTrace tailWord_2524529 prefixEnd_2524529 864197868809639001584939 := by
  unfold tailWord_2524529
  simp only [CollatzResearch.WordTrace]
  refine ⟨92077137071070063072288641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61384758047380042048192427 92077137071070063072288641)
  ·
    refine ⟨69057852803302547304216481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92077137071070063072288641 69057852803302547304216481)
    ·
      refine ⟨51793389602476910478162361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69057852803302547304216481 51793389602476910478162361)
      ·
        refine ⟨38845042201857682858621771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51793389602476910478162361 38845042201857682858621771)
        ·
          refine ⟨58267563302786524287932657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38845042201857682858621771 58267563302786524287932657)
          ·
            refine ⟨43700672477089893215949493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58267563302786524287932657 43700672477089893215949493)
            ·
              refine ⟨4096938044727177488995265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43700672477089893215949493 4096938044727177488995265)
              ·
                refine ⟨3072703533545383116746449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4096938044727177488995265 3072703533545383116746449)
                ·
                  refine ⟨2304527650159037337559837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3072703533545383116746449 2304527650159037337559837)
                  ·
                    refine ⟨864197868809639001584939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2304527650159037337559837 864197868809639001584939)
                    ·
                      rfl

theorem cell22_2524529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 2, 2, 3].length) (baseStart_2524529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2524529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2524529 prefixEnd_2524529 := by exact prefixLift 2524529
  have htrace : WordTrace (prefixWord ++ tailWord_2524529) baseStart_2524529 baseEnd_2524529 := by
    simpa [prefixWord, tailWord_2524529, baseEnd_2524529] using wordTrace_append hprefix tailTrace_2524529
  have hstable : (prefixWord ++ tailWord_2524529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2524529).length < 2 ^ (prefixWord ++ tailWord_2524529).sum := by decide
  have hdescent : baseEnd_2524529 < baseStart_2524529 := by decide
  rcases family_descends (prefixWord ++ tailWord_2524529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2524546 : List Nat := [3, 4, 2, 1, 1, 1, 3, 1, 1, 5]
def baseStart_2524546 : Nat := 118140960795 + 2524546 * 2 ^ 59
def prefixEnd_2524546 : Nat := 4983230072969 + 3 ^ 40 * 2524546 * 2
def baseEnd_2524546 : Nat := 864203688257056623909887

theorem tailTrace_2524546 : CollatzResearch.WordTrace tailWord_2524546 prefixEnd_2524546 864203688257056623909887 := by
  unfold tailWord_2524546
  simp only [CollatzResearch.WordTrace]
  refine ⟨23019439278002118743914373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61385171408005649983771661 23019439278002118743914373)
  ·
    refine ⟨4316144864625397264483945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23019439278002118743914373 4316144864625397264483945)
    ·
      refine ⟨3237108648469047948362959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4316144864625397264483945 3237108648469047948362959)
      ·
        refine ⟨4855662972703571922544439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3237108648469047948362959 4855662972703571922544439)
        ·
          refine ⟨7283494459055357883816659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4855662972703571922544439 7283494459055357883816659)
          ·
            refine ⟨10925241688583036825724989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7283494459055357883816659 10925241688583036825724989)
            ·
              refine ⟨4096965633218638809646871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10925241688583036825724989 4096965633218638809646871)
              ·
                refine ⟨6145448449827958214470307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4096965633218638809646871 6145448449827958214470307)
                ·
                  refine ⟨9218172674741937321705461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6145448449827958214470307 9218172674741937321705461)
                  ·
                    refine ⟨864203688257056623909887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9218172674741937321705461 864203688257056623909887)
                    ·
                      rfl

theorem cell22_2524546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_2524546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2524546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2524546 prefixEnd_2524546 := by exact prefixLift 2524546
  have htrace : WordTrace (prefixWord ++ tailWord_2524546) baseStart_2524546 baseEnd_2524546 := by
    simpa [prefixWord, tailWord_2524546, baseEnd_2524546] using wordTrace_append hprefix tailTrace_2524546
  have hstable : (prefixWord ++ tailWord_2524546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2524546).length < 2 ^ (prefixWord ++ tailWord_2524546).sum := by decide
  have hdescent : baseEnd_2524546 < baseStart_2524546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2524546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2524664 : List Nat := [2, 1, 2, 1, 1, 6, 2, 1, 1, 5]
def baseStart_2524664 : Nat := 118140960795 + 2524664 * 2 ^ 59
def prefixEnd_2524664 : Nat := 4983230072969 + 3 ^ 40 * 2524664 * 2
def baseEnd_2524664 : Nat := 864244082068543649459525

theorem tailTrace_2524664 : CollatzResearch.WordTrace tailWord_2524664 prefixEnd_2524664 864244082068543649459525 := by
  unfold tailWord_2524664
  simp only [CollatzResearch.WordTrace]
  refine ⟨46041030462790490564226523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61388040617053987418968697 46041030462790490564226523)
  ·
    refine ⟨69061545694185735846339785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46041030462790490564226523 69061545694185735846339785)
    ·
      refine ⟨51796159270639301884754839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69061545694185735846339785 51796159270639301884754839)
      ·
        refine ⟨77694238905958952827132259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51796159270639301884754839 77694238905958952827132259)
        ·
          refine ⟨116541358358938429240698389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77694238905958952827132259 116541358358938429240698389)
          ·
            refine ⟨5462876173075238870657737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 116541358358938429240698389 5462876173075238870657737)
            ·
              refine ⟨4097157129806429152993303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5462876173075238870657737 4097157129806429152993303)
              ·
                refine ⟨6145735694709643729489955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4097157129806429152993303 6145735694709643729489955)
                ·
                  refine ⟨9218603542064465594234933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6145735694709643729489955 9218603542064465594234933)
                  ·
                    refine ⟨864244082068543649459525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9218603542064465594234933 864244082068543649459525)
                    ·
                      rfl

theorem cell22_2524664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 1, 1, 5].length) (baseStart_2524664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2524664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2524664 prefixEnd_2524664 := by exact prefixLift 2524664
  have htrace : WordTrace (prefixWord ++ tailWord_2524664) baseStart_2524664 baseEnd_2524664 := by
    simpa [prefixWord, tailWord_2524664, baseEnd_2524664] using wordTrace_append hprefix tailTrace_2524664
  have hstable : (prefixWord ++ tailWord_2524664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2524664).length < 2 ^ (prefixWord ++ tailWord_2524664).sum := by decide
  have hdescent : baseEnd_2524664 < baseStart_2524664 := by decide
  rcases family_descends (prefixWord ++ tailWord_2524664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2524679 : List Nat := [1, 1, 4, 3, 2, 2, 1, 1, 1, 6]
def baseStart_2524679 : Nat := 118140960795 + 2524679 * 2 ^ 59
def prefixEnd_2524679 : Nat := 4983230072969 + 3 ^ 40 * 2524679 * 2
def baseEnd_2524679 : Nat := 864249216875088610334479

theorem tailTrace_2524679 : CollatzResearch.WordTrace tailWord_2524679 prefixEnd_2524679 864249216875088610334479 := by
  unfold tailWord_2524679
  simp only [CollatzResearch.WordTrace]
  refine ⟨92082608020526638690249091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61388405347017759126832727 92082608020526638690249091)
  ·
    refine ⟨138123912030789958035373637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92082608020526638690249091 138123912030789958035373637)
    ·
      refine ⟨25898233505773117131632557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 138123912030789958035373637 25898233505773117131632557)
      ·
        refine ⟨9711837564664918924362209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25898233505773117131632557 9711837564664918924362209)
        ·
          refine ⟨7283878173498689193271657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9711837564664918924362209 7283878173498689193271657)
          ·
            refine ⟨5462908630124016894953743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7283878173498689193271657 5462908630124016894953743)
            ·
              refine ⟨8194362945186025342430615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5462908630124016894953743 8194362945186025342430615)
              ·
                refine ⟨12291544417779038013645923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8194362945186025342430615 12291544417779038013645923)
                ·
                  refine ⟨18437316626668557020468885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12291544417779038013645923 18437316626668557020468885)
                  ·
                    refine ⟨864249216875088610334479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18437316626668557020468885 864249216875088610334479)
                    ·
                      rfl

theorem cell22_2524679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 1, 1, 6].length) (baseStart_2524679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2524679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2524679 prefixEnd_2524679 := by exact prefixLift 2524679
  have htrace : WordTrace (prefixWord ++ tailWord_2524679) baseStart_2524679 baseEnd_2524679 := by
    simpa [prefixWord, tailWord_2524679, baseEnd_2524679] using wordTrace_append hprefix tailTrace_2524679
  have hstable : (prefixWord ++ tailWord_2524679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2524679).length < 2 ^ (prefixWord ++ tailWord_2524679).sum := by decide
  have hdescent : baseEnd_2524679 < baseStart_2524679 := by decide
  rcases family_descends (prefixWord ++ tailWord_2524679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2524685 : List Nat := [1, 7, 1, 1, 2, 1, 1, 3, 1, 4]
def baseStart_2524685 : Nat := 118140960795 + 2524685 * 2 ^ 59
def prefixEnd_2524685 : Nat := 4983230072969 + 3 ^ 40 * 2524685 * 2
def baseEnd_2524685 : Nat := 864251270797706594684461

theorem tailTrace_2524685 : CollatzResearch.WordTrace tailWord_2524685 prefixEnd_2524685 864251270797706594684461 := by
  unfold tailWord_2524685
  simp only [CollatzResearch.WordTrace]
  refine ⟨92082826858504901714967509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61388551239003267809978339 92082826858504901714967509)
  ·
    refine ⟨2158191254496208633944551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 92082826858504901714967509 2158191254496208633944551)
    ·
      refine ⟨3237286881744312950916827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2158191254496208633944551 3237286881744312950916827)
      ·
        refine ⟨4855930322616469426375241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3237286881744312950916827 4855930322616469426375241)
        ·
          refine ⟨3641947741962352069781431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4855930322616469426375241 3641947741962352069781431)
          ·
            refine ⟨5462921612943528104672147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3641947741962352069781431 5462921612943528104672147)
            ·
              refine ⟨8194382419415292157008221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5462921612943528104672147 8194382419415292157008221)
              ·
                refine ⟨3072893407280734558878083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8194382419415292157008221 3072893407280734558878083)
                ·
                  refine ⟨4609340110921101838317125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3072893407280734558878083 4609340110921101838317125)
                  ·
                    refine ⟨864251270797706594684461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4609340110921101838317125 864251270797706594684461)
                    ·
                      rfl

theorem cell22_2524685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_2524685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2524685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2524685 prefixEnd_2524685 := by exact prefixLift 2524685
  have htrace : WordTrace (prefixWord ++ tailWord_2524685) baseStart_2524685 baseEnd_2524685 := by
    simpa [prefixWord, tailWord_2524685, baseEnd_2524685] using wordTrace_append hprefix tailTrace_2524685
  have hstable : (prefixWord ++ tailWord_2524685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2524685).length < 2 ^ (prefixWord ++ tailWord_2524685).sum := by decide
  have hdescent : baseEnd_2524685 < baseStart_2524685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2524685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2524769 : List Nat := [1, 2, 3, 1, 1, 3, 2, 2, 3, 4]
def baseStart_2524769 : Nat := 118140960795 + 2524769 * 2 ^ 59
def prefixEnd_2524769 : Nat := 4983230072969 + 3 ^ 40 * 2524769 * 2
def baseEnd_2524769 : Nat := 864280025714358375584203

theorem tailTrace_2524769 : CollatzResearch.WordTrace tailWord_2524769 prefixEnd_2524769 864280025714358375584203 := by
  unfold tailWord_2524769
  simp only [CollatzResearch.WordTrace]
  refine ⟨92085890590200584061025361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61390593726800389374016907 92085890590200584061025361)
  ·
    refine ⟨69064417942650438045769021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92085890590200584061025361 69064417942650438045769021)
    ·
      refine ⟨25899156728493914267163383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69064417942650438045769021 25899156728493914267163383)
      ·
        refine ⟨38848735092740871400745075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25899156728493914267163383 38848735092740871400745075)
        ·
          refine ⟨58273102639111307101117613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38848735092740871400745075 58273102639111307101117613)
          ·
            refine ⟨21852413489666740162919105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58273102639111307101117613 21852413489666740162919105)
            ·
              refine ⟨16389310117250055122189329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21852413489666740162919105 16389310117250055122189329)
              ·
                refine ⟨12291982587937541341641997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16389310117250055122189329 12291982587937541341641997)
                ·
                  refine ⟨4609493470476578003115749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12291982587937541341641997 4609493470476578003115749)
                  ·
                    refine ⟨864280025714358375584203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4609493470476578003115749 864280025714358375584203)
                    ·
                      rfl

theorem cell22_2524769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 2, 3, 4].length) (baseStart_2524769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2524769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2524769 prefixEnd_2524769 := by exact prefixLift 2524769
  have htrace : WordTrace (prefixWord ++ tailWord_2524769) baseStart_2524769 baseEnd_2524769 := by
    simpa [prefixWord, tailWord_2524769, baseEnd_2524769] using wordTrace_append hprefix tailTrace_2524769
  have hstable : (prefixWord ++ tailWord_2524769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2524769).length < 2 ^ (prefixWord ++ tailWord_2524769).sum := by decide
  have hdescent : baseEnd_2524769 < baseStart_2524769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2524769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2524773 : List Nat := [1, 3, 1, 3, 3, 3, 2, 1, 5]
def baseStart_2524773 : Nat := 118140960795 + 2524773 * 2 ^ 59
def prefixEnd_2524773 : Nat := 4983230072969 + 3 ^ 40 * 2524773 * 2
def baseEnd_2524773 : Nat := 288093798332034566161397

theorem tailTrace_2524773 : CollatzResearch.WordTrace tailWord_2524773 prefixEnd_2524773 288093798332034566161397 := by
  unfold tailWord_2524773
  simp only [CollatzResearch.WordTrace]
  refine ⟨92086036482186092744170973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61390690988124061829447315 92086036482186092744170973)
  ·
    refine ⟨34532263680819784779064115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92086036482186092744170973 34532263680819784779064115)
    ·
      refine ⟨51798395521229677168596173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34532263680819784779064115 51798395521229677168596173)
      ·
        refine ⟨19424398320461128938223565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51798395521229677168596173 19424398320461128938223565)
        ·
          refine ⟨7284149370172923351833837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19424398320461128938223565 7284149370172923351833837)
          ·
            refine ⟨2731556013814846256937689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7284149370172923351833837 2731556013814846256937689)
            ·
              refine ⟨2048667010361134692703267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2731556013814846256937689 2048667010361134692703267)
              ·
                refine ⟨3073000515541702039054901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2048667010361134692703267 3073000515541702039054901)
                ·
                  refine ⟨288093798332034566161397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3073000515541702039054901 288093798332034566161397)
                  ·
                    rfl

theorem cell22_2524773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 2, 1, 5].length) (baseStart_2524773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2524773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2524773 prefixEnd_2524773 := by exact prefixLift 2524773
  have htrace : WordTrace (prefixWord ++ tailWord_2524773) baseStart_2524773 baseEnd_2524773 := by
    simpa [prefixWord, tailWord_2524773, baseEnd_2524773] using wordTrace_append hprefix tailTrace_2524773
  have hstable : (prefixWord ++ tailWord_2524773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2524773).length < 2 ^ (prefixWord ++ tailWord_2524773).sum := by decide
  have hdescent : baseEnd_2524773 < baseStart_2524773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2524773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2524786 : List Nat := [3, 2, 1, 2, 3, 2, 1, 1, 3, 4]
def baseStart_2524786 : Nat := 118140960795 + 2524786 * 2 ^ 59
def prefixEnd_2524786 : Nat := 4983230072969 + 3 ^ 40 * 2524786 * 2
def baseEnd_2524786 : Nat := 864285845161775997909151

theorem tailTrace_2524786 : CollatzResearch.WordTrace tailWord_2524786 prefixEnd_2524786 864285845161775997909151 := by
  unfold tailWord_2524786
  simp only [CollatzResearch.WordTrace]
  refine ⟨23021627657784748991098553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61391007087425997309596141 23021627657784748991098553)
  ·
    refine ⟨17266220743338561743323915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23021627657784748991098553 17266220743338561743323915)
    ·
      refine ⟨25899331115007842614985873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17266220743338561743323915 25899331115007842614985873)
      ·
        refine ⟨19424498336255881961239405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25899331115007842614985873 19424498336255881961239405)
        ·
          refine ⟨7284186876095955735464777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19424498336255881961239405 7284186876095955735464777)
          ·
            refine ⟨5463140157071966801598583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7284186876095955735464777 5463140157071966801598583)
            ·
              refine ⟨8194710235607950202397875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5463140157071966801598583 8194710235607950202397875)
              ·
                refine ⟨12292065353411925303596813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8194710235607950202397875 12292065353411925303596813)
                ·
                  refine ⟨4609524507529471988848805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12292065353411925303596813 4609524507529471988848805)
                  ·
                    refine ⟨864285845161775997909151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4609524507529471988848805 864285845161775997909151)
                    ·
                      rfl

theorem cell22_2524786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 1, 3, 4].length) (baseStart_2524786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2524786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2524786 prefixEnd_2524786 := by exact prefixLift 2524786
  have htrace : WordTrace (prefixWord ++ tailWord_2524786) baseStart_2524786 baseEnd_2524786 := by
    simpa [prefixWord, tailWord_2524786, baseEnd_2524786] using wordTrace_append hprefix tailTrace_2524786
  have hstable : (prefixWord ++ tailWord_2524786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2524786).length < 2 ^ (prefixWord ++ tailWord_2524786).sum := by decide
  have hdescent : baseEnd_2524786 < baseStart_2524786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2524786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2524833 : List Nat := [1, 2, 3, 3, 2, 1, 2, 3, 2, 3]
def baseStart_2524833 : Nat := 118140960795 + 2524833 * 2 ^ 59
def prefixEnd_2524833 : Nat := 4983230072969 + 3 ^ 40 * 2524833 * 2
def baseEnd_2524833 : Nat := 864301934222283541984007

theorem tailTrace_2524833 : CollatzResearch.WordTrace tailWord_2524833 prefixEnd_2524833 864301934222283541984007 := by
  unfold tailWord_2524833
  simp only [CollatzResearch.WordTrace]
  refine ⟨92088224861968722991355153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61392149907979148660903435 92088224861968722991355153)
  ·
    refine ⟨69066168646476542243516365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92088224861968722991355153 69066168646476542243516365)
    ·
      refine ⟨25899813242428703341318637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69066168646476542243516365 25899813242428703341318637)
      ·
        refine ⟨9712429965910763752994489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25899813242428703341318637 9712429965910763752994489)
        ·
          refine ⟨7284322474433072814745867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9712429965910763752994489 7284322474433072814745867)
          ·
            refine ⟨10926483711649609222118801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7284322474433072814745867 10926483711649609222118801)
            ·
              refine ⟨8194862783737206916589101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10926483711649609222118801 8194862783737206916589101)
              ·
                refine ⟨3073073543901452593720913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8194862783737206916589101 3073073543901452593720913)
                ·
                  refine ⟨2304805157926089445290685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3073073543901452593720913 2304805157926089445290685)
                  ·
                    refine ⟨864301934222283541984007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2304805157926089445290685 864301934222283541984007)
                    ·
                      rfl

theorem cell22_2524833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 3, 2, 3].length) (baseStart_2524833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2524833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2524833 prefixEnd_2524833 := by exact prefixLift 2524833
  have htrace : WordTrace (prefixWord ++ tailWord_2524833) baseStart_2524833 baseEnd_2524833 := by
    simpa [prefixWord, tailWord_2524833, baseEnd_2524833] using wordTrace_append hprefix tailTrace_2524833
  have hstable : (prefixWord ++ tailWord_2524833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2524833).length < 2 ^ (prefixWord ++ tailWord_2524833).sum := by decide
  have hdescent : baseEnd_2524833 < baseStart_2524833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2524833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2524861 : List Nat := [1, 4, 1, 2, 1, 2, 1, 2, 5, 3]
def baseStart_2524861 : Nat := 118140960795 + 2524861 * 2 ^ 59
def prefixEnd_2524861 : Nat := 4983230072969 + 3 ^ 40 * 2524861 * 2
def baseEnd_2524861 : Nat := 864311519194500802283921

theorem tailTrace_2524861 : CollatzResearch.WordTrace tailWord_2524861 prefixEnd_2524861 864311519194500802283921 := by
  unfold tailWord_2524861
  simp only [CollatzResearch.WordTrace]
  refine ⟨92089246105867283773374437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61392830737244855848916291 92089246105867283773374437)
  ·
    refine ⟨17266733644850115707507707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92089246105867283773374437 17266733644850115707507707)
    ·
      refine ⟨25900100467275173561261561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17266733644850115707507707 25900100467275173561261561)
      ·
        refine ⟨19425075350456380170946171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25900100467275173561261561 19425075350456380170946171)
        ·
          refine ⟨29137613025684570256419257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19425075350456380170946171 29137613025684570256419257)
          ·
            refine ⟨21853209769263427692314443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29137613025684570256419257 21853209769263427692314443)
            ·
              refine ⟨32779814653895141538471665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21853209769263427692314443 32779814653895141538471665)
              ·
                refine ⟨24584860990421356153853749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32779814653895141538471665 24584860990421356153853749)
                ·
                  refine ⟨2304830717852002139423789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24584860990421356153853749 2304830717852002139423789)
                  ·
                    refine ⟨864311519194500802283921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2304830717852002139423789 864311519194500802283921)
                    ·
                      rfl

theorem cell22_2524861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 5, 3].length) (baseStart_2524861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2524861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2524861 prefixEnd_2524861 := by exact prefixLift 2524861
  have htrace : WordTrace (prefixWord ++ tailWord_2524861) baseStart_2524861 baseEnd_2524861 := by
    simpa [prefixWord, tailWord_2524861, baseEnd_2524861] using wordTrace_append hprefix tailTrace_2524861
  have hstable : (prefixWord ++ tailWord_2524861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2524861).length < 2 ^ (prefixWord ++ tailWord_2524861).sum := by decide
  have hdescent : baseEnd_2524861 < baseStart_2524861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2524861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
