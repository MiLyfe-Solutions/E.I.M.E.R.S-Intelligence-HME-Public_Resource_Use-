import V185TrunkScan20Chunk011

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_73168 : List Nat := [2, 1, 1, 1, 1, 2, 2, 5, 5]
def baseStart_73168 : Nat := 118140960795 + 73168 * 2 ^ 59
def prefixEnd_73168 : Nat := 4983230072969 + 3 ^ 40 * 73168 * 2
def baseEnd_73168 : Nat := 33395868914022189834233

theorem tailTrace_73168 : CollatzResearch.WordTrace tailWord_73168 prefixEnd_73168 33395868914022189834233 := by
  unfold tailWord_73168
  simp only [CollatzResearch.WordTrace]
  refine ⟨1334328099466153472322079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1779104132621537963096105 1334328099466153472322079)
  ·
    refine ⟨2001492149199230208483119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1334328099466153472322079 2001492149199230208483119)
    ·
      refine ⟨3002238223798845312724679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2001492149199230208483119 3002238223798845312724679)
      ·
        refine ⟨4503357335698267969087019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3002238223798845312724679 4503357335698267969087019)
        ·
          refine ⟨6755036003547401953630529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4503357335698267969087019 6755036003547401953630529)
          ·
            refine ⟨5066277002660551465222897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6755036003547401953630529 5066277002660551465222897)
            ·
              refine ⟨3799707751995413598917173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5066277002660551465222897 3799707751995413598917173)
              ·
                refine ⟨356222601749570024898485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3799707751995413598917173 356222601749570024898485)
                ·
                  refine ⟨33395868914022189834233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 356222601749570024898485 33395868914022189834233)
                  ·
                    rfl

theorem cell20_73168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 5, 5].length) (baseStart_73168 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_73168 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_73168 prefixEnd_73168 := by exact prefixLift 73168
  have htrace : WordTrace (prefixWord ++ tailWord_73168) baseStart_73168 baseEnd_73168 := by
    simpa [prefixWord, tailWord_73168, baseEnd_73168] using wordTrace_append hprefix tailTrace_73168
  have hstable : (prefixWord ++ tailWord_73168).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73168).length < 2 ^ (prefixWord ++ tailWord_73168).sum := by decide
  have hdescent : baseEnd_73168 < baseStart_73168 := by decide
  rcases family_descends (prefixWord ++ tailWord_73168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73181 : List Nat := [1, 4, 3, 1, 1, 3, 3, 1, 3]
def baseStart_73181 : Nat := 118140960795 + 73181 * 2 ^ 59
def prefixEnd_73181 : Nat := 4983230072969 + 3 ^ 40 * 73181 * 2
def baseEnd_73181 : Nat := 33401802468251922400847

theorem tailTrace_73181 : CollatzResearch.WordTrace tailWord_73181 prefixEnd_73181 33401802468251922400847 := by
  unfold tailWord_73181
  simp only [CollatzResearch.WordTrace]
  refine ⟨2669130347885210164867397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1779420231923473443244931 2669130347885210164867397)
  ·
    refine ⟨500461940228476905912637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2669130347885210164867397 500461940228476905912637)
    ·
      refine ⟨187673227585678839717239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 500461940228476905912637 187673227585678839717239)
      ·
        refine ⟨281509841378518259575859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187673227585678839717239 281509841378518259575859)
        ·
          refine ⟨422264762067777389363789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 281509841378518259575859 422264762067777389363789)
          ·
            refine ⟨158349285775416521011421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 422264762067777389363789 158349285775416521011421)
            ·
              refine ⟨59380982165781195379283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 158349285775416521011421 59380982165781195379283)
              ·
                refine ⟨89071473248671793068925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59380982165781195379283 89071473248671793068925)
                ·
                  refine ⟨33401802468251922400847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 89071473248671793068925 33401802468251922400847)
                  ·
                    rfl

theorem cell20_73181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 3, 1, 3].length) (baseStart_73181 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_73181 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_73181 prefixEnd_73181 := by exact prefixLift 73181
  have htrace : WordTrace (prefixWord ++ tailWord_73181) baseStart_73181 baseEnd_73181 := by
    simpa [prefixWord, tailWord_73181, baseEnd_73181] using wordTrace_append hprefix tailTrace_73181
  have hstable : (prefixWord ++ tailWord_73181).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73181).length < 2 ^ (prefixWord ++ tailWord_73181).sum := by decide
  have hdescent : baseEnd_73181 < baseStart_73181 := by decide
  rcases family_descends (prefixWord ++ tailWord_73181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73192 : List Nat := [2, 1, 4, 1, 1, 2, 1, 4, 4]
def baseStart_73192 : Nat := 118140960795 + 73192 * 2 ^ 59
def prefixEnd_73192 : Nat := 4983230072969 + 3 ^ 40 * 73192 * 2
def baseEnd_73192 : Nat := 33406823167984773034135

theorem tailTrace_73192 : CollatzResearch.WordTrace tailWord_73192 prefixEnd_73192 33406823167984773034135 := by
  unfold tailWord_73192
  simp only [CollatzResearch.WordTrace]
  refine ⟨1334765775422679521758915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1779687700563572695678553 1334765775422679521758915)
  ·
    refine ⟨2002148663134019282638373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1334765775422679521758915 2002148663134019282638373)
    ·
      refine ⟨375402874337628615494695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2002148663134019282638373 375402874337628615494695)
      ·
        refine ⟨563104311506442923242043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 375402874337628615494695 563104311506442923242043)
        ·
          refine ⟨844656467259664384863065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 563104311506442923242043 844656467259664384863065)
          ·
            refine ⟨633492350444748288647299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 844656467259664384863065 633492350444748288647299)
            ·
              refine ⟨950238525667122432970949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 633492350444748288647299 950238525667122432970949)
              ·
                refine ⟨178169723562585456182053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 950238525667122432970949 178169723562585456182053)
                ·
                  refine ⟨33406823167984773034135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 178169723562585456182053 33406823167984773034135)
                  ·
                    rfl

theorem cell20_73192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 4, 4].length) (baseStart_73192 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_73192 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_73192 prefixEnd_73192 := by exact prefixLift 73192
  have htrace : WordTrace (prefixWord ++ tailWord_73192) baseStart_73192 baseEnd_73192 := by
    simpa [prefixWord, tailWord_73192, baseEnd_73192] using wordTrace_append hprefix tailTrace_73192
  have hstable : (prefixWord ++ tailWord_73192).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73192).length < 2 ^ (prefixWord ++ tailWord_73192).sum := by decide
  have hdescent : baseEnd_73192 < baseStart_73192 := by decide
  rcases family_descends (prefixWord ++ tailWord_73192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73205 : List Nat := [1, 3, 5, 1, 1, 1, 3, 3, 2]
def baseStart_73205 : Nat := 118140960795 + 73205 * 2 ^ 59
def prefixEnd_73205 : Nat := 4983230072969 + 3 ^ 40 * 73205 * 2
def baseEnd_73205 : Nat := 33412756722214505600749

theorem tailTrace_73205 : CollatzResearch.WordTrace tailWord_73205 prefixEnd_73205 33412756722214505600749 := by
  unfold tailWord_73205
  simp only [CollatzResearch.WordTrace]
  refine ⟨2670005699798262263741069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1780003799865508175827379 2670005699798262263741069)
  ·
    refine ⟨1001252137424348348902901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2670005699798262263741069 1001252137424348348902901)
    ·
      refine ⟨93867387883532657709647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1001252137424348348902901 93867387883532657709647)
      ·
        refine ⟨140801081825298986564471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93867387883532657709647 140801081825298986564471)
        ·
          refine ⟨211201622737948479846707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140801081825298986564471 211201622737948479846707)
          ·
            refine ⟨316802434106922719770061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 211201622737948479846707 316802434106922719770061)
            ·
              refine ⟨118800912790096019913773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 316802434106922719770061 118800912790096019913773)
              ·
                refine ⟨44550342296286007467665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 118800912790096019913773 44550342296286007467665)
                ·
                  refine ⟨33412756722214505600749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44550342296286007467665 33412756722214505600749)
                  ·
                    rfl

theorem cell20_73205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 3, 2].length) (baseStart_73205 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_73205 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_73205 prefixEnd_73205 := by exact prefixLift 73205
  have htrace : WordTrace (prefixWord ++ tailWord_73205) baseStart_73205 baseEnd_73205 := by
    simpa [prefixWord, tailWord_73205, baseEnd_73205] using wordTrace_append hprefix tailTrace_73205
  have hstable : (prefixWord ++ tailWord_73205).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73205).length < 2 ^ (prefixWord ++ tailWord_73205).sum := by decide
  have hdescent : baseEnd_73205 < baseStart_73205 := by decide
  rcases family_descends (prefixWord ++ tailWord_73205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73223 : List Nat := [1, 1, 4, 3, 2, 1, 2, 1, 5]
def baseStart_73223 : Nat := 118140960795 + 73223 * 2 ^ 59
def prefixEnd_73223 : Nat := 4983230072969 + 3 ^ 40 * 73223 * 2
def baseEnd_73223 : Nat := 33420972412686443000675

theorem tailTrace_73223 : CollatzResearch.WordTrace tailWord_73223 prefixEnd_73223 33420972412686443000675 := by
  unfold tailWord_73223
  simp only [CollatzResearch.WordTrace]
  refine ⟨2670662213733051337896323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1780441475822034225264215 2670662213733051337896323)
  ·
    refine ⟨4005993320599577006844485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2670662213733051337896323 4005993320599577006844485)
    ·
      refine ⟨751123747612420688783341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4005993320599577006844485 751123747612420688783341)
      ·
        refine ⟨281671405354657758293753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 751123747612420688783341 281671405354657758293753)
        ·
          refine ⟨211253554015993318720315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 281671405354657758293753 211253554015993318720315)
          ·
            refine ⟨316880331023989978080473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 211253554015993318720315 316880331023989978080473)
            ·
              refine ⟨237660248267992483560355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 316880331023989978080473 237660248267992483560355)
              ·
                refine ⟨356490372401988725340533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 237660248267992483560355 356490372401988725340533)
                ·
                  refine ⟨33420972412686443000675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 356490372401988725340533 33420972412686443000675)
                  ·
                    rfl

theorem cell20_73223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 1, 5].length) (baseStart_73223 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_73223 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_73223 prefixEnd_73223 := by exact prefixLift 73223
  have htrace : WordTrace (prefixWord ++ tailWord_73223) baseStart_73223 baseEnd_73223 := by
    simpa [prefixWord, tailWord_73223, baseEnd_73223] using wordTrace_append hprefix tailTrace_73223
  have hstable : (prefixWord ++ tailWord_73223).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73223).length < 2 ^ (prefixWord ++ tailWord_73223).sum := by decide
  have hdescent : baseEnd_73223 < baseStart_73223 := by decide
  rcases family_descends (prefixWord ++ tailWord_73223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73237 : List Nat := [1, 3, 2, 1, 3, 2, 1, 7]
def baseStart_73237 : Nat := 118140960795 + 73237 * 2 ^ 59
def prefixEnd_73237 : Nat := 4983230072969 + 3 ^ 40 * 73237 * 2
def baseEnd_73237 : Nat := 11142454131388205511317

theorem tailTrace_73237 : CollatzResearch.WordTrace tailWord_73237 prefixEnd_73237 11142454131388205511317 := by
  unfold tailWord_73237
  simp only [CollatzResearch.WordTrace]
  refine ⟨2671172835682331728905965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1780781890454887819270643 2671172835682331728905965)
  ·
    refine ⟨1001689813380874398339737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2671172835682331728905965 1001689813380874398339737)
    ·
      refine ⟨751267360035655798754803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1001689813380874398339737 751267360035655798754803)
      ·
        refine ⟨1126901040053483698132205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 751267360035655798754803 1126901040053483698132205)
        ·
          refine ⟨422587890020056386799577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1126901040053483698132205 422587890020056386799577)
          ·
            refine ⟨316940917515042290099683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 422587890020056386799577 316940917515042290099683)
            ·
              refine ⟨475411376272563435149525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 316940917515042290099683 475411376272563435149525)
              ·
                refine ⟨11142454131388205511317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 475411376272563435149525 11142454131388205511317)
                ·
                  rfl

theorem cell20_73237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 7].length) (baseStart_73237 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_73237 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_73237 prefixEnd_73237 := by exact prefixLift 73237
  have htrace : WordTrace (prefixWord ++ tailWord_73237) baseStart_73237 baseEnd_73237 := by
    simpa [prefixWord, tailWord_73237, baseEnd_73237] using wordTrace_append hprefix tailTrace_73237
  have hstable : (prefixWord ++ tailWord_73237).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73237).length < 2 ^ (prefixWord ++ tailWord_73237).sum := by decide
  have hdescent : baseEnd_73237 < baseStart_73237 := by decide
  rcases family_descends (prefixWord ++ tailWord_73237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73240 : List Nat := [2, 1, 2, 3, 4, 1, 1, 3, 3]
def baseStart_73240 : Nat := 118140960795 + 73240 * 2 ^ 59
def prefixEnd_73240 : Nat := 4983230072969 + 3 ^ 40 * 73240 * 2
def baseEnd_73240 : Nat := 33428731675909939433939

theorem tailTrace_73240 : CollatzResearch.WordTrace tailWord_73240 prefixEnd_73240 33428731675909939433939 := by
  unfold tailWord_73240
  simp only [CollatzResearch.WordTrace]
  refine ⟨1335641127335731620632587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1780854836447642160843449 1335641127335731620632587)
  ·
    refine ⟨2003461691003597430948881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1335641127335731620632587 2003461691003597430948881)
    ·
      refine ⟨1502596268252698073211661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2003461691003597430948881 1502596268252698073211661)
      ·
        refine ⟨563473600594761777454373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1502596268252698073211661 563473600594761777454373)
        ·
          refine ⟨105651300111517833272695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 563473600594761777454373 105651300111517833272695)
          ·
            refine ⟨158476950167276749909043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105651300111517833272695 158476950167276749909043)
            ·
              refine ⟨237715425250915124863565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 158476950167276749909043 237715425250915124863565)
              ·
                refine ⟨89143284469093171823837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 237715425250915124863565 89143284469093171823837)
                ·
                  refine ⟨33428731675909939433939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 89143284469093171823837 33428731675909939433939)
                  ·
                    rfl

theorem cell20_73240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 3, 3].length) (baseStart_73240 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_73240 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_73240 prefixEnd_73240 := by exact prefixLift 73240
  have htrace : WordTrace (prefixWord ++ tailWord_73240) baseStart_73240 baseEnd_73240 := by
    simpa [prefixWord, tailWord_73240, baseEnd_73240] using wordTrace_append hprefix tailTrace_73240
  have hstable : (prefixWord ++ tailWord_73240).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73240).length < 2 ^ (prefixWord ++ tailWord_73240).sum := by decide
  have hdescent : baseEnd_73240 < baseStart_73240 := by decide
  rcases family_descends (prefixWord ++ tailWord_73240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73285 : List Nat := [1, 3, 1, 1, 1, 4, 3, 4, 2]
def baseStart_73285 : Nat := 118140960795 + 73285 * 2 ^ 59
def prefixEnd_73285 : Nat := 4983230072969 + 3 ^ 40 * 73285 * 2
def baseEnd_73285 : Nat := 33449270902089782933755

theorem tailTrace_73285 : CollatzResearch.WordTrace tailWord_73285 prefixEnd_73285 33449270902089782933755 := by
  unfold tailWord_73285
  simp only [CollatzResearch.WordTrace]
  refine ⟨2672923539508435926653309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1781949026338957284435539 2672923539508435926653309)
  ·
    refine ⟨1002346327315663472494991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2672923539508435926653309 1002346327315663472494991)
    ·
      refine ⟨1503519490973495208742487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1002346327315663472494991 1503519490973495208742487)
      ·
        refine ⟨2255279236460242813113731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1503519490973495208742487 2255279236460242813113731)
        ·
          refine ⟨3382918854690364219670597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2255279236460242813113731 3382918854690364219670597)
          ·
            refine ⟨634297285254443291188237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3382918854690364219670597 634297285254443291188237)
            ·
              refine ⟨237861481970416234195589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 634297285254443291188237 237861481970416234195589)
              ·
                refine ⟨44599027869453043911673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 237861481970416234195589 44599027869453043911673)
                ·
                  refine ⟨33449270902089782933755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44599027869453043911673 33449270902089782933755)
                  ·
                    rfl

theorem cell20_73285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 4, 2].length) (baseStart_73285 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_73285 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_73285 prefixEnd_73285 := by exact prefixLift 73285
  have htrace : WordTrace (prefixWord ++ tailWord_73285) baseStart_73285 baseEnd_73285 := by
    simpa [prefixWord, tailWord_73285, baseEnd_73285] using wordTrace_append hprefix tailTrace_73285
  have hstable : (prefixWord ++ tailWord_73285).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73285).length < 2 ^ (prefixWord ++ tailWord_73285).sum := by decide
  have hdescent : baseEnd_73285 < baseStart_73285 := by decide
  rcases family_descends (prefixWord ++ tailWord_73285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73289 : List Nat := [1, 2, 1, 1, 2, 2, 1, 2, 8]
def baseStart_73289 : Nat := 118140960795 + 73289 * 2 ^ 59
def prefixEnd_73289 : Nat := 4983230072969 + 3 ^ 40 * 73289 * 2
def baseEnd_73289 : Nat := 33451096611083546800405

theorem tailTrace_73289 : CollatzResearch.WordTrace tailWord_73289 prefixEnd_73289 33451096611083546800405 := by
  unfold tailWord_73289
  simp only [CollatzResearch.WordTrace]
  refine ⟨2673069431493944609798921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1782046287662629739865947 2673069431493944609798921)
  ·
    refine ⟨2004802073620458457349191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2673069431493944609798921 2004802073620458457349191)
    ·
      refine ⟨3007203110430687686023787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2004802073620458457349191 3007203110430687686023787)
      ·
        refine ⟨4510804665646031529035681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3007203110430687686023787 4510804665646031529035681)
        ·
          refine ⟨3383103499234523646776761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4510804665646031529035681 3383103499234523646776761)
          ·
            refine ⟨2537327624425892735082571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3383103499234523646776761 2537327624425892735082571)
            ·
              refine ⟨3805991436638839102623857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2537327624425892735082571 3805991436638839102623857)
              ·
                refine ⟨2854493577479129326967893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3805991436638839102623857 2854493577479129326967893)
                ·
                  refine ⟨33451096611083546800405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2854493577479129326967893 33451096611083546800405)
                  ·
                    rfl

theorem cell20_73289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 8].length) (baseStart_73289 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_73289 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_73289 prefixEnd_73289 := by exact prefixLift 73289
  have htrace : WordTrace (prefixWord ++ tailWord_73289) baseStart_73289 baseEnd_73289 := by
    simpa [prefixWord, tailWord_73289, baseEnd_73289] using wordTrace_append hprefix tailTrace_73289
  have hstable : (prefixWord ++ tailWord_73289).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73289).length < 2 ^ (prefixWord ++ tailWord_73289).sum := by decide
  have hdescent : baseEnd_73289 < baseStart_73289 := by decide
  rcases family_descends (prefixWord ++ tailWord_73289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73292 : List Nat := [2, 2, 1, 3, 1, 5, 1, 5]
def baseStart_73292 : Nat := 118140960795 + 73292 * 2 ^ 59
def prefixEnd_73292 : Nat := 4983230072969 + 3 ^ 40 * 73292 * 2
def baseEnd_73292 : Nat := 11150821964276289900131

theorem tailTrace_73292 : CollatzResearch.WordTrace tailWord_73292 prefixEnd_73292 11150821964276289900131 := by
  unfold tailWord_73292
  simp only [CollatzResearch.WordTrace]
  refine ⟨1336589425241538061079065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1782119233655384081438753 1336589425241538061079065)
  ·
    refine ⟨1002442068931153545809299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1336589425241538061079065 1002442068931153545809299)
    ·
      refine ⟨1503663103396730318713949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1002442068931153545809299 1503663103396730318713949)
      ·
        refine ⟨563873663773773869517731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1503663103396730318713949 563873663773773869517731)
        ·
          refine ⟨845810495660660804276597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 563873663773773869517731 845810495660660804276597)
          ·
            refine ⟨79294733968186950400931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 845810495660660804276597 79294733968186950400931)
            ·
              refine ⟨118942100952280425601397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79294733968186950400931 118942100952280425601397)
              ·
                refine ⟨11150821964276289900131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 118942100952280425601397 11150821964276289900131)
                ·
                  rfl

theorem cell20_73292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 5].length) (baseStart_73292 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_73292 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_73292 prefixEnd_73292 := by exact prefixLift 73292
  have htrace : WordTrace (prefixWord ++ tailWord_73292) baseStart_73292 baseEnd_73292 := by
    simpa [prefixWord, tailWord_73292, baseEnd_73292] using wordTrace_append hprefix tailTrace_73292
  have hstable : (prefixWord ++ tailWord_73292).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73292).length < 2 ^ (prefixWord ++ tailWord_73292).sum := by decide
  have hdescent : baseEnd_73292 < baseStart_73292 := by decide
  rcases family_descends (prefixWord ++ tailWord_73292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73327 : List Nat := [1, 1, 2, 1, 3, 2, 1, 1, 8]
def baseStart_73327 : Nat := 118140960795 + 73327 * 2 ^ 59
def prefixEnd_73327 : Nat := 4983230072969 + 3 ^ 40 * 73327 * 2
def baseEnd_73327 : Nat := 33468440846524303533583

theorem tailTrace_73327 : CollatzResearch.WordTrace tailWord_73327 prefixEnd_73327 33468440846524303533583 := by
  unfold tailWord_73327
  simp only [CollatzResearch.WordTrace]
  refine ⟨2674455405356277099682235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1782970270237518066454823 2674455405356277099682235)
  ·
    refine ⟨4011683108034415649523353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2674455405356277099682235 4011683108034415649523353)
    ·
      refine ⟨3008762331025811737142515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4011683108034415649523353 3008762331025811737142515)
      ·
        refine ⟨4513143496538717605713773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3008762331025811737142515 4513143496538717605713773)
        ·
          refine ⟨1692428811202019102142665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4513143496538717605713773 1692428811202019102142665)
          ·
            refine ⟨1269321608401514326606999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1692428811202019102142665 1269321608401514326606999)
            ·
              refine ⟨1903982412602271489910499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1269321608401514326606999 1903982412602271489910499)
              ·
                refine ⟨2855973618903407234865749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1903982412602271489910499 2855973618903407234865749)
                ·
                  refine ⟨33468440846524303533583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2855973618903407234865749 33468440846524303533583)
                  ·
                    rfl

theorem cell20_73327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 8].length) (baseStart_73327 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_73327 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_73327 prefixEnd_73327 := by exact prefixLift 73327
  have htrace : WordTrace (prefixWord ++ tailWord_73327) baseStart_73327 baseEnd_73327 := by
    simpa [prefixWord, tailWord_73327, baseEnd_73327] using wordTrace_append hprefix tailTrace_73327
  have hstable : (prefixWord ++ tailWord_73327).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73327).length < 2 ^ (prefixWord ++ tailWord_73327).sum := by decide
  have hdescent : baseEnd_73327 < baseStart_73327 := by decide
  rcases family_descends (prefixWord ++ tailWord_73327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73333 : List Nat := [1, 3, 4, 2, 1, 3, 1, 2, 3]
def baseStart_73333 : Nat := 118140960795 + 73333 * 2 ^ 59
def prefixEnd_73333 : Nat := 4983230072969 + 3 ^ 40 * 73333 * 2
def baseEnd_73333 : Nat := 33471179410014949333559

theorem tailTrace_73333 : CollatzResearch.WordTrace tailWord_73333 prefixEnd_73333 33471179410014949333559 := by
  unfold tailWord_73333
  simp only [CollatzResearch.WordTrace]
  refine ⟨2674674243334540124400653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1783116162223026749600435 2674674243334540124400653)
  ·
    refine ⟨1003002841250452546650245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2674674243334540124400653 1003002841250452546650245)
    ·
      refine ⟨188063032734459852496921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1003002841250452546650245 188063032734459852496921)
      ·
        refine ⟨141047274550844889372691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188063032734459852496921 141047274550844889372691)
        ·
          refine ⟨211570911826267334059037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141047274550844889372691 211570911826267334059037)
          ·
            refine ⟨79339091934850250272139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 211570911826267334059037 79339091934850250272139)
            ·
              refine ⟨119008637902275375408209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79339091934850250272139 119008637902275375408209)
              ·
                refine ⟨89256478426706531556157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 119008637902275375408209 89256478426706531556157)
                ·
                  refine ⟨33471179410014949333559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 89256478426706531556157 33471179410014949333559)
                  ·
                    rfl

theorem cell20_73333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 2, 3].length) (baseStart_73333 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_73333 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_73333 prefixEnd_73333 := by exact prefixLift 73333
  have htrace : WordTrace (prefixWord ++ tailWord_73333) baseStart_73333 baseEnd_73333 := by
    simpa [prefixWord, tailWord_73333, baseEnd_73333] using wordTrace_append hprefix tailTrace_73333
  have hstable : (prefixWord ++ tailWord_73333).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73333).length < 2 ^ (prefixWord ++ tailWord_73333).sum := by decide
  have hdescent : baseEnd_73333 < baseStart_73333 := by decide
  rcases family_descends (prefixWord ++ tailWord_73333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73344 : List Nat := [2, 1, 1, 2, 1, 4, 4, 1, 4]
def baseStart_73344 : Nat := 118140960795 + 73344 * 2 ^ 59
def prefixEnd_73344 : Nat := 4983230072969 + 3 ^ 40 * 73344 * 2
def baseEnd_73344 : Nat := 33476200109747799966847

theorem tailTrace_73344 : CollatzResearch.WordTrace tailWord_73344 prefixEnd_73344 33476200109747799966847 := by
  unfold tailWord_73344
  simp only [CollatzResearch.WordTrace]
  refine ⟨1337537723147344501525543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1783383630863126002034057 1337537723147344501525543)
  ·
    refine ⟨2006306584721016752288315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1337537723147344501525543 2006306584721016752288315)
    ·
      refine ⟨3009459877081525128432473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2006306584721016752288315 3009459877081525128432473)
      ·
        refine ⟨2257094907811143846324355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3009459877081525128432473 2257094907811143846324355)
        ·
          refine ⟨3385642361716715769486533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2257094907811143846324355 3385642361716715769486533)
          ·
            refine ⟨634807942821884206778725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3385642361716715769486533 634807942821884206778725)
            ·
              refine ⟨119026489279103288771011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 634807942821884206778725 119026489279103288771011)
              ·
                refine ⟨178539733918654933156517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119026489279103288771011 178539733918654933156517)
                ·
                  refine ⟨33476200109747799966847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 178539733918654933156517 33476200109747799966847)
                  ·
                    rfl

theorem cell20_73344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 1, 4].length) (baseStart_73344 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_73344 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_73344 prefixEnd_73344 := by exact prefixLift 73344
  have htrace : WordTrace (prefixWord ++ tailWord_73344) baseStart_73344 baseEnd_73344 := by
    simpa [prefixWord, tailWord_73344, baseEnd_73344] using wordTrace_append hprefix tailTrace_73344
  have hstable : (prefixWord ++ tailWord_73344).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73344).length < 2 ^ (prefixWord ++ tailWord_73344).sum := by decide
  have hdescent : baseEnd_73344 < baseStart_73344 := by decide
  rcases family_descends (prefixWord ++ tailWord_73344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73364 : List Nat := [2, 4, 2, 2, 2, 2, 2, 4]
def baseStart_73364 : Nat := 118140960795 + 73364 * 2 ^ 59
def prefixEnd_73364 : Nat := 4983230072969 + 3 ^ 40 * 73364 * 2
def baseEnd_73364 : Nat := 11161776218238873100033

theorem tailTrace_73364 : CollatzResearch.WordTrace tailWord_73364 prefixEnd_73364 11161776218238873100033 := by
  unfold tailWord_73364
  simp only [CollatzResearch.WordTrace]
  refine ⟨1337902453111116209389573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1783869937481488279186097 1337902453111116209389573)
  ·
    refine ⟨250856709958334289260545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1337902453111116209389573 250856709958334289260545)
    ·
      refine ⟨188142532468750716945409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 250856709958334289260545 188142532468750716945409)
      ·
        refine ⟨141106899351563037709057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188142532468750716945409 141106899351563037709057)
        ·
          refine ⟨105830174513672278281793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141106899351563037709057 105830174513672278281793)
          ·
            refine ⟨79372630885254208711345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105830174513672278281793 79372630885254208711345)
            ·
              refine ⟨59529473163940656533509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79372630885254208711345 59529473163940656533509)
              ·
                refine ⟨11161776218238873100033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59529473163940656533509 11161776218238873100033)
                ·
                  rfl

theorem cell20_73364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 2, 4].length) (baseStart_73364 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_73364 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_73364 prefixEnd_73364 := by exact prefixLift 73364
  have htrace : WordTrace (prefixWord ++ tailWord_73364) baseStart_73364 baseEnd_73364 := by
    simpa [prefixWord, tailWord_73364, baseEnd_73364] using wordTrace_append hprefix tailTrace_73364
  have hstable : (prefixWord ++ tailWord_73364).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73364).length < 2 ^ (prefixWord ++ tailWord_73364).sum := by decide
  have hdescent : baseEnd_73364 < baseStart_73364 := by decide
  rcases family_descends (prefixWord ++ tailWord_73364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73368 : List Nat := [2, 1, 2, 4, 1, 2, 4, 4]
def baseStart_73368 : Nat := 118140960795 + 73368 * 2 ^ 59
def prefixEnd_73368 : Nat := 4983230072969 + 3 ^ 40 * 73368 * 2
def baseEnd_73368 : Nat := 11162384787903461055583

theorem tailTrace_73368 : CollatzResearch.WordTrace tailWord_73368 prefixEnd_73368 11162384787903461055583 := by
  unfold tailWord_73368
  simp only [CollatzResearch.WordTrace]
  refine ⟨1337975399103870550962379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1783967198805160734616505 1337975399103870550962379)
  ·
    refine ⟨2006963098655805826443569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1337975399103870550962379 2006963098655805826443569)
    ·
      refine ⟨1505222323991854369832677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2006963098655805826443569 1505222323991854369832677)
      ·
        refine ⟨282229185748472694343627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1505222323991854369832677 282229185748472694343627)
        ·
          refine ⟨423343778622709041515441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 282229185748472694343627 423343778622709041515441)
          ·
            refine ⟨317507833967031781136581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 423343778622709041515441 317507833967031781136581)
            ·
              refine ⟨59532718868818458963109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 317507833967031781136581 59532718868818458963109)
              ·
                refine ⟨11162384787903461055583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59532718868818458963109 11162384787903461055583)
                ·
                  rfl

theorem cell20_73368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 4, 4].length) (baseStart_73368 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_73368 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_73368 prefixEnd_73368 := by exact prefixLift 73368
  have htrace : WordTrace (prefixWord ++ tailWord_73368) baseStart_73368 baseEnd_73368 := by
    simpa [prefixWord, tailWord_73368, baseEnd_73368] using wordTrace_append hprefix tailTrace_73368
  have hstable : (prefixWord ++ tailWord_73368).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73368).length < 2 ^ (prefixWord ++ tailWord_73368).sum := by decide
  have hdescent : baseEnd_73368 < baseStart_73368 := by decide
  rcases family_descends (prefixWord ++ tailWord_73368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73399 : List Nat := [1, 1, 3, 1, 5, 3, 1, 1, 4]
def baseStart_73399 : Nat := 118140960795 + 73399 * 2 ^ 59
def prefixEnd_73399 : Nat := 4983230072969 + 3 ^ 40 * 73399 * 2
def baseEnd_73399 : Nat := 33501303608412053133289

theorem tailTrace_73399 : CollatzResearch.WordTrace tailWord_73399 prefixEnd_73399 33501303608412053133289 := by
  unfold tailWord_73399
  simp only [CollatzResearch.WordTrace]
  refine ⟨2677081461095433396303251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1784720974063622264202167 2677081461095433396303251)
  ·
    refine ⟨4015622191643150094454877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2677081461095433396303251 4015622191643150094454877)
    ·
      refine ⟨1505858321866181285420579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4015622191643150094454877 1505858321866181285420579)
      ·
        refine ⟨2258787482799271928130869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1505858321866181285420579 2258787482799271928130869)
        ·
          refine ⟨211761326512431743262269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2258787482799271928130869 211761326512431743262269)
          ·
            refine ⟨79410497442161903723351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 211761326512431743262269 79410497442161903723351)
            ·
              refine ⟨119115746163242855585027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79410497442161903723351 119115746163242855585027)
              ·
                refine ⟨178673619244864283377541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119115746163242855585027 178673619244864283377541)
                ·
                  refine ⟨33501303608412053133289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 178673619244864283377541 33501303608412053133289)
                  ·
                    rfl

theorem cell20_73399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 1, 4].length) (baseStart_73399 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_73399 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_73399 prefixEnd_73399 := by exact prefixLift 73399
  have htrace : WordTrace (prefixWord ++ tailWord_73399) baseStart_73399 baseEnd_73399 := by
    simpa [prefixWord, tailWord_73399, baseEnd_73399] using wordTrace_append hprefix tailTrace_73399
  have hstable : (prefixWord ++ tailWord_73399).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73399).length < 2 ^ (prefixWord ++ tailWord_73399).sum := by decide
  have hdescent : baseEnd_73399 < baseStart_73399 := by decide
  rcases family_descends (prefixWord ++ tailWord_73399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73406 : List Nat := [4, 2, 1, 1, 2, 3, 2, 5]
def baseStart_73406 : Nat := 118140960795 + 73406 * 2 ^ 59
def prefixEnd_73406 : Nat := 4983230072969 + 3 ^ 40 * 73406 * 2
def baseEnd_73406 : Nat := 11168166199717046633309

theorem tailTrace_73406 : CollatzResearch.WordTrace tailWord_73406 prefixEnd_73406 11168166199717046633309 := by
  unfold tailWord_73406
  simp only [CollatzResearch.WordTrace]
  refine ⟨334667096508759198976009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1784891181380049061205381 334667096508759198976009)
  ·
    refine ⟨251000322381569399232007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 334667096508759198976009 251000322381569399232007)
    ·
      refine ⟨376500483572354098848011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251000322381569399232007 376500483572354098848011)
      ·
        refine ⟨564750725358531148272017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 376500483572354098848011 564750725358531148272017)
        ·
          refine ⟨423563044018898361204013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 564750725358531148272017 423563044018898361204013)
          ·
            refine ⟨158836141507086885451505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 423563044018898361204013 158836141507086885451505)
            ·
              refine ⟨119127106130315164088629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 158836141507086885451505 119127106130315164088629)
              ·
                refine ⟨11168166199717046633309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 119127106130315164088629 11168166199717046633309)
                ·
                  rfl

theorem cell20_73406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 5].length) (baseStart_73406 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_73406 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_73406 prefixEnd_73406 := by exact prefixLift 73406
  have htrace : WordTrace (prefixWord ++ tailWord_73406) baseStart_73406 baseEnd_73406 := by
    simpa [prefixWord, tailWord_73406, baseEnd_73406] using wordTrace_append hprefix tailTrace_73406
  have hstable : (prefixWord ++ tailWord_73406).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73406).length < 2 ^ (prefixWord ++ tailWord_73406).sum := by decide
  have hdescent : baseEnd_73406 < baseStart_73406 := by decide
  rcases family_descends (prefixWord ++ tailWord_73406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73447 : List Nat := [1, 1, 5, 4, 1, 1, 2, 2, 3]
def baseStart_73447 : Nat := 118140960795 + 73447 * 2 ^ 59
def prefixEnd_73447 : Nat := 4983230072969 + 3 ^ 40 * 73447 * 2
def baseEnd_73447 : Nat := 33523212116337219533093

theorem tailTrace_73447 : CollatzResearch.WordTrace tailWord_73447 prefixEnd_73447 33523212116337219533093 := by
  unfold tailWord_73447
  simp only [CollatzResearch.WordTrace]
  refine ⟨2678832164921537594050595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1785888109947691729367063 2678832164921537594050595)
  ·
    refine ⟨4018248247382306391075893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2678832164921537594050595 4018248247382306391075893)
    ·
      refine ⟨376710773192091224163365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4018248247382306391075893 376710773192091224163365)
      ·
        refine ⟨70633269973517104530631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 376710773192091224163365 70633269973517104530631)
        ·
          refine ⟨105949904960275656795947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70633269973517104530631 105949904960275656795947)
          ·
            refine ⟨158924857440413485193921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105949904960275656795947 158924857440413485193921)
            ·
              refine ⟨119193643080310113895441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 158924857440413485193921 119193643080310113895441)
              ·
                refine ⟨89395232310232585421581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 119193643080310113895441 89395232310232585421581)
                ·
                  refine ⟨33523212116337219533093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 89395232310232585421581 33523212116337219533093)
                  ·
                    rfl

theorem cell20_73447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 2, 3].length) (baseStart_73447 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_73447 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_73447 prefixEnd_73447 := by exact prefixLift 73447
  have htrace : WordTrace (prefixWord ++ tailWord_73447) baseStart_73447 baseEnd_73447 := by
    simpa [prefixWord, tailWord_73447, baseEnd_73447] using wordTrace_append hprefix tailTrace_73447
  have hstable : (prefixWord ++ tailWord_73447).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73447).length < 2 ^ (prefixWord ++ tailWord_73447).sum := by decide
  have hdescent : baseEnd_73447 < baseStart_73447 := by decide
  rcases family_descends (prefixWord ++ tailWord_73447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73458 : List Nat := [3, 2, 1, 3, 1, 1, 2, 3, 4]
def baseStart_73458 : Nat := 118140960795 + 73458 * 2 ^ 59
def prefixEnd_73458 : Nat := 4983230072969 + 3 ^ 40 * 73458 * 2
def baseEnd_73458 : Nat := 33528232816070070166381

theorem tailTrace_73458 : CollatzResearch.WordTrace tailWord_73458 prefixEnd_73458 33528232816070070166381 := by
  unfold tailWord_73458
  simp only [CollatzResearch.WordTrace]
  refine ⟨669808341970421618175257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1786155578587790981800685 669808341970421618175257)
  ·
    refine ⟨502356256477816213631443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 669808341970421618175257 502356256477816213631443)
    ·
      refine ⟨753534384716724320447165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 502356256477816213631443 753534384716724320447165)
      ·
        refine ⟨282575394268771620167687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 753534384716724320447165 282575394268771620167687)
        ·
          refine ⟨423863091403157430251531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 282575394268771620167687 423863091403157430251531)
          ·
            refine ⟨635794637104736145377297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 423863091403157430251531 635794637104736145377297)
            ·
              refine ⟨476845977828552109032973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 635794637104736145377297 476845977828552109032973)
              ·
                refine ⟨178817241685707040887365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 476845977828552109032973 178817241685707040887365)
                ·
                  refine ⟨33528232816070070166381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 178817241685707040887365 33528232816070070166381)
                  ·
                    rfl

theorem cell20_73458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_73458 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_73458 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_73458 prefixEnd_73458 := by exact prefixLift 73458
  have htrace : WordTrace (prefixWord ++ tailWord_73458) baseStart_73458 baseEnd_73458 := by
    simpa [prefixWord, tailWord_73458, baseEnd_73458] using wordTrace_append hprefix tailTrace_73458
  have hstable : (prefixWord ++ tailWord_73458).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73458).length < 2 ^ (prefixWord ++ tailWord_73458).sum := by decide
  have hdescent : baseEnd_73458 < baseStart_73458 := by decide
  rcases family_descends (prefixWord ++ tailWord_73458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73482 : List Nat := [3, 1, 2, 2, 1, 4, 3, 4]
def baseStart_73482 : Nat := 118140960795 + 73482 * 2 ^ 59
def prefixEnd_73482 : Nat := 4983230072969 + 3 ^ 40 * 73482 * 2
def baseEnd_73482 : Nat := 11179729023344217788761

theorem tailTrace_73482 : CollatzResearch.WordTrace tailWord_73482 prefixEnd_73482 11179729023344217788761 := by
  unfold tailWord_73482
  simp only [CollatzResearch.WordTrace]
  refine ⟨670027179948684642893675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1786739146529825714383133 670027179948684642893675)
  ·
    refine ⟨1005040769923026964340513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 670027179948684642893675 1005040769923026964340513)
    ·
      refine ⟨753780577442270223255385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1005040769923026964340513 753780577442270223255385)
      ·
        refine ⟨565335433081702667441539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 753780577442270223255385 565335433081702667441539)
        ·
          refine ⟨848003149622554001162309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 565335433081702667441539 848003149622554001162309)
          ·
            refine ⟨159000590554228875217933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 848003149622554001162309 159000590554228875217933)
            ·
              refine ⟨59625221457835828206725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 159000590554228875217933 59625221457835828206725)
              ·
                refine ⟨11179729023344217788761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59625221457835828206725 11179729023344217788761)
                ·
                  rfl

theorem cell20_73482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 3, 4].length) (baseStart_73482 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_73482 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_73482 prefixEnd_73482 := by exact prefixLift 73482
  have htrace : WordTrace (prefixWord ++ tailWord_73482) baseStart_73482 baseEnd_73482 := by
    simpa [prefixWord, tailWord_73482, baseEnd_73482] using wordTrace_append hprefix tailTrace_73482
  have hstable : (prefixWord ++ tailWord_73482).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73482).length < 2 ^ (prefixWord ++ tailWord_73482).sum := by decide
  have hdescent : baseEnd_73482 < baseStart_73482 := by decide
  rcases family_descends (prefixWord ++ tailWord_73482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73568 : List Nat := [2, 1, 1, 3, 3, 3, 3, 2, 2]
def baseStart_73568 : Nat := 118140960795 + 73568 * 2 ^ 59
def prefixEnd_73568 : Nat := 4983230072969 + 3 ^ 40 * 73568 * 2
def baseEnd_73568 : Nat := 33578439813398576499265

theorem tailTrace_73568 : CollatzResearch.WordTrace tailWord_73568 prefixEnd_73568 33578439813398576499265 := by
  unfold tailWord_73568
  simp only [CollatzResearch.WordTrace]
  refine ⟨1341622698741587629602679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1788830264988783506136905 1341622698741587629602679)
  ·
    refine ⟨2012434048112381444404019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1341622698741587629602679 2012434048112381444404019)
    ·
      refine ⟨3018651072168572166606029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2012434048112381444404019 3018651072168572166606029)
      ·
        refine ⟨1131994152063214562477261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3018651072168572166606029 1131994152063214562477261)
        ·
          refine ⟨424497807023705460928973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1131994152063214562477261 424497807023705460928973)
          ·
            refine ⟨159186677633889547848365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 424497807023705460928973 159186677633889547848365)
            ·
              refine ⟨59695004112708580443137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 159186677633889547848365 59695004112708580443137)
              ·
                refine ⟨44771253084531435332353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59695004112708580443137 44771253084531435332353)
                ·
                  refine ⟨33578439813398576499265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44771253084531435332353 33578439813398576499265)
                  ·
                    rfl

theorem cell20_73568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 3, 2, 2].length) (baseStart_73568 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_73568 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_73568 prefixEnd_73568 := by exact prefixLift 73568
  have htrace : WordTrace (prefixWord ++ tailWord_73568) baseStart_73568 baseEnd_73568 := by
    simpa [prefixWord, tailWord_73568, baseEnd_73568] using wordTrace_append hprefix tailTrace_73568
  have hstable : (prefixWord ++ tailWord_73568).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73568).length < 2 ^ (prefixWord ++ tailWord_73568).sum := by decide
  have hdescent : baseEnd_73568 < baseStart_73568 := by decide
  rcases family_descends (prefixWord ++ tailWord_73568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73578 : List Nat := [3, 1, 3, 4, 1, 2, 2, 1, 3]
def baseStart_73578 : Nat := 118140960795 + 73578 * 2 ^ 59
def prefixEnd_73578 : Nat := 4983230072969 + 3 ^ 40 * 73578 * 2
def baseEnd_73578 : Nat := 33583004085882986165891

theorem tailTrace_73578 : CollatzResearch.WordTrace tailWord_73578 prefixEnd_73578 33583004085882986165891 := by
  unfold tailWord_73578
  simp only [CollatzResearch.WordTrace]
  refine ⟨670902531861736741767347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1789073418297964644712925 670902531861736741767347)
  ·
    refine ⟨1006353797792605112651021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 670902531861736741767347 1006353797792605112651021)
    ·
      refine ⟨377382674172226917244133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1006353797792605112651021 377382674172226917244133)
      ·
        refine ⟨70759251407292546983275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 377382674172226917244133 70759251407292546983275)
        ·
          refine ⟨106138877110938820474913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70759251407292546983275 106138877110938820474913)
          ·
            refine ⟨79604157833204115356185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106138877110938820474913 79604157833204115356185)
            ·
              refine ⟨59703118374903086517139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79604157833204115356185 59703118374903086517139)
              ·
                refine ⟨89554677562354629775709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59703118374903086517139 89554677562354629775709)
                ·
                  refine ⟨33583004085882986165891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 89554677562354629775709 33583004085882986165891)
                  ·
                    rfl

theorem cell20_73578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 2, 1, 3].length) (baseStart_73578 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_73578 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_73578 prefixEnd_73578 := by exact prefixLift 73578
  have htrace : WordTrace (prefixWord ++ tailWord_73578) baseStart_73578 baseEnd_73578 := by
    simpa [prefixWord, tailWord_73578, baseEnd_73578] using wordTrace_append hprefix tailTrace_73578
  have hstable : (prefixWord ++ tailWord_73578).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73578).length < 2 ^ (prefixWord ++ tailWord_73578).sum := by decide
  have hdescent : baseEnd_73578 < baseStart_73578 := by decide
  rcases family_descends (prefixWord ++ tailWord_73578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73582 : List Nat := [4, 1, 2, 3, 1, 2, 1, 3, 3]
def baseStart_73582 : Nat := 118140960795 + 73582 * 2 ^ 59
def prefixEnd_73582 : Nat := 4983230072969 + 3 ^ 40 * 73582 * 2
def baseEnd_73582 : Nat := 33584829794876750032541

theorem tailTrace_73582 : CollatzResearch.WordTrace tailWord_73582 prefixEnd_73582 33584829794876750032541 := by
  unfold tailWord_73582
  simp only [CollatzResearch.WordTrace]
  refine ⟨335469502429056956276875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1789170679621637100143333 335469502429056956276875)
  ·
    refine ⟨503204253643585434415313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 335469502429056956276875 503204253643585434415313)
    ·
      refine ⟨377403190232689075811485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 503204253643585434415313 377403190232689075811485)
      ·
        refine ⟨141526196337258403429307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 377403190232689075811485 141526196337258403429307)
        ·
          refine ⟨212289294505887605143961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141526196337258403429307 212289294505887605143961)
          ·
            refine ⟨159216970879415703857971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 212289294505887605143961 159216970879415703857971)
            ·
              refine ⟨238825456319123555786957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159216970879415703857971 238825456319123555786957)
              ·
                refine ⟨89559546119671333420109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 238825456319123555786957 89559546119671333420109)
                ·
                  refine ⟨33584829794876750032541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 89559546119671333420109 33584829794876750032541)
                  ·
                    rfl

theorem cell20_73582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 3, 3].length) (baseStart_73582 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_73582 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_73582 prefixEnd_73582 := by exact prefixLift 73582
  have htrace : WordTrace (prefixWord ++ tailWord_73582) baseStart_73582 baseEnd_73582 := by
    simpa [prefixWord, tailWord_73582, baseEnd_73582] using wordTrace_append hprefix tailTrace_73582
  have hstable : (prefixWord ++ tailWord_73582).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73582).length < 2 ^ (prefixWord ++ tailWord_73582).sum := by decide
  have hdescent : baseEnd_73582 < baseStart_73582 := by decide
  rcases family_descends (prefixWord ++ tailWord_73582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73593 : List Nat := [1, 2, 1, 3, 2, 2, 2, 1, 6]
def baseStart_73593 : Nat := 118140960795 + 73593 * 2 ^ 59
def prefixEnd_73593 : Nat := 4983230072969 + 3 ^ 40 * 73593 * 2
def baseEnd_73593 : Nat := 33589850494609600665829

theorem tailTrace_73593 : CollatzResearch.WordTrace tailWord_73593 prefixEnd_73593 33589850494609600665829 := by
  unfold tailWord_73593
  simp only [CollatzResearch.WordTrace]
  refine ⟨2684157222392604528865433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1789438148261736352576955 2684157222392604528865433)
  ·
    refine ⟨2013117916794453396649075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2684157222392604528865433 2013117916794453396649075)
    ·
      refine ⟨3019676875191680094973613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2013117916794453396649075 3019676875191680094973613)
      ·
        refine ⟨1132378828196880035615105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3019676875191680094973613 1132378828196880035615105)
        ·
          refine ⟨849284121147660026711329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1132378828196880035615105 849284121147660026711329)
          ·
            refine ⟨636963090860745020033497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 849284121147660026711329 636963090860745020033497)
            ·
              refine ⟨477722318145558765025123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 636963090860745020033497 477722318145558765025123)
              ·
                refine ⟨716583477218338147537685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 477722318145558765025123 716583477218338147537685)
                ·
                  refine ⟨33589850494609600665829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 716583477218338147537685 33589850494609600665829)
                  ·
                    rfl

theorem cell20_73593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 6].length) (baseStart_73593 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_73593 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_73593 prefixEnd_73593 := by exact prefixLift 73593
  have htrace : WordTrace (prefixWord ++ tailWord_73593) baseStart_73593 baseEnd_73593 := by
    simpa [prefixWord, tailWord_73593, baseEnd_73593] using wordTrace_append hprefix tailTrace_73593
  have hstable : (prefixWord ++ tailWord_73593).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73593).length < 2 ^ (prefixWord ++ tailWord_73593).sum := by decide
  have hdescent : baseEnd_73593 < baseStart_73593 := by decide
  rcases family_descends (prefixWord ++ tailWord_73593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73600 : List Nat := [2, 1, 1, 2, 1, 2, 3, 8]
def baseStart_73600 : Nat := 118140960795 + 73600 * 2 ^ 59
def prefixEnd_73600 : Nat := 4983230072969 + 3 ^ 40 * 73600 * 2
def baseEnd_73600 : Nat := 11197681828449562477489

theorem tailTrace_73600 : CollatzResearch.WordTrace tailWord_73600 prefixEnd_73600 11197681828449562477489 := by
  unfold tailWord_73600
  simp only [CollatzResearch.WordTrace]
  refine ⟨1342206266683622362185127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1789608355578163149580169 1342206266683622362185127)
  ·
    refine ⟨2013309400025433543277691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1342206266683622362185127 2013309400025433543277691)
    ·
      refine ⟨3019964100038150314916537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2013309400025433543277691 3019964100038150314916537)
      ·
        refine ⟨2264973075028612736187403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3019964100038150314916537 2264973075028612736187403)
        ·
          refine ⟨3397459612542919104281105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2264973075028612736187403 3397459612542919104281105)
          ·
            refine ⟨2548094709407189328210829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3397459612542919104281105 2548094709407189328210829)
            ·
              refine ⟨955535516027695998079061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2548094709407189328210829 955535516027695998079061)
              ·
                refine ⟨11197681828449562477489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 955535516027695998079061 11197681828449562477489)
                ·
                  rfl

theorem cell20_73600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 8].length) (baseStart_73600 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_73600 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_73600 prefixEnd_73600 := by exact prefixLift 73600
  have htrace : WordTrace (prefixWord ++ tailWord_73600) baseStart_73600 baseEnd_73600 := by
    simpa [prefixWord, tailWord_73600, baseEnd_73600] using wordTrace_append hprefix tailTrace_73600
  have hstable : (prefixWord ++ tailWord_73600).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73600).length < 2 ^ (prefixWord ++ tailWord_73600).sum := by decide
  have hdescent : baseEnd_73600 < baseStart_73600 := by decide
  rcases family_descends (prefixWord ++ tailWord_73600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73620 : List Nat := [2, 4, 2, 1, 1, 3, 2, 2, 3]
def baseStart_73620 : Nat := 118140960795 + 73620 * 2 ^ 59
def prefixEnd_73620 : Nat := 4983230072969 + 3 ^ 40 * 73620 * 2
def baseEnd_73620 : Nat := 33602174030317506765719

theorem tailTrace_73620 : CollatzResearch.WordTrace tailWord_73620 prefixEnd_73620 33602174030317506765719 := by
  unfold tailWord_73620
  simp only [CollatzResearch.WordTrace]
  refine ⟨1342570996647394070049157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1790094662196525426732209 1342570996647394070049157)
  ·
    refine ⟨251732061871386388134217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1342570996647394070049157 251732061871386388134217)
    ·
      refine ⟨188799046403539791100663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 251732061871386388134217 188799046403539791100663)
      ·
        refine ⟨283198569605309686650995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188799046403539791100663 283198569605309686650995)
        ·
          refine ⟨424797854407964529976493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 283198569605309686650995 424797854407964529976493)
          ·
            refine ⟨159299195402986698741185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 424797854407964529976493 159299195402986698741185)
            ·
              refine ⟨119474396552240024055889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 159299195402986698741185 119474396552240024055889)
              ·
                refine ⟨89605797414180018041917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 119474396552240024055889 89605797414180018041917)
                ·
                  refine ⟨33602174030317506765719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 89605797414180018041917 33602174030317506765719)
                  ·
                    rfl

theorem cell20_73620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_73620 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_73620 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_73620 prefixEnd_73620 := by exact prefixLift 73620
  have htrace : WordTrace (prefixWord ++ tailWord_73620) baseStart_73620 baseEnd_73620 := by
    simpa [prefixWord, tailWord_73620, baseEnd_73620] using wordTrace_append hprefix tailTrace_73620
  have hstable : (prefixWord ++ tailWord_73620).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73620).length < 2 ^ (prefixWord ++ tailWord_73620).sum := by decide
  have hdescent : baseEnd_73620 < baseStart_73620 := by decide
  rcases family_descends (prefixWord ++ tailWord_73620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73630 : List Nat := [4, 3, 1, 3, 1, 2, 1, 5]
def baseStart_73630 : Nat := 118140960795 + 73630 * 2 ^ 59
def prefixEnd_73630 : Nat := 4983230072969 + 3 ^ 40 * 73630 * 2
def baseEnd_73630 : Nat := 11202246100933972144115

theorem tailTrace_73630 : CollatzResearch.WordTrace tailWord_73630 prefixEnd_73630 11202246100933972144115 := by
  unfold tailWord_73630
  simp only [CollatzResearch.WordTrace]
  refine ⟨335688340407319980995293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1790337815505706565308229 335688340407319980995293)
  ·
    refine ⟨125883127652744992873235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 335688340407319980995293 125883127652744992873235)
    ·
      refine ⟨188824691479117489309853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125883127652744992873235 188824691479117489309853)
      ·
        refine ⟨70809259304669058491195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 188824691479117489309853 70809259304669058491195)
        ·
          refine ⟨106213888957003587736793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70809259304669058491195 106213888957003587736793)
          ·
            refine ⟨79660416717752690802595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106213888957003587736793 79660416717752690802595)
            ·
              refine ⟨119490625076629036203893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79660416717752690802595 119490625076629036203893)
              ·
                refine ⟨11202246100933972144115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 119490625076629036203893 11202246100933972144115)
                ·
                  rfl

theorem cell20_73630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 5].length) (baseStart_73630 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_73630 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_73630 prefixEnd_73630 := by exact prefixLift 73630
  have htrace : WordTrace (prefixWord ++ tailWord_73630) baseStart_73630 baseEnd_73630 := by
    simpa [prefixWord, tailWord_73630, baseEnd_73630] using wordTrace_append hprefix tailTrace_73630
  have hstable : (prefixWord ++ tailWord_73630).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73630).length < 2 ^ (prefixWord ++ tailWord_73630).sum := by decide
  have hdescent : baseEnd_73630 < baseStart_73630 := by decide
  rcases family_descends (prefixWord ++ tailWord_73630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73710 : List Nat := [4, 1, 2, 1, 3, 1, 4, 4]
def baseStart_73710 : Nat := 118140960795 + 73710 * 2 ^ 59
def prefixEnd_73710 : Nat := 4983230072969 + 3 ^ 40 * 73710 * 2
def baseEnd_73710 : Nat := 11214417494225731255117

theorem tailTrace_73710 : CollatzResearch.WordTrace tailWord_73710 prefixEnd_73710 11214417494225731255117 := by
  unfold tailWord_73710
  simp only [CollatzResearch.WordTrace]
  refine ⟨336053070371091688859323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1792283041979155673916389 336053070371091688859323)
  ·
    refine ⟨504079605556637533288985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 336053070371091688859323 504079605556637533288985)
    ·
      refine ⟨378059704167478149966739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 504079605556637533288985 378059704167478149966739)
      ·
        refine ⟨567089556251217224950109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 378059704167478149966739 567089556251217224950109)
        ·
          refine ⟨212658583594206459356291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 567089556251217224950109 212658583594206459356291)
          ·
            refine ⟨318987875391309689034437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212658583594206459356291 318987875391309689034437)
            ·
              refine ⟨59810226635870566693957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 318987875391309689034437 59810226635870566693957)
              ·
                refine ⟨11214417494225731255117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59810226635870566693957 11214417494225731255117)
                ·
                  rfl

theorem cell20_73710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 4, 4].length) (baseStart_73710 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_73710 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_73710 prefixEnd_73710 := by exact prefixLift 73710
  have htrace : WordTrace (prefixWord ++ tailWord_73710) baseStart_73710 baseEnd_73710 := by
    simpa [prefixWord, tailWord_73710, baseEnd_73710] using wordTrace_append hprefix tailTrace_73710
  have hstable : (prefixWord ++ tailWord_73710).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73710).length < 2 ^ (prefixWord ++ tailWord_73710).sum := by decide
  have hdescent : baseEnd_73710 < baseStart_73710 := by decide
  rcases family_descends (prefixWord ++ tailWord_73710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73751 : List Nat := [1, 1, 3, 5, 2, 2, 2, 1, 3]
def baseStart_73751 : Nat := 118140960795 + 73751 * 2 ^ 59
def prefixEnd_73751 : Nat := 4983230072969 + 3 ^ 40 * 73751 * 2
def baseEnd_73751 : Nat := 33661965999863273398517

theorem tailTrace_73751 : CollatzResearch.WordTrace tailWord_73751 prefixEnd_73751 33661965999863273398517 := by
  unfold tailWord_73751
  simp only [CollatzResearch.WordTrace]
  refine ⟨2689919955820197513117107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1793279970546798342078071 2689919955820197513117107)
  ·
    refine ⟨4034879933730296269675661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2689919955820197513117107 4034879933730296269675661)
    ·
      refine ⟨1513079975148861101128373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4034879933730296269675661 1513079975148861101128373)
      ·
        refine ⟨141851247670205728230785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1513079975148861101128373 141851247670205728230785)
        ·
          refine ⟨106388435752654296173089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141851247670205728230785 106388435752654296173089)
          ·
            refine ⟨79791326814490722129817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106388435752654296173089 79791326814490722129817)
            ·
              refine ⟨59843495110868041597363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79791326814490722129817 59843495110868041597363)
              ·
                refine ⟨89765242666302062396045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59843495110868041597363 89765242666302062396045)
                ·
                  refine ⟨33661965999863273398517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 89765242666302062396045 33661965999863273398517)
                  ·
                    rfl

theorem cell20_73751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 2, 1, 3].length) (baseStart_73751 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_73751 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_73751 prefixEnd_73751 := by exact prefixLift 73751
  have htrace : WordTrace (prefixWord ++ tailWord_73751) baseStart_73751 baseEnd_73751 := by
    simpa [prefixWord, tailWord_73751, baseEnd_73751] using wordTrace_append hprefix tailTrace_73751
  have hstable : (prefixWord ++ tailWord_73751).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73751).length < 2 ^ (prefixWord ++ tailWord_73751).sum := by decide
  have hdescent : baseEnd_73751 < baseStart_73751 := by decide
  rcases family_descends (prefixWord ++ tailWord_73751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73793 : List Nat := [1, 2, 5, 1, 2, 1, 1, 4, 3]
def baseStart_73793 : Nat := 118140960795 + 73793 * 2 ^ 59
def prefixEnd_73793 : Nat := 4983230072969 + 3 ^ 40 * 73793 * 2
def baseEnd_73793 : Nat := 33681135944297793998345

theorem tailTrace_73793 : CollatzResearch.WordTrace tailWord_73793 prefixEnd_73793 33681135944297793998345 := by
  unfold tailWord_73793
  simp only [CollatzResearch.WordTrace]
  refine ⟨2691451821668038686146033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1794301214445359124097355 2691451821668038686146033)
  ·
    refine ⟨2018588866251029014609525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2691451821668038686146033 2018588866251029014609525)
    ·
      refine ⟨189242706211033970119643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2018588866251029014609525 189242706211033970119643)
      ·
        refine ⟨283864059316550955179465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189242706211033970119643 283864059316550955179465)
        ·
          refine ⟨212898044487413216384599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 283864059316550955179465 212898044487413216384599)
          ·
            refine ⟨319347066731119824576899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212898044487413216384599 319347066731119824576899)
            ·
              refine ⟨479020600096679736865349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 319347066731119824576899 479020600096679736865349)
              ·
                refine ⟨89816362518127450662253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 479020600096679736865349 89816362518127450662253)
                ·
                  refine ⟨33681135944297793998345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 89816362518127450662253 33681135944297793998345)
                  ·
                    rfl

theorem cell20_73793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 4, 3].length) (baseStart_73793 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_73793 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_73793 prefixEnd_73793 := by exact prefixLift 73793
  have htrace : WordTrace (prefixWord ++ tailWord_73793) baseStart_73793 baseEnd_73793 := by
    simpa [prefixWord, tailWord_73793, baseEnd_73793] using wordTrace_append hprefix tailTrace_73793
  have hstable : (prefixWord ++ tailWord_73793).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73793).length < 2 ^ (prefixWord ++ tailWord_73793).sum := by decide
  have hdescent : baseEnd_73793 < baseStart_73793 := by decide
  rcases family_descends (prefixWord ++ tailWord_73793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73828 : List Nat := [2, 3, 1, 1, 2, 1, 2, 8]
def baseStart_73828 : Nat := 118140960795 + 73828 * 2 ^ 59
def prefixEnd_73828 : Nat := 4983230072969 + 3 ^ 40 * 73828 * 2
def baseEnd_73828 : Nat := 11232370299331075943845

theorem tailTrace_73828 : CollatzResearch.WordTrace tailWord_73828 prefixEnd_73828 11232370299331075943845 := by
  unfold tailWord_73828
  simp only [CollatzResearch.WordTrace]
  refine ⟨1346364188270619831835069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1795152251027493109113425 1346364188270619831835069)
  ·
    refine ⟨504886570601482436938151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1346364188270619831835069 504886570601482436938151)
    ·
      refine ⟨757329855902223655407227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 504886570601482436938151 757329855902223655407227)
      ·
        refine ⟨1135994783853335483110841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 757329855902223655407227 1135994783853335483110841)
        ·
          refine ⟨851996087890001612333131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1135994783853335483110841 851996087890001612333131)
          ·
            refine ⟨1277994131835002418499697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 851996087890001612333131 1277994131835002418499697)
            ·
              refine ⟨958495598876251813874773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1277994131835002418499697 958495598876251813874773)
              ·
                refine ⟨11232370299331075943845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 958495598876251813874773 11232370299331075943845)
                ·
                  rfl

theorem cell20_73828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 8].length) (baseStart_73828 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_73828 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_73828 prefixEnd_73828 := by exact prefixLift 73828
  have htrace : WordTrace (prefixWord ++ tailWord_73828) baseStart_73828 baseEnd_73828 := by
    simpa [prefixWord, tailWord_73828, baseEnd_73828] using wordTrace_append hprefix tailTrace_73828
  have hstable : (prefixWord ++ tailWord_73828).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73828).length < 2 ^ (prefixWord ++ tailWord_73828).sum := by decide
  have hdescent : baseEnd_73828 < baseStart_73828 := by decide
  rcases family_descends (prefixWord ++ tailWord_73828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73834 : List Nat := [3, 1, 3, 2, 3, 1, 2, 3, 2]
def baseStart_73834 : Nat := 118140960795 + 73834 * 2 ^ 59
def prefixEnd_73834 : Nat := 4983230072969 + 3 ^ 40 * 73834 * 2
def baseEnd_73834 : Nat := 33699849461483873631511

theorem tailTrace_73834 : CollatzResearch.WordTrace tailWord_73834 prefixEnd_73834 33699849461483873631511 := by
  unfold tailWord_73834
  simp only [CollatzResearch.WordTrace]
  refine ⟨673236803629875672097139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1795298143013001792259037 673236803629875672097139)
  ·
    refine ⟨1009855205444813508145709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 673236803629875672097139 1009855205444813508145709)
    ·
      refine ⟨378695702041805065554641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1009855205444813508145709 378695702041805065554641)
      ·
        refine ⟨284021776531353799165981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 378695702041805065554641 284021776531353799165981)
        ·
          refine ⟨106508166199257674687243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 284021776531353799165981 106508166199257674687243)
          ·
            refine ⟨159762249298886512030865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106508166199257674687243 159762249298886512030865)
            ·
              refine ⟨119821686974164884023149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 159762249298886512030865 119821686974164884023149)
              ·
                refine ⟨44933132615311831508681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 119821686974164884023149 44933132615311831508681)
                ·
                  refine ⟨33699849461483873631511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44933132615311831508681 33699849461483873631511)
                  ·
                    rfl

theorem cell20_73834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 3, 2].length) (baseStart_73834 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_73834 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_73834 prefixEnd_73834 := by exact prefixLift 73834
  have htrace : WordTrace (prefixWord ++ tailWord_73834) baseStart_73834 baseEnd_73834 := by
    simpa [prefixWord, tailWord_73834, baseEnd_73834] using wordTrace_append hprefix tailTrace_73834
  have hstable : (prefixWord ++ tailWord_73834).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73834).length < 2 ^ (prefixWord ++ tailWord_73834).sum := by decide
  have hdescent : baseEnd_73834 < baseStart_73834 := by decide
  rcases family_descends (prefixWord ++ tailWord_73834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73852 : List Nat := [2, 2, 2, 1, 1, 5, 1, 1, 5]
def baseStart_73852 : Nat := 118140960795 + 73852 * 2 ^ 59
def prefixEnd_73852 : Nat := 4983230072969 + 3 ^ 40 * 73852 * 2
def baseEnd_73852 : Nat := 33708065151955811031437

theorem tailTrace_73852 : CollatzResearch.WordTrace tailWord_73852 prefixEnd_73852 33708065151955811031437 := by
  unfold tailWord_73852
  simp only [CollatzResearch.WordTrace]
  refine ⟨1346801864227145881271905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1795735818969527841695873 1346801864227145881271905)
  ·
    refine ⟨1010101398170359410953929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1346801864227145881271905 1010101398170359410953929)
    ·
      refine ⟨757576048627769558215447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1010101398170359410953929 757576048627769558215447)
      ·
        refine ⟨1136364072941654337323171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 757576048627769558215447 1136364072941654337323171)
        ·
          refine ⟨1704546109412481505984757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1136364072941654337323171 1704546109412481505984757)
          ·
            refine ⟨159801197757420141186071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1704546109412481505984757 159801197757420141186071)
            ·
              refine ⟨239701796636130211779107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159801197757420141186071 239701796636130211779107)
              ·
                refine ⟨359552694954195317668661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 239701796636130211779107 359552694954195317668661)
                ·
                  refine ⟨33708065151955811031437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 359552694954195317668661 33708065151955811031437)
                  ·
                    rfl

theorem cell20_73852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 1, 5].length) (baseStart_73852 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_73852 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_73852 prefixEnd_73852 := by exact prefixLift 73852
  have htrace : WordTrace (prefixWord ++ tailWord_73852) baseStart_73852 baseEnd_73852 := by
    simpa [prefixWord, tailWord_73852, baseEnd_73852] using wordTrace_append hprefix tailTrace_73852
  have hstable : (prefixWord ++ tailWord_73852).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73852).length < 2 ^ (prefixWord ++ tailWord_73852).sum := by decide
  have hdescent : baseEnd_73852 < baseStart_73852 := by decide
  rcases family_descends (prefixWord ++ tailWord_73852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73859 : List Nat := [1, 1, 1, 3, 3, 3, 1, 3, 4]
def baseStart_73859 : Nat := 118140960795 + 73859 * 2 ^ 59
def prefixEnd_73859 : Nat := 4983230072969 + 3 ^ 40 * 73859 * 2
def baseEnd_73859 : Nat := 33711260142694897798075

theorem tailTrace_73859 : CollatzResearch.WordTrace tailWord_73859 prefixEnd_73859 33711260142694897798075 := by
  unfold tailWord_73859
  simp only [CollatzResearch.WordTrace]
  refine ⟨2693859039428931958048631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1795906026285954638699087 2693859039428931958048631)
  ·
    refine ⟨4040788559143397937072947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2693859039428931958048631 4040788559143397937072947)
    ·
      refine ⟨6061182838715096905609421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4040788559143397937072947 6061182838715096905609421)
      ·
        refine ⟨2272943564518161339603533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6061182838715096905609421 2272943564518161339603533)
        ·
          refine ⟨852353836694310502351325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2272943564518161339603533 852353836694310502351325)
          ·
            refine ⟨319632688760366438381747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 852353836694310502351325 319632688760366438381747)
            ·
              refine ⟨479449033140549657572621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 319632688760366438381747 479449033140549657572621)
              ·
                refine ⟨179793387427706121589733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 479449033140549657572621 179793387427706121589733)
                ·
                  refine ⟨33711260142694897798075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 179793387427706121589733 33711260142694897798075)
                  ·
                    rfl

theorem cell20_73859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 3, 4].length) (baseStart_73859 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_73859 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_73859 prefixEnd_73859 := by exact prefixLift 73859
  have htrace : WordTrace (prefixWord ++ tailWord_73859) baseStart_73859 baseEnd_73859 := by
    simpa [prefixWord, tailWord_73859, baseEnd_73859] using wordTrace_append hprefix tailTrace_73859
  have hstable : (prefixWord ++ tailWord_73859).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73859).length < 2 ^ (prefixWord ++ tailWord_73859).sum := by decide
  have hdescent : baseEnd_73859 < baseStart_73859 := by decide
  rcases family_descends (prefixWord ++ tailWord_73859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73879 : List Nat := [1, 1, 3, 3, 5, 1, 2, 4]
def baseStart_73879 : Nat := 118140960795 + 73879 * 2 ^ 59
def prefixEnd_73879 : Nat := 4983230072969 + 3 ^ 40 * 73879 * 2
def baseEnd_73879 : Nat := 11240129562554572377109

theorem tailTrace_73879 : CollatzResearch.WordTrace tailWord_73879 prefixEnd_73879 11240129562554572377109 := by
  unfold tailWord_73879
  simp only [CollatzResearch.WordTrace]
  refine ⟨2694588499356475373776691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1796392332904316915851127 2694588499356475373776691)
  ·
    refine ⟨4041882749034713060665037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2694588499356475373776691 4041882749034713060665037)
    ·
      refine ⟨1515706030888017397749389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4041882749034713060665037 1515706030888017397749389)
      ·
        refine ⟨568389761583006524156021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1515706030888017397749389 568389761583006524156021)
        ·
          refine ⟨53286540148406861639627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 568389761583006524156021 53286540148406861639627)
          ·
            refine ⟨79929810222610292459441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53286540148406861639627 79929810222610292459441)
            ·
              refine ⟨59947357666957719344581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79929810222610292459441 59947357666957719344581)
              ·
                refine ⟨11240129562554572377109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59947357666957719344581 11240129562554572377109)
                ·
                  rfl

theorem cell20_73879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 2, 4].length) (baseStart_73879 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_73879 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_73879 prefixEnd_73879 := by exact prefixLift 73879
  have htrace : WordTrace (prefixWord ++ tailWord_73879) baseStart_73879 baseEnd_73879 := by
    simpa [prefixWord, tailWord_73879, baseEnd_73879] using wordTrace_append hprefix tailTrace_73879
  have hstable : (prefixWord ++ tailWord_73879).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73879).length < 2 ^ (prefixWord ++ tailWord_73879).sum := by decide
  have hdescent : baseEnd_73879 < baseStart_73879 := by decide
  rcases family_descends (prefixWord ++ tailWord_73879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73914 : List Nat := [3, 1, 1, 1, 2, 2, 2, 6, 2]
def baseStart_73914 : Nat := 118140960795 + 73914 * 2 ^ 59
def prefixEnd_73914 : Nat := 4983230072969 + 3 ^ 40 * 73914 * 2
def baseEnd_73914 : Nat := 33736363641359150964517

theorem tailTrace_73914 : CollatzResearch.WordTrace tailWord_73914 prefixEnd_73914 33736363641359150964517 := by
  unfold tailWord_73914
  simp only [CollatzResearch.WordTrace]
  refine ⟨673966263557419087825199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1797243369486450900867197 673966263557419087825199)
  ·
    refine ⟨1010949395336128631737799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 673966263557419087825199 1010949395336128631737799)
    ·
      refine ⟨1516424093004192947606699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1010949395336128631737799 1516424093004192947606699)
      ·
        refine ⟨2274636139506289421410049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1516424093004192947606699 2274636139506289421410049)
        ·
          refine ⟨1705977104629717066057537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2274636139506289421410049 1705977104629717066057537)
          ·
            refine ⟨1279482828472287799543153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1705977104629717066057537 1279482828472287799543153)
            ·
              refine ⟨959612121354215849657365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1279482828472287799543153 959612121354215849657365)
              ·
                refine ⟨44981818188478867952689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 959612121354215849657365 44981818188478867952689)
                ·
                  refine ⟨33736363641359150964517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44981818188478867952689 33736363641359150964517)
                  ·
                    rfl

theorem cell20_73914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 6, 2].length) (baseStart_73914 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_73914 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_73914 prefixEnd_73914 := by exact prefixLift 73914
  have htrace : WordTrace (prefixWord ++ tailWord_73914) baseStart_73914 baseEnd_73914 := by
    simpa [prefixWord, tailWord_73914, baseEnd_73914] using wordTrace_append hprefix tailTrace_73914
  have hstable : (prefixWord ++ tailWord_73914).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73914).length < 2 ^ (prefixWord ++ tailWord_73914).sum := by decide
  have hdescent : baseEnd_73914 < baseStart_73914 := by decide
  rcases family_descends (prefixWord ++ tailWord_73914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73924 : List Nat := [2, 3, 3, 1, 2, 1, 4, 1, 3]
def baseStart_73924 : Nat := 118140960795 + 73924 * 2 ^ 59
def prefixEnd_73924 : Nat := 4983230072969 + 3 ^ 40 * 73924 * 2
def baseEnd_73924 : Nat := 33740927913843560631143

theorem tailTrace_73924 : CollatzResearch.WordTrace tailWord_73924 prefixEnd_73924 33740927913843560631143 := by
  unfold tailWord_73924
  simp only [CollatzResearch.WordTrace]
  refine ⟨1348114892096724029582413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1797486522795632039443217 1348114892096724029582413)
  ·
    refine ⟨505543084536271511093405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1348114892096724029582413 505543084536271511093405)
    ·
      refine ⟨189578656701101816660027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 505543084536271511093405 189578656701101816660027)
      ·
        refine ⟨284367985051652724990041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189578656701101816660027 284367985051652724990041)
        ·
          refine ⟨213275988788739543742531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 284367985051652724990041 213275988788739543742531)
          ·
            refine ⟨319913983183109315613797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213275988788739543742531 319913983183109315613797)
            ·
              refine ⟨59983871846832996677587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 319913983183109315613797 59983871846832996677587)
              ·
                refine ⟨89975807770249495016381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59983871846832996677587 89975807770249495016381)
                ·
                  refine ⟨33740927913843560631143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 89975807770249495016381 33740927913843560631143)
                  ·
                    rfl

theorem cell20_73924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 4, 1, 3].length) (baseStart_73924 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_73924 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_73924 prefixEnd_73924 := by exact prefixLift 73924
  have htrace : WordTrace (prefixWord ++ tailWord_73924) baseStart_73924 baseEnd_73924 := by
    simpa [prefixWord, tailWord_73924, baseEnd_73924] using wordTrace_append hprefix tailTrace_73924
  have hstable : (prefixWord ++ tailWord_73924).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73924).length < 2 ^ (prefixWord ++ tailWord_73924).sum := by decide
  have hdescent : baseEnd_73924 < baseStart_73924 := by decide
  rcases family_descends (prefixWord ++ tailWord_73924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73952 : List Nat := [2, 1, 1, 3, 1, 3, 2, 5, 2]
def baseStart_73952 : Nat := 118140960795 + 73952 * 2 ^ 59
def prefixEnd_73952 : Nat := 4983230072969 + 3 ^ 40 * 73952 * 2
def baseEnd_73952 : Nat := 33753707876799907697695

theorem tailTrace_73952 : CollatzResearch.WordTrace tailWord_73952 prefixEnd_73952 33753707876799907697695 := by
  unfold tailWord_73952
  simp only [CollatzResearch.WordTrace]
  refine ⟨1348625514046004420592055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1798167352061339227456073 1348625514046004420592055)
  ·
    refine ⟨2022938271069006630888083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1348625514046004420592055 2022938271069006630888083)
    ·
      refine ⟨3034407406603509946332125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2022938271069006630888083 3034407406603509946332125)
      ·
        refine ⟨1137902777476316229874547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3034407406603509946332125 1137902777476316229874547)
        ·
          refine ⟨1706854166214474344811821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1137902777476316229874547 1706854166214474344811821)
          ·
            refine ⟨640070312330427879304433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1706854166214474344811821 640070312330427879304433)
            ·
              refine ⟨480052734247820909478325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 640070312330427879304433 480052734247820909478325)
              ·
                refine ⟨45004943835733210263593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 480052734247820909478325 45004943835733210263593)
                ·
                  refine ⟨33753707876799907697695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45004943835733210263593 33753707876799907697695)
                  ·
                    rfl

theorem cell20_73952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 5, 2].length) (baseStart_73952 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_73952 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_73952 prefixEnd_73952 := by exact prefixLift 73952
  have htrace : WordTrace (prefixWord ++ tailWord_73952) baseStart_73952 baseEnd_73952 := by
    simpa [prefixWord, tailWord_73952, baseEnd_73952] using wordTrace_append hprefix tailTrace_73952
  have hstable : (prefixWord ++ tailWord_73952).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73952).length < 2 ^ (prefixWord ++ tailWord_73952).sum := by decide
  have hdescent : baseEnd_73952 < baseStart_73952 := by decide
  rcases family_descends (prefixWord ++ tailWord_73952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73965 : List Nat := [1, 5, 1, 2, 3, 2, 2, 2, 2]
def baseStart_73965 : Nat := 118140960795 + 73965 * 2 ^ 59
def prefixEnd_73965 : Nat := 4983230072969 + 3 ^ 40 * 73965 * 2
def baseEnd_73965 : Nat := 33759641431029640264309

theorem tailTrace_73965 : CollatzResearch.WordTrace tailWord_73965 prefixEnd_73965 33759641431029640264309 := by
  unfold tailWord_73965
  simp only [CollatzResearch.WordTrace]
  refine ⟨2697725177044912061407349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1798483451363274707604899 2697725177044912061407349)
  ·
    refine ⟨252911735347960505756939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2697725177044912061407349 252911735347960505756939)
    ·
      refine ⟨379367603021940758635409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252911735347960505756939 379367603021940758635409)
      ·
        refine ⟨284525702266455568976557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 379367603021940758635409 284525702266455568976557)
        ·
          refine ⟨106697138349920838366209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 284525702266455568976557 106697138349920838366209)
          ·
            refine ⟨80022853762440628774657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106697138349920838366209 80022853762440628774657)
            ·
              refine ⟨60017140321830471580993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80022853762440628774657 60017140321830471580993)
              ·
                refine ⟨45012855241372853685745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60017140321830471580993 45012855241372853685745)
                ·
                  refine ⟨33759641431029640264309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45012855241372853685745 33759641431029640264309)
                  ·
                    rfl

theorem cell20_73965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 2, 2, 2].length) (baseStart_73965 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_73965 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_73965 prefixEnd_73965 := by exact prefixLift 73965
  have htrace : WordTrace (prefixWord ++ tailWord_73965) baseStart_73965 baseEnd_73965 := by
    simpa [prefixWord, tailWord_73965, baseEnd_73965] using wordTrace_append hprefix tailTrace_73965
  have hstable : (prefixWord ++ tailWord_73965).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73965).length < 2 ^ (prefixWord ++ tailWord_73965).sum := by decide
  have hdescent : baseEnd_73965 < baseStart_73965 := by decide
  rcases family_descends (prefixWord ++ tailWord_73965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73969 : List Nat := [1, 2, 2, 2, 2, 1, 6, 2, 2]
def baseStart_73969 : Nat := 118140960795 + 73969 * 2 ^ 59
def prefixEnd_73969 : Nat := 4983230072969 + 3 ^ 40 * 73969 * 2
def baseEnd_73969 : Nat := 33761467140023404130959

theorem tailTrace_73969 : CollatzResearch.WordTrace tailWord_73969 prefixEnd_73969 33761467140023404130959 := by
  unfold tailWord_73969
  simp only [CollatzResearch.WordTrace]
  refine ⟨2697871069030420744552961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1798580712686947163035307 2697871069030420744552961)
  ·
    refine ⟨2023403301772815558414721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2697871069030420744552961 2023403301772815558414721)
    ·
      refine ⟨1517552476329611668811041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2023403301772815558414721 1517552476329611668811041)
      ·
        refine ⟨1138164357247208751608281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1517552476329611668811041 1138164357247208751608281)
        ·
          refine ⟨853623267935406563706211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1138164357247208751608281 853623267935406563706211)
          ·
            refine ⟨1280434901903109845559317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 853623267935406563706211 1280434901903109845559317)
            ·
              refine ⟨60020386026708274010593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1280434901903109845559317 60020386026708274010593)
              ·
                refine ⟨45015289520031205507945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60020386026708274010593 45015289520031205507945)
                ·
                  refine ⟨33761467140023404130959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45015289520031205507945 33761467140023404130959)
                  ·
                    rfl

theorem cell20_73969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 6, 2, 2].length) (baseStart_73969 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_73969 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_73969 prefixEnd_73969 := by exact prefixLift 73969
  have htrace : WordTrace (prefixWord ++ tailWord_73969) baseStart_73969 baseEnd_73969 := by
    simpa [prefixWord, tailWord_73969, baseEnd_73969] using wordTrace_append hprefix tailTrace_73969
  have hstable : (prefixWord ++ tailWord_73969).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73969).length < 2 ^ (prefixWord ++ tailWord_73969).sum := by decide
  have hdescent : baseEnd_73969 < baseStart_73969 := by decide
  rcases family_descends (prefixWord ++ tailWord_73969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74007 : List Nat := [1, 1, 3, 4, 1, 3, 2, 3, 2]
def baseStart_74007 : Nat := 118140960795 + 74007 * 2 ^ 59
def prefixEnd_74007 : Nat := 4983230072969 + 3 ^ 40 * 74007 * 2
def baseEnd_74007 : Nat := 33778811375464160864137

theorem tailTrace_74007 : CollatzResearch.WordTrace tailWord_74007 prefixEnd_74007 33778811375464160864137 := by
  unfold tailWord_74007
  simp only [CollatzResearch.WordTrace]
  refine ⟨2699257042892753234436275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1799504695261835489624183 2699257042892753234436275)
  ·
    refine ⟨4048885564339129851654413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2699257042892753234436275 4048885564339129851654413)
    ·
      refine ⟨1518332086627173694370405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4048885564339129851654413 1518332086627173694370405)
      ·
        refine ⟨284687266242595067694451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1518332086627173694370405 284687266242595067694451)
        ·
          refine ⟨427030899363892601541677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 284687266242595067694451 427030899363892601541677)
          ·
            refine ⟨160136587261459725578129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 427030899363892601541677 160136587261459725578129)
            ·
              refine ⟨120102440446094794183597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 160136587261459725578129 120102440446094794183597)
              ·
                refine ⟨45038415167285547818849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 120102440446094794183597 45038415167285547818849)
                ·
                  refine ⟨33778811375464160864137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45038415167285547818849 33778811375464160864137)
                  ·
                    rfl

theorem cell20_74007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 3, 2].length) (baseStart_74007 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_74007 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_74007 prefixEnd_74007 := by exact prefixLift 74007
  have htrace : WordTrace (prefixWord ++ tailWord_74007) baseStart_74007 baseEnd_74007 := by
    simpa [prefixWord, tailWord_74007, baseEnd_74007] using wordTrace_append hprefix tailTrace_74007
  have hstable : (prefixWord ++ tailWord_74007).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74007).length < 2 ^ (prefixWord ++ tailWord_74007).sum := by decide
  have hdescent : baseEnd_74007 < baseStart_74007 := by decide
  rcases family_descends (prefixWord ++ tailWord_74007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74014 : List Nat := [4, 3, 2, 1, 1, 2, 7]
def baseStart_74014 : Nat := 118140960795 + 74014 * 2 ^ 59
def prefixEnd_74014 : Nat := 4983230072969 + 3 ^ 40 * 74014 * 2
def baseEnd_74014 : Nat := 3753556262911471958975

theorem tailTrace_74014 : CollatzResearch.WordTrace tailWord_74014 prefixEnd_74014 3753556262911471958975 := by
  unfold tailWord_74014
  simp only [CollatzResearch.WordTrace]
  refine ⟨337439044233424178742637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1799674902578262286627397 337439044233424178742637)
  ·
    refine ⟨126539641587534067028489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 337439044233424178742637 126539641587534067028489)
    ·
      refine ⟨94904731190650550271367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126539641587534067028489 94904731190650550271367)
      ·
        refine ⟨142357096785975825407051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94904731190650550271367 142357096785975825407051)
        ·
          refine ⟨213535645178963738110577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142357096785975825407051 213535645178963738110577)
          ·
            refine ⟨160151733884222803582933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 213535645178963738110577 160151733884222803582933)
            ·
              refine ⟨3753556262911471958975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 160151733884222803582933 3753556262911471958975)
              ·
                rfl

theorem cell20_74014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 7].length) (baseStart_74014 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_74014 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_74014 prefixEnd_74014 := by exact prefixLift 74014
  have htrace : WordTrace (prefixWord ++ tailWord_74014) baseStart_74014 baseEnd_74014 := by
    simpa [prefixWord, tailWord_74014, baseEnd_74014] using wordTrace_append hprefix tailTrace_74014
  have hstable : (prefixWord ++ tailWord_74014).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74014).length < 2 ^ (prefixWord ++ tailWord_74014).sum := by decide
  have hdescent : baseEnd_74014 < baseStart_74014 := by decide
  rcases family_descends (prefixWord ++ tailWord_74014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74028 : List Nat := [2, 2, 1, 1, 1, 3, 4, 4, 2]
def baseStart_74028 : Nat := 118140960795 + 74028 * 2 ^ 59
def prefixEnd_74028 : Nat := 4983230072969 + 3 ^ 40 * 74028 * 2
def baseEnd_74028 : Nat := 33788396347681421164051

theorem tailTrace_74028 : CollatzResearch.WordTrace tailWord_74028 prefixEnd_74028 33788396347681421164051 := by
  unfold tailWord_74028
  simp only [CollatzResearch.WordTrace]
  refine ⟨1350011487908336910475369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1800015317211115880633825 1350011487908336910475369)
  ·
    refine ⟨1012508615931252682856527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1350011487908336910475369 1012508615931252682856527)
    ·
      refine ⟨1518762923896879024284791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1012508615931252682856527 1518762923896879024284791)
      ·
        refine ⟨2278144385845318536427187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1518762923896879024284791 2278144385845318536427187)
        ·
          refine ⟨3417216578767977804640781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2278144385845318536427187 3417216578767977804640781)
          ·
            refine ⟨1281456217037991676740293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3417216578767977804640781 1281456217037991676740293)
            ·
              refine ⟨240273040694623439388805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1281456217037991676740293 240273040694623439388805)
              ·
                refine ⟨45051195130241894885401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 240273040694623439388805 45051195130241894885401)
                ·
                  refine ⟨33788396347681421164051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45051195130241894885401 33788396347681421164051)
                  ·
                    rfl

theorem cell20_74028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 4, 2].length) (baseStart_74028 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_74028 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_74028 prefixEnd_74028 := by exact prefixLift 74028
  have htrace : WordTrace (prefixWord ++ tailWord_74028) baseStart_74028 baseEnd_74028 := by
    simpa [prefixWord, tailWord_74028, baseEnd_74028] using wordTrace_append hprefix tailTrace_74028
  have hstable : (prefixWord ++ tailWord_74028).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74028).length < 2 ^ (prefixWord ++ tailWord_74028).sum := by decide
  have hdescent : baseEnd_74028 < baseStart_74028 := by decide
  rcases family_descends (prefixWord ++ tailWord_74028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74052 : List Nat := [2, 3, 4, 1, 2, 1, 1, 6]
def baseStart_74052 : Nat := 118140960795 + 74052 * 2 ^ 59
def prefixEnd_74052 : Nat := 4983230072969 + 3 ^ 40 * 74052 * 2
def baseEnd_74052 : Nat := 11266450200548001454651

theorem tailTrace_74052 : CollatzResearch.WordTrace tailWord_74052 prefixEnd_74052 11266450200548001454651 := by
  unfold tailWord_74052
  simp only [CollatzResearch.WordTrace]
  refine ⟨1350449163864862959912205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1800598885153150613216273 1350449163864862959912205)
  ·
    refine ⟨506418436449323609967077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1350449163864862959912205 506418436449323609967077)
    ·
      refine ⟨94953456834248176868827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 506418436449323609967077 94953456834248176868827)
      ·
        refine ⟨142430185251372265303241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94953456834248176868827 142430185251372265303241)
        ·
          refine ⟨106822638938529198977431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142430185251372265303241 106822638938529198977431)
          ·
            refine ⟨160233958407793798466147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106822638938529198977431 160233958407793798466147)
            ·
              refine ⟨240350937611690697699221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 160233958407793798466147 240350937611690697699221)
              ·
                refine ⟨11266450200548001454651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 240350937611690697699221 11266450200548001454651)
                ·
                  rfl

theorem cell20_74052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 6].length) (baseStart_74052 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_74052 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_74052 prefixEnd_74052 := by exact prefixLift 74052
  have htrace : WordTrace (prefixWord ++ tailWord_74052) baseStart_74052 baseEnd_74052 := by
    simpa [prefixWord, tailWord_74052, baseEnd_74052] using wordTrace_append hprefix tailTrace_74052
  have hstable : (prefixWord ++ tailWord_74052).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74052).length < 2 ^ (prefixWord ++ tailWord_74052).sum := by decide
  have hdescent : baseEnd_74052 < baseStart_74052 := by decide
  rcases family_descends (prefixWord ++ tailWord_74052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74083 : List Nat := [1, 1, 1, 5, 2, 1, 5, 2, 2]
def baseStart_74083 : Nat := 118140960795 + 74083 * 2 ^ 59
def prefixEnd_74083 : Nat := 4983230072969 + 3 ^ 40 * 74083 * 2
def baseEnd_74083 : Nat := 33813499846345674330493

theorem tailTrace_74083 : CollatzResearch.WordTrace tailWord_74083 prefixEnd_74083 33813499846345674330493 := by
  unfold tailWord_74083
  simp only [CollatzResearch.WordTrace]
  refine ⟨2702028990617418214202903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1801352660411612142801935 2702028990617418214202903)
  ·
    refine ⟨4053043485926127321304355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2702028990617418214202903 4053043485926127321304355)
    ·
      refine ⟨6079565228889190981956533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4053043485926127321304355 6079565228889190981956533)
      ·
        refine ⟨569959240208361654558425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6079565228889190981956533 569959240208361654558425)
        ·
          refine ⟨427469430156271240918819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 569959240208361654558425 427469430156271240918819)
          ·
            refine ⟨641204145234406861378229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 427469430156271240918819 641204145234406861378229)
            ·
              refine ⟨60112888615725643254209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 641204145234406861378229 60112888615725643254209)
              ·
                refine ⟨45084666461794232440657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60112888615725643254209 45084666461794232440657)
                ·
                  refine ⟨33813499846345674330493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45084666461794232440657 33813499846345674330493)
                  ·
                    rfl

theorem cell20_74083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 5, 2, 2].length) (baseStart_74083 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_74083 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_74083 prefixEnd_74083 := by exact prefixLift 74083
  have htrace : WordTrace (prefixWord ++ tailWord_74083) baseStart_74083 baseEnd_74083 := by
    simpa [prefixWord, tailWord_74083, baseEnd_74083] using wordTrace_append hprefix tailTrace_74083
  have hstable : (prefixWord ++ tailWord_74083).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74083).length < 2 ^ (prefixWord ++ tailWord_74083).sum := by decide
  have hdescent : baseEnd_74083 < baseStart_74083 := by decide
  rcases family_descends (prefixWord ++ tailWord_74083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74132 : List Nat := [2, 4, 2, 1, 11]
def baseStart_74132 : Nat := 118140960795 + 74132 * 2 ^ 59
def prefixEnd_74132 : Nat := 4983230072969 + 3 ^ 40 * 74132 * 2
def baseEnd_74132 : Nat := 417726725697768909839

theorem tailTrace_74132 : CollatzResearch.WordTrace tailWord_74132 prefixEnd_74132 417726725697768909839 := by
  unfold tailWord_74132
  simp only [CollatzResearch.WordTrace]
  refine ⟨1351908083719949791368325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1802544111626599721824433 1351908083719949791368325)
  ·
    refine ⟨253482765697490585881561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1351908083719949791368325 253482765697490585881561)
    ·
      refine ⟨190112074273117939411171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 253482765697490585881561 190112074273117939411171)
      ·
        refine ⟨285168111409676909116757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190112074273117939411171 285168111409676909116757)
        ·
          refine ⟨417726725697768909839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 285168111409676909116757 417726725697768909839)
          ·
            rfl

theorem cell20_74132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 11].length) (baseStart_74132 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_74132 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_74132 prefixEnd_74132 := by exact prefixLift 74132
  have htrace : WordTrace (prefixWord ++ tailWord_74132) baseStart_74132 baseEnd_74132 := by
    simpa [prefixWord, tailWord_74132, baseEnd_74132] using wordTrace_append hprefix tailTrace_74132
  have hstable : (prefixWord ++ tailWord_74132).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74132).length < 2 ^ (prefixWord ++ tailWord_74132).sum := by decide
  have hdescent : baseEnd_74132 < baseStart_74132 := by decide
  rcases family_descends (prefixWord ++ tailWord_74132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74134 : List Nat := [5, 3, 1, 2, 1, 1, 1, 4, 2]
def baseStart_74134 : Nat := 118140960795 + 74134 * 2 ^ 59
def prefixEnd_74134 : Nat := 4983230072969 + 3 ^ 40 * 74134 * 2
def baseEnd_74134 : Nat := 33836777636016163630285

theorem tailTrace_74134 : CollatzResearch.WordTrace tailWord_74134 prefixEnd_74134 33836777636016163630285 := by
  unfold tailWord_74134
  simp only [CollatzResearch.WordTrace]
  refine ⟨168993069589540870269341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1802592742288435949539637 168993069589540870269341)
  ·
    refine ⟨63372401096077826351003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168993069589540870269341 63372401096077826351003)
    ·
      refine ⟨95058601644116739526505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63372401096077826351003 95058601644116739526505)
      ·
        refine ⟨71293951233087554644879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95058601644116739526505 71293951233087554644879)
        ·
          refine ⟨106940926849631331967319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71293951233087554644879 106940926849631331967319)
          ·
            refine ⟨160411390274446997950979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106940926849631331967319 160411390274446997950979)
            ·
              refine ⟨240617085411670496926469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 160411390274446997950979 240617085411670496926469)
              ·
                refine ⟨45115703514688218173713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 240617085411670496926469 45115703514688218173713)
                ·
                  refine ⟨33836777636016163630285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45115703514688218173713 33836777636016163630285)
                  ·
                    rfl

theorem cell20_74134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_74134 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_74134 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_74134 prefixEnd_74134 := by exact prefixLift 74134
  have htrace : WordTrace (prefixWord ++ tailWord_74134) baseStart_74134 baseEnd_74134 := by
    simpa [prefixWord, tailWord_74134, baseEnd_74134] using wordTrace_append hprefix tailTrace_74134
  have hstable : (prefixWord ++ tailWord_74134).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74134).length < 2 ^ (prefixWord ++ tailWord_74134).sum := by decide
  have hdescent : baseEnd_74134 < baseStart_74134 := by decide
  rcases family_descends (prefixWord ++ tailWord_74134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74138 : List Nat := [3, 1, 1, 4, 1, 4, 2, 2, 2]
def baseStart_74138 : Nat := 118140960795 + 74138 * 2 ^ 59
def prefixEnd_74138 : Nat := 4983230072969 + 3 ^ 40 * 74138 * 2
def baseEnd_74138 : Nat := 33838603345009927496935

theorem tailTrace_74138 : CollatzResearch.WordTrace tailWord_74138 prefixEnd_74138 33838603345009927496935 := by
  unfold tailWord_74138
  simp only [CollatzResearch.WordTrace]
  refine ⟨676008751354540651863767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1802690003612108404970045 676008751354540651863767)
  ·
    refine ⟨1014013127031810977795651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 676008751354540651863767 1014013127031810977795651)
    ·
      refine ⟨1521019690547716466693477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1014013127031810977795651 1521019690547716466693477)
      ·
        refine ⟨285191191977696837505027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1521019690547716466693477 285191191977696837505027)
        ·
          refine ⟨427786787966545256257541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 285191191977696837505027 427786787966545256257541)
          ·
            refine ⟨80210022743727235548289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 427786787966545256257541 80210022743727235548289)
            ·
              refine ⟨60157517057795426661217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80210022743727235548289 60157517057795426661217)
              ·
                refine ⟨45118137793346569995913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60157517057795426661217 45118137793346569995913)
                ·
                  refine ⟨33838603345009927496935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45118137793346569995913 33838603345009927496935)
                  ·
                    rfl

theorem cell20_74138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 2, 2, 2].length) (baseStart_74138 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_74138 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_74138 prefixEnd_74138 := by exact prefixLift 74138
  have htrace : WordTrace (prefixWord ++ tailWord_74138) baseStart_74138 baseEnd_74138 := by
    simpa [prefixWord, tailWord_74138, baseEnd_74138] using wordTrace_append hprefix tailTrace_74138
  have hstable : (prefixWord ++ tailWord_74138).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74138).length < 2 ^ (prefixWord ++ tailWord_74138).sum := by decide
  have hdescent : baseEnd_74138 < baseStart_74138 := by decide
  rcases family_descends (prefixWord ++ tailWord_74138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74145 : List Nat := [1, 2, 3, 5, 2, 1, 1, 5]
def baseStart_74145 : Nat := 118140960795 + 74145 * 2 ^ 59
def prefixEnd_74145 : Nat := 4983230072969 + 3 ^ 40 * 74145 * 2
def baseEnd_74145 : Nat := 11280599445249671421191

theorem tailTrace_74145 : CollatzResearch.WordTrace tailWord_74145 prefixEnd_74145 11280599445249671421191 := by
  unfold tailWord_74145
  simp only [CollatzResearch.WordTrace]
  refine ⟨2704290316392802802959889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1802860210928535201973259 2704290316392802802959889)
  ·
    refine ⟨2028217737294602102219917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2704290316392802802959889 2028217737294602102219917)
    ·
      refine ⟨760581651485475788332469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2028217737294602102219917 760581651485475788332469)
      ·
        refine ⟨71304529826763355156169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 760581651485475788332469 71304529826763355156169)
        ·
          refine ⟨53478397370072516367127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71304529826763355156169 53478397370072516367127)
          ·
            refine ⟨80217596055108774550691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53478397370072516367127 80217596055108774550691)
            ·
              refine ⟨120326394082663161826037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80217596055108774550691 120326394082663161826037)
              ·
                refine ⟨11280599445249671421191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 120326394082663161826037 11280599445249671421191)
                ·
                  rfl

theorem cell20_74145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 5].length) (baseStart_74145 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_74145 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_74145 prefixEnd_74145 := by exact prefixLift 74145
  have htrace : WordTrace (prefixWord ++ tailWord_74145) baseStart_74145 baseEnd_74145 := by
    simpa [prefixWord, tailWord_74145, baseEnd_74145] using wordTrace_append hprefix tailTrace_74145
  have hstable : (prefixWord ++ tailWord_74145).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74145).length < 2 ^ (prefixWord ++ tailWord_74145).sum := by decide
  have hdescent : baseEnd_74145 < baseStart_74145 := by decide
  rcases family_descends (prefixWord ++ tailWord_74145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74201 : List Nat := [1, 2, 1, 2, 4, 1, 4, 1, 4]
def baseStart_74201 : Nat := 118140960795 + 74201 * 2 ^ 59
def prefixEnd_74201 : Nat := 4983230072969 + 3 ^ 40 * 74201 * 2
def baseEnd_74201 : Nat := 33867358261661708396677

theorem tailTrace_74201 : CollatzResearch.WordTrace tailWord_74201 prefixEnd_74201 33867358261661708396677 := by
  unfold tailWord_74201
  simp only [CollatzResearch.WordTrace]
  refine ⟨2706332804189924366998457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1804221869459949577998971 2706332804189924366998457)
  ·
    refine ⟨2029749603142443275248843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2706332804189924366998457 2029749603142443275248843)
    ·
      refine ⟨3044624404713664912873265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2029749603142443275248843 3044624404713664912873265)
      ·
        refine ⟨2283468303535248684654949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3044624404713664912873265 2283468303535248684654949)
        ·
          refine ⟨428150306912859128372803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2283468303535248684654949 428150306912859128372803)
          ·
            refine ⟨642225460369288692559205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 428150306912859128372803 642225460369288692559205)
            ·
              refine ⟨120417273819241629854851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 642225460369288692559205 120417273819241629854851)
              ·
                refine ⟨180625910728862444782277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120417273819241629854851 180625910728862444782277)
                ·
                  refine ⟨33867358261661708396677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 180625910728862444782277 33867358261661708396677)
                  ·
                    rfl

theorem cell20_74201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 1, 4].length) (baseStart_74201 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_74201 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_74201 prefixEnd_74201 := by exact prefixLift 74201
  have htrace : WordTrace (prefixWord ++ tailWord_74201) baseStart_74201 baseEnd_74201 := by
    simpa [prefixWord, tailWord_74201, baseEnd_74201] using wordTrace_append hprefix tailTrace_74201
  have hstable : (prefixWord ++ tailWord_74201).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74201).length < 2 ^ (prefixWord ++ tailWord_74201).sum := by decide
  have hdescent : baseEnd_74201 < baseStart_74201 := by decide
  rcases family_descends (prefixWord ++ tailWord_74201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74242 : List Nat := [3, 4, 1, 2, 2, 2, 6]
def baseStart_74242 : Nat := 118140960795 + 74242 * 2 ^ 59
def prefixEnd_74242 : Nat := 4983230072969 + 3 ^ 40 * 74242 * 2
def baseEnd_74242 : Nat := 3765119086538643114427

theorem tailTrace_74242 : CollatzResearch.WordTrace tailWord_74242 prefixEnd_74242 3765119086538643114427 := by
  unfold tailWord_74242
  simp only [CollatzResearch.WordTrace]
  refine ⟨676957049260347092310245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1805218798027592246160653 676957049260347092310245)
  ·
    refine ⟨126929446736315079808171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 676957049260347092310245 126929446736315079808171)
    ·
      refine ⟨190394170104472619712257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126929446736315079808171 190394170104472619712257)
      ·
        refine ⟨142795627578354464784193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190394170104472619712257 142795627578354464784193)
        ·
          refine ⟨107096720683765848588145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142795627578354464784193 107096720683765848588145)
          ·
            refine ⟨80322540512824386441109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107096720683765848588145 80322540512824386441109)
            ·
              refine ⟨3765119086538643114427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 80322540512824386441109 3765119086538643114427)
              ·
                rfl

theorem cell20_74242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 6].length) (baseStart_74242 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_74242 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_74242 prefixEnd_74242 := by exact prefixLift 74242
  have htrace : WordTrace (prefixWord ++ tailWord_74242) baseStart_74242 baseEnd_74242 := by
    simpa [prefixWord, tailWord_74242, baseEnd_74242] using wordTrace_append hprefix tailTrace_74242
  have hstable : (prefixWord ++ tailWord_74242).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74242).length < 2 ^ (prefixWord ++ tailWord_74242).sum := by decide
  have hdescent : baseEnd_74242 < baseStart_74242 := by decide
  rcases family_descends (prefixWord ++ tailWord_74242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74311 : List Nat := [1, 1, 4, 1, 4, 1, 4, 2, 2]
def baseStart_74311 : Nat := 118140960795 + 74311 * 2 ^ 59
def prefixEnd_74311 : Nat := 4983230072969 + 3 ^ 40 * 74311 * 2
def baseEnd_74311 : Nat := 33917565258990214729561

theorem tailTrace_74311 : CollatzResearch.WordTrace tailWord_74311 prefixEnd_74311 33917565258990214729561 := by
  unfold tailWord_74311
  simp only [CollatzResearch.WordTrace]
  refine ⟨2710344833791413153502787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1806896555860942102335191 2710344833791413153502787)
  ·
    refine ⟨4065517250687119730254181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2710344833791413153502787 4065517250687119730254181)
    ·
      refine ⟨762284484503834949422659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4065517250687119730254181 762284484503834949422659)
      ·
        refine ⟨1143426726755752424133989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 762284484503834949422659 1143426726755752424133989)
        ·
          refine ⟨214392511266703579525123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1143426726755752424133989 214392511266703579525123)
          ·
            refine ⟨321588766900055369287685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214392511266703579525123 321588766900055369287685)
            ·
              refine ⟨60297893793760381741441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 321588766900055369287685 60297893793760381741441)
              ·
                refine ⟨45223420345320286306081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60297893793760381741441 45223420345320286306081)
                ·
                  refine ⟨33917565258990214729561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45223420345320286306081 33917565258990214729561)
                  ·
                    rfl

theorem cell20_74311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 4, 2, 2].length) (baseStart_74311 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_74311 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_74311 prefixEnd_74311 := by exact prefixLift 74311
  have htrace : WordTrace (prefixWord ++ tailWord_74311) baseStart_74311 baseEnd_74311 := by
    simpa [prefixWord, tailWord_74311, baseEnd_74311] using wordTrace_append hprefix tailTrace_74311
  have hstable : (prefixWord ++ tailWord_74311).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74311).length < 2 ^ (prefixWord ++ tailWord_74311).sum := by decide
  have hdescent : baseEnd_74311 < baseStart_74311 := by decide
  rcases family_descends (prefixWord ++ tailWord_74311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74332 : List Nat := [2, 2, 4, 1, 3, 1, 1, 2, 4]
def baseStart_74332 : Nat := 118140960795 + 74332 * 2 ^ 59
def prefixEnd_74332 : Nat := 4983230072969 + 3 ^ 40 * 74332 * 2
def baseEnd_74332 : Nat := 33927150231207475029475

theorem tailTrace_74332 : CollatzResearch.WordTrace tailWord_74332 prefixEnd_74332 33927150231207475029475 := by
  unfold tailWord_74332
  simp only [CollatzResearch.WordTrace]
  refine ⟨1355555383357666870008625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1807407177810222493344833 1355555383357666870008625)
  ·
    refine ⟨1016666537518250152506469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1355555383357666870008625 1016666537518250152506469)
    ·
      refine ⟨190624975784671903594963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1016666537518250152506469 190624975784671903594963)
      ·
        refine ⟨285937463677007855392445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190624975784671903594963 285937463677007855392445)
        ·
          refine ⟨107226548878877945772167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 285937463677007855392445 107226548878877945772167)
          ·
            refine ⟨160839823318316918658251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107226548878877945772167 160839823318316918658251)
            ·
              refine ⟨241259734977475377987377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 160839823318316918658251 241259734977475377987377)
              ·
                refine ⟨180944801233106533490533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 241259734977475377987377 180944801233106533490533)
                ·
                  refine ⟨33927150231207475029475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 180944801233106533490533 33927150231207475029475)
                  ·
                    rfl

theorem cell20_74332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 2, 4].length) (baseStart_74332 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_74332 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_74332 prefixEnd_74332 := by exact prefixLift 74332
  have htrace : WordTrace (prefixWord ++ tailWord_74332) baseStart_74332 baseEnd_74332 := by
    simpa [prefixWord, tailWord_74332, baseEnd_74332] using wordTrace_append hprefix tailTrace_74332
  have hstable : (prefixWord ++ tailWord_74332).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74332).length < 2 ^ (prefixWord ++ tailWord_74332).sum := by decide
  have hdescent : baseEnd_74332 < baseStart_74332 := by decide
  rcases family_descends (prefixWord ++ tailWord_74332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74336 : List Nat := [2, 1, 1, 3, 2, 1, 3, 1, 6]
def baseStart_74336 : Nat := 118140960795 + 74336 * 2 ^ 59
def prefixEnd_74336 : Nat := 4983230072969 + 3 ^ 40 * 74336 * 2
def baseEnd_74336 : Nat := 33928975940201238896125

theorem tailTrace_74336 : CollatzResearch.WordTrace tailWord_74336 prefixEnd_74336 33928975940201238896125 := by
  unfold tailWord_74336
  simp only [CollatzResearch.WordTrace]
  refine ⟨1355628329350421211581431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1807504439133894948775241 1355628329350421211581431)
  ·
    refine ⟨2033442494025631817372147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1355628329350421211581431 2033442494025631817372147)
    ·
      refine ⟨3050163741038447726058221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2033442494025631817372147 3050163741038447726058221)
      ·
        refine ⟨1143811402889417897271833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3050163741038447726058221 1143811402889417897271833)
        ·
          refine ⟨857858552167063422953875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1143811402889417897271833 857858552167063422953875)
          ·
            refine ⟨1286787828250595134430813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 857858552167063422953875 1286787828250595134430813)
            ·
              refine ⟨482545435593973175411555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1286787828250595134430813 482545435593973175411555)
              ·
                refine ⟨723818153390959763117333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 482545435593973175411555 723818153390959763117333)
                ·
                  refine ⟨33928975940201238896125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 723818153390959763117333 33928975940201238896125)
                  ·
                    rfl

theorem cell20_74336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 6].length) (baseStart_74336 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_74336 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_74336 prefixEnd_74336 := by exact prefixLift 74336
  have htrace : WordTrace (prefixWord ++ tailWord_74336) baseStart_74336 baseEnd_74336 := by
    simpa [prefixWord, tailWord_74336, baseEnd_74336] using wordTrace_append hprefix tailTrace_74336
  have hstable : (prefixWord ++ tailWord_74336).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74336).length < 2 ^ (prefixWord ++ tailWord_74336).sum := by decide
  have hdescent : baseEnd_74336 < baseStart_74336 := by decide
  rcases family_descends (prefixWord ++ tailWord_74336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74349 : List Nat := [1, 5, 1, 1, 3, 2, 2, 3, 2]
def baseStart_74349 : Nat := 118140960795 + 74349 * 2 ^ 59
def prefixEnd_74349 : Nat := 4983230072969 + 3 ^ 40 * 74349 * 2
def baseEnd_74349 : Nat := 33934909494430971462739

theorem tailTrace_74349 : CollatzResearch.WordTrace tailWord_74349 prefixEnd_74349 33934909494430971462739 := by
  unfold tailWord_74349
  simp only [CollatzResearch.WordTrace]
  refine ⟨2711730807653745643386101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1807820538435830428924067 2711730807653745643386101)
  ·
    refine ⟨254224763217538654067447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2711730807653745643386101 254224763217538654067447)
    ·
      refine ⟨381337144826307981101171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254224763217538654067447 381337144826307981101171)
      ·
        refine ⟨572005717239461971651757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 381337144826307981101171 572005717239461971651757)
        ·
          refine ⟨214502143964798239369409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 572005717239461971651757 214502143964798239369409)
          ·
            refine ⟨160876607973598679527057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 214502143964798239369409 160876607973598679527057)
            ·
              refine ⟨120657455980199009645293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 160876607973598679527057 120657455980199009645293)
              ·
                refine ⟨45246545992574628616985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 120657455980199009645293 45246545992574628616985)
                ·
                  refine ⟨33934909494430971462739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45246545992574628616985 33934909494430971462739)
                  ·
                    rfl

theorem cell20_74349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 3, 2].length) (baseStart_74349 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_74349 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_74349 prefixEnd_74349 := by exact prefixLift 74349
  have htrace : WordTrace (prefixWord ++ tailWord_74349) baseStart_74349 baseEnd_74349 := by
    simpa [prefixWord, tailWord_74349, baseEnd_74349] using wordTrace_append hprefix tailTrace_74349
  have hstable : (prefixWord ++ tailWord_74349).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74349).length < 2 ^ (prefixWord ++ tailWord_74349).sum := by decide
  have hdescent : baseEnd_74349 < baseStart_74349 := by decide
  rcases family_descends (prefixWord ++ tailWord_74349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74367 : List Nat := [1, 1, 2, 2, 1, 1, 1, 8, 3]
def baseStart_74367 : Nat := 118140960795 + 74367 * 2 ^ 59
def prefixEnd_74367 : Nat := 4983230072969 + 3 ^ 40 * 74367 * 2
def baseEnd_74367 : Nat := 33943125184902908862665

theorem tailTrace_74367 : CollatzResearch.WordTrace tailWord_74367 prefixEnd_74367 33943125184902908862665 := by
  unfold tailWord_74367
  simp only [CollatzResearch.WordTrace]
  refine ⟨2712387321588534717541355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1808258214392356478360903 2712387321588534717541355)
  ·
    refine ⟨4068580982382802076312033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2712387321588534717541355 4068580982382802076312033)
    ·
      refine ⟨3051435736787101557234025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4068580982382802076312033 3051435736787101557234025)
      ·
        refine ⟨2288576802590326167925519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3051435736787101557234025 2288576802590326167925519)
        ·
          refine ⟨3432865203885489251888279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2288576802590326167925519 3432865203885489251888279)
          ·
            refine ⟨5149297805828233877832419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3432865203885489251888279 5149297805828233877832419)
            ·
              refine ⟨7723946708742350816748629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5149297805828233877832419 7723946708742350816748629)
              ·
                refine ⟨90515000493074423633773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7723946708742350816748629 90515000493074423633773)
                ·
                  refine ⟨33943125184902908862665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 90515000493074423633773 33943125184902908862665)
                  ·
                    rfl

theorem cell20_74367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 8, 3].length) (baseStart_74367 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_74367 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_74367 prefixEnd_74367 := by exact prefixLift 74367
  have htrace : WordTrace (prefixWord ++ tailWord_74367) baseStart_74367 baseEnd_74367 := by
    simpa [prefixWord, tailWord_74367, baseEnd_74367] using wordTrace_append hprefix tailTrace_74367
  have hstable : (prefixWord ++ tailWord_74367).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74367).length < 2 ^ (prefixWord ++ tailWord_74367).sum := by decide
  have hdescent : baseEnd_74367 < baseStart_74367 := by decide
  rcases family_descends (prefixWord ++ tailWord_74367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74419 : List Nat := [1, 1, 1, 2, 3, 4, 8]
def baseStart_74419 : Nat := 118140960795 + 74419 * 2 ^ 59
def prefixEnd_74419 : Nat := 4983230072969 + 3 ^ 40 * 74419 * 2
def baseEnd_74419 : Nat := 3774095489091315458791

theorem tailTrace_74419 : CollatzResearch.WordTrace tailWord_74419 prefixEnd_74419 3774095489091315458791 := by
  unfold tailWord_74419
  simp only [CollatzResearch.WordTrace]
  refine ⟨2714283917400147598434311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1809522611600098398956207 2714283917400147598434311)
  ·
    refine ⟨4071425876100221397651467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2714283917400147598434311 4071425876100221397651467)
    ·
      refine ⟨6107138814150332096477201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4071425876100221397651467 6107138814150332096477201)
      ·
        refine ⟨4580354110612749072357901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6107138814150332096477201 4580354110612749072357901)
        ·
          refine ⟨1717632791479780902134213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4580354110612749072357901 1717632791479780902134213)
          ·
            refine ⟨322056148402458919150165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1717632791479780902134213 322056148402458919150165)
            ·
              refine ⟨3774095489091315458791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 322056148402458919150165 3774095489091315458791)
              ·
                rfl

theorem cell20_74419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 8].length) (baseStart_74419 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_74419 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_74419 prefixEnd_74419 := by exact prefixLift 74419
  have htrace : WordTrace (prefixWord ++ tailWord_74419) baseStart_74419 baseEnd_74419 := by
    simpa [prefixWord, tailWord_74419, baseEnd_74419] using wordTrace_append hprefix tailTrace_74419
  have hstable : (prefixWord ++ tailWord_74419).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74419).length < 2 ^ (prefixWord ++ tailWord_74419).sum := by decide
  have hdescent : baseEnd_74419 < baseStart_74419 := by decide
  rcases family_descends (prefixWord ++ tailWord_74419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74429 : List Nat := [1, 4, 1, 2, 1, 3, 3, 1, 4]
def baseStart_74429 : Nat := 118140960795 + 74429 * 2 ^ 59
def prefixEnd_74429 : Nat := 4983230072969 + 3 ^ 40 * 74429 * 2
def baseEnd_74429 : Nat := 33971423674306248795745

theorem tailTrace_74429 : CollatzResearch.WordTrace tailWord_74429 prefixEnd_74429 33971423674306248795745 := by
  unfold tailWord_74429
  simp only [CollatzResearch.WordTrace]
  refine ⟨2714648647363919306298341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1809765764909279537532227 2714648647363919306298341)
  ·
    refine ⟨508996621380734869930939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2714648647363919306298341 508996621380734869930939)
    ·
      refine ⟨763494932071102304896409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 508996621380734869930939 763494932071102304896409)
      ·
        refine ⟨572621199053326728672307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 763494932071102304896409 572621199053326728672307)
        ·
          refine ⟨858931798579990093008461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 572621199053326728672307 858931798579990093008461)
          ·
            refine ⟨322099424467496284878173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 858931798579990093008461 322099424467496284878173)
            ·
              refine ⟨120787284175311106829315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 322099424467496284878173 120787284175311106829315)
              ·
                refine ⟨181180926262966660243973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120787284175311106829315 181180926262966660243973)
                ·
                  refine ⟨33971423674306248795745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 181180926262966660243973 33971423674306248795745)
                  ·
                    rfl

theorem cell20_74429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_74429 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_74429 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_74429 prefixEnd_74429 := by exact prefixLift 74429
  have htrace : WordTrace (prefixWord ++ tailWord_74429) baseStart_74429 baseEnd_74429 := by
    simpa [prefixWord, tailWord_74429, baseEnd_74429] using wordTrace_append hprefix tailTrace_74429
  have hstable : (prefixWord ++ tailWord_74429).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74429).length < 2 ^ (prefixWord ++ tailWord_74429).sum := by decide
  have hdescent : baseEnd_74429 < baseStart_74429 := by decide
  rcases family_descends (prefixWord ++ tailWord_74429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74436 : List Nat := [2, 3, 3, 1, 1, 2, 1, 7]
def baseStart_74436 : Nat := 118140960795 + 74436 * 2 ^ 59
def prefixEnd_74436 : Nat := 4983230072969 + 3 ^ 40 * 74436 * 2
def baseEnd_74436 : Nat := 11324872888348445187461

theorem tailTrace_74436 : CollatzResearch.WordTrace tailWord_74436 prefixEnd_74436 11324872888348445187461 := by
  unfold tailWord_74436
  simp only [CollatzResearch.WordTrace]
  refine ⟨1357451979169279750901581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1809935972225706334535441 1357451979169279750901581)
  ·
    refine ⟨509044492188479906588093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1357451979169279750901581 509044492188479906588093)
    ·
      refine ⟨190891684570679964970535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 509044492188479906588093 190891684570679964970535)
      ·
        refine ⟨286337526856019947455803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190891684570679964970535 286337526856019947455803)
        ·
          refine ⟨429506290284029921183705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 286337526856019947455803 429506290284029921183705)
          ·
            refine ⟨322129717713022440887779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 429506290284029921183705 322129717713022440887779)
            ·
              refine ⟨483194576569533661331669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 322129717713022440887779 483194576569533661331669)
              ·
                refine ⟨11324872888348445187461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 483194576569533661331669 11324872888348445187461)
                ·
                  rfl

theorem cell20_74436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 7].length) (baseStart_74436 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_74436 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_74436 prefixEnd_74436 := by exact prefixLift 74436
  have htrace : WordTrace (prefixWord ++ tailWord_74436) baseStart_74436 baseEnd_74436 := by
    simpa [prefixWord, tailWord_74436, baseEnd_74436] using wordTrace_append hprefix tailTrace_74436
  have hstable : (prefixWord ++ tailWord_74436).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74436).length < 2 ^ (prefixWord ++ tailWord_74436).sum := by decide
  have hdescent : baseEnd_74436 < baseStart_74436 := by decide
  rcases family_descends (prefixWord ++ tailWord_74436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74457 : List Nat := [1, 2, 1, 2, 3, 2, 1, 8]
def baseStart_74457 : Nat := 118140960795 + 74457 * 2 ^ 59
def prefixEnd_74457 : Nat := 4983230072969 + 3 ^ 40 * 74457 * 2
def baseEnd_74457 : Nat := 11328067879087531954099

theorem tailTrace_74457 : CollatzResearch.WordTrace tailWord_74457 prefixEnd_74457 11328067879087531954099 := by
  unfold tailWord_74457
  simp only [CollatzResearch.WordTrace]
  refine ⟨2715669891262480088317625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1810446594174986725545083 2715669891262480088317625)
  ·
    refine ⟨2036752418446860066238219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2715669891262480088317625 2036752418446860066238219)
    ·
      refine ⟨3055128627670290099357329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2036752418446860066238219 3055128627670290099357329)
      ·
        refine ⟨2291346470752717574517997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3055128627670290099357329 2291346470752717574517997)
        ·
          refine ⟨859254926532269090444249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2291346470752717574517997 859254926532269090444249)
          ·
            refine ⟨644441194899201817833187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 859254926532269090444249 644441194899201817833187)
            ·
              refine ⟨966661792348802726749781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 644441194899201817833187 966661792348802726749781)
              ·
                refine ⟨11328067879087531954099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 966661792348802726749781 11328067879087531954099)
                ·
                  rfl

theorem cell20_74457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 8].length) (baseStart_74457 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_74457 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_74457 prefixEnd_74457 := by exact prefixLift 74457
  have htrace : WordTrace (prefixWord ++ tailWord_74457) baseStart_74457 baseEnd_74457 := by
    simpa [prefixWord, tailWord_74457, baseEnd_74457] using wordTrace_append hprefix tailTrace_74457
  have hstable : (prefixWord ++ tailWord_74457).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74457).length < 2 ^ (prefixWord ++ tailWord_74457).sum := by decide
  have hdescent : baseEnd_74457 < baseStart_74457 := by decide
  rcases family_descends (prefixWord ++ tailWord_74457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74488 : List Nat := [2, 1, 2, 1, 1, 2, 4, 3, 4]
def baseStart_74488 : Nat := 118140960795 + 74488 * 2 ^ 59
def prefixEnd_74488 : Nat := 4983230072969 + 3 ^ 40 * 74488 * 2
def baseEnd_74488 : Nat := 33998352881964265828837

theorem tailTrace_74488 : CollatzResearch.WordTrace tailWord_74488 prefixEnd_74488 33998352881964265828837 := by
  unfold tailWord_74488
  simp only [CollatzResearch.WordTrace]
  refine ⟨1358400277075086191348059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1811200369433448255130745 1358400277075086191348059)
  ·
    refine ⟨2037600415612629287022089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1358400277075086191348059 2037600415612629287022089)
    ·
      refine ⟨1528200311709471965266567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2037600415612629287022089 1528200311709471965266567)
      ·
        refine ⟨2292300467564207947899851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1528200311709471965266567 2292300467564207947899851)
        ·
          refine ⟨3438450701346311921849777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2292300467564207947899851 3438450701346311921849777)
          ·
            refine ⟨2578838026009733941387333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3438450701346311921849777 2578838026009733941387333)
            ·
              refine ⟨483532129876825114010125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2578838026009733941387333 483532129876825114010125)
              ·
                refine ⟨181324548703809417753797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 483532129876825114010125 181324548703809417753797)
                ·
                  refine ⟨33998352881964265828837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 181324548703809417753797 33998352881964265828837)
                  ·
                    rfl

theorem cell20_74488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 3, 4].length) (baseStart_74488 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_74488 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_74488 prefixEnd_74488 := by exact prefixLift 74488
  have htrace : WordTrace (prefixWord ++ tailWord_74488) baseStart_74488 baseEnd_74488 := by
    simpa [prefixWord, tailWord_74488, baseEnd_74488] using wordTrace_append hprefix tailTrace_74488
  have hstable : (prefixWord ++ tailWord_74488).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74488).length < 2 ^ (prefixWord ++ tailWord_74488).sum := by decide
  have hdescent : baseEnd_74488 < baseStart_74488 := by decide
  rcases family_descends (prefixWord ++ tailWord_74488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74522 : List Nat := [3, 1, 1, 3, 2, 1, 4, 3, 2]
def baseStart_74522 : Nat := 118140960795 + 74522 * 2 ^ 59
def prefixEnd_74522 : Nat := 4983230072969 + 3 ^ 40 * 74522 * 2
def baseEnd_74522 : Nat := 34013871408411258695365

theorem tailTrace_74522 : CollatzResearch.WordTrace tailWord_74522 prefixEnd_74522 34013871408411258695365 := by
  unfold tailWord_74522
  simp only [CollatzResearch.WordTrace]
  refine ⟨679510159006749047358455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1812027090684664126289213 679510159006749047358455)
  ·
    refine ⟨1019265238510123571037683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 679510159006749047358455 1019265238510123571037683)
    ·
      refine ⟨1528897857765185356556525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1019265238510123571037683 1528897857765185356556525)
      ·
        refine ⟨573336696661944508708697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1528897857765185356556525 573336696661944508708697)
        ·
          refine ⟨430002522496458381531523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 573336696661944508708697 430002522496458381531523)
          ·
            refine ⟨645003783744687572297285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 430002522496458381531523 645003783744687572297285)
            ·
              refine ⟨120938209452128919805741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 645003783744687572297285 120938209452128919805741)
              ·
                refine ⟨45351828544548344927153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 120938209452128919805741 45351828544548344927153)
                ·
                  refine ⟨34013871408411258695365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45351828544548344927153 34013871408411258695365)
                  ·
                    rfl

theorem cell20_74522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 3, 2].length) (baseStart_74522 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_74522 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_74522 prefixEnd_74522 := by exact prefixLift 74522
  have htrace : WordTrace (prefixWord ++ tailWord_74522) baseStart_74522 baseEnd_74522 := by
    simpa [prefixWord, tailWord_74522, baseEnd_74522] using wordTrace_append hprefix tailTrace_74522
  have hstable : (prefixWord ++ tailWord_74522).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74522).length < 2 ^ (prefixWord ++ tailWord_74522).sum := by decide
  have hdescent : baseEnd_74522 < baseStart_74522 := by decide
  rcases family_descends (prefixWord ++ tailWord_74522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74532 : List Nat := [2, 3, 1, 3, 4, 1, 1, 2, 3]
def baseStart_74532 : Nat := 118140960795 + 74532 * 2 ^ 59
def prefixEnd_74532 : Nat := 4983230072969 + 3 ^ 40 * 74532 * 2
def baseEnd_74532 : Nat := 34018435680895668361991

theorem tailTrace_74532 : CollatzResearch.WordTrace tailWord_74532 prefixEnd_74532 34018435680895668361991 := by
  unfold tailWord_74532
  simp only [CollatzResearch.WordTrace]
  refine ⟨1359202682995383948648925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1812270243993845264865233 1359202682995383948648925)
  ·
    refine ⟨509701006123268980743347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1359202682995383948648925 509701006123268980743347)
    ·
      refine ⟨764551509184903471115021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 509701006123268980743347 764551509184903471115021)
      ·
        refine ⟨286706815944338801668133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 764551509184903471115021 286706815944338801668133)
        ·
          refine ⟨53757527989563525312775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 286706815944338801668133 53757527989563525312775)
          ·
            refine ⟨80636291984345287969163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53757527989563525312775 80636291984345287969163)
            ·
              refine ⟨120954437976517931953745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80636291984345287969163 120954437976517931953745)
              ·
                refine ⟨90715828482388448965309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 120954437976517931953745 90715828482388448965309)
                ·
                  refine ⟨34018435680895668361991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 90715828482388448965309 34018435680895668361991)
                  ·
                    rfl

theorem cell20_74532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 2, 3].length) (baseStart_74532 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_74532 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_74532 prefixEnd_74532 := by exact prefixLift 74532
  have htrace : WordTrace (prefixWord ++ tailWord_74532) baseStart_74532 baseEnd_74532 := by
    simpa [prefixWord, tailWord_74532, baseEnd_74532] using wordTrace_append hprefix tailTrace_74532
  have hstable : (prefixWord ++ tailWord_74532).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74532).length < 2 ^ (prefixWord ++ tailWord_74532).sum := by decide
  have hdescent : baseEnd_74532 < baseStart_74532 := by decide
  rcases family_descends (prefixWord ++ tailWord_74532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74533 : List Nat := [1, 3, 1, 2, 3, 1, 9]
def baseStart_74533 : Nat := 118140960795 + 74533 * 2 ^ 59
def prefixEnd_74533 : Nat := 4983230072969 + 3 ^ 40 * 74533 * 2
def baseEnd_74533 : Nat := 3779876900904901036517

theorem tailTrace_74533 : CollatzResearch.WordTrace tailWord_74533 prefixEnd_74533 3779876900904901036517 := by
  unfold tailWord_74533
  simp only [CollatzResearch.WordTrace]
  refine ⟨2718441838987145068084253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1812294559324763378722835 2718441838987145068084253)
  ·
    refine ⟨1019415689620179400531595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2718441838987145068084253 1019415689620179400531595)
    ·
      refine ⟨1529123534430269100797393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1019415689620179400531595 1529123534430269100797393)
      ·
        refine ⟨1146842650822701825598045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1529123534430269100797393 1146842650822701825598045)
        ·
          refine ⟨430065994058513184599267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1146842650822701825598045 430065994058513184599267)
          ·
            refine ⟨645098991087769776898901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 430065994058513184599267 645098991087769776898901)
            ·
              refine ⟨3779876900904901036517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 645098991087769776898901 3779876900904901036517)
              ·
                rfl

theorem cell20_74533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 9].length) (baseStart_74533 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_74533 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_74533 prefixEnd_74533 := by exact prefixLift 74533
  have htrace : WordTrace (prefixWord ++ tailWord_74533) baseStart_74533 baseEnd_74533 := by
    simpa [prefixWord, tailWord_74533, baseEnd_74533] using wordTrace_append hprefix tailTrace_74533
  have hstable : (prefixWord ++ tailWord_74533).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74533).length < 2 ^ (prefixWord ++ tailWord_74533).sum := by decide
  have hdescent : baseEnd_74533 < baseStart_74533 := by decide
  rcases family_descends (prefixWord ++ tailWord_74533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74573 : List Nat := [1, 6, 1, 2, 3, 1, 1, 3, 2]
def baseStart_74573 : Nat := 118140960795 + 74573 * 2 ^ 59
def prefixEnd_74573 : Nat := 4983230072969 + 3 ^ 40 * 74573 * 2
def baseEnd_74573 : Nat := 34037149198081747995157

theorem tailTrace_74573 : CollatzResearch.WordTrace tailWord_74573 prefixEnd_74573 34037149198081747995157 := by
  unfold tailWord_74573
  simp only [CollatzResearch.WordTrace]
  refine ⟨2719900758842231899540373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1813267172561487933026915 2719900758842231899540373)
  ·
    refine ⟨127495348070729620290955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 2719900758842231899540373 127495348070729620290955)
    ·
      refine ⟨191243022106094430436433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127495348070729620290955 191243022106094430436433)
      ·
        refine ⟨143432266579570822827325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191243022106094430436433 143432266579570822827325)
        ·
          refine ⟨53787099967339058560247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 143432266579570822827325 53787099967339058560247)
          ·
            refine ⟨80680649951008587840371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53787099967339058560247 80680649951008587840371)
            ·
              refine ⟨121020974926512881760557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80680649951008587840371 121020974926512881760557)
              ·
                refine ⟨45382865597442330660209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 121020974926512881760557 45382865597442330660209)
                ·
                  refine ⟨34037149198081747995157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45382865597442330660209 34037149198081747995157)
                  ·
                    rfl

theorem cell20_74573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_74573 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_74573 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_74573 prefixEnd_74573 := by exact prefixLift 74573
  have htrace : WordTrace (prefixWord ++ tailWord_74573) baseStart_74573 baseEnd_74573 := by
    simpa [prefixWord, tailWord_74573, baseEnd_74573] using wordTrace_append hprefix tailTrace_74573
  have hstable : (prefixWord ++ tailWord_74573).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74573).length < 2 ^ (prefixWord ++ tailWord_74573).sum := by decide
  have hdescent : baseEnd_74573 < baseStart_74573 := by decide
  rcases family_descends (prefixWord ++ tailWord_74573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74577 : List Nat := [1, 2, 2, 1, 6, 2, 1, 3, 2]
def baseStart_74577 : Nat := 118140960795 + 74577 * 2 ^ 59
def prefixEnd_74577 : Nat := 4983230072969 + 3 ^ 40 * 74577 * 2
def baseEnd_74577 : Nat := 34038974907075511861807

theorem tailTrace_74577 : CollatzResearch.WordTrace tailWord_74577 prefixEnd_74577 34038974907075511861807 := by
  unfold tailWord_74577
  simp only [CollatzResearch.WordTrace]
  refine ⟨2720046650827740582685985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1813364433885160388457323 2720046650827740582685985)
  ·
    refine ⟨2040034988120805437014489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2720046650827740582685985 2040034988120805437014489)
    ·
      refine ⟨1530026241090604077760867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2040034988120805437014489 1530026241090604077760867)
      ·
        refine ⟨2295039361635906116641301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1530026241090604077760867 2295039361635906116641301)
        ·
          refine ⟨107579970076683099217561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 2295039361635906116641301 107579970076683099217561)
          ·
            refine ⟨80684977557512324413171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107579970076683099217561 80684977557512324413171)
            ·
              refine ⟨121027466336268486619757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80684977557512324413171 121027466336268486619757)
              ·
                refine ⟨45385299876100682482409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 121027466336268486619757 45385299876100682482409)
                ·
                  refine ⟨34038974907075511861807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45385299876100682482409 34038974907075511861807)
                  ·
                    rfl

theorem cell20_74577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 3, 2].length) (baseStart_74577 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_74577 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_74577 prefixEnd_74577 := by exact prefixLift 74577
  have htrace : WordTrace (prefixWord ++ tailWord_74577) baseStart_74577 baseEnd_74577 := by
    simpa [prefixWord, tailWord_74577, baseEnd_74577] using wordTrace_append hprefix tailTrace_74577
  have hstable : (prefixWord ++ tailWord_74577).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74577).length < 2 ^ (prefixWord ++ tailWord_74577).sum := by decide
  have hdescent : baseEnd_74577 < baseStart_74577 := by decide
  rcases family_descends (prefixWord ++ tailWord_74577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74588 : List Nat := [2, 2, 4, 2, 1, 1, 8]
def baseStart_74588 : Nat := 118140960795 + 74588 * 2 ^ 59
def prefixEnd_74588 : Nat := 4983230072969 + 3 ^ 40 * 74588 * 2
def baseEnd_74588 : Nat := 3782666178534262499455

theorem tailTrace_74588 : CollatzResearch.WordTrace tailWord_74588 prefixEnd_74588 3782666178534262499455 := by
  unfold tailWord_74588
  simp only [CollatzResearch.WordTrace]
  refine ⟨1360223926893944730668209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1813631902525259640890945 1360223926893944730668209)
  ·
    refine ⟨1020167945170458548001157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1360223926893944730668209 1020167945170458548001157)
    ·
      refine ⟨191281489719460977750217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1020167945170458548001157 191281489719460977750217)
      ·
        refine ⟨143461117289595733312663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191281489719460977750217 143461117289595733312663)
        ·
          refine ⟨215191675934393599968995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143461117289595733312663 215191675934393599968995)
          ·
            refine ⟨322787513901590399953493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215191675934393599968995 322787513901590399953493)
            ·
              refine ⟨3782666178534262499455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 322787513901590399953493 3782666178534262499455)
              ·
                rfl

theorem cell20_74588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 8].length) (baseStart_74588 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_74588 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_74588 prefixEnd_74588 := by exact prefixLift 74588
  have htrace : WordTrace (prefixWord ++ tailWord_74588) baseStart_74588 baseEnd_74588 := by
    simpa [prefixWord, tailWord_74588, baseEnd_74588] using wordTrace_append hprefix tailTrace_74588
  have hstable : (prefixWord ++ tailWord_74588).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74588).length < 2 ^ (prefixWord ++ tailWord_74588).sum := by decide
  have hdescent : baseEnd_74588 < baseStart_74588 := by decide
  rcases family_descends (prefixWord ++ tailWord_74588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74594 : List Nat := [3, 3, 2, 1, 3, 1, 3, 2, 2]
def baseStart_74594 : Nat := 118140960795 + 74594 * 2 ^ 59
def prefixEnd_74594 : Nat := 4983230072969 + 3 ^ 40 * 74594 * 2
def baseEnd_74594 : Nat := 34046734170299008295071

theorem tailTrace_74594 : CollatzResearch.WordTrace tailWord_74594 prefixEnd_74594 34046734170299008295071 := by
  unfold tailWord_74594
  simp only [CollatzResearch.WordTrace]
  refine ⟨680166672941538121513709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1813777794510768324036557 680166672941538121513709)
  ·
    refine ⟨255062502353076795567641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 680166672941538121513709 255062502353076795567641)
    ·
      refine ⟨191296876764807596675731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 255062502353076795567641 191296876764807596675731)
      ·
        refine ⟨286945315147211395013597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191296876764807596675731 286945315147211395013597)
        ·
          refine ⟨107604493180204273130099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 286945315147211395013597 107604493180204273130099)
          ·
            refine ⟨161406739770306409695149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107604493180204273130099 161406739770306409695149)
            ·
              refine ⟨60527527413864903635681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 161406739770306409695149 60527527413864903635681)
              ·
                refine ⟨45395645560398677726761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60527527413864903635681 45395645560398677726761)
                ·
                  refine ⟨34046734170299008295071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45395645560398677726761 34046734170299008295071)
                  ·
                    rfl

theorem cell20_74594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 3, 2, 2].length) (baseStart_74594 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_74594 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_74594 prefixEnd_74594 := by exact prefixLift 74594
  have htrace : WordTrace (prefixWord ++ tailWord_74594) baseStart_74594 baseEnd_74594 := by
    simpa [prefixWord, tailWord_74594, baseEnd_74594] using wordTrace_append hprefix tailTrace_74594
  have hstable : (prefixWord ++ tailWord_74594).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74594).length < 2 ^ (prefixWord ++ tailWord_74594).sum := by decide
  have hdescent : baseEnd_74594 < baseStart_74594 := by decide
  rcases family_descends (prefixWord ++ tailWord_74594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74595 : List Nat := [1, 1, 1, 5, 3, 1, 2, 1, 5]
def baseStart_74595 : Nat := 118140960795 + 74595 * 2 ^ 59
def prefixEnd_74595 : Nat := 4983230072969 + 3 ^ 40 * 74595 * 2
def baseEnd_74595 : Nat := 34047190597547449261733

theorem tailTrace_74595 : CollatzResearch.WordTrace tailWord_74595 prefixEnd_74595 34047190597547449261733 := by
  unfold tailWord_74595
  simp only [CollatzResearch.WordTrace]
  refine ⟨2720703164762529656841239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1813802109841686437894159 2720703164762529656841239)
  ·
    refine ⟨4081054747143794485261859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2720703164762529656841239 4081054747143794485261859)
    ·
      refine ⟨6121582120715691727892789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4081054747143794485261859 6121582120715691727892789)
      ·
        refine ⟨573898323817096099489949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6121582120715691727892789 573898323817096099489949)
        ·
          refine ⟨215211871431411037308731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 573898323817096099489949 215211871431411037308731)
          ·
            refine ⟨322817807147116555963097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215211871431411037308731 322817807147116555963097)
            ·
              refine ⟨242113355360337416972323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 322817807147116555963097 242113355360337416972323)
              ·
                refine ⟨363170033040506125458485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 242113355360337416972323 363170033040506125458485)
                ·
                  refine ⟨34047190597547449261733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 363170033040506125458485 34047190597547449261733)
                  ·
                    rfl

theorem cell20_74595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 1, 5].length) (baseStart_74595 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_74595 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_74595 prefixEnd_74595 := by exact prefixLift 74595
  have htrace : WordTrace (prefixWord ++ tailWord_74595) baseStart_74595 baseEnd_74595 := by
    simpa [prefixWord, tailWord_74595, baseEnd_74595] using wordTrace_append hprefix tailTrace_74595
  have hstable : (prefixWord ++ tailWord_74595).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74595).length < 2 ^ (prefixWord ++ tailWord_74595).sum := by decide
  have hdescent : baseEnd_74595 < baseStart_74595 := by decide
  rcases family_descends (prefixWord ++ tailWord_74595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74609 : List Nat := [1, 2, 2, 2, 1, 4, 1, 7]
def baseStart_74609 : Nat := 118140960795 + 74609 * 2 ^ 59
def prefixEnd_74609 : Nat := 4983230072969 + 3 ^ 40 * 74609 * 2
def baseEnd_74609 : Nat := 11351193526341874265003

theorem tailTrace_74609 : CollatzResearch.WordTrace tailWord_74609 prefixEnd_74609 11351193526341874265003 := by
  unfold tailWord_74609
  simp only [CollatzResearch.WordTrace]
  refine ⟨2721213786711810047850881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1814142524474540031900587 2721213786711810047850881)
  ·
    refine ⟨2040910340033857535888161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2721213786711810047850881 2040910340033857535888161)
    ·
      refine ⟨1530682755025393151916121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2040910340033857535888161 1530682755025393151916121)
      ·
        refine ⟨1148012066269044863937091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1530682755025393151916121 1148012066269044863937091)
        ·
          refine ⟨1722018099403567295905637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1148012066269044863937091 1722018099403567295905637)
          ·
            refine ⟨322878393638168867982307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1722018099403567295905637 322878393638168867982307)
            ·
              refine ⟨484317590457253301973461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 322878393638168867982307 484317590457253301973461)
              ·
                refine ⟨11351193526341874265003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 484317590457253301973461 11351193526341874265003)
                ·
                  rfl

theorem cell20_74609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 7].length) (baseStart_74609 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_74609 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_74609 prefixEnd_74609 := by exact prefixLift 74609
  have htrace : WordTrace (prefixWord ++ tailWord_74609) baseStart_74609 baseEnd_74609 := by
    simpa [prefixWord, tailWord_74609, baseEnd_74609] using wordTrace_append hprefix tailTrace_74609
  have hstable : (prefixWord ++ tailWord_74609).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74609).length < 2 ^ (prefixWord ++ tailWord_74609).sum := by decide
  have hdescent : baseEnd_74609 < baseStart_74609 := by decide
  rcases family_descends (prefixWord ++ tailWord_74609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74616 : List Nat := [2, 1, 2, 1, 1, 1, 1, 4, 7]
def baseStart_74616 : Nat := 118140960795 + 74616 * 2 ^ 59
def prefixEnd_74616 : Nat := 4983230072969 + 3 ^ 40 * 74616 * 2
def baseEnd_74616 : Nat := 34056775569764709561647

theorem tailTrace_74616 : CollatzResearch.WordTrace tailWord_74616 prefixEnd_74616 34056775569764709561647 := by
  unfold tailWord_74616
  simp only [CollatzResearch.WordTrace]
  refine ⟨1360734548843225121677851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1814312731790966828903801 1360734548843225121677851)
  ·
    refine ⟨2041101823264837682516777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1360734548843225121677851 2041101823264837682516777)
    ·
      refine ⟨1530826367448628261887583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2041101823264837682516777 1530826367448628261887583)
      ·
        refine ⟨2296239551172942392831375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1530826367448628261887583 2296239551172942392831375)
        ·
          refine ⟨3444359326759413589247063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2296239551172942392831375 3444359326759413589247063)
          ·
            refine ⟨5166538990139120383870595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3444359326759413589247063 5166538990139120383870595)
            ·
              refine ⟨7749808485208680575805893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5166538990139120383870595 7749808485208680575805893)
              ·
                refine ⟨1453089090976627607963605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7749808485208680575805893 1453089090976627607963605)
                ·
                  refine ⟨34056775569764709561647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1453089090976627607963605 34056775569764709561647)
                  ·
                    rfl

theorem cell20_74616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 7].length) (baseStart_74616 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_74616 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_74616 prefixEnd_74616 := by exact prefixLift 74616
  have htrace : WordTrace (prefixWord ++ tailWord_74616) baseStart_74616 baseEnd_74616 := by
    simpa [prefixWord, tailWord_74616, baseEnd_74616] using wordTrace_append hprefix tailTrace_74616
  have hstable : (prefixWord ++ tailWord_74616).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74616).length < 2 ^ (prefixWord ++ tailWord_74616).sum := by decide
  have hdescent : baseEnd_74616 < baseStart_74616 := by decide
  rcases family_descends (prefixWord ++ tailWord_74616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74646 : List Nat := [5, 3, 1, 1, 1, 1, 1, 4, 3]
def baseStart_74646 : Nat := 118140960795 + 74646 * 2 ^ 59
def prefixEnd_74646 : Nat := 4983230072969 + 3 ^ 40 * 74646 * 2
def baseEnd_74646 : Nat := 34070468387217938561525

theorem tailTrace_74646 : CollatzResearch.WordTrace tailWord_74646 prefixEnd_74646 34070468387217938561525 := by
  unfold tailWord_74646
  simp only [CollatzResearch.WordTrace]
  refine ⟨170160205473610335434237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1815042191718510244631861 170160205473610335434237)
  ·
    refine ⟨63810077052603875787839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170160205473610335434237 63810077052603875787839)
    ·
      refine ⟨95715115578905813681759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63810077052603875787839 95715115578905813681759)
      ·
        refine ⟨143572673368358720522639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95715115578905813681759 143572673368358720522639)
        ·
          refine ⟨215359010052538080783959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143572673368358720522639 215359010052538080783959)
          ·
            refine ⟨323038515078807121175939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215359010052538080783959 323038515078807121175939)
            ·
              refine ⟨484557772618210681763909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 323038515078807121175939 484557772618210681763909)
              ·
                refine ⟨90854582365914502830733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 484557772618210681763909 90854582365914502830733)
                ·
                  refine ⟨34070468387217938561525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 90854582365914502830733 34070468387217938561525)
                  ·
                    rfl

theorem cell20_74646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_74646 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_74646 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_74646 prefixEnd_74646 := by exact prefixLift 74646
  have htrace : WordTrace (prefixWord ++ tailWord_74646) baseStart_74646 baseEnd_74646 := by
    simpa [prefixWord, tailWord_74646, baseEnd_74646] using wordTrace_append hprefix tailTrace_74646
  have hstable : (prefixWord ++ tailWord_74646).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74646).length < 2 ^ (prefixWord ++ tailWord_74646).sum := by decide
  have hdescent : baseEnd_74646 < baseStart_74646 := by decide
  rcases family_descends (prefixWord ++ tailWord_74646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74695 : List Nat := [1, 1, 4, 1, 1, 2, 3, 5, 2]
def baseStart_74695 : Nat := 118140960795 + 74695 * 2 ^ 59
def prefixEnd_74695 : Nat := 4983230072969 + 3 ^ 40 * 74695 * 2
def baseEnd_74695 : Nat := 34092833322391545927991

theorem tailTrace_74695 : CollatzResearch.WordTrace tailWord_74695 prefixEnd_74695 34092833322391545927991 := by
  unfold tailWord_74695
  simp only [CollatzResearch.WordTrace]
  refine ⟨2724350464400246735481539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1816233642933497823654359 2724350464400246735481539)
  ·
    refine ⟨4086525696600370103222309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2724350464400246735481539 4086525696600370103222309)
    ·
      refine ⟨766223568112569394354183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4086525696600370103222309 766223568112569394354183)
      ·
        refine ⟨1149335352168854091531275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 766223568112569394354183 1149335352168854091531275)
        ·
          refine ⟨1724003028253281137296913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1149335352168854091531275 1724003028253281137296913)
          ·
            refine ⟨1293002271189960852972685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1724003028253281137296913 1293002271189960852972685)
            ·
              refine ⟨484875851696235319864757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1293002271189960852972685 484875851696235319864757)
              ·
                refine ⟨45457111096522061237321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 484875851696235319864757 45457111096522061237321)
                ·
                  refine ⟨34092833322391545927991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45457111096522061237321 34092833322391545927991)
                  ·
                    rfl

theorem cell20_74695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 5, 2].length) (baseStart_74695 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_74695 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_74695 prefixEnd_74695 := by exact prefixLift 74695
  have htrace : WordTrace (prefixWord ++ tailWord_74695) baseStart_74695 baseEnd_74695 := by
    simpa [prefixWord, tailWord_74695, baseEnd_74695] using wordTrace_append hprefix tailTrace_74695
  have hstable : (prefixWord ++ tailWord_74695).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74695).length < 2 ^ (prefixWord ++ tailWord_74695).sum := by decide
  have hdescent : baseEnd_74695 < baseStart_74695 := by decide
  rcases family_descends (prefixWord ++ tailWord_74695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74722 : List Nat := [3, 3, 3, 1, 1, 2, 3, 1, 3]
def baseStart_74722 : Nat := 118140960795 + 74722 * 2 ^ 59
def prefixEnd_74722 : Nat := 4983230072969 + 3 ^ 40 * 74722 * 2
def baseEnd_74722 : Nat := 34105156858099452027881

theorem tailTrace_74722 : CollatzResearch.WordTrace tailWord_74722 prefixEnd_74722 34105156858099452027881 := by
  unfold tailWord_74722
  simp only [CollatzResearch.WordTrace]
  refine ⟨681333808825607586678605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1816890156868286897809613 681333808825607586678605)
  ·
    refine ⟨255500178309602845004477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 681333808825607586678605 255500178309602845004477)
    ·
      refine ⟨95812566866101066876679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 255500178309602845004477 95812566866101066876679)
      ·
        refine ⟨143718850299151600315019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95812566866101066876679 143718850299151600315019)
        ·
          refine ⟨215578275448727400472529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143718850299151600315019 215578275448727400472529)
          ·
            refine ⟨161683706586545550354397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 215578275448727400472529 161683706586545550354397)
            ·
              refine ⟨60631389969954581382899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 161683706586545550354397 60631389969954581382899)
              ·
                refine ⟨90947084954931872074349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60631389969954581382899 90947084954931872074349)
                ·
                  refine ⟨34105156858099452027881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 90947084954931872074349 34105156858099452027881)
                  ·
                    rfl

theorem cell20_74722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_74722 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_74722 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_74722 prefixEnd_74722 := by exact prefixLift 74722
  have htrace : WordTrace (prefixWord ++ tailWord_74722) baseStart_74722 baseEnd_74722 := by
    simpa [prefixWord, tailWord_74722, baseEnd_74722] using wordTrace_append hprefix tailTrace_74722
  have hstable : (prefixWord ++ tailWord_74722).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74722).length < 2 ^ (prefixWord ++ tailWord_74722).sum := by decide
  have hdescent : baseEnd_74722 < baseStart_74722 := by decide
  rcases family_descends (prefixWord ++ tailWord_74722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74723 : List Nat := [1, 1, 1, 6, 1, 1, 2, 7]
def baseStart_74723 : Nat := 118140960795 + 74723 * 2 ^ 59
def prefixEnd_74723 : Nat := 4983230072969 + 3 ^ 40 * 74723 * 2
def baseEnd_74723 : Nat := 11368537761782630998181

theorem tailTrace_74723 : CollatzResearch.WordTrace tailWord_74723 prefixEnd_74723 11368537761782630998181 := by
  unfold tailWord_74723
  simp only [CollatzResearch.WordTrace]
  refine ⟨2725371708298807517500823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1816914472199205011667215 2725371708298807517500823)
  ·
    refine ⟨4088057562448211276251235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2725371708298807517500823 4088057562448211276251235)
    ·
      refine ⟨6132086343672316914376853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4088057562448211276251235 6132086343672316914376853)
      ·
        refine ⟨287441547359639855361415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 6132086343672316914376853 287441547359639855361415)
        ·
          refine ⟨431162321039459783042123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 287441547359639855361415 431162321039459783042123)
          ·
            refine ⟨646743481559189674563185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 431162321039459783042123 646743481559189674563185)
            ·
              refine ⟨485057611169392255922389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 646743481559189674563185 485057611169392255922389)
              ·
                refine ⟨11368537761782630998181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 485057611169392255922389 11368537761782630998181)
                ·
                  rfl

theorem cell20_74723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 7].length) (baseStart_74723 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_74723 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_74723 prefixEnd_74723 := by exact prefixLift 74723
  have htrace : WordTrace (prefixWord ++ tailWord_74723) baseStart_74723 baseEnd_74723 := by
    simpa [prefixWord, tailWord_74723, baseEnd_74723] using wordTrace_append hprefix tailTrace_74723
  have hstable : (prefixWord ++ tailWord_74723).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74723).length < 2 ^ (prefixWord ++ tailWord_74723).sum := by decide
  have hdescent : baseEnd_74723 < baseStart_74723 := by decide
  rcases family_descends (prefixWord ++ tailWord_74723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74822 : List Nat := [6, 1, 1, 1, 1, 2, 4, 2, 2]
def baseStart_74822 : Nat := 118140960795 + 74822 * 2 ^ 59
def prefixEnd_74822 : Nat := 4983230072969 + 3 ^ 40 * 74822 * 2
def baseEnd_74822 : Nat := 34150799582943548694139

theorem tailTrace_74822 : CollatzResearch.WordTrace tailWord_74822 prefixEnd_74822 34150799582943548694139 := by
  unfold tailWord_74822
  simp only [CollatzResearch.WordTrace]
  refine ⟨85280704216879607042335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 1819321689960098283569813 85280704216879607042335)
  ·
    refine ⟨127921056325319410563503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85280704216879607042335 127921056325319410563503)
    ·
      refine ⟨191881584487979115845255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127921056325319410563503 191881584487979115845255)
      ·
        refine ⟨287822376731968673767883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191881584487979115845255 287822376731968673767883)
        ·
          refine ⟨431733565097953010651825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 287822376731968673767883 431733565097953010651825)
          ·
            refine ⟨323800173823464757988869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 431733565097953010651825 323800173823464757988869)
            ·
              refine ⟨60712532591899642122913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 323800173823464757988869 60712532591899642122913)
              ·
                refine ⟨45534399443924731592185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60712532591899642122913 45534399443924731592185)
                ·
                  refine ⟨34150799582943548694139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45534399443924731592185 34150799582943548694139)
                  ·
                    rfl

theorem cell20_74822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_74822 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_74822 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_74822 prefixEnd_74822 := by exact prefixLift 74822
  have htrace : WordTrace (prefixWord ++ tailWord_74822) baseStart_74822 baseEnd_74822 := by
    simpa [prefixWord, tailWord_74822, baseEnd_74822] using wordTrace_append hprefix tailTrace_74822
  have hstable : (prefixWord ++ tailWord_74822).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74822).length < 2 ^ (prefixWord ++ tailWord_74822).sum := by decide
  have hdescent : baseEnd_74822 < baseStart_74822 := by decide
  rcases family_descends (prefixWord ++ tailWord_74822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74823 : List Nat := [1, 1, 4, 1, 3, 2, 1, 4, 3]
def baseStart_74823 : Nat := 118140960795 + 74823 * 2 ^ 59
def prefixEnd_74823 : Nat := 4983230072969 + 3 ^ 40 * 74823 * 2
def baseEnd_74823 : Nat := 34151256010191989660801

theorem tailTrace_74823 : CollatzResearch.WordTrace tailWord_74823 prefixEnd_74823 34151256010191989660801 := by
  unfold tailWord_74823
  simp only [CollatzResearch.WordTrace]
  refine ⟨2729019007936524596141123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1819346005291016397427415 2729019007936524596141123)
  ·
    refine ⟨4093528511904786894211685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2729019007936524596141123 4093528511904786894211685)
    ·
      refine ⟨767536595982147542664691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4093528511904786894211685 767536595982147542664691)
      ·
        refine ⟨1151304893973221313997037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 767536595982147542664691 1151304893973221313997037)
        ·
          refine ⟨431739335239957992748889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1151304893973221313997037 431739335239957992748889)
          ·
            refine ⟨323804501429968494561667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 431739335239957992748889 323804501429968494561667)
            ·
              refine ⟨485706752144952741842501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 323804501429968494561667 485706752144952741842501)
              ·
                refine ⟨91070016027178639095469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 485706752144952741842501 91070016027178639095469)
                ·
                  refine ⟨34151256010191989660801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 91070016027178639095469 34151256010191989660801)
                  ·
                    rfl

theorem cell20_74823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 4, 3].length) (baseStart_74823 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_74823 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_74823 prefixEnd_74823 := by exact prefixLift 74823
  have htrace : WordTrace (prefixWord ++ tailWord_74823) baseStart_74823 baseEnd_74823 := by
    simpa [prefixWord, tailWord_74823, baseEnd_74823] using wordTrace_append hprefix tailTrace_74823
  have hstable : (prefixWord ++ tailWord_74823).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74823).length < 2 ^ (prefixWord ++ tailWord_74823).sum := by decide
  have hdescent : baseEnd_74823 < baseStart_74823 := by decide
  rcases family_descends (prefixWord ++ tailWord_74823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74826 : List Nat := [3, 1, 2, 1, 1, 2, 6, 2, 2]
def baseStart_74826 : Nat := 118140960795 + 74826 * 2 ^ 59
def prefixEnd_74826 : Nat := 4983230072969 + 3 ^ 40 * 74826 * 2
def baseEnd_74826 : Nat := 34152625291937312560789

theorem tailTrace_74826 : CollatzResearch.WordTrace tailWord_74826 prefixEnd_74826 34152625291937312560789 := by
  unfold tailWord_74826
  simp only [CollatzResearch.WordTrace]
  refine ⟨682282106731414027125083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1819418951283770739000221 682282106731414027125083)
  ·
    refine ⟨1023423160097121040687625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 682282106731414027125083 1023423160097121040687625)
    ·
      refine ⟨767567370072840780515719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1023423160097121040687625 767567370072840780515719)
      ·
        refine ⟨1151351055109261170773579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 767567370072840780515719 1151351055109261170773579)
        ·
          refine ⟨1727026582663891756160369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1151351055109261170773579 1727026582663891756160369)
          ·
            refine ⟨1295269936997918817120277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1727026582663891756160369 1295269936997918817120277)
            ·
              refine ⟨60715778296777444552513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1295269936997918817120277 60715778296777444552513)
              ·
                refine ⟨45536833722583083414385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60715778296777444552513 45536833722583083414385)
                ·
                  refine ⟨34152625291937312560789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45536833722583083414385 34152625291937312560789)
                  ·
                    rfl

theorem cell20_74826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 6, 2, 2].length) (baseStart_74826 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_74826 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_74826 prefixEnd_74826 := by exact prefixLift 74826
  have htrace : WordTrace (prefixWord ++ tailWord_74826) baseStart_74826 baseEnd_74826 := by
    simpa [prefixWord, tailWord_74826, baseEnd_74826] using wordTrace_append hprefix tailTrace_74826
  have hstable : (prefixWord ++ tailWord_74826).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74826).length < 2 ^ (prefixWord ++ tailWord_74826).sum := by decide
  have hdescent : baseEnd_74826 < baseStart_74826 := by decide
  rcases family_descends (prefixWord ++ tailWord_74826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74830 : List Nat := [4, 1, 1, 1, 1, 3, 2, 3, 4]
def baseStart_74830 : Nat := 118140960795 + 74830 * 2 ^ 59
def prefixEnd_74830 : Nat := 4983230072969 + 3 ^ 40 * 74830 * 2
def baseEnd_74830 : Nat := 34154451000931076427439

theorem tailTrace_74830 : CollatzResearch.WordTrace tailWord_74830 prefixEnd_74830 34154451000931076427439 := by
  unfold tailWord_74830
  simp only [CollatzResearch.WordTrace]
  refine ⟨341159289863895598955743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1819516212607443194430629 341159289863895598955743)
  ·
    refine ⟨511738934795843398433615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 341159289863895598955743 511738934795843398433615)
    ·
      refine ⟨767608402193765097650423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 511738934795843398433615 767608402193765097650423)
      ·
        refine ⟨1151412603290647646475635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 767608402193765097650423 1151412603290647646475635)
        ·
          refine ⟨1727118904935971469713453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1151412603290647646475635 1727118904935971469713453)
          ·
            refine ⟨647669589350989301142545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1727118904935971469713453 647669589350989301142545)
            ·
              refine ⟨485752192013241975856909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 647669589350989301142545 485752192013241975856909)
              ·
                refine ⟨182157072004965740946341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 485752192013241975856909 182157072004965740946341)
                ·
                  refine ⟨34154451000931076427439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 182157072004965740946341 34154451000931076427439)
                  ·
                    rfl

theorem cell20_74830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_74830 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_74830 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_74830 prefixEnd_74830 := by exact prefixLift 74830
  have htrace : WordTrace (prefixWord ++ tailWord_74830) baseStart_74830 baseEnd_74830 := by
    simpa [prefixWord, tailWord_74830, baseEnd_74830] using wordTrace_append hprefix tailTrace_74830
  have hstable : (prefixWord ++ tailWord_74830).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74830).length < 2 ^ (prefixWord ++ tailWord_74830).sum := by decide
  have hdescent : baseEnd_74830 < baseStart_74830 := by decide
  rcases family_descends (prefixWord ++ tailWord_74830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74885 : List Nat := [1, 3, 1, 1, 6, 1, 2, 1, 4]
def baseStart_74885 : Nat := 118140960795 + 74885 * 2 ^ 59
def prefixEnd_74885 : Nat := 4983230072969 + 3 ^ 40 * 74885 * 2
def baseEnd_74885 : Nat := 34179554499595329593881

theorem tailTrace_74885 : CollatzResearch.WordTrace tailWord_74885 prefixEnd_74885 34179554499595329593881 := by
  unfold tailWord_74885
  simp only [CollatzResearch.WordTrace]
  refine ⟨2731280333711909184898109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1820853555807939456598739 2731280333711909184898109)
  ·
    refine ⟨1024230125141965944336791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2731280333711909184898109 1024230125141965944336791)
    ·
      refine ⟨1536345187712948916505187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1024230125141965944336791 1536345187712948916505187)
      ·
        refine ⟨2304517781569423374757781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1536345187712948916505187 2304517781569423374757781)
        ·
          refine ⟨108024271011066720691771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 2304517781569423374757781 108024271011066720691771)
          ·
            refine ⟨162036406516600081037657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108024271011066720691771 162036406516600081037657)
            ·
              refine ⟨121527304887450060778243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 162036406516600081037657 121527304887450060778243)
              ·
                refine ⟨182290957331175091167365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 121527304887450060778243 182290957331175091167365)
                ·
                  refine ⟨34179554499595329593881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 182290957331175091167365 34179554499595329593881)
                  ·
                    rfl

theorem cell20_74885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 1, 4].length) (baseStart_74885 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_74885 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_74885 prefixEnd_74885 := by exact prefixLift 74885
  have htrace : WordTrace (prefixWord ++ tailWord_74885) baseStart_74885 baseEnd_74885 := by
    simpa [prefixWord, tailWord_74885, baseEnd_74885] using wordTrace_append hprefix tailTrace_74885
  have hstable : (prefixWord ++ tailWord_74885).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74885).length < 2 ^ (prefixWord ++ tailWord_74885).sum := by decide
  have hdescent : baseEnd_74885 < baseStart_74885 := by decide
  rcases family_descends (prefixWord ++ tailWord_74885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74913 : List Nat := [1, 2, 3, 3, 1, 1, 3, 6]
def baseStart_74913 : Nat := 118140960795 + 74913 * 2 ^ 59
def prefixEnd_74913 : Nat := 4983230072969 + 3 ^ 40 * 74913 * 2
def baseEnd_74913 : Nat := 11397444820850558886811

theorem tailTrace_74913 : CollatzResearch.WordTrace tailWord_74913 prefixEnd_74913 11397444820850558886811 := by
  unfold tailWord_74913
  simp only [CollatzResearch.WordTrace]
  refine ⟨2732301577610469966917393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1821534385073646644611595 2732301577610469966917393)
  ·
    refine ⟨2049226183207852475188045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2732301577610469966917393 2049226183207852475188045)
    ·
      refine ⟨768459818702944678195517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2049226183207852475188045 768459818702944678195517)
      ·
        refine ⟨288172432013604254323319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 768459818702944678195517 288172432013604254323319)
        ·
          refine ⟨432258648020406381484979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 288172432013604254323319 432258648020406381484979)
          ·
            refine ⟨648387972030609572227469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 432258648020406381484979 648387972030609572227469)
            ·
              refine ⟨243145489511478589585301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 648387972030609572227469 243145489511478589585301)
              ·
                refine ⟨11397444820850558886811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 243145489511478589585301 11397444820850558886811)
                ·
                  rfl

theorem cell20_74913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 6].length) (baseStart_74913 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_74913 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_74913 prefixEnd_74913 := by exact prefixLift 74913
  have htrace : WordTrace (prefixWord ++ tailWord_74913) baseStart_74913 baseEnd_74913 := by
    simpa [prefixWord, tailWord_74913, baseEnd_74913] using wordTrace_append hprefix tailTrace_74913
  have hstable : (prefixWord ++ tailWord_74913).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74913).length < 2 ^ (prefixWord ++ tailWord_74913).sum := by decide
  have hdescent : baseEnd_74913 < baseStart_74913 := by decide
  rcases family_descends (prefixWord ++ tailWord_74913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74919 : List Nat := [1, 1, 6, 2, 1, 3, 1, 3, 2]
def baseStart_74919 : Nat := 118140960795 + 74919 * 2 ^ 59
def prefixEnd_74919 : Nat := 4983230072969 + 3 ^ 40 * 74919 * 2
def baseEnd_74919 : Nat := 34195073026042322460409

theorem tailTrace_74919 : CollatzResearch.WordTrace tailWord_74919 prefixEnd_74919 34195073026042322460409 := by
  unfold tailWord_74919
  simp only [CollatzResearch.WordTrace]
  refine ⟨2732520415588732991635811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1821680277059155327757207 2732520415588732991635811)
  ·
    refine ⟨4098780623383099487453717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2732520415588732991635811 4098780623383099487453717)
    ·
      refine ⟨192130341721082788474393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 4098780623383099487453717 192130341721082788474393)
      ·
        refine ⟨144097756290812091355795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192130341721082788474393 144097756290812091355795)
        ·
          refine ⟨216146634436218137033693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144097756290812091355795 216146634436218137033693)
          ·
            refine ⟨81054987913581801387635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 216146634436218137033693 81054987913581801387635)
            ·
              refine ⟨121582481870372702081453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81054987913581801387635 121582481870372702081453)
              ·
                refine ⟨45593430701389763280545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 121582481870372702081453 45593430701389763280545)
                ·
                  refine ⟨34195073026042322460409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45593430701389763280545 34195073026042322460409)
                  ·
                    rfl

theorem cell20_74919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 3, 2].length) (baseStart_74919 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_74919 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_74919 prefixEnd_74919 := by exact prefixLift 74919
  have htrace : WordTrace (prefixWord ++ tailWord_74919) baseStart_74919 baseEnd_74919 := by
    simpa [prefixWord, tailWord_74919, baseEnd_74919] using wordTrace_append hprefix tailTrace_74919
  have hstable : (prefixWord ++ tailWord_74919).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74919).length < 2 ^ (prefixWord ++ tailWord_74919).sum := by decide
  have hdescent : baseEnd_74919 < baseStart_74919 := by decide
  rcases family_descends (prefixWord ++ tailWord_74919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74927 : List Nat := [1, 1, 2, 1, 2, 3, 2, 2, 6]
def baseStart_74927 : Nat := 118140960795 + 74927 * 2 ^ 59
def prefixEnd_74927 : Nat := 4983230072969 + 3 ^ 40 * 74927 * 2
def baseEnd_74927 : Nat := 34198724444029850193709

theorem tailTrace_74927 : CollatzResearch.WordTrace tailWord_74927 prefixEnd_74927 34198724444029850193709 := by
  unfold tailWord_74927
  simp only [CollatzResearch.WordTrace]
  refine ⟨2732812199559750357927035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1821874799706500238618023 2732812199559750357927035)
  ·
    refine ⟨4099218299339625536890553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2732812199559750357927035 4099218299339625536890553)
    ·
      refine ⟨3074413724504719152667915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4099218299339625536890553 3074413724504719152667915)
      ·
        refine ⟨4611620586757078729001873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3074413724504719152667915 4611620586757078729001873)
        ·
          refine ⟨3458715440067809046751405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4611620586757078729001873 3458715440067809046751405)
          ·
            refine ⟨1297018290025428392531777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3458715440067809046751405 1297018290025428392531777)
            ·
              refine ⟨972763717519071294398833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1297018290025428392531777 972763717519071294398833)
              ·
                refine ⟨729572788139303470799125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 972763717519071294398833 729572788139303470799125)
                ·
                  refine ⟨34198724444029850193709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 729572788139303470799125 34198724444029850193709)
                  ·
                    rfl

theorem cell20_74927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 6].length) (baseStart_74927 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_74927 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_74927 prefixEnd_74927 := by exact prefixLift 74927
  have htrace : WordTrace (prefixWord ++ tailWord_74927) baseStart_74927 baseEnd_74927 := by
    simpa [prefixWord, tailWord_74927, baseEnd_74927] using wordTrace_append hprefix tailTrace_74927
  have hstable : (prefixWord ++ tailWord_74927).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74927).length < 2 ^ (prefixWord ++ tailWord_74927).sum := by decide
  have hdescent : baseEnd_74927 < baseStart_74927 := by decide
  rcases family_descends (prefixWord ++ tailWord_74927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74946 : List Nat := [3, 5, 1, 1, 3, 1, 2, 1, 3]
def baseStart_74946 : Nat := 118140960795 + 74946 * 2 ^ 59
def prefixEnd_74946 : Nat := 4983230072969 + 3 ^ 40 * 74946 * 2
def baseEnd_74946 : Nat := 34207396561750228560299

theorem tailTrace_74946 : CollatzResearch.WordTrace tailWord_74946 prefixEnd_74946 34207396561750228560299 := by
  unfold tailWord_74946
  simp only [CollatzResearch.WordTrace]
  refine ⟨683376296622729150717173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1822336790993944401912461 683376296622729150717173)
  ·
    refine ⟨64066527808380857879735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 683376296622729150717173 64066527808380857879735)
    ·
      refine ⟨96099791712571286819603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64066527808380857879735 96099791712571286819603)
      ·
        refine ⟨144149687568856930229405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96099791712571286819603 144149687568856930229405)
        ·
          refine ⟨54056132838321348836027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 144149687568856930229405 54056132838321348836027)
          ·
            refine ⟨81084199257482023254041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54056132838321348836027 81084199257482023254041)
            ·
              refine ⟨60813149443111517440531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81084199257482023254041 60813149443111517440531)
              ·
                refine ⟨91219724164667276160797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60813149443111517440531 91219724164667276160797)
                ·
                  refine ⟨34207396561750228560299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 91219724164667276160797 34207396561750228560299)
                  ·
                    rfl

theorem cell20_74946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_74946 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_74946 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_74946 prefixEnd_74946 := by exact prefixLift 74946
  have htrace : WordTrace (prefixWord ++ tailWord_74946) baseStart_74946 baseEnd_74946 := by
    simpa [prefixWord, tailWord_74946, baseEnd_74946] using wordTrace_append hprefix tailTrace_74946
  have hstable : (prefixWord ++ tailWord_74946).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74946).length < 2 ^ (prefixWord ++ tailWord_74946).sum := by decide
  have hdescent : baseEnd_74946 < baseStart_74946 := by decide
  rcases family_descends (prefixWord ++ tailWord_74946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74954 : List Nat := [3, 1, 2, 1, 3, 2, 4, 1, 3]
def baseStart_74954 : Nat := 118140960795 + 74954 * 2 ^ 59
def prefixEnd_74954 : Nat := 4983230072969 + 3 ^ 40 * 74954 * 2
def baseEnd_74954 : Nat := 34211047979737756293599

theorem tailTrace_74954 : CollatzResearch.WordTrace tailWord_74954 prefixEnd_74954 34211047979737756293599 := by
  unfold tailWord_74954
  simp only [CollatzResearch.WordTrace]
  refine ⟨683449242615483492289979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1822531313641289312773277 683449242615483492289979)
  ·
    refine ⟨1025173863923225238434969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 683449242615483492289979 1025173863923225238434969)
    ·
      refine ⟨768880397942418928826227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1025173863923225238434969 768880397942418928826227)
      ·
        refine ⟨1153320596913628393239341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 768880397942418928826227 1153320596913628393239341)
        ·
          refine ⟨432495223842610647464753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1153320596913628393239341 432495223842610647464753)
          ·
            refine ⟨324371417881957985598565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 432495223842610647464753 324371417881957985598565)
            ·
              refine ⟨60819640852867122299731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 324371417881957985598565 60819640852867122299731)
              ·
                refine ⟨91229461279300683449597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60819640852867122299731 91229461279300683449597)
                ·
                  refine ⟨34211047979737756293599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 91229461279300683449597 34211047979737756293599)
                  ·
                    rfl

theorem cell20_74954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 4, 1, 3].length) (baseStart_74954 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_74954 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_74954 prefixEnd_74954 := by exact prefixLift 74954
  have htrace : WordTrace (prefixWord ++ tailWord_74954) baseStart_74954 baseEnd_74954 := by
    simpa [prefixWord, tailWord_74954, baseEnd_74954] using wordTrace_append hprefix tailTrace_74954
  have hstable : (prefixWord ++ tailWord_74954).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74954).length < 2 ^ (prefixWord ++ tailWord_74954).sum := by decide
  have hdescent : baseEnd_74954 < baseStart_74954 := by decide
  rcases family_descends (prefixWord ++ tailWord_74954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74989 : List Nat := [1, 5, 1, 2, 2, 9]
def baseStart_74989 : Nat := 118140960795 + 74989 * 2 ^ 59
def prefixEnd_74989 : Nat := 4983230072969 + 3 ^ 40 * 74989 * 2
def baseEnd_74989 : Nat := 1267667516053081115807

theorem tailTrace_74989 : CollatzResearch.WordTrace tailWord_74989 prefixEnd_74989 1267667516053081115807 := by
  unfold tailWord_74989
  simp only [CollatzResearch.WordTrace]
  refine ⟨2735073525335134946684021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1823382350223423297789347 2735073525335134946684021)
  ·
    refine ⟨256413143000168901251627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2735073525335134946684021 256413143000168901251627)
    ·
      refine ⟨384619714500253351877441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256413143000168901251627 384619714500253351877441)
      ·
        refine ⟨288464785875190013908081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 384619714500253351877441 288464785875190013908081)
        ·
          refine ⟨216348589406392510431061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 288464785875190013908081 216348589406392510431061)
          ·
            refine ⟨1267667516053081115807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 216348589406392510431061 1267667516053081115807)
            ·
              rfl

theorem cell20_74989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 9].length) (baseStart_74989 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_74989 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_74989 prefixEnd_74989 := by exact prefixLift 74989
  have htrace : WordTrace (prefixWord ++ tailWord_74989) baseStart_74989 baseEnd_74989 := by
    simpa [prefixWord, tailWord_74989, baseEnd_74989] using wordTrace_append hprefix tailTrace_74989
  have hstable : (prefixWord ++ tailWord_74989).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74989).length < 2 ^ (prefixWord ++ tailWord_74989).sum := by decide
  have hdescent : baseEnd_74989 < baseStart_74989 := by decide
  rcases family_descends (prefixWord ++ tailWord_74989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75006 : List Nat := [4, 2, 2, 1, 1, 2, 3, 5]
def baseStart_75006 : Nat := 118140960795 + 75006 * 2 ^ 59
def prefixEnd_75006 : Nat := 4983230072969 + 3 ^ 40 * 75006 * 2
def baseEnd_75006 : Nat := 11411594065552228853351

theorem tailTrace_75006 : CollatzResearch.WordTrace tailWord_75006 prefixEnd_75006 11411594065552228853351 := by
  unfold tailWord_75006
  simp only [CollatzResearch.WordTrace]
  refine ⟨341961695784193356256609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1823795710849031233368581 341961695784193356256609)
  ·
    refine ⟨256471271838145017192457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 341961695784193356256609 256471271838145017192457)
    ·
      refine ⟨192353453878608762894343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 256471271838145017192457 192353453878608762894343)
      ·
        refine ⟨288530180817913144341515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192353453878608762894343 288530180817913144341515)
        ·
          refine ⟨432795271226869716512273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 288530180817913144341515 432795271226869716512273)
          ·
            refine ⟨324596453420152287384205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 432795271226869716512273 324596453420152287384205)
            ·
              refine ⟨121723670032557107769077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 324596453420152287384205 121723670032557107769077)
              ·
                refine ⟨11411594065552228853351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 121723670032557107769077 11411594065552228853351)
                ·
                  rfl

theorem cell20_75006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 5].length) (baseStart_75006 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_75006 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_75006 prefixEnd_75006 := by exact prefixLift 75006
  have htrace : WordTrace (prefixWord ++ tailWord_75006) baseStart_75006 baseEnd_75006 := by
    simpa [prefixWord, tailWord_75006, baseEnd_75006] using wordTrace_append hprefix tailTrace_75006
  have hstable : (prefixWord ++ tailWord_75006).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75006).length < 2 ^ (prefixWord ++ tailWord_75006).sum := by decide
  have hdescent : baseEnd_75006 < baseStart_75006 := by decide
  rcases family_descends (prefixWord ++ tailWord_75006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75020 : List Nat := [2, 2, 1, 2, 2, 4, 1, 2, 4]
def baseStart_75020 : Nat := 118140960795 + 75020 * 2 ^ 59
def prefixEnd_75020 : Nat := 4983230072969 + 3 ^ 40 * 75020 * 2
def baseEnd_75020 : Nat := 34241172178134860093329

theorem tailTrace_75020 : CollatzResearch.WordTrace tailWord_75020 prefixEnd_75020 34241172178134860093329 := by
  unfold tailWord_75020
  simp only [CollatzResearch.WordTrace]
  refine ⟨1368102094111413620531257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1824136125481884827375009 1368102094111413620531257)
  ·
    refine ⟨1026076570583560215398443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1368102094111413620531257 1026076570583560215398443)
    ·
      refine ⟨1539114855875340323097665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1026076570583560215398443 1539114855875340323097665)
      ·
        refine ⟨1154336141906505242323249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1539114855875340323097665 1154336141906505242323249)
        ·
          refine ⟨865752106429878931742437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1154336141906505242323249 865752106429878931742437)
          ·
            refine ⟨162328519955602299701707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 865752106429878931742437 162328519955602299701707)
            ·
              refine ⟨243492779933403449552561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162328519955602299701707 243492779933403449552561)
              ·
                refine ⟨182619584950052587164421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 243492779933403449552561 182619584950052587164421)
                ·
                  refine ⟨34241172178134860093329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 182619584950052587164421 34241172178134860093329)
                  ·
                    rfl

theorem cell20_75020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 2, 4].length) (baseStart_75020 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_75020 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_75020 prefixEnd_75020 := by exact prefixLift 75020
  have htrace : WordTrace (prefixWord ++ tailWord_75020) baseStart_75020 baseEnd_75020 := by
    simpa [prefixWord, tailWord_75020, baseEnd_75020] using wordTrace_append hprefix tailTrace_75020
  have hstable : (prefixWord ++ tailWord_75020).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75020).length < 2 ^ (prefixWord ++ tailWord_75020).sum := by decide
  have hdescent : baseEnd_75020 < baseStart_75020 := by decide
  rcases family_descends (prefixWord ++ tailWord_75020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75041 : List Nat := [1, 2, 3, 2, 1, 1, 1, 1, 8]
def baseStart_75041 : Nat := 118140960795 + 75041 * 2 ^ 59
def prefixEnd_75041 : Nat := 4983230072969 + 3 ^ 40 * 75041 * 2
def baseEnd_75041 : Nat := 34250757150352120393243

theorem tailTrace_75041 : CollatzResearch.WordTrace tailWord_75041 prefixEnd_75041 34250757150352120393243 := by
  unfold tailWord_75041
  simp only [CollatzResearch.WordTrace]
  refine ⟨2736970121146747827576977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1824646747431165218384651 2736970121146747827576977)
  ·
    refine ⟨2052727590860060870682733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2736970121146747827576977 2052727590860060870682733)
    ·
      refine ⟨769772846572522826506025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2052727590860060870682733 769772846572522826506025)
      ·
        refine ⟨577329634929392119879519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 769772846572522826506025 577329634929392119879519)
        ·
          refine ⟨865994452394088179819279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 577329634929392119879519 865994452394088179819279)
          ·
            refine ⟨1298991678591132269728919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 865994452394088179819279 1298991678591132269728919)
            ·
              refine ⟨1948487517886698404593379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1298991678591132269728919 1948487517886698404593379)
              ·
                refine ⟨2922731276830047606890069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1948487517886698404593379 2922731276830047606890069)
                ·
                  refine ⟨34250757150352120393243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2922731276830047606890069 34250757150352120393243)
                  ·
                    rfl

theorem cell20_75041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 8].length) (baseStart_75041 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_75041 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_75041 prefixEnd_75041 := by exact prefixLift 75041
  have htrace : WordTrace (prefixWord ++ tailWord_75041) baseStart_75041 baseEnd_75041 := by
    simpa [prefixWord, tailWord_75041, baseEnd_75041] using wordTrace_append hprefix tailTrace_75041
  have hstable : (prefixWord ++ tailWord_75041).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75041).length < 2 ^ (prefixWord ++ tailWord_75041).sum := by decide
  have hdescent : baseEnd_75041 < baseStart_75041 := by decide
  rcases family_descends (prefixWord ++ tailWord_75041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75058 : List Nat := [3, 2, 1, 1, 4, 1, 1, 3, 4]
def baseStart_75058 : Nat := 118140960795 + 75058 * 2 ^ 59
def prefixEnd_75058 : Nat := 4983230072969 + 3 ^ 40 * 75058 * 2
def baseEnd_75058 : Nat := 34258516413575616826507

theorem tailTrace_75058 : CollatzResearch.WordTrace tailWord_75058 prefixEnd_75058 34258516413575616826507 := by
  unfold tailWord_75058
  simp only [CollatzResearch.WordTrace]
  refine ⟨684397540521289932736457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1825060108056773153963885 684397540521289932736457)
  ·
    refine ⟨513298155390967449552343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 684397540521289932736457 513298155390967449552343)
    ·
      refine ⟨769947233086451174328515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 513298155390967449552343 769947233086451174328515)
      ·
        refine ⟨1154920849629676761492773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 769947233086451174328515 1154920849629676761492773)
        ·
          refine ⟨216547659305564392779895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1154920849629676761492773 216547659305564392779895)
          ·
            refine ⟨324821488958346589169843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216547659305564392779895 324821488958346589169843)
            ·
              refine ⟨487232233437519883754765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 324821488958346589169843 487232233437519883754765)
              ·
                refine ⟨182712087539069956408037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 487232233437519883754765 182712087539069956408037)
                ·
                  refine ⟨34258516413575616826507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 182712087539069956408037 34258516413575616826507)
                  ·
                    rfl

theorem cell20_75058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_75058 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_75058 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_75058 prefixEnd_75058 := by exact prefixLift 75058
  have htrace : WordTrace (prefixWord ++ tailWord_75058) baseStart_75058 baseEnd_75058 := by
    simpa [prefixWord, tailWord_75058, baseEnd_75058] using wordTrace_append hprefix tailTrace_75058
  have hstable : (prefixWord ++ tailWord_75058).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75058).length < 2 ^ (prefixWord ++ tailWord_75058).sum := by decide
  have hdescent : baseEnd_75058 < baseStart_75058 := by decide
  rcases family_descends (prefixWord ++ tailWord_75058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75068 : List Nat := [2, 2, 2, 2, 1, 4, 3, 1, 3]
def baseStart_75068 : Nat := 118140960795 + 75068 * 2 ^ 59
def prefixEnd_75068 : Nat := 4983230072969 + 3 ^ 40 * 75068 * 2
def baseEnd_75068 : Nat := 34263080686060026493133

theorem tailTrace_75068 : CollatzResearch.WordTrace tailWord_75068 prefixEnd_75068 34263080686060026493133 := by
  unfold tailWord_75068
  simp only [CollatzResearch.WordTrace]
  refine ⟨1368977446024465719404929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1825303261365954292539905 1368977446024465719404929)
  ·
    refine ⟨1026733084518349289553697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1368977446024465719404929 1026733084518349289553697)
    ·
      refine ⟨770049813388761967165273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1026733084518349289553697 770049813388761967165273)
      ·
        refine ⟨577537360041571475373955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 770049813388761967165273 577537360041571475373955)
        ·
          refine ⟨866306040062357213060933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 577537360041571475373955 866306040062357213060933)
          ·
            refine ⟨162432382511691977448925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 866306040062357213060933 162432382511691977448925)
            ·
              refine ⟨60912143441884491543347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 162432382511691977448925 60912143441884491543347)
              ·
                refine ⟨91368215162826737315021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60912143441884491543347 91368215162826737315021)
                ·
                  refine ⟨34263080686060026493133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 91368215162826737315021 34263080686060026493133)
                  ·
                    rfl

theorem cell20_75068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 3, 1, 3].length) (baseStart_75068 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_75068 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_75068 prefixEnd_75068 := by exact prefixLift 75068
  have htrace : WordTrace (prefixWord ++ tailWord_75068) baseStart_75068 baseEnd_75068 := by
    simpa [prefixWord, tailWord_75068, baseEnd_75068] using wordTrace_append hprefix tailTrace_75068
  have hstable : (prefixWord ++ tailWord_75068).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75068).length < 2 ^ (prefixWord ++ tailWord_75068).sum := by decide
  have hdescent : baseEnd_75068 < baseStart_75068 := by decide
  rcases family_descends (prefixWord ++ tailWord_75068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75078 : List Nat := [6, 1, 1, 3, 1, 1, 1, 6]
def baseStart_75078 : Nat := 118140960795 + 75078 * 2 ^ 59
def prefixEnd_75078 : Nat := 4983230072969 + 3 ^ 40 * 75078 * 2
def baseEnd_75078 : Nat := 11422548319514812053253

theorem tailTrace_75078 : CollatzResearch.WordTrace tailWord_75078 prefixEnd_75078 11422548319514812053253 := by
  unfold tailWord_75078
  simp only [CollatzResearch.WordTrace]
  refine ⟨85572488187896973333559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 1825546414675135431115925 85572488187896973333559)
  ·
    refine ⟨128358732281845460000339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85572488187896973333559 128358732281845460000339)
    ·
      refine ⟨192538098422768190000509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128358732281845460000339 192538098422768190000509)
      ·
        refine ⟨72201786908538071250191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 192538098422768190000509 72201786908538071250191)
        ·
          refine ⟨108302680362807106875287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72201786908538071250191 108302680362807106875287)
          ·
            refine ⟨162454020544210660312931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108302680362807106875287 162454020544210660312931)
            ·
              refine ⟨243681030816315990469397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162454020544210660312931 243681030816315990469397)
              ·
                refine ⟨11422548319514812053253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 243681030816315990469397 11422548319514812053253)
                ·
                  rfl

theorem cell20_75078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_75078 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_75078 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_75078 prefixEnd_75078 := by exact prefixLift 75078
  have htrace : WordTrace (prefixWord ++ tailWord_75078) baseStart_75078 baseEnd_75078 := by
    simpa [prefixWord, tailWord_75078, baseEnd_75078] using wordTrace_append hprefix tailTrace_75078
  have hstable : (prefixWord ++ tailWord_75078).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75078).length < 2 ^ (prefixWord ++ tailWord_75078).sum := by decide
  have hdescent : baseEnd_75078 < baseStart_75078 := by decide
  rcases family_descends (prefixWord ++ tailWord_75078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75158 : List Nat := [5, 3, 1, 11]
def baseStart_75158 : Nat := 118140960795 + 75158 * 2 ^ 59
def prefixEnd_75158 : Nat := 4983230072969 + 3 ^ 40 * 75158 * 2
def baseEnd_75158 : Nat := 141169379170451495855

theorem tailTrace_75158 : CollatzResearch.WordTrace tailWord_75158 prefixEnd_75158 141169379170451495855 := by
  unfold tailWord_75158
  simp only [CollatzResearch.WordTrace]
  refine ⟨171327341357679800599133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1827491641148584539724085 171327341357679800599133)
  ·
    refine ⟨64247753009129925224675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171327341357679800599133 64247753009129925224675)
    ·
      refine ⟨96371629513694887837013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64247753009129925224675 96371629513694887837013)
      ·
        refine ⟨141169379170451495855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 96371629513694887837013 141169379170451495855)
        ·
          rfl

theorem cell20_75158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 11].length) (baseStart_75158 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_75158 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_75158 prefixEnd_75158 := by exact prefixLift 75158
  have htrace : WordTrace (prefixWord ++ tailWord_75158) baseStart_75158 baseEnd_75158 := by
    simpa [prefixWord, tailWord_75158, baseEnd_75158] using wordTrace_append hprefix tailTrace_75158
  have hstable : (prefixWord ++ tailWord_75158).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75158).length < 2 ^ (prefixWord ++ tailWord_75158).sum := by decide
  have hdescent : baseEnd_75158 < baseStart_75158 := by decide
  rcases family_descends (prefixWord ++ tailWord_75158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75164 : List Nat := [2, 2, 3, 4, 1, 2, 2, 2, 2]
def baseStart_75164 : Nat := 118140960795 + 75164 * 2 ^ 59
def prefixEnd_75164 : Nat := 4983230072969 + 3 ^ 40 * 75164 * 2
def baseEnd_75164 : Nat := 34306897701910359292741

theorem tailTrace_75164 : CollatzResearch.WordTrace tailWord_75164 prefixEnd_75164 34306897701910359292741 := by
  unfold tailWord_75164
  simp only [CollatzResearch.WordTrace]
  refine ⟨1370728149850569917152273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1827637533134093222869697 1370728149850569917152273)
  ·
    refine ⟨1028046112387927437864205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1370728149850569917152273 1028046112387927437864205)
    ·
      refine ⟨385517292145472789199077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1028046112387927437864205 385517292145472789199077)
      ·
        refine ⟨72284492277276147974827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 385517292145472789199077 72284492277276147974827)
        ·
          refine ⟨108426738415914221962241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72284492277276147974827 108426738415914221962241)
          ·
            refine ⟨81320053811935666471681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108426738415914221962241 81320053811935666471681)
            ·
              refine ⟨60990040358951749853761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81320053811935666471681 60990040358951749853761)
              ·
                refine ⟨45742530269213812390321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60990040358951749853761 45742530269213812390321)
                ·
                  refine ⟨34306897701910359292741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45742530269213812390321 34306897701910359292741)
                  ·
                    rfl

theorem cell20_75164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 2, 2, 2].length) (baseStart_75164 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_75164 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_75164 prefixEnd_75164 := by exact prefixLift 75164
  have htrace : WordTrace (prefixWord ++ tailWord_75164) baseStart_75164 baseEnd_75164 := by
    simpa [prefixWord, tailWord_75164, baseEnd_75164] using wordTrace_append hprefix tailTrace_75164
  have hstable : (prefixWord ++ tailWord_75164).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75164).length < 2 ^ (prefixWord ++ tailWord_75164).sum := by decide
  have hdescent : baseEnd_75164 < baseStart_75164 := by decide
  rcases family_descends (prefixWord ++ tailWord_75164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75165 : List Nat := [1, 4, 2, 1, 3, 1, 1, 4, 3]
def baseStart_75165 : Nat := 118140960795 + 75165 * 2 ^ 59
def prefixEnd_75165 : Nat := 4983230072969 + 3 ^ 40 * 75165 * 2
def baseEnd_75165 : Nat := 34307354129158800259403

theorem tailTrace_75165 : CollatzResearch.WordTrace tailWord_75165 prefixEnd_75165 34307354129158800259403 := by
  unfold tailWord_75165
  simp only [CollatzResearch.WordTrace]
  refine ⟨2741492772697517005090949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1827661848465011336727299 2741492772697517005090949)
  ·
    refine ⟨514029894880784438454553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2741492772697517005090949 514029894880784438454553)
    ·
      refine ⟨385522421160588328840915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 514029894880784438454553 385522421160588328840915)
      ·
        refine ⟨578283631740882493261373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 385522421160588328840915 578283631740882493261373)
        ·
          refine ⟨216856361902830934973015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 578283631740882493261373 216856361902830934973015)
          ·
            refine ⟨325284542854246402459523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216856361902830934973015 325284542854246402459523)
            ·
              refine ⟨487926814281369603689285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 325284542854246402459523 487926814281369603689285)
              ·
                refine ⟨91486277677756800691741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 487926814281369603689285 91486277677756800691741)
                ·
                  refine ⟨34307354129158800259403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 91486277677756800691741 34307354129158800259403)
                  ·
                    rfl

theorem cell20_75165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 4, 3].length) (baseStart_75165 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_75165 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_75165 prefixEnd_75165 := by exact prefixLift 75165
  have htrace : WordTrace (prefixWord ++ tailWord_75165) baseStart_75165 baseEnd_75165 := by
    simpa [prefixWord, tailWord_75165, baseEnd_75165] using wordTrace_append hprefix tailTrace_75165
  have hstable : (prefixWord ++ tailWord_75165).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75165).length < 2 ^ (prefixWord ++ tailWord_75165).sum := by decide
  have hdescent : baseEnd_75165 < baseStart_75165 := by decide
  rcases family_descends (prefixWord ++ tailWord_75165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75200 : List Nat := [2, 1, 1, 2, 3, 1, 2, 8]
def baseStart_75200 : Nat := 118140960795 + 75200 * 2 ^ 59
def prefixEnd_75200 : Nat := 4983230072969 + 3 ^ 40 * 75200 * 2
def baseEnd_75200 : Nat := 11441109694284744697531

theorem tailTrace_75200 : CollatzResearch.WordTrace tailWord_75200 prefixEnd_75200 11441109694284744697531 := by
  unfold tailWord_75200
  simp only [CollatzResearch.WordTrace]
  refine ⟨1371384663785358991307527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1828512885047145321743369 1371384663785358991307527)
  ·
    refine ⟨2057076995678038486961291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1371384663785358991307527 2057076995678038486961291)
    ·
      refine ⟨3085615493517057730441937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2057076995678038486961291 3085615493517057730441937)
      ·
        refine ⟨2314211620137793297831453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3085615493517057730441937 2314211620137793297831453)
        ·
          refine ⟨867829357551672486686795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2314211620137793297831453 867829357551672486686795)
          ·
            refine ⟨1301744036327508730030193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 867829357551672486686795 1301744036327508730030193)
            ·
              refine ⟨976308027245631547522645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1301744036327508730030193 976308027245631547522645)
              ·
                refine ⟨11441109694284744697531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 976308027245631547522645 11441109694284744697531)
                ·
                  rfl

theorem cell20_75200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 8].length) (baseStart_75200 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_75200 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_75200 prefixEnd_75200 := by exact prefixLift 75200
  have htrace : WordTrace (prefixWord ++ tailWord_75200) baseStart_75200 baseEnd_75200 := by
    simpa [prefixWord, tailWord_75200, baseEnd_75200] using wordTrace_append hprefix tailTrace_75200
  have hstable : (prefixWord ++ tailWord_75200).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75200).length < 2 ^ (prefixWord ++ tailWord_75200).sum := by decide
  have hdescent : baseEnd_75200 < baseStart_75200 := by decide
  rcases family_descends (prefixWord ++ tailWord_75200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75293 : List Nat := [1, 4, 2, 2, 1, 1, 4, 5]
def baseStart_75293 : Nat := 118140960795 + 75293 * 2 ^ 59
def prefixEnd_75293 : Nat := 4983230072969 + 3 ^ 40 * 75293 * 2
def baseEnd_75293 : Nat := 11455258938986414664071

theorem tailTrace_75293 : CollatzResearch.WordTrace tailWord_75293 prefixEnd_75293 11455258938986414664071 := by
  unfold tailWord_75293
  simp only [CollatzResearch.WordTrace]
  refine ⟨2746161316233794865750533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1830774210822529910500355 2746161316233794865750533)
  ·
    refine ⟨514905246793836537328225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2746161316233794865750533 514905246793836537328225)
    ·
      refine ⟨386178935095377402996169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 514905246793836537328225 386178935095377402996169)
      ·
        refine ⟨289634201321533052247127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 386178935095377402996169 289634201321533052247127)
        ·
          refine ⟨434451301982299578370691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 289634201321533052247127 434451301982299578370691)
          ·
            refine ⟨651676952973449367556037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 434451301982299578370691 651676952973449367556037)
            ·
              refine ⟨122189428682521756416757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 651676952973449367556037 122189428682521756416757)
              ·
                refine ⟨11455258938986414664071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 122189428682521756416757 11455258938986414664071)
                ·
                  rfl

theorem cell20_75293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 5].length) (baseStart_75293 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_75293 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_75293 prefixEnd_75293 := by exact prefixLift 75293
  have htrace : WordTrace (prefixWord ++ tailWord_75293) baseStart_75293 baseEnd_75293 := by
    simpa [prefixWord, tailWord_75293, baseEnd_75293] using wordTrace_append hprefix tailTrace_75293
  have hstable : (prefixWord ++ tailWord_75293).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75293).length < 2 ^ (prefixWord ++ tailWord_75293).sum := by decide
  have hdescent : baseEnd_75293 < baseStart_75293 := by decide
  rcases family_descends (prefixWord ++ tailWord_75293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75296 : List Nat := [2, 1, 1, 6, 1, 1, 4, 1, 3]
def baseStart_75296 : Nat := 118140960795 + 75296 * 2 ^ 59
def prefixEnd_75296 : Nat := 4983230072969 + 3 ^ 40 * 75296 * 2
def baseEnd_75296 : Nat := 34367146098704566892201

theorem tailTrace_75296 : CollatzResearch.WordTrace tailWord_75296 prefixEnd_75296 34367146098704566892201 := by
  unfold tailWord_75296
  simp only [CollatzResearch.WordTrace]
  refine ⟨1373135367611463189054871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1830847156815284252073161 1373135367611463189054871)
  ·
    refine ⟨2059703051417194783582307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1373135367611463189054871 2059703051417194783582307)
    ·
      refine ⟨3089554577125792175373461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2059703051417194783582307 3089554577125792175373461)
      ·
        refine ⟨144822870802771508220631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 3089554577125792175373461 144822870802771508220631)
        ·
          refine ⟨217234306204157262330947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144822870802771508220631 217234306204157262330947)
          ·
            refine ⟨325851459306235893496421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217234306204157262330947 325851459306235893496421)
            ·
              refine ⟨61097148619919230030579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 325851459306235893496421 61097148619919230030579)
              ·
                refine ⟨91645722929878845045869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61097148619919230030579 91645722929878845045869)
                ·
                  refine ⟨34367146098704566892201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 91645722929878845045869 34367146098704566892201)
                  ·
                    rfl

theorem cell20_75296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 4, 1, 3].length) (baseStart_75296 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_75296 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_75296 prefixEnd_75296 := by exact prefixLift 75296
  have htrace : WordTrace (prefixWord ++ tailWord_75296) baseStart_75296 baseEnd_75296 := by
    simpa [prefixWord, tailWord_75296, baseEnd_75296] using wordTrace_append hprefix tailTrace_75296
  have hstable : (prefixWord ++ tailWord_75296).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75296).length < 2 ^ (prefixWord ++ tailWord_75296).sum := by decide
  have hdescent : baseEnd_75296 < baseStart_75296 := by decide
  rcases family_descends (prefixWord ++ tailWord_75296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75345 : List Nat := [1, 2, 2, 1, 3, 2, 2, 3, 4]
def baseStart_75345 : Nat := 118140960795 + 75345 * 2 ^ 59
def prefixEnd_75345 : Nat := 4983230072969 + 3 ^ 40 * 75345 * 2
def baseEnd_75345 : Nat := 34389511033878174258667

theorem tailTrace_75345 : CollatzResearch.WordTrace tailWord_75345 prefixEnd_75345 34389511033878174258667 := by
  unfold tailWord_75345
  simp only [CollatzResearch.WordTrace]
  refine ⟨2748057912045407746643489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1832038608030271831095659 2748057912045407746643489)
  ·
    refine ⟨2061043434034055809982617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2748057912045407746643489 2061043434034055809982617)
    ·
      refine ⟨1545782575525541857486963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2061043434034055809982617 1545782575525541857486963)
      ·
        refine ⟨2318673863288312786230445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1545782575525541857486963 2318673863288312786230445)
        ·
          refine ⟨869502698733117294836417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2318673863288312786230445 869502698733117294836417)
          ·
            refine ⟨652127024049837971127313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 869502698733117294836417 652127024049837971127313)
            ·
              refine ⟨489095268037378478345485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 652127024049837971127313 489095268037378478345485)
              ·
                refine ⟨183410725514016929379557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 489095268037378478345485 183410725514016929379557)
                ·
                  refine ⟨34389511033878174258667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 183410725514016929379557 34389511033878174258667)
                  ·
                    rfl

theorem cell20_75345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 3, 4].length) (baseStart_75345 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_75345 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_75345 prefixEnd_75345 := by exact prefixLift 75345
  have htrace : WordTrace (prefixWord ++ tailWord_75345) baseStart_75345 baseEnd_75345 := by
    simpa [prefixWord, tailWord_75345, baseEnd_75345] using wordTrace_append hprefix tailTrace_75345
  have hstable : (prefixWord ++ tailWord_75345).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75345).length < 2 ^ (prefixWord ++ tailWord_75345).sum := by decide
  have hdescent : baseEnd_75345 < baseStart_75345 := by decide
  rcases family_descends (prefixWord ++ tailWord_75345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75359 : List Nat := [1, 1, 2, 3, 1, 1, 1, 1, 9]
def baseStart_75359 : Nat := 118140960795 + 75359 * 2 ^ 59
def prefixEnd_75359 : Nat := 4983230072969 + 3 ^ 40 * 75359 * 2
def baseEnd_75359 : Nat := 34395901015356347791943

theorem tailTrace_75359 : CollatzResearch.WordTrace tailWord_75359 prefixEnd_75359 34395901015356347791943 := by
  unfold tailWord_75359
  simp only [CollatzResearch.WordTrace]
  refine ⟨2748568533994688137653131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1832379022663125425102087 2748568533994688137653131)
  ·
    refine ⟨4122852800992032206479697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2748568533994688137653131 4122852800992032206479697)
    ·
      refine ⟨3092139600744024154859773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4122852800992032206479697 3092139600744024154859773)
      ·
        refine ⟨1159552350279009058072415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3092139600744024154859773 1159552350279009058072415)
        ·
          refine ⟨1739328525418513587108623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1159552350279009058072415 1739328525418513587108623)
          ·
            refine ⟨2608992788127770380662935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1739328525418513587108623 2608992788127770380662935)
            ·
              refine ⟨3913489182191655570994403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2608992788127770380662935 3913489182191655570994403)
              ·
                refine ⟨5870233773287483356491605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3913489182191655570994403 5870233773287483356491605)
                ·
                  refine ⟨34395901015356347791943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 5870233773287483356491605 34395901015356347791943)
                  ·
                    rfl

theorem cell20_75359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 9].length) (baseStart_75359 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_75359 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_75359 prefixEnd_75359 := by exact prefixLift 75359
  have htrace : WordTrace (prefixWord ++ tailWord_75359) baseStart_75359 baseEnd_75359 := by
    simpa [prefixWord, tailWord_75359, baseEnd_75359] using wordTrace_append hprefix tailTrace_75359
  have hstable : (prefixWord ++ tailWord_75359).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75359).length < 2 ^ (prefixWord ++ tailWord_75359).sum := by decide
  have hdescent : baseEnd_75359 < baseStart_75359 := by decide
  rcases family_descends (prefixWord ++ tailWord_75359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75393 : List Nat := [1, 2, 4, 2, 1, 2, 3, 2, 3]
def baseStart_75393 : Nat := 118140960795 + 75393 * 2 ^ 59
def prefixEnd_75393 : Nat := 4983230072969 + 3 ^ 40 * 75393 * 2
def baseEnd_75393 : Nat := 34411419541803340658471

theorem tailTrace_75393 : CollatzResearch.WordTrace tailWord_75393 prefixEnd_75393 34411419541803340658471 := by
  unfold tailWord_75393
  simp only [CollatzResearch.WordTrace]
  refine ⟨2749808615871511944390833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1833205743914341296260555 2749808615871511944390833)
  ·
    refine ⟨2062356461903633958293125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2749808615871511944390833 2062356461903633958293125)
    ·
      refine ⟨386691836606931367179961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2062356461903633958293125 386691836606931367179961)
      ·
        refine ⟨290018877455198525384971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 386691836606931367179961 290018877455198525384971)
        ·
          refine ⟨435028316182797788077457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 290018877455198525384971 435028316182797788077457)
          ·
            refine ⟨326271237137098341058093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 435028316182797788077457 326271237137098341058093)
            ·
              refine ⟨122351713926411877896785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 326271237137098341058093 122351713926411877896785)
              ·
                refine ⟨91763785444808908422589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 122351713926411877896785 91763785444808908422589)
                ·
                  refine ⟨34411419541803340658471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 91763785444808908422589 34411419541803340658471)
                  ·
                    rfl

theorem cell20_75393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 2, 3].length) (baseStart_75393 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_75393 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_75393 prefixEnd_75393 := by exact prefixLift 75393
  have htrace : WordTrace (prefixWord ++ tailWord_75393) baseStart_75393 baseEnd_75393 := by
    simpa [prefixWord, tailWord_75393, baseEnd_75393] using wordTrace_append hprefix tailTrace_75393
  have hstable : (prefixWord ++ tailWord_75393).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75393).length < 2 ^ (prefixWord ++ tailWord_75393).sum := by decide
  have hdescent : baseEnd_75393 < baseStart_75393 := by decide
  rcases family_descends (prefixWord ++ tailWord_75393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75424 : List Nat := [2, 1, 1, 4, 3, 3, 2, 4]
def baseStart_75424 : Nat := 118140960795 + 75424 * 2 ^ 59
def prefixEnd_75424 : Nat := 4983230072969 + 3 ^ 40 * 75424 * 2
def baseEnd_75424 : Nat := 11475189595501670208337

theorem tailTrace_75424 : CollatzResearch.WordTrace tailWord_75424 prefixEnd_75424 11475189595501670208337 := by
  unfold tailWord_75424
  simp only [CollatzResearch.WordTrace]
  refine ⟨1375469639379602119384663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1833959519172802825846217 1375469639379602119384663)
  ·
    refine ⟨2063204459069403179076995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1375469639379602119384663 2063204459069403179076995)
    ·
      refine ⟨3094806688604104768615493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2063204459069403179076995 3094806688604104768615493)
      ·
        refine ⟨580276254113269644115405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3094806688604104768615493 580276254113269644115405)
        ·
          refine ⟨217603595292476116543277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 580276254113269644115405 217603595292476116543277)
          ·
            refine ⟨81601348234678543703729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 217603595292476116543277 81601348234678543703729)
            ·
              refine ⟨61201011176008907777797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81601348234678543703729 61201011176008907777797)
              ·
                refine ⟨11475189595501670208337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61201011176008907777797 11475189595501670208337)
                ·
                  rfl

theorem cell20_75424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 2, 4].length) (baseStart_75424 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_75424 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_75424 prefixEnd_75424 := by exact prefixLift 75424
  have htrace : WordTrace (prefixWord ++ tailWord_75424) baseStart_75424 baseEnd_75424 := by
    simpa [prefixWord, tailWord_75424, baseEnd_75424] using wordTrace_append hprefix tailTrace_75424
  have hstable : (prefixWord ++ tailWord_75424).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75424).length < 2 ^ (prefixWord ++ tailWord_75424).sum := by decide
  have hdescent : baseEnd_75424 < baseStart_75424 := by decide
  rcases family_descends (prefixWord ++ tailWord_75424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75452 : List Nat := [2, 2, 2, 3, 1, 2, 2, 1, 5]
def baseStart_75452 : Nat := 118140960795 + 75452 * 2 ^ 59
def prefixEnd_75452 : Nat := 4983230072969 + 3 ^ 40 * 75452 * 2
def baseEnd_75452 : Nat := 34438348749461357691563

theorem tailTrace_75452 : CollatzResearch.WordTrace tailWord_75452 prefixEnd_75452 34438348749461357691563 := by
  unfold tailWord_75452
  simp only [CollatzResearch.WordTrace]
  refine ⟨1375980261328882510394305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1834640348438510013859073 1375980261328882510394305)
  ·
    refine ⟨1031985195996661882795729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1375980261328882510394305 1031985195996661882795729)
    ·
      refine ⟨773988896997496412096797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1031985195996661882795729 773988896997496412096797)
      ·
        refine ⟨290245836374061154536299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 773988896997496412096797 290245836374061154536299)
        ·
          refine ⟨435368754561091731804449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 290245836374061154536299 435368754561091731804449)
          ·
            refine ⟨326526565920818798853337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 435368754561091731804449 326526565920818798853337)
            ·
              refine ⟨244894924440614099140003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 326526565920818798853337 244894924440614099140003)
              ·
                refine ⟨367342386660921148710005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 244894924440614099140003 367342386660921148710005)
                ·
                  refine ⟨34438348749461357691563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 367342386660921148710005 34438348749461357691563)
                  ·
                    rfl

theorem cell20_75452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 1, 5].length) (baseStart_75452 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_75452 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_75452 prefixEnd_75452 := by exact prefixLift 75452
  have htrace : WordTrace (prefixWord ++ tailWord_75452) baseStart_75452 baseEnd_75452 := by
    simpa [prefixWord, tailWord_75452, baseEnd_75452] using wordTrace_append hprefix tailTrace_75452
  have hstable : (prefixWord ++ tailWord_75452).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75452).length < 2 ^ (prefixWord ++ tailWord_75452).sum := by decide
  have hdescent : baseEnd_75452 < baseStart_75452 := by decide
  rcases family_descends (prefixWord ++ tailWord_75452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75455 : List Nat := [1, 1, 2, 2, 2, 3, 5, 2, 2]
def baseStart_75455 : Nat := 118140960795 + 75455 * 2 ^ 59
def prefixEnd_75455 : Nat := 4983230072969 + 3 ^ 40 * 75455 * 2
def baseEnd_75455 : Nat := 34439718031206680591551

theorem tailTrace_75455 : CollatzResearch.WordTrace tailWord_75455 prefixEnd_75455 34439718031206680591551 := by
  unfold tailWord_75455
  simp only [CollatzResearch.WordTrace]
  refine ⟨2752069941646896533147819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1834713294431264355431879 2752069941646896533147819)
  ·
    refine ⟨4128104912470344799721729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2752069941646896533147819 4128104912470344799721729)
    ·
      refine ⟨3096078684352758599791297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4128104912470344799721729 3096078684352758599791297)
      ·
        refine ⟨2322059013264568949843473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3096078684352758599791297 2322059013264568949843473)
        ·
          refine ⟨1741544259948426712382605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2322059013264568949843473 1741544259948426712382605)
          ·
            refine ⟨653079097480660017143477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1741544259948426712382605 653079097480660017143477)
            ·
              refine ⟨61226165388811876607201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 653079097480660017143477 61226165388811876607201)
              ·
                refine ⟨45919624041608907455401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61226165388811876607201 45919624041608907455401)
                ·
                  refine ⟨34439718031206680591551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45919624041608907455401 34439718031206680591551)
                  ·
                    rfl

theorem cell20_75455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 5, 2, 2].length) (baseStart_75455 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_75455 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_75455 prefixEnd_75455 := by exact prefixLift 75455
  have htrace : WordTrace (prefixWord ++ tailWord_75455) baseStart_75455 baseEnd_75455 := by
    simpa [prefixWord, tailWord_75455, baseEnd_75455] using wordTrace_append hprefix tailTrace_75455
  have hstable : (prefixWord ++ tailWord_75455).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75455).length < 2 ^ (prefixWord ++ tailWord_75455).sum := by decide
  have hdescent : baseEnd_75455 < baseStart_75455 := by decide
  rcases family_descends (prefixWord ++ tailWord_75455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75458 : List Nat := [3, 5, 1, 2, 1, 1, 2, 5]
def baseStart_75458 : Nat := 118140960795 + 75458 * 2 ^ 59
def prefixEnd_75458 : Nat := 4983230072969 + 3 ^ 40 * 75458 * 2
def baseEnd_75458 : Nat := 11480362437650667830513

theorem tailTrace_75458 : CollatzResearch.WordTrace tailWord_75458 prefixEnd_75458 11480362437650667830513 := by
  unfold tailWord_75458
  simp only [CollatzResearch.WordTrace]
  refine ⟨688044840159007011376757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1834786240424018697004685 688044840159007011376757)
  ·
    refine ⟨64504203764906907316571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 688044840159007011376757 64504203764906907316571)
    ·
      refine ⟨96756305647360360974857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64504203764906907316571 96756305647360360974857)
      ·
        refine ⟨72567229235520270731143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96756305647360360974857 72567229235520270731143)
        ·
          refine ⟨108850843853280406096715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72567229235520270731143 108850843853280406096715)
          ·
            refine ⟨163276265779920609145073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108850843853280406096715 163276265779920609145073)
            ·
              refine ⟨122457199334940456858805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 163276265779920609145073 122457199334940456858805)
              ·
                refine ⟨11480362437650667830513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 122457199334940456858805 11480362437650667830513)
                ·
                  rfl

theorem cell20_75458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 5].length) (baseStart_75458 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_75458 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_75458 prefixEnd_75458 := by exact prefixLift 75458
  have htrace : WordTrace (prefixWord ++ tailWord_75458) baseStart_75458 baseEnd_75458 := by
    simpa [prefixWord, tailWord_75458, baseEnd_75458] using wordTrace_append hprefix tailTrace_75458
  have hstable : (prefixWord ++ tailWord_75458).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75458).length < 2 ^ (prefixWord ++ tailWord_75458).sum := by decide
  have hdescent : baseEnd_75458 < baseStart_75458 := by decide
  rcases family_descends (prefixWord ++ tailWord_75458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75510 : List Nat := [5, 1, 1, 1, 1, 3, 4, 2, 2]
def baseStart_75510 : Nat := 118140960795 + 75510 * 2 ^ 59
def prefixEnd_75510 : Nat := 4983230072969 + 3 ^ 40 * 75510 * 2
def baseEnd_75510 : Nat := 34464821529870933757993

theorem tailTrace_75510 : CollatzResearch.WordTrace tailWord_75510 prefixEnd_75510 34464821529870933757993 := by
  unfold tailWord_75510
  simp only [CollatzResearch.WordTrace]
  refine ⟨172129747277977557899999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1836050637631760617599989 172129747277977557899999)
  ·
    refine ⟨258194620916966336849999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172129747277977557899999 258194620916966336849999)
    ·
      refine ⟨387291931375449505274999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258194620916966336849999 387291931375449505274999)
      ·
        refine ⟨580937897063174257912499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 387291931375449505274999 580937897063174257912499)
        ·
          refine ⟨871406845594761386868749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 580937897063174257912499 871406845594761386868749)
          ·
            refine ⟨326777567098035520075781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 871406845594761386868749 326777567098035520075781)
            ·
              refine ⟨61270793830881660014209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 326777567098035520075781 61270793830881660014209)
              ·
                refine ⟨45953095373161245010657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61270793830881660014209 45953095373161245010657)
                ·
                  refine ⟨34464821529870933757993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45953095373161245010657 34464821529870933757993)
                  ·
                    rfl

theorem cell20_75510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 4, 2, 2].length) (baseStart_75510 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_75510 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_75510 prefixEnd_75510 := by exact prefixLift 75510
  have htrace : WordTrace (prefixWord ++ tailWord_75510) baseStart_75510 baseEnd_75510 := by
    simpa [prefixWord, tailWord_75510, baseEnd_75510] using wordTrace_append hprefix tailTrace_75510
  have hstable : (prefixWord ++ tailWord_75510).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75510).length < 2 ^ (prefixWord ++ tailWord_75510).sum := by decide
  have hdescent : baseEnd_75510 < baseStart_75510 := by decide
  rcases family_descends (prefixWord ++ tailWord_75510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75511 : List Nat := [1, 1, 3, 1, 1, 1, 4, 3, 5]
def baseStart_75511 : Nat := 118140960795 + 75511 * 2 ^ 59
def prefixEnd_75511 : Nat := 4983230072969 + 3 ^ 40 * 75511 * 2
def baseEnd_75511 : Nat := 34465277957119374724655

theorem tailTrace_75511 : CollatzResearch.WordTrace tailWord_75511 prefixEnd_75511 34465277957119374724655 := by
  unfold tailWord_75511
  simp only [CollatzResearch.WordTrace]
  refine ⟨2754112429444018097186387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1836074952962678731457591 2754112429444018097186387)
  ·
    refine ⟨4131168644166027145779581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2754112429444018097186387 4131168644166027145779581)
    ·
      refine ⟨1549188241562260179667343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4131168644166027145779581 1549188241562260179667343)
      ·
        refine ⟨2323782362343390269501015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1549188241562260179667343 2323782362343390269501015)
        ·
          refine ⟨3485673543515085404251523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2323782362343390269501015 3485673543515085404251523)
          ·
            refine ⟨5228510315272628106377285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3485673543515085404251523 5228510315272628106377285)
            ·
              refine ⟨980345684113617769945741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5228510315272628106377285 980345684113617769945741)
              ·
                refine ⟨367629631542606663729653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 980345684113617769945741 367629631542606663729653)
                ·
                  refine ⟨34465277957119374724655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 367629631542606663729653 34465277957119374724655)
                  ·
                    rfl

theorem cell20_75511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 5].length) (baseStart_75511 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_75511 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_75511 prefixEnd_75511 := by exact prefixLift 75511
  have htrace : WordTrace (prefixWord ++ tailWord_75511) baseStart_75511 baseEnd_75511 := by
    simpa [prefixWord, tailWord_75511, baseEnd_75511] using wordTrace_append hprefix tailTrace_75511
  have hstable : (prefixWord ++ tailWord_75511).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75511).length < 2 ^ (prefixWord ++ tailWord_75511).sum := by decide
  have hdescent : baseEnd_75511 < baseStart_75511 := by decide
  rcases family_descends (prefixWord ++ tailWord_75511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75528 : List Nat := [2, 1, 3, 2, 2, 1, 1, 5, 3]
def baseStart_75528 : Nat := 118140960795 + 75528 * 2 ^ 59
def prefixEnd_75528 : Nat := 4983230072969 + 3 ^ 40 * 75528 * 2
def baseEnd_75528 : Nat := 34473037220342871157919

theorem tailTrace_75528 : CollatzResearch.WordTrace tailWord_75528 prefixEnd_75528 34473037220342871157919 := by
  unfold tailWord_75528
  simp only [CollatzResearch.WordTrace]
  refine ⟨1377366235191215000277619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1836488313588286667036825 1377366235191215000277619)
  ·
    refine ⟨2066049352786822500416429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1377366235191215000277619 2066049352786822500416429)
    ·
      refine ⟨774768507295058437656161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2066049352786822500416429 774768507295058437656161)
      ·
        refine ⟨581076380471293828242121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 774768507295058437656161 581076380471293828242121)
        ·
          refine ⟨435807285353470371181591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 581076380471293828242121 435807285353470371181591)
          ·
            refine ⟨653710928030205556772387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 435807285353470371181591 653710928030205556772387)
            ·
              refine ⟨980566392045308335158581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 653710928030205556772387 980566392045308335158581)
              ·
                refine ⟨91928099254247656421117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 980566392045308335158581 91928099254247656421117)
                ·
                  refine ⟨34473037220342871157919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 91928099254247656421117 34473037220342871157919)
                  ·
                    rfl

theorem cell20_75528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 5, 3].length) (baseStart_75528 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_75528 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_75528 prefixEnd_75528 := by exact prefixLift 75528
  have htrace : WordTrace (prefixWord ++ tailWord_75528) baseStart_75528 baseEnd_75528 := by
    simpa [prefixWord, tailWord_75528, baseEnd_75528] using wordTrace_append hprefix tailTrace_75528
  have hstable : (prefixWord ++ tailWord_75528).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75528).length < 2 ^ (prefixWord ++ tailWord_75528).sum := by decide
  have hdescent : baseEnd_75528 < baseStart_75528 := by decide
  rcases family_descends (prefixWord ++ tailWord_75528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75604 : List Nat := [2, 4, 1, 1, 3, 1, 1, 2, 5]
def baseStart_75604 : Nat := 118140960795 + 75604 * 2 ^ 59
def prefixEnd_75604 : Nat := 4983230072969 + 3 ^ 40 * 75604 * 2
def baseEnd_75604 : Nat := 34507725691224384624275

theorem tailTrace_75604 : CollatzResearch.WordTrace tailWord_75604 prefixEnd_75604 34507725691224384624275 := by
  unfold tailWord_75604
  simp only [CollatzResearch.WordTrace]
  refine ⟨1378752209053547490160933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1838336278738063320214577 1378752209053547490160933)
  ·
    refine ⟨258516039197540154405175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1378752209053547490160933 258516039197540154405175)
    ·
      refine ⟨387774058796310231607763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258516039197540154405175 387774058796310231607763)
      ·
        refine ⟨581661088194465347411645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 387774058796310231607763 581661088194465347411645)
        ·
          refine ⟨218122908072924505279367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 581661088194465347411645 218122908072924505279367)
          ·
            refine ⟨327184362109386757919051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 218122908072924505279367 327184362109386757919051)
            ·
              refine ⟨490776543164080136878577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 327184362109386757919051 490776543164080136878577)
              ·
                refine ⟨368082407373060102658933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 490776543164080136878577 368082407373060102658933)
                ·
                  refine ⟨34507725691224384624275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 368082407373060102658933 34507725691224384624275)
                  ·
                    rfl

theorem cell20_75604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_75604 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_75604 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_75604 prefixEnd_75604 := by exact prefixLift 75604
  have htrace : WordTrace (prefixWord ++ tailWord_75604) baseStart_75604 baseEnd_75604 := by
    simpa [prefixWord, tailWord_75604, baseEnd_75604] using wordTrace_append hprefix tailTrace_75604
  have hstable : (prefixWord ++ tailWord_75604).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75604).length < 2 ^ (prefixWord ++ tailWord_75604).sum := by decide
  have hdescent : baseEnd_75604 < baseStart_75604 := by decide
  rcases family_descends (prefixWord ++ tailWord_75604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75628 : List Nat := [2, 2, 1, 1, 4, 4, 1, 1, 4]
def baseStart_75628 : Nat := 118140960795 + 75628 * 2 ^ 59
def prefixEnd_75628 : Nat := 4983230072969 + 3 ^ 40 * 75628 * 2
def baseEnd_75628 : Nat := 34518679945186967824177

theorem tailTrace_75628 : CollatzResearch.WordTrace tailWord_75628 prefixEnd_75628 34518679945186967824177 := by
  unfold tailWord_75628
  simp only [CollatzResearch.WordTrace]
  refine ⟨1379189885010073539597769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1838919846680098052797025 1379189885010073539597769)
  ·
    refine ⟨1034392413757555154698327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1379189885010073539597769 1034392413757555154698327)
    ·
      refine ⟨1551588620636332732047491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1034392413757555154698327 1551588620636332732047491)
      ·
        refine ⟨2327382930954499098071237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1551588620636332732047491 2327382930954499098071237)
        ·
          refine ⟨436384299553968580888357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2327382930954499098071237 436384299553968580888357)
          ·
            refine ⟨81822056166369108916567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 436384299553968580888357 81822056166369108916567)
            ·
              refine ⟨122733084249553663374851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81822056166369108916567 122733084249553663374851)
              ·
                refine ⟨184099626374330495062277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122733084249553663374851 184099626374330495062277)
                ·
                  refine ⟨34518679945186967824177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 184099626374330495062277 34518679945186967824177)
                  ·
                    rfl

theorem cell20_75628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 4].length) (baseStart_75628 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_75628 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_75628 prefixEnd_75628 := by exact prefixLift 75628
  have htrace : WordTrace (prefixWord ++ tailWord_75628) baseStart_75628 baseEnd_75628 := by
    simpa [prefixWord, tailWord_75628, baseEnd_75628] using wordTrace_append hprefix tailTrace_75628
  have hstable : (prefixWord ++ tailWord_75628).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75628).length < 2 ^ (prefixWord ++ tailWord_75628).sum := by decide
  have hdescent : baseEnd_75628 < baseStart_75628 := by decide
  rcases family_descends (prefixWord ++ tailWord_75628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75638 : List Nat := [5, 1, 1, 3, 2, 1, 1, 3, 3]
def baseStart_75638 : Nat := 118140960795 + 75638 * 2 ^ 59
def prefixEnd_75638 : Nat := 4983230072969 + 3 ^ 40 * 75638 * 2
def baseEnd_75638 : Nat := 34523244217671377490803

theorem tailTrace_75638 : CollatzResearch.WordTrace tailWord_75638 prefixEnd_75638 34523244217671377490803 := by
  unfold tailWord_75638
  simp only [CollatzResearch.WordTrace]
  refine ⟨172421531248994924191223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1839162999989279191373045 172421531248994924191223)
  ·
    refine ⟨258632296873492386286835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172421531248994924191223 258632296873492386286835)
    ·
      refine ⟨387948445310238579430253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258632296873492386286835 387948445310238579430253)
      ·
        refine ⟨145480666991339467286345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 387948445310238579430253 145480666991339467286345)
        ·
          refine ⟨109110500243504600464759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145480666991339467286345 109110500243504600464759)
          ·
            refine ⟨163665750365256900697139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109110500243504600464759 163665750365256900697139)
            ·
              refine ⟨245498625547885351045709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163665750365256900697139 245498625547885351045709)
              ·
                refine ⟨92061984580457006642141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 245498625547885351045709 92061984580457006642141)
                ·
                  refine ⟨34523244217671377490803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 92061984580457006642141 34523244217671377490803)
                  ·
                    rfl

theorem cell20_75638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_75638 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_75638 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_75638 prefixEnd_75638 := by exact prefixLift 75638
  have htrace : WordTrace (prefixWord ++ tailWord_75638) baseStart_75638 baseEnd_75638 := by
    simpa [prefixWord, tailWord_75638, baseEnd_75638] using wordTrace_append hprefix tailTrace_75638
  have hstable : (prefixWord ++ tailWord_75638).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75638).length < 2 ^ (prefixWord ++ tailWord_75638).sum := by decide
  have hdescent : baseEnd_75638 < baseStart_75638 := by decide
  rcases family_descends (prefixWord ++ tailWord_75638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75679 : List Nat := [1, 1, 2, 5, 4, 1, 2, 2, 2]
def baseStart_75679 : Nat := 118140960795 + 75679 * 2 ^ 59
def prefixEnd_75679 : Nat := 4983230072969 + 3 ^ 40 * 75679 * 2
def baseEnd_75679 : Nat := 34541957734857457123969

theorem tailTrace_75679 : CollatzResearch.WordTrace tailWord_75679 prefixEnd_75679 34541957734857457123969 := by
  unfold tailWord_75679
  simp only [CollatzResearch.WordTrace]
  refine ⟨2760239892835382789302091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1840159928556921859534727 2760239892835382789302091)
  ·
    refine ⟨4140359839253074183953137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2760239892835382789302091 4140359839253074183953137)
    ·
      refine ⟨3105269879439805637964853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4140359839253074183953137 3105269879439805637964853)
      ·
        refine ⟨291119051197481778559205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3105269879439805637964853 291119051197481778559205)
        ·
          refine ⟨54584822099527833479851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 291119051197481778559205 54584822099527833479851)
          ·
            refine ⟨81877233149291750219777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54584822099527833479851 81877233149291750219777)
            ·
              refine ⟨61407924861968812664833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81877233149291750219777 61407924861968812664833)
              ·
                refine ⟨46055943646476609498625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61407924861968812664833 46055943646476609498625)
                ·
                  refine ⟨34541957734857457123969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46055943646476609498625 34541957734857457123969)
                  ·
                    rfl

theorem cell20_75679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 2, 2, 2].length) (baseStart_75679 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_75679 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_75679 prefixEnd_75679 := by exact prefixLift 75679
  have htrace : WordTrace (prefixWord ++ tailWord_75679) baseStart_75679 baseEnd_75679 := by
    simpa [prefixWord, tailWord_75679, baseEnd_75679] using wordTrace_append hprefix tailTrace_75679
  have hstable : (prefixWord ++ tailWord_75679).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75679).length < 2 ^ (prefixWord ++ tailWord_75679).sum := by decide
  have hdescent : baseEnd_75679 < baseStart_75679 := by decide
  rcases family_descends (prefixWord ++ tailWord_75679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75732 : List Nat := [2, 4, 1, 2, 1, 1, 9]
def baseStart_75732 : Nat := 118140960795 + 75732 * 2 ^ 59
def prefixEnd_75732 : Nat := 4983230072969 + 3 ^ 40 * 75732 * 2
def baseEnd_75732 : Nat := 3840683153224980928565

theorem tailTrace_75732 : CollatzResearch.WordTrace tailWord_75732 prefixEnd_75732 3840683153224980928565 := by
  unfold tailWord_75732
  simp only [CollatzResearch.WordTrace]
  refine ⟨1381086480821686420490725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1841448641095581893987633 1381086480821686420490725)
  ·
    refine ⟨258953715154066203842011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1381086480821686420490725 258953715154066203842011)
    ·
      refine ⟨388430572731099305763017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258953715154066203842011 388430572731099305763017)
      ·
        refine ⟨291322929548324479322263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 388430572731099305763017 291322929548324479322263)
        ·
          refine ⟨436984394322486718983395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 291322929548324479322263 436984394322486718983395)
          ·
            refine ⟨655476591483730078475093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 436984394322486718983395 655476591483730078475093)
            ·
              refine ⟨3840683153224980928565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 655476591483730078475093 3840683153224980928565)
              ·
                rfl

theorem cell20_75732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 9].length) (baseStart_75732 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_75732 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_75732 prefixEnd_75732 := by exact prefixLift 75732
  have htrace : WordTrace (prefixWord ++ tailWord_75732) baseStart_75732 baseEnd_75732 := by
    simpa [prefixWord, tailWord_75732, baseEnd_75732] using wordTrace_append hprefix tailTrace_75732
  have hstable : (prefixWord ++ tailWord_75732).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75732).length < 2 ^ (prefixWord ++ tailWord_75732).sum := by decide
  have hdescent : baseEnd_75732 < baseStart_75732 := by decide
  rcases family_descends (prefixWord ++ tailWord_75732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75777 : List Nat := [1, 2, 4, 1, 2, 1, 1, 1, 7]
def baseStart_75777 : Nat := 118140960795 + 75777 * 2 ^ 59
def prefixEnd_75777 : Nat := 4983230072969 + 3 ^ 40 * 75777 * 2
def baseEnd_75777 : Nat := 34586687605204671856901

theorem tailTrace_75777 : CollatzResearch.WordTrace tailWord_75777 prefixEnd_75777 34586687605204671856901 := by
  unfold tailWord_75777
  simp only [CollatzResearch.WordTrace]
  refine ⟨2763814246480345526369585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1842542830986897017579723 2763814246480345526369585)
  ·
    refine ⟨2072860684860259144777189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2763814246480345526369585 2072860684860259144777189)
    ·
      refine ⟨388661378411298589645723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2072860684860259144777189 388661378411298589645723)
      ·
        refine ⟨582992067616947884468585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 388661378411298589645723 582992067616947884468585)
        ·
          refine ⟨437244050712710913351439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 582992067616947884468585 437244050712710913351439)
          ·
            refine ⟨655866076069066370027159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 437244050712710913351439 655866076069066370027159)
            ·
              refine ⟨983799114103599555040739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 655866076069066370027159 983799114103599555040739)
              ·
                refine ⟨1475698671155399332561109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 983799114103599555040739 1475698671155399332561109)
                ·
                  refine ⟨34586687605204671856901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1475698671155399332561109 34586687605204671856901)
                  ·
                    rfl

theorem cell20_75777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 7].length) (baseStart_75777 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_75777 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_75777 prefixEnd_75777 := by exact prefixLift 75777
  have htrace : WordTrace (prefixWord ++ tailWord_75777) baseStart_75777 baseEnd_75777 := by
    simpa [prefixWord, tailWord_75777, baseEnd_75777] using wordTrace_append hprefix tailTrace_75777
  have hstable : (prefixWord ++ tailWord_75777).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75777).length < 2 ^ (prefixWord ++ tailWord_75777).sum := by decide
  have hdescent : baseEnd_75777 < baseStart_75777 := by decide
  rcases family_descends (prefixWord ++ tailWord_75777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75797 : List Nat := [1, 3, 2, 1, 6, 1, 1, 1, 4]
def baseStart_75797 : Nat := 118140960795 + 75797 * 2 ^ 59
def prefixEnd_75797 : Nat := 4983230072969 + 3 ^ 40 * 75797 * 2
def baseEnd_75797 : Nat := 34595816150173491190153

theorem tailTrace_75797 : CollatzResearch.WordTrace tailWord_75797 prefixEnd_75797 34595816150173491190153 := by
  unfold tailWord_75797
  simp only [CollatzResearch.WordTrace]
  refine ⟨2764543706407888942097645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1843029137605259294731763 2764543706407888942097645)
  ·
    refine ⟨1036703889902958353286617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2764543706407888942097645 1036703889902958353286617)
    ·
      refine ⟨777527917427218764964963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1036703889902958353286617 777527917427218764964963)
      ·
        refine ⟨1166291876140828147447445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 777527917427218764964963 1166291876140828147447445)
        ·
          refine ⟨54669931694101319411599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1166291876140828147447445 54669931694101319411599)
          ·
            refine ⟨82004897541151979117399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54669931694101319411599 82004897541151979117399)
            ·
              refine ⟨123007346311727968676099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82004897541151979117399 123007346311727968676099)
              ·
                refine ⟨184511019467591953014149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123007346311727968676099 184511019467591953014149)
                ·
                  refine ⟨34595816150173491190153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 184511019467591953014149 34595816150173491190153)
                  ·
                    rfl

theorem cell20_75797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 1, 4].length) (baseStart_75797 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_75797 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_75797 prefixEnd_75797 := by exact prefixLift 75797
  have htrace : WordTrace (prefixWord ++ tailWord_75797) baseStart_75797 baseEnd_75797 := by
    simpa [prefixWord, tailWord_75797, baseEnd_75797] using wordTrace_append hprefix tailTrace_75797
  have hstable : (prefixWord ++ tailWord_75797).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75797).length < 2 ^ (prefixWord ++ tailWord_75797).sum := by decide
  have hdescent : baseEnd_75797 < baseStart_75797 := by decide
  rcases family_descends (prefixWord ++ tailWord_75797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75877 : List Nat := [1, 3, 1, 3, 2, 3, 1, 2, 4]
def baseStart_75877 : Nat := 118140960795 + 75877 * 2 ^ 59
def prefixEnd_75877 : Nat := 4983230072969 + 3 ^ 40 * 75877 * 2
def baseEnd_75877 : Nat := 34632330330048768523159

theorem tailTrace_75877 : CollatzResearch.WordTrace tailWord_75877 prefixEnd_75877 34632330330048768523159 := by
  unfold tailWord_75877
  simp only [CollatzResearch.WordTrace]
  refine ⟨2767461546118062605009885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1844974364078708403339923 2767461546118062605009885)
  ·
    refine ⟨1037798079794273476878707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2767461546118062605009885 1037798079794273476878707)
    ·
      refine ⟨1556697119691410215318061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1037798079794273476878707 1556697119691410215318061)
      ·
        refine ⟨583761419884278830744273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1556697119691410215318061 583761419884278830744273)
        ·
          refine ⟨437821064913209123058205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 583761419884278830744273 437821064913209123058205)
          ·
            refine ⟨164182899342453421146827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 437821064913209123058205 164182899342453421146827)
            ·
              refine ⟨246274349013680131720241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164182899342453421146827 246274349013680131720241)
              ·
                refine ⟨184705761760260098790181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 246274349013680131720241 184705761760260098790181)
                ·
                  refine ⟨34632330330048768523159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 184705761760260098790181 34632330330048768523159)
                  ·
                    rfl

theorem cell20_75877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 2, 4].length) (baseStart_75877 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_75877 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_75877 prefixEnd_75877 := by exact prefixLift 75877
  have htrace : WordTrace (prefixWord ++ tailWord_75877) baseStart_75877 baseEnd_75877 := by
    simpa [prefixWord, tailWord_75877, baseEnd_75877] using wordTrace_append hprefix tailTrace_75877
  have hstable : (prefixWord ++ tailWord_75877).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75877).length < 2 ^ (prefixWord ++ tailWord_75877).sum := by decide
  have hdescent : baseEnd_75877 < baseStart_75877 := by decide
  rcases family_descends (prefixWord ++ tailWord_75877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75922 : List Nat := [3, 2, 3, 1, 1, 1, 2, 7]
def baseStart_75922 : Nat := 118140960795 + 75922 * 2 ^ 59
def prefixEnd_75922 : Nat := 4983230072969 + 3 ^ 40 * 75922 * 2
def baseEnd_75922 : Nat := 11550956518742870674325

theorem tailTrace_75922 : CollatzResearch.WordTrace tailWord_75922 prefixEnd_75922 11550956518742870674325 := by
  unfold tailWord_75922
  simp only [CollatzResearch.WordTrace]
  refine ⟨692275707738758822599505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1846068553970023526932013 692275707738758822599505)
  ·
    refine ⟨519206780804069116949629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 692275707738758822599505 519206780804069116949629)
    ·
      refine ⟨194702542801525918856111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 519206780804069116949629 194702542801525918856111)
      ·
        refine ⟨292053814202288878284167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194702542801525918856111 292053814202288878284167)
        ·
          refine ⟨438080721303433317426251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 292053814202288878284167 438080721303433317426251)
          ·
            refine ⟨657121081955149976139377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 438080721303433317426251 657121081955149976139377)
            ·
              refine ⟨492840811466362482104533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 657121081955149976139377 492840811466362482104533)
              ·
                refine ⟨11550956518742870674325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 492840811466362482104533 11550956518742870674325)
                ·
                  rfl

theorem cell20_75922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 7].length) (baseStart_75922 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_75922 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_75922 prefixEnd_75922 := by exact prefixLift 75922
  have htrace : WordTrace (prefixWord ++ tailWord_75922) baseStart_75922 baseEnd_75922 := by
    simpa [prefixWord, tailWord_75922, baseEnd_75922] using wordTrace_append hprefix tailTrace_75922
  have hstable : (prefixWord ++ tailWord_75922).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75922).length < 2 ^ (prefixWord ++ tailWord_75922).sum := by decide
  have hdescent : baseEnd_75922 < baseStart_75922 := by decide
  rcases family_descends (prefixWord ++ tailWord_75922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75929 : List Nat := [1, 2, 1, 2, 1, 2, 1, 7, 3]
def baseStart_75929 : Nat := 118140960795 + 75929 * 2 ^ 59
def prefixEnd_75929 : Nat := 4983230072969 + 3 ^ 40 * 75929 * 2
def baseEnd_75929 : Nat := 34656064546967698789613

theorem tailTrace_75929 : CollatzResearch.WordTrace tailWord_75929 prefixEnd_75929 34656064546967698789613 := by
  unfold tailWord_75929
  simp only [CollatzResearch.WordTrace]
  refine ⟨2769358141929675485902841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1846238761286450323935227 2769358141929675485902841)
  ·
    refine ⟨2077018606447256614427131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2769358141929675485902841 2077018606447256614427131)
    ·
      refine ⟨3115527909670884921640697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2077018606447256614427131 3115527909670884921640697)
      ·
        refine ⟨2336645932253163691230523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3115527909670884921640697 2336645932253163691230523)
        ·
          refine ⟨3504968898379745536845785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2336645932253163691230523 3504968898379745536845785)
          ·
            refine ⟨2628726673784809152634339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3504968898379745536845785 2628726673784809152634339)
            ·
              refine ⟨3943090010677213728951509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2628726673784809152634339 3943090010677213728951509)
              ·
                refine ⟨92416172125247196772301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3943090010677213728951509 92416172125247196772301)
                ·
                  refine ⟨34656064546967698789613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 92416172125247196772301 34656064546967698789613)
                  ·
                    rfl

theorem cell20_75929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 7, 3].length) (baseStart_75929 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_75929 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_75929 prefixEnd_75929 := by exact prefixLift 75929
  have htrace : WordTrace (prefixWord ++ tailWord_75929) baseStart_75929 baseEnd_75929 := by
    simpa [prefixWord, tailWord_75929, baseEnd_75929] using wordTrace_append hprefix tailTrace_75929
  have hstable : (prefixWord ++ tailWord_75929).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75929).length < 2 ^ (prefixWord ++ tailWord_75929).sum := by decide
  have hdescent : baseEnd_75929 < baseStart_75929 := by decide
  rcases family_descends (prefixWord ++ tailWord_75929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75949 : List Nat := [1, 5, 2, 1, 2, 1, 3, 3, 2]
def baseStart_75949 : Nat := 118140960795 + 75949 * 2 ^ 59
def prefixEnd_75949 : Nat := 4983230072969 + 3 ^ 40 * 75949 * 2
def baseEnd_75949 : Nat := 34665193091936518122865

theorem tailTrace_75949 : CollatzResearch.WordTrace tailWord_75949 prefixEnd_75949 34665193091936518122865 := by
  unfold tailWord_75949
  simp only [CollatzResearch.WordTrace]
  refine ⟨2770087601857218901630901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1846725067904812601087267 2770087601857218901630901)
  ·
    refine ⟨259695712674114272027897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2770087601857218901630901 259695712674114272027897)
    ·
      refine ⟨194771784505585704020923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 259695712674114272027897 194771784505585704020923)
      ·
        refine ⟨292157676758378556031385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194771784505585704020923 292157676758378556031385)
        ·
          refine ⟨219118257568783917023539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 292157676758378556031385 219118257568783917023539)
          ·
            refine ⟨328677386353175875535309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219118257568783917023539 328677386353175875535309)
            ·
              refine ⟨123254019882440953325741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 328677386353175875535309 123254019882440953325741)
              ·
                refine ⟨46220257455915357497153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 123254019882440953325741 46220257455915357497153)
                ·
                  refine ⟨34665193091936518122865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46220257455915357497153 34665193091936518122865)
                  ·
                    rfl

theorem cell20_75949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 3, 2].length) (baseStart_75949 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_75949 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_75949 prefixEnd_75949 := by exact prefixLift 75949
  have htrace : WordTrace (prefixWord ++ tailWord_75949) baseStart_75949 baseEnd_75949 := by
    simpa [prefixWord, tailWord_75949, baseEnd_75949] using wordTrace_append hprefix tailTrace_75949
  have hstable : (prefixWord ++ tailWord_75949).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75949).length < 2 ^ (prefixWord ++ tailWord_75949).sum := by decide
  have hdescent : baseEnd_75949 < baseStart_75949 := by decide
  rcases family_descends (prefixWord ++ tailWord_75949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75966 : List Nat := [4, 2, 1, 1, 4, 1, 3, 2, 2]
def baseStart_75966 : Nat := 118140960795 + 75966 * 2 ^ 59
def prefixEnd_75966 : Nat := 4983230072969 + 3 ^ 40 * 75966 * 2
def baseEnd_75966 : Nat := 34672952355160014556129

theorem tailTrace_75966 : CollatzResearch.WordTrace tailWord_75966 prefixEnd_75966 34672952355160014556129 := by
  unfold tailWord_75966
  simp only [CollatzResearch.WordTrace]
  refine ⟨346338455349453850624969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1847138428530420536666501 346338455349453850624969)
  ·
    refine ⟨259753841512090387968727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 346338455349453850624969 259753841512090387968727)
    ·
      refine ⟨389630762268135581953091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259753841512090387968727 389630762268135581953091)
      ·
        refine ⟨584446143402203372929637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 389630762268135581953091 584446143402203372929637)
        ·
          refine ⟨109583651887913132424307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 584446143402203372929637 109583651887913132424307)
          ·
            refine ⟨164375477831869698636461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109583651887913132424307 164375477831869698636461)
            ·
              refine ⟨61640804186951136988673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 164375477831869698636461 61640804186951136988673)
              ·
                refine ⟨46230603140213352741505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61640804186951136988673 46230603140213352741505)
                ·
                  refine ⟨34672952355160014556129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46230603140213352741505 34672952355160014556129)
                  ·
                    rfl

theorem cell20_75966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 3, 2, 2].length) (baseStart_75966 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_75966 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_75966 prefixEnd_75966 := by exact prefixLift 75966
  have htrace : WordTrace (prefixWord ++ tailWord_75966) baseStart_75966 baseEnd_75966 := by
    simpa [prefixWord, tailWord_75966, baseEnd_75966] using wordTrace_append hprefix tailTrace_75966
  have hstable : (prefixWord ++ tailWord_75966).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75966).length < 2 ^ (prefixWord ++ tailWord_75966).sum := by decide
  have hdescent : baseEnd_75966 < baseStart_75966 := by decide
  rcases family_descends (prefixWord ++ tailWord_75966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75967 : List Nat := [1, 1, 2, 2, 2, 2, 1, 6, 3]
def baseStart_75967 : Nat := 118140960795 + 75967 * 2 ^ 59
def prefixEnd_75967 : Nat := 4983230072969 + 3 ^ 40 * 75967 * 2
def baseEnd_75967 : Nat := 34673408782408455522791

theorem tailTrace_75967 : CollatzResearch.WordTrace tailWord_75967 prefixEnd_75967 34673408782408455522791 := by
  unfold tailWord_75967
  simp only [CollatzResearch.WordTrace]
  refine ⟨2770744115792007975786155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1847162743861338650524103 2770744115792007975786155)
  ·
    refine ⟨4156116173688011963679233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2770744115792007975786155 4156116173688011963679233)
    ·
      refine ⟨3117087130266008972759425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4156116173688011963679233 3117087130266008972759425)
      ·
        refine ⟨2337815347699506729569569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3117087130266008972759425 2337815347699506729569569)
        ·
          refine ⟨1753361510774630047177177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2337815347699506729569569 1753361510774630047177177)
          ·
            refine ⟨1315021133080972535382883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1753361510774630047177177 1315021133080972535382883)
            ·
              refine ⟨1972531699621458803074325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1315021133080972535382883 1972531699621458803074325)
              ·
                refine ⟨92462423419755881394109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1972531699621458803074325 92462423419755881394109)
                ·
                  refine ⟨34673408782408455522791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 92462423419755881394109 34673408782408455522791)
                  ·
                    rfl

theorem cell20_75967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 6, 3].length) (baseStart_75967 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_75967 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_75967 prefixEnd_75967 := by exact prefixLift 75967
  have htrace : WordTrace (prefixWord ++ tailWord_75967) baseStart_75967 baseEnd_75967 := by
    simpa [prefixWord, tailWord_75967, baseEnd_75967] using wordTrace_append hprefix tailTrace_75967
  have hstable : (prefixWord ++ tailWord_75967).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75967).length < 2 ^ (prefixWord ++ tailWord_75967).sum := by decide
  have hdescent : baseEnd_75967 < baseStart_75967 := by decide
  rcases family_descends (prefixWord ++ tailWord_75967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76022 : List Nat := [5, 1, 1, 1, 1, 1, 3, 4, 3]
def baseStart_76022 : Nat := 118140960795 + 76022 * 2 ^ 59
def prefixEnd_76022 : Nat := 4983230072969 + 3 ^ 40 * 76022 * 2
def baseEnd_76022 : Nat := 34698512281072708689233

theorem tailTrace_76022 : CollatzResearch.WordTrace tailWord_76022 prefixEnd_76022 34698512281072708689233 := by
  unfold tailWord_76022
  simp only [CollatzResearch.WordTrace]
  refine ⟨173296883162047023064895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1848500087061834912692213 173296883162047023064895)
  ·
    refine ⟨259945324743070534597343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173296883162047023064895 259945324743070534597343)
    ·
      refine ⟨389917987114605801896015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259945324743070534597343 389917987114605801896015)
      ·
        refine ⟨584876980671908702844023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 389917987114605801896015 584876980671908702844023)
        ·
          refine ⟨877315471007863054266035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 584876980671908702844023 877315471007863054266035)
          ·
            refine ⟨1315973206511794581399053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 877315471007863054266035 1315973206511794581399053)
            ·
              refine ⟨493489952441922968024645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1315973206511794581399053 493489952441922968024645)
              ·
                refine ⟨92529366082860556504621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 493489952441922968024645 92529366082860556504621)
                ·
                  refine ⟨34698512281072708689233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 92529366082860556504621 34698512281072708689233)
                  ·
                    rfl

theorem cell20_76022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_76022 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_76022 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_76022 prefixEnd_76022 := by exact prefixLift 76022
  have htrace : WordTrace (prefixWord ++ tailWord_76022) baseStart_76022 baseEnd_76022 := by
    simpa [prefixWord, tailWord_76022, baseEnd_76022] using wordTrace_append hprefix tailTrace_76022
  have hstable : (prefixWord ++ tailWord_76022).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76022).length < 2 ^ (prefixWord ++ tailWord_76022).sum := by decide
  have hdescent : baseEnd_76022 < baseStart_76022 := by decide
  rcases family_descends (prefixWord ++ tailWord_76022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76043 : List Nat := [1, 1, 1, 1, 5, 2, 1, 5, 3]
def baseStart_76043 : Nat := 118140960795 + 76043 * 2 ^ 59
def prefixEnd_76043 : Nat := 4983230072969 + 3 ^ 40 * 76043 * 2
def baseEnd_76043 : Nat := 34708097253289968989147

theorem tailTrace_76043 : CollatzResearch.WordTrace tailWord_76043 prefixEnd_76043 34708097253289968989147 := by
  unfold tailWord_76043
  simp only [CollatzResearch.WordTrace]
  refine ⟨2773516063516672955552783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1849010709011115303701855 2773516063516672955552783)
  ·
    refine ⟨4160274095275009433329175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2773516063516672955552783 4160274095275009433329175)
    ·
      refine ⟨6240411142912514149993763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4160274095275009433329175 6240411142912514149993763)
      ·
        refine ⟨9360616714368771224990645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6240411142912514149993763 9360616714368771224990645)
        ·
          refine ⟨877557816972072302342873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9360616714368771224990645 877557816972072302342873)
          ·
            refine ⟨658168362729054226757155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 877557816972072302342873 658168362729054226757155)
            ·
              refine ⟨987252544093581340135733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 658168362729054226757155 987252544093581340135733)
              ·
                refine ⟨92554926008773250637725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 987252544093581340135733 92554926008773250637725)
                ·
                  refine ⟨34708097253289968989147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 92554926008773250637725 34708097253289968989147)
                  ·
                    rfl

theorem cell20_76043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 5, 3].length) (baseStart_76043 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_76043 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_76043 prefixEnd_76043 := by exact prefixLift 76043
  have htrace : WordTrace (prefixWord ++ tailWord_76043) baseStart_76043 baseEnd_76043 := by
    simpa [prefixWord, tailWord_76043, baseEnd_76043] using wordTrace_append hprefix tailTrace_76043
  have hstable : (prefixWord ++ tailWord_76043).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76043).length < 2 ^ (prefixWord ++ tailWord_76043).sum := by decide
  have hdescent : baseEnd_76043 < baseStart_76043 := by decide
  rcases family_descends (prefixWord ++ tailWord_76043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76077 : List Nat := [1, 5, 3, 1, 2, 1, 1, 1, 5]
def baseStart_76077 : Nat := 118140960795 + 76077 * 2 ^ 59
def prefixEnd_76077 : Nat := 4983230072969 + 3 ^ 40 * 76077 * 2
def baseEnd_76077 : Nat := 34723615779736961855675

theorem tailTrace_76077 : CollatzResearch.WordTrace tailWord_76077 prefixEnd_76077 34723615779736961855675 := by
  unfold tailWord_76077
  simp only [CollatzResearch.WordTrace]
  refine ⟨2774756145393496762290485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1849837430262331174860323 2774756145393496762290485)
  ·
    refine ⟨260133388630640321464733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2774756145393496762290485 260133388630640321464733)
    ·
      refine ⟨97550020736490120549275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 260133388630640321464733 97550020736490120549275)
      ·
        refine ⟨146325031104735180823913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97550020736490120549275 146325031104735180823913)
        ·
          refine ⟨109743773328551385617935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146325031104735180823913 109743773328551385617935)
          ·
            refine ⟨164615659992827078426903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109743773328551385617935 164615659992827078426903)
            ·
              refine ⟨246923489989240617640355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164615659992827078426903 246923489989240617640355)
              ·
                refine ⟨370385234983860926460533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 246923489989240617640355 370385234983860926460533)
                ·
                  refine ⟨34723615779736961855675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 370385234983860926460533 34723615779736961855675)
                  ·
                    rfl

theorem cell20_76077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_76077 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_76077 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_76077 prefixEnd_76077 := by exact prefixLift 76077
  have htrace : WordTrace (prefixWord ++ tailWord_76077) baseStart_76077 baseEnd_76077 := by
    simpa [prefixWord, tailWord_76077, baseEnd_76077] using wordTrace_append hprefix tailTrace_76077
  have hstable : (prefixWord ++ tailWord_76077).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76077).length < 2 ^ (prefixWord ++ tailWord_76077).sum := by decide
  have hdescent : baseEnd_76077 < baseStart_76077 := by decide
  rcases family_descends (prefixWord ++ tailWord_76077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76084 : List Nat := [2, 5, 1, 1, 1, 3, 2, 1, 4]
def baseStart_76084 : Nat := 118140960795 + 76084 * 2 ^ 59
def prefixEnd_76084 : Nat := 4983230072969 + 3 ^ 40 * 76084 * 2
def baseEnd_76084 : Nat := 34726810770476048622313

theorem tailTrace_76084 : CollatzResearch.WordTrace tailWord_76084 prefixEnd_76084 34726810770476048622313 := by
  unfold tailWord_76084
  simp only [CollatzResearch.WordTrace]
  refine ⟨1387505728184068478897653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1850007637578757971863537 1387505728184068478897653)
  ·
    refine ⟨130078662017256419896655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1387505728184068478897653 130078662017256419896655)
    ·
      refine ⟨195117993025884629844983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130078662017256419896655 195117993025884629844983)
      ·
        refine ⟨292676989538826944767475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195117993025884629844983 292676989538826944767475)
        ·
          refine ⟨439015484308240417151213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 292676989538826944767475 439015484308240417151213)
          ·
            refine ⟨164630806615590156431705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 439015484308240417151213 164630806615590156431705)
            ·
              refine ⟨123473104961692617323779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 164630806615590156431705 123473104961692617323779)
              ·
                refine ⟨185209657442538925985669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123473104961692617323779 185209657442538925985669)
                ·
                  refine ⟨34726810770476048622313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 185209657442538925985669 34726810770476048622313)
                  ·
                    rfl

theorem cell20_76084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_76084 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_76084 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_76084 prefixEnd_76084 := by exact prefixLift 76084
  have htrace : WordTrace (prefixWord ++ tailWord_76084) baseStart_76084 baseEnd_76084 := by
    simpa [prefixWord, tailWord_76084, baseEnd_76084] using wordTrace_append hprefix tailTrace_76084
  have hstable : (prefixWord ++ tailWord_76084).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76084).length < 2 ^ (prefixWord ++ tailWord_76084).sum := by decide
  have hdescent : baseEnd_76084 < baseStart_76084 := by decide
  rcases family_descends (prefixWord ++ tailWord_76084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76088 : List Nat := [2, 1, 2, 1, 3, 1, 3, 3, 4]
def baseStart_76088 : Nat := 118140960795 + 76088 * 2 ^ 59
def prefixEnd_76088 : Nat := 4983230072969 + 3 ^ 40 * 76088 * 2
def baseEnd_76088 : Nat := 34728636479469812488963

theorem tailTrace_76088 : CollatzResearch.WordTrace tailWord_76088 prefixEnd_76088 34728636479469812488963 := by
  unfold tailWord_76088
  simp only [CollatzResearch.WordTrace]
  refine ⟨1387578674176822820470459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1850104898902430427293945 1387578674176822820470459)
  ·
    refine ⟨2081368011265234230705689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1387578674176822820470459 2081368011265234230705689)
    ·
      refine ⟨1561026008448925673029267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2081368011265234230705689 1561026008448925673029267)
      ·
        refine ⟨2341539012673388509543901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1561026008448925673029267 2341539012673388509543901)
        ·
          refine ⟨878077129752520691078963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2341539012673388509543901 878077129752520691078963)
          ·
            refine ⟨1317115694628781036618445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 878077129752520691078963 1317115694628781036618445)
            ·
              refine ⟨493918385485792888731917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1317115694628781036618445 493918385485792888731917)
              ·
                refine ⟨185219394557172333274469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 493918385485792888731917 185219394557172333274469)
                ·
                  refine ⟨34728636479469812488963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 185219394557172333274469 34728636479469812488963)
                  ·
                    rfl

theorem cell20_76088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 3, 4].length) (baseStart_76088 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_76088 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_76088 prefixEnd_76088 := by exact prefixLift 76088
  have htrace : WordTrace (prefixWord ++ tailWord_76088) baseStart_76088 baseEnd_76088 := by
    simpa [prefixWord, tailWord_76088, baseEnd_76088] using wordTrace_append hprefix tailTrace_76088
  have hstable : (prefixWord ++ tailWord_76088).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76088).length < 2 ^ (prefixWord ++ tailWord_76088).sum := by decide
  have hdescent : baseEnd_76088 < baseStart_76088 := by decide
  rcases family_descends (prefixWord ++ tailWord_76088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76095 : List Nat := [1, 1, 2, 2, 4, 1, 2, 7]
def baseStart_76095 : Nat := 118140960795 + 76095 * 2 ^ 59
def prefixEnd_76095 : Nat := 4983230072969 + 3 ^ 40 * 76095 * 2
def baseEnd_76095 : Nat := 11577277156736299751867

theorem tailTrace_76095 : CollatzResearch.WordTrace tailWord_76095 prefixEnd_76095 11577277156736299751867 := by
  unfold tailWord_76095
  simp only [CollatzResearch.WordTrace]
  refine ⟨2775412659328285836445739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1850275106218857224297159 2775412659328285836445739)
  ·
    refine ⟨4163118988992428754668609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2775412659328285836445739 4163118988992428754668609)
    ·
      refine ⟨3122339241744321566001457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4163118988992428754668609 3122339241744321566001457)
      ·
        refine ⟨2341754431308241174501093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3122339241744321566001457 2341754431308241174501093)
        ·
          refine ⟨439078955870295220218955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2341754431308241174501093 439078955870295220218955)
          ·
            refine ⟨658618433805442830328433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 439078955870295220218955 658618433805442830328433)
            ·
              refine ⟨493963825354082122746325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 658618433805442830328433 493963825354082122746325)
              ·
                refine ⟨11577277156736299751867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 493963825354082122746325 11577277156736299751867)
                ·
                  rfl

theorem cell20_76095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 7].length) (baseStart_76095 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_76095 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_76095 prefixEnd_76095 := by exact prefixLift 76095
  have htrace : WordTrace (prefixWord ++ tailWord_76095) baseStart_76095 baseEnd_76095 := by
    simpa [prefixWord, tailWord_76095, baseEnd_76095] using wordTrace_append hprefix tailTrace_76095
  have hstable : (prefixWord ++ tailWord_76095).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76095).length < 2 ^ (prefixWord ++ tailWord_76095).sum := by decide
  have hdescent : baseEnd_76095 < baseStart_76095 := by decide
  rcases family_descends (prefixWord ++ tailWord_76095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76112 : List Nat := [2, 1, 1, 1, 1, 6, 4, 4]
def baseStart_76112 : Nat := 118140960795 + 76112 * 2 ^ 59
def prefixEnd_76112 : Nat := 4983230072969 + 3 ^ 40 * 76112 * 2
def baseEnd_76112 : Nat := 11579863577810798562955

theorem tailTrace_76112 : CollatzResearch.WordTrace tailWord_76112 prefixEnd_76112 11579863577810798562955 := by
  unfold tailWord_76112
  simp only [CollatzResearch.WordTrace]
  refine ⟨1388016350133348869907295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1850688466844465159876393 1388016350133348869907295)
  ·
    refine ⟨2082024525200023304860943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1388016350133348869907295 2082024525200023304860943)
    ·
      refine ⟨3123036787800034957291415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2082024525200023304860943 3123036787800034957291415)
      ·
        refine ⟨4684555181700052435937123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3123036787800034957291415 4684555181700052435937123)
        ·
          refine ⟨7026832772550078653905685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4684555181700052435937123 7026832772550078653905685)
          ·
            refine ⟨329382786213284936901829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 7026832772550078653905685 329382786213284936901829)
            ·
              refine ⟨61759272414990925669093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 329382786213284936901829 61759272414990925669093)
              ·
                refine ⟨11579863577810798562955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61759272414990925669093 11579863577810798562955)
                ·
                  rfl

theorem cell20_76112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 4, 4].length) (baseStart_76112 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_76112 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_76112 prefixEnd_76112 := by exact prefixLift 76112
  have htrace : WordTrace (prefixWord ++ tailWord_76112) baseStart_76112 baseEnd_76112 := by
    simpa [prefixWord, tailWord_76112, baseEnd_76112] using wordTrace_append hprefix tailTrace_76112
  have hstable : (prefixWord ++ tailWord_76112).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76112).length < 2 ^ (prefixWord ++ tailWord_76112).sum := by decide
  have hdescent : baseEnd_76112 < baseStart_76112 := by decide
  rcases family_descends (prefixWord ++ tailWord_76112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76133 : List Nat := [1, 3, 1, 3, 1, 3, 8]
def baseStart_76133 : Nat := 118140960795 + 76133 * 2 ^ 59
def prefixEnd_76133 : Nat := 4983230072969 + 3 ^ 40 * 76133 * 2
def baseEnd_76133 : Nat := 3861019522849961776531

theorem tailTrace_76133 : CollatzResearch.WordTrace tailWord_76133 prefixEnd_76133 3861019522849961776531 := by
  unfold tailWord_76133
  simp only [CollatzResearch.WordTrace]
  refine ⟨2776798633190618326329053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1851199088793745550886035 2776798633190618326329053)
  ·
    refine ⟨1041299487446481872373395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2776798633190618326329053 1041299487446481872373395)
    ·
      refine ⟨1561949231169722808560093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1041299487446481872373395 1561949231169722808560093)
      ·
        refine ⟨585730961688646053210035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1561949231169722808560093 585730961688646053210035)
        ·
          refine ⟨878596442532969079815053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 585730961688646053210035 878596442532969079815053)
          ·
            refine ⟨329473665949863404930645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 878596442532969079815053 329473665949863404930645)
            ·
              refine ⟨3861019522849961776531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 329473665949863404930645 3861019522849961776531)
              ·
                rfl

theorem cell20_76133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 8].length) (baseStart_76133 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_76133 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_76133 prefixEnd_76133 := by exact prefixLift 76133
  have htrace : WordTrace (prefixWord ++ tailWord_76133) baseStart_76133 baseEnd_76133 := by
    simpa [prefixWord, tailWord_76133, baseEnd_76133] using wordTrace_append hprefix tailTrace_76133
  have hstable : (prefixWord ++ tailWord_76133).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76133).length < 2 ^ (prefixWord ++ tailWord_76133).sum := by decide
  have hdescent : baseEnd_76133 < baseStart_76133 := by decide
  rcases family_descends (prefixWord ++ tailWord_76133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76164 : List Nat := [2, 3, 2, 1, 1, 2, 2, 1, 6]
def baseStart_76164 : Nat := 118140960795 + 76164 * 2 ^ 59
def prefixEnd_76164 : Nat := 4983230072969 + 3 ^ 40 * 76164 * 2
def baseEnd_76164 : Nat := 34763324950351325955319

theorem tailTrace_76164 : CollatzResearch.WordTrace tailWord_76164 prefixEnd_76164 34763324950351325955319 := by
  unfold tailWord_76164
  simp only [CollatzResearch.WordTrace]
  refine ⟨1388964648039155310353773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1851952864052207080471697 1388964648039155310353773)
  ·
    refine ⟨520861743014683241382665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1388964648039155310353773 520861743014683241382665)
    ·
      refine ⟨390646307261012431036999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 520861743014683241382665 390646307261012431036999)
      ·
        refine ⟨585969460891518646555499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 390646307261012431036999 585969460891518646555499)
        ·
          refine ⟨878954191337277969833249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 585969460891518646555499 878954191337277969833249)
          ·
            refine ⟨659215643502958477374937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 878954191337277969833249 659215643502958477374937)
            ·
              refine ⟨494411732627218858031203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 659215643502958477374937 494411732627218858031203)
              ·
                refine ⟨741617598940828287046805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 494411732627218858031203 741617598940828287046805)
                ·
                  refine ⟨34763324950351325955319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 741617598940828287046805 34763324950351325955319)
                  ·
                    rfl

theorem cell20_76164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_76164 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_76164 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_76164 prefixEnd_76164 := by exact prefixLift 76164
  have htrace : WordTrace (prefixWord ++ tailWord_76164) baseStart_76164 baseEnd_76164 := by
    simpa [prefixWord, tailWord_76164, baseEnd_76164] using wordTrace_append hprefix tailTrace_76164
  have hstable : (prefixWord ++ tailWord_76164).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76164).length < 2 ^ (prefixWord ++ tailWord_76164).sum := by decide
  have hdescent : baseEnd_76164 < baseStart_76164 := by decide
  rcases family_descends (prefixWord ++ tailWord_76164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76171 : List Nat := [1, 1, 1, 1, 4, 4, 2, 6]
def baseStart_76171 : Nat := 118140960795 + 76171 * 2 ^ 59
def prefixEnd_76171 : Nat := 4983230072969 + 3 ^ 40 * 76171 * 2
def baseEnd_76171 : Nat := 11588839980363470907319

theorem tailTrace_76171 : CollatzResearch.WordTrace tailWord_76171 prefixEnd_76171 11588839980363470907319 := by
  unfold tailWord_76171
  simp only [CollatzResearch.WordTrace]
  refine ⟨2778184607052950816212367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1852123071368633877474911 2778184607052950816212367)
  ·
    refine ⟨4167276910579426224318551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2778184607052950816212367 4167276910579426224318551)
    ·
      refine ⟨6250915365869139336477827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4167276910579426224318551 6250915365869139336477827)
      ·
        refine ⟨9376373048803709004716741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6250915365869139336477827 9376373048803709004716741)
        ·
          refine ⟨1758069946650695438384389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9376373048803709004716741 1758069946650695438384389)
          ·
            refine ⟨329638114997005394697073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1758069946650695438384389 329638114997005394697073)
            ·
              refine ⟨247228586247754046022805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 329638114997005394697073 247228586247754046022805)
              ·
                refine ⟨11588839980363470907319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 247228586247754046022805 11588839980363470907319)
                ·
                  rfl

theorem cell20_76171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 6].length) (baseStart_76171 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_76171 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_76171 prefixEnd_76171 := by exact prefixLift 76171
  have htrace : WordTrace (prefixWord ++ tailWord_76171) baseStart_76171 baseEnd_76171 := by
    simpa [prefixWord, tailWord_76171, baseEnd_76171] using wordTrace_append hprefix tailTrace_76171
  have hstable : (prefixWord ++ tailWord_76171).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76171).length < 2 ^ (prefixWord ++ tailWord_76171).sum := by decide
  have hdescent : baseEnd_76171 < baseStart_76171 := by decide
  rcases family_descends (prefixWord ++ tailWord_76171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76181 : List Nat := [1, 3, 2, 1, 1, 2, 1, 7, 2]
def baseStart_76181 : Nat := 118140960795 + 76181 * 2 ^ 59
def prefixEnd_76181 : Nat := 4983230072969 + 3 ^ 40 * 76181 * 2
def baseEnd_76181 : Nat := 34771084213574822388583

theorem tailTrace_76181 : CollatzResearch.WordTrace tailWord_76181 prefixEnd_76181 34771084213574822388583 := by
  unfold tailWord_76181
  simp only [CollatzResearch.WordTrace]
  refine ⟨2778549337016722524076397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1852366224677815016050931 2778549337016722524076397)
  ·
    refine ⟨1041956001381270946528649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2778549337016722524076397 1041956001381270946528649)
    ·
      refine ⟨781467001035953209896487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1041956001381270946528649 781467001035953209896487)
      ·
        refine ⟨1172200501553929814844731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 781467001035953209896487 1172200501553929814844731)
        ·
          refine ⟨1758300752330894722267097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1172200501553929814844731 1758300752330894722267097)
          ·
            refine ⟨1318725564248171041700323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1758300752330894722267097 1318725564248171041700323)
            ·
              refine ⟨1978088346372256562550485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1318725564248171041700323 1978088346372256562550485)
              ·
                refine ⟨46361445618099763184777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1978088346372256562550485 46361445618099763184777)
                ·
                  refine ⟨34771084213574822388583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46361445618099763184777 34771084213574822388583)
                  ·
                    rfl

theorem cell20_76181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 7, 2].length) (baseStart_76181 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_76181 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_76181 prefixEnd_76181 := by exact prefixLift 76181
  have htrace : WordTrace (prefixWord ++ tailWord_76181) baseStart_76181 baseEnd_76181 := by
    simpa [prefixWord, tailWord_76181, baseEnd_76181] using wordTrace_append hprefix tailTrace_76181
  have hstable : (prefixWord ++ tailWord_76181).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76181).length < 2 ^ (prefixWord ++ tailWord_76181).sum := by decide
  have hdescent : baseEnd_76181 < baseStart_76181 := by decide
  rcases family_descends (prefixWord ++ tailWord_76181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76195 : List Nat := [1, 1, 1, 4, 1, 4, 1, 4, 3]
def baseStart_76195 : Nat := 118140960795 + 76195 * 2 ^ 59
def prefixEnd_76195 : Nat := 4983230072969 + 3 ^ 40 * 76195 * 2
def baseEnd_76195 : Nat := 34777474195052995921859

theorem tailTrace_76195 : CollatzResearch.WordTrace tailWord_76195 prefixEnd_76195 34777474195052995921859 := by
  unfold tailWord_76195
  simp only [CollatzResearch.WordTrace]
  refine ⟨2779059958966002915086039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1852706639310668610057359 2779059958966002915086039)
  ·
    refine ⟨4168589938449004372629059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2779059958966002915086039 4168589938449004372629059)
    ·
      refine ⟨6252884907673506558943589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4168589938449004372629059 6252884907673506558943589)
      ·
        refine ⟨1172415920188782479801923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6252884907673506558943589 1172415920188782479801923)
        ·
          refine ⟨1758623880283173719702885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1172415920188782479801923 1758623880283173719702885)
          ·
            refine ⟨329741977553095072444291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1758623880283173719702885 329741977553095072444291)
            ·
              refine ⟨494612966329642608666437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 329741977553095072444291 494612966329642608666437)
              ·
                refine ⟨92739931186807989124957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 494612966329642608666437 92739931186807989124957)
                ·
                  refine ⟨34777474195052995921859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 92739931186807989124957 34777474195052995921859)
                  ·
                    rfl

theorem cell20_76195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 4, 3].length) (baseStart_76195 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_76195 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_76195 prefixEnd_76195 := by exact prefixLift 76195
  have htrace : WordTrace (prefixWord ++ tailWord_76195) baseStart_76195 baseEnd_76195 := by
    simpa [prefixWord, tailWord_76195, baseEnd_76195] using wordTrace_append hprefix tailTrace_76195
  have hstable : (prefixWord ++ tailWord_76195).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76195).length < 2 ^ (prefixWord ++ tailWord_76195).sum := by decide
  have hdescent : baseEnd_76195 < baseStart_76195 := by decide
  rcases family_descends (prefixWord ++ tailWord_76195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76216 : List Nat := [2, 1, 2, 1, 2, 2, 1, 2, 7]
def baseStart_76216 : Nat := 118140960795 + 76216 * 2 ^ 59
def prefixEnd_76216 : Nat := 4983230072969 + 3 ^ 40 * 76216 * 2
def baseEnd_76216 : Nat := 34787059167270256221773

theorem tailTrace_76216 : CollatzResearch.WordTrace tailWord_76216 prefixEnd_76216 34787059167270256221773 := by
  unfold tailWord_76216
  simp only [CollatzResearch.WordTrace]
  refine ⟨1389912945944961750800251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1853217261259949001067001 1389912945944961750800251)
  ·
    refine ⟨2084869418917442626200377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1389912945944961750800251 2084869418917442626200377)
    ·
      refine ⟨1563652064188081969650283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2084869418917442626200377 1563652064188081969650283)
      ·
        refine ⟨2345478096282122954475425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1563652064188081969650283 2345478096282122954475425)
        ·
          refine ⟨1759108572211592215856569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2345478096282122954475425 1759108572211592215856569)
          ·
            refine ⟨1319331429158694161892427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1759108572211592215856569 1319331429158694161892427)
            ·
              refine ⟨1978997143738041242838641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1319331429158694161892427 1978997143738041242838641)
              ·
                refine ⟨1484247857803530932128981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1978997143738041242838641 1484247857803530932128981)
                ·
                  refine ⟨34787059167270256221773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1484247857803530932128981 34787059167270256221773)
                  ·
                    rfl

theorem cell20_76216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 7].length) (baseStart_76216 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_76216 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_76216 prefixEnd_76216 := by exact prefixLift 76216
  have htrace : WordTrace (prefixWord ++ tailWord_76216) baseStart_76216 baseEnd_76216 := by
    simpa [prefixWord, tailWord_76216, baseEnd_76216] using wordTrace_append hprefix tailTrace_76216
  have hstable : (prefixWord ++ tailWord_76216).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76216).length < 2 ^ (prefixWord ++ tailWord_76216).sum := by decide
  have hdescent : baseEnd_76216 < baseStart_76216 := by decide
  rcases family_descends (prefixWord ++ tailWord_76216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76257 : List Nat := [1, 2, 3, 1, 2, 2, 1, 6, 2]
def baseStart_76257 : Nat := 118140960795 + 76257 * 2 ^ 59
def prefixEnd_76257 : Nat := 4983230072969 + 3 ^ 40 * 76257 * 2
def baseEnd_76257 : Nat := 34805772684456335854939

theorem tailTrace_76257 : CollatzResearch.WordTrace tailWord_76257 prefixEnd_76257 34805772684456335854939 := by
  unfold tailWord_76257
  simp only [CollatzResearch.WordTrace]
  refine ⟨2781321284741387503843025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1854214189827591669228683 2781321284741387503843025)
  ·
    refine ⟨2085990963556040627882269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2781321284741387503843025 2085990963556040627882269)
    ·
      refine ⟨782246611333515235455851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2085990963556040627882269 782246611333515235455851)
      ·
        refine ⟨1173369917000272853183777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 782246611333515235455851 1173369917000272853183777)
        ·
          refine ⟨880027437750204639887833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1173369917000272853183777 880027437750204639887833)
          ·
            refine ⟨660020578312653479915875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 880027437750204639887833 660020578312653479915875)
            ·
              refine ⟨990030867468980219873813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 660020578312653479915875 990030867468980219873813)
              ·
                refine ⟨46407696912608447806585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 990030867468980219873813 46407696912608447806585)
                ·
                  refine ⟨34805772684456335854939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46407696912608447806585 34805772684456335854939)
                  ·
                    rfl

theorem cell20_76257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 6, 2].length) (baseStart_76257 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_76257 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_76257 prefixEnd_76257 := by exact prefixLift 76257
  have htrace : WordTrace (prefixWord ++ tailWord_76257) baseStart_76257 baseEnd_76257 := by
    simpa [prefixWord, tailWord_76257, baseEnd_76257] using wordTrace_append hprefix tailTrace_76257
  have hstable : (prefixWord ++ tailWord_76257).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76257).length < 2 ^ (prefixWord ++ tailWord_76257).sum := by decide
  have hdescent : baseEnd_76257 < baseStart_76257 := by decide
  rcases family_descends (prefixWord ++ tailWord_76257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76277 : List Nat := [1, 3, 5, 1, 3, 1, 2, 4]
def baseStart_76277 : Nat := 118140960795 + 76277 * 2 ^ 59
def prefixEnd_76277 : Nat := 4983230072969 + 3 ^ 40 * 76277 * 2
def baseEnd_76277 : Nat := 11604967076475051729397

theorem tailTrace_76277 : CollatzResearch.WordTrace tailWord_76277 prefixEnd_76277 11604967076475051729397 := by
  unfold tailWord_76277
  simp only [CollatzResearch.WordTrace]
  refine ⟨2782050744668930919571085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1854700496445953946380723 2782050744668930919571085)
  ·
    refine ⟨1043269029250849094839157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2782050744668930919571085 1043269029250849094839157)
    ·
      refine ⟨97806471492267102641171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1043269029250849094839157 97806471492267102641171)
      ·
        refine ⟨146709707238400653961757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97806471492267102641171 146709707238400653961757)
        ·
          refine ⟨55016140214400245235659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 146709707238400653961757 55016140214400245235659)
          ·
            refine ⟨82524210321600367853489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55016140214400245235659 82524210321600367853489)
            ·
              refine ⟨61893157741200275890117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82524210321600367853489 61893157741200275890117)
              ·
                refine ⟨11604967076475051729397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61893157741200275890117 11604967076475051729397)
                ·
                  rfl

theorem cell20_76277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 2, 4].length) (baseStart_76277 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_76277 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_76277 prefixEnd_76277 := by exact prefixLift 76277
  have htrace : WordTrace (prefixWord ++ tailWord_76277) baseStart_76277 baseEnd_76277 := by
    simpa [prefixWord, tailWord_76277, baseEnd_76277] using wordTrace_append hprefix tailTrace_76277
  have hstable : (prefixWord ++ tailWord_76277).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76277).length < 2 ^ (prefixWord ++ tailWord_76277).sum := by decide
  have hdescent : baseEnd_76277 < baseStart_76277 := by decide
  rcases family_descends (prefixWord ++ tailWord_76277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76285 : List Nat := [1, 4, 1, 1, 1, 3, 3, 6]
def baseStart_76285 : Nat := 118140960795 + 76285 * 2 ^ 59
def prefixEnd_76285 : Nat := 4983230072969 + 3 ^ 40 * 76285 * 2
def baseEnd_76285 : Nat := 11606184215804227640497

theorem tailTrace_76285 : CollatzResearch.WordTrace tailWord_76285 prefixEnd_76285 11606184215804227640497 := by
  unfold tailWord_76285
  simp only [CollatzResearch.WordTrace]
  refine ⟨2782342528639948285862309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1854895019093298857241539 2782342528639948285862309)
  ·
    refine ⟨521689224119990303599183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2782342528639948285862309 521689224119990303599183)
    ·
      refine ⟨782533836179985455398775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 521689224119990303599183 782533836179985455398775)
      ·
        refine ⟨1173800754269978183098163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 782533836179985455398775 1173800754269978183098163)
        ·
          refine ⟨1760701131404967274647245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1173800754269978183098163 1760701131404967274647245)
          ·
            refine ⟨660262924276862727992717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1760701131404967274647245 660262924276862727992717)
            ·
              refine ⟨247598596603823522997269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 660262924276862727992717 247598596603823522997269)
              ·
                refine ⟨11606184215804227640497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 247598596603823522997269 11606184215804227640497)
                ·
                  rfl

theorem cell20_76285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 6].length) (baseStart_76285 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_76285 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_76285 prefixEnd_76285 := by exact prefixLift 76285
  have htrace : WordTrace (prefixWord ++ tailWord_76285) baseStart_76285 baseEnd_76285 := by
    simpa [prefixWord, tailWord_76285, baseEnd_76285] using wordTrace_append hprefix tailTrace_76285
  have hstable : (prefixWord ++ tailWord_76285).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76285).length < 2 ^ (prefixWord ++ tailWord_76285).sum := by decide
  have hdescent : baseEnd_76285 < baseStart_76285 := by decide
  rcases family_descends (prefixWord ++ tailWord_76285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76302 : List Nat := [4, 1, 1, 2, 3, 3, 6]
def baseStart_76302 : Nat := 118140960795 + 76302 * 2 ^ 59
def prefixEnd_76302 : Nat := 4983230072969 + 3 ^ 40 * 76302 * 2
def baseEnd_76302 : Nat := 3869590212292908817195

theorem tailTrace_76302 : CollatzResearch.WordTrace tailWord_76302 prefixEnd_76302 3869590212292908817195 := by
  unfold tailWord_76302
  simp only [CollatzResearch.WordTrace]
  refine ⟨347870321197295023653895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1855308379718906792820773 347870321197295023653895)
  ·
    refine ⟨521805481795942535480843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 347870321197295023653895 521805481795942535480843)
    ·
      refine ⟨782708222693913803221265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 521805481795942535480843 782708222693913803221265)
      ·
        refine ⟨587031167020435352415949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 782708222693913803221265 587031167020435352415949)
        ·
          refine ⟨220136687632663257155981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 587031167020435352415949 220136687632663257155981)
          ·
            refine ⟨82551257862248721433493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 220136687632663257155981 82551257862248721433493)
            ·
              refine ⟨3869590212292908817195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 82551257862248721433493 3869590212292908817195)
              ·
                rfl

theorem cell20_76302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 6].length) (baseStart_76302 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_76302 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_76302 prefixEnd_76302 := by exact prefixLift 76302
  have htrace : WordTrace (prefixWord ++ tailWord_76302) baseStart_76302 baseEnd_76302 := by
    simpa [prefixWord, tailWord_76302, baseEnd_76302] using wordTrace_append hprefix tailTrace_76302
  have hstable : (prefixWord ++ tailWord_76302).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76302).length < 2 ^ (prefixWord ++ tailWord_76302).sum := by decide
  have hdescent : baseEnd_76302 < baseStart_76302 := by decide
  rcases family_descends (prefixWord ++ tailWord_76302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76308 : List Nat := [2, 4, 3, 1, 1, 2, 3, 2, 2]
def baseStart_76308 : Nat := 118140960795 + 76308 * 2 ^ 59
def prefixEnd_76308 : Nat := 4983230072969 + 3 ^ 40 * 76308 * 2
def baseEnd_76308 : Nat := 34829050474126825154731

theorem tailTrace_76308 : CollatzResearch.WordTrace tailWord_76308 prefixEnd_76308 34829050474126825154731 := by
  unfold tailWord_76308
  simp only [CollatzResearch.WordTrace]
  refine ⟨1391590703778311606974789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1855454271704415475966385 1391590703778311606974789)
  ·
    refine ⟨260923256958433426307773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1391590703778311606974789 260923256958433426307773)
    ·
      refine ⟨97846221359412534865415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 260923256958433426307773 97846221359412534865415)
      ·
        refine ⟨146769332039118802298123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97846221359412534865415 146769332039118802298123)
        ·
          refine ⟨220153998058678203447185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146769332039118802298123 220153998058678203447185)
          ·
            refine ⟨165115498544008652585389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 220153998058678203447185 165115498544008652585389)
            ·
              refine ⟨61918311954003244719521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 165115498544008652585389 61918311954003244719521)
              ·
                refine ⟨46438733965502433539641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61918311954003244719521 46438733965502433539641)
                ·
                  refine ⟨34829050474126825154731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46438733965502433539641 34829050474126825154731)
                  ·
                    rfl

theorem cell20_76308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 3, 2, 2].length) (baseStart_76308 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_76308 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_76308 prefixEnd_76308 := by exact prefixLift 76308
  have htrace : WordTrace (prefixWord ++ tailWord_76308) baseStart_76308 baseEnd_76308 := by
    simpa [prefixWord, tailWord_76308, baseEnd_76308] using wordTrace_append hprefix tailTrace_76308
  have hstable : (prefixWord ++ tailWord_76308).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76308).length < 2 ^ (prefixWord ++ tailWord_76308).sum := by decide
  have hdescent : baseEnd_76308 < baseStart_76308 := by decide
  rcases family_descends (prefixWord ++ tailWord_76308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76309 : List Nat := [1, 3, 2, 1, 3, 1, 2, 4, 3]
def baseStart_76309 : Nat := 118140960795 + 76309 * 2 ^ 59
def prefixEnd_76309 : Nat := 4983230072969 + 3 ^ 40 * 76309 * 2
def baseEnd_76309 : Nat := 34829506901375266121393

theorem tailTrace_76309 : CollatzResearch.WordTrace tailWord_76309 prefixEnd_76309 34829506901375266121393 := by
  unfold tailWord_76309
  simp only [CollatzResearch.WordTrace]
  refine ⟨2783217880553000384735981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1855478587035333589823987 2783217880553000384735981)
  ·
    refine ⟨1043706705207375144275993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2783217880553000384735981 1043706705207375144275993)
    ·
      refine ⟨782780028905531358206995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1043706705207375144275993 782780028905531358206995)
      ·
        refine ⟨1174170043358297037310493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 782780028905531358206995 1174170043358297037310493)
        ·
          refine ⟨440313766259361388991435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1174170043358297037310493 440313766259361388991435)
          ·
            refine ⟨660470649389042083487153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 440313766259361388991435 660470649389042083487153)
            ·
              refine ⟨495352987041781562615365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 660470649389042083487153 495352987041781562615365)
              ·
                refine ⟨92878685070334042990381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 495352987041781562615365 92878685070334042990381)
                ·
                  refine ⟨34829506901375266121393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 92878685070334042990381 34829506901375266121393)
                  ·
                    rfl

theorem cell20_76309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 4, 3].length) (baseStart_76309 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_76309 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_76309 prefixEnd_76309 := by exact prefixLift 76309
  have htrace : WordTrace (prefixWord ++ tailWord_76309) baseStart_76309 baseEnd_76309 := by
    simpa [prefixWord, tailWord_76309, baseEnd_76309] using wordTrace_append hprefix tailTrace_76309
  have hstable : (prefixWord ++ tailWord_76309).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76309).length < 2 ^ (prefixWord ++ tailWord_76309).sum := by decide
  have hdescent : baseEnd_76309 < baseStart_76309 := by decide
  rcases family_descends (prefixWord ++ tailWord_76309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76323 : List Nat := [1, 1, 1, 4, 4, 1, 1, 7]
def baseStart_76323 : Nat := 118140960795 + 76323 * 2 ^ 59
def prefixEnd_76323 : Nat := 4983230072969 + 3 ^ 40 * 76323 * 2
def baseEnd_76323 : Nat := 11611965627617813218223

theorem tailTrace_76323 : CollatzResearch.WordTrace tailWord_76323 prefixEnd_76323 11611965627617813218223 := by
  unfold tailWord_76323
  simp only [CollatzResearch.WordTrace]
  refine ⟨2783728502502280775745623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1855819001668187183830415 2783728502502280775745623)
  ·
    refine ⟨4175592753753421163618435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2783728502502280775745623 4175592753753421163618435)
    ·
      refine ⟨6263389130630131745427653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4175592753753421163618435 6263389130630131745427653)
      ·
        refine ⟨1174385461993149702267685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6263389130630131745427653 1174385461993149702267685)
        ·
          refine ⟨220197274123715569175191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1174385461993149702267685 220197274123715569175191)
          ·
            refine ⟨330295911185573353762787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 220197274123715569175191 330295911185573353762787)
            ·
              refine ⟨495443866778360030644181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 330295911185573353762787 495443866778360030644181)
              ·
                refine ⟨11611965627617813218223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 495443866778360030644181 11611965627617813218223)
                ·
                  rfl

theorem cell20_76323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 7].length) (baseStart_76323 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_76323 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_76323 prefixEnd_76323 := by exact prefixLift 76323
  have htrace : WordTrace (prefixWord ++ tailWord_76323) baseStart_76323 baseEnd_76323 := by
    simpa [prefixWord, tailWord_76323, baseEnd_76323] using wordTrace_append hprefix tailTrace_76323
  have hstable : (prefixWord ++ tailWord_76323).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76323).length < 2 ^ (prefixWord ++ tailWord_76323).sum := by decide
  have hdescent : baseEnd_76323 < baseStart_76323 := by decide
  rcases family_descends (prefixWord ++ tailWord_76323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76385 : List Nat := [1, 2, 3, 1, 1, 4, 2, 3, 3]
def baseStart_76385 : Nat := 118140960795 + 76385 * 2 ^ 59
def prefixEnd_76385 : Nat := 4983230072969 + 3 ^ 40 * 76385 * 2
def baseEnd_76385 : Nat := 34864195372256779587749

theorem tailTrace_76385 : CollatzResearch.WordTrace tailWord_76385 prefixEnd_76385 34864195372256779587749 := by
  unfold tailWord_76385
  simp only [CollatzResearch.WordTrace]
  refine ⟨2785989828277665364502609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1857326552185110243001739 2785989828277665364502609)
  ·
    refine ⟨2089492371208249023376957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2785989828277665364502609 2089492371208249023376957)
    ·
      refine ⟨783559639203093383766359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2089492371208249023376957 783559639203093383766359)
      ·
        refine ⟨1175339458804640075649539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 783559639203093383766359 1175339458804640075649539)
        ·
          refine ⟨1763009188206960113474309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1175339458804640075649539 1763009188206960113474309)
          ·
            refine ⟨330564222788805021276433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1763009188206960113474309 330564222788805021276433)
            ·
              refine ⟨247923167091603765957325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 330564222788805021276433 247923167091603765957325)
              ·
                refine ⟨92971187659351412233997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 247923167091603765957325 92971187659351412233997)
                ·
                  refine ⟨34864195372256779587749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 92971187659351412233997 34864195372256779587749)
                  ·
                    rfl

theorem cell20_76385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 3, 3].length) (baseStart_76385 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_76385 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_76385 prefixEnd_76385 := by exact prefixLift 76385
  have htrace : WordTrace (prefixWord ++ tailWord_76385) baseStart_76385 baseEnd_76385 := by
    simpa [prefixWord, tailWord_76385, baseEnd_76385] using wordTrace_append hprefix tailTrace_76385
  have hstable : (prefixWord ++ tailWord_76385).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76385).length < 2 ^ (prefixWord ++ tailWord_76385).sum := by decide
  have hdescent : baseEnd_76385 < baseStart_76385 := by decide
  rcases family_descends (prefixWord ++ tailWord_76385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76405 : List Nat := [1, 3, 4, 2, 2, 1, 2, 3, 2]
def baseStart_76405 : Nat := 118140960795 + 76405 * 2 ^ 59
def prefixEnd_76405 : Nat := 4983230072969 + 3 ^ 40 * 76405 * 2
def baseEnd_76405 : Nat := 34873323917225598921001

theorem tailTrace_76405 : CollatzResearch.WordTrace tailWord_76405 prefixEnd_76405 34873323917225598921001 := by
  unfold tailWord_76405
  simp only [CollatzResearch.WordTrace]
  refine ⟨2786719288205208780230669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1857812858803472520153779 2786719288205208780230669)
  ·
    refine ⟨1045019733076953292586501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2786719288205208780230669 1045019733076953292586501)
    ·
      refine ⟨195941199951928742359969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1045019733076953292586501 195941199951928742359969)
      ·
        refine ⟨146955899963946556769977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195941199951928742359969 146955899963946556769977)
        ·
          refine ⟨110216924972959917577483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146955899963946556769977 110216924972959917577483)
          ·
            refine ⟨165325387459439876366225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110216924972959917577483 165325387459439876366225)
            ·
              refine ⟨123994040594579907274669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 165325387459439876366225 123994040594579907274669)
              ·
                refine ⟨46497765222967465228001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 123994040594579907274669 46497765222967465228001)
                ·
                  refine ⟨34873323917225598921001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46497765222967465228001 34873323917225598921001)
                  ·
                    rfl

theorem cell20_76405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 3, 2].length) (baseStart_76405 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_76405 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_76405 prefixEnd_76405 := by exact prefixLift 76405
  have htrace : WordTrace (prefixWord ++ tailWord_76405) baseStart_76405 baseEnd_76405 := by
    simpa [prefixWord, tailWord_76405, baseEnd_76405] using wordTrace_append hprefix tailTrace_76405
  have hstable : (prefixWord ++ tailWord_76405).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76405).length < 2 ^ (prefixWord ++ tailWord_76405).sum := by decide
  have hdescent : baseEnd_76405 < baseStart_76405 := by decide
  rcases family_descends (prefixWord ++ tailWord_76405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76409 : List Nat := [1, 2, 1, 3, 3, 2, 1, 5, 2]
def baseStart_76409 : Nat := 118140960795 + 76409 * 2 ^ 59
def prefixEnd_76409 : Nat := 4983230072969 + 3 ^ 40 * 76409 * 2
def baseEnd_76409 : Nat := 34875149626219362787651

theorem tailTrace_76409 : CollatzResearch.WordTrace tailWord_76409 prefixEnd_76409 34875149626219362787651 := by
  unfold tailWord_76409
  simp only [CollatzResearch.WordTrace]
  refine ⟨2786865180190717463376281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1857910120127144975584187 2786865180190717463376281)
  ·
    refine ⟨2090148885143038097532211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2786865180190717463376281 2090148885143038097532211)
    ·
      refine ⟨3135223327714557146298317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2090148885143038097532211 3135223327714557146298317)
      ·
        refine ⟨1175708747892958929861869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3135223327714557146298317 1175708747892958929861869)
        ·
          refine ⟨440890780459859598698201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1175708747892958929861869 440890780459859598698201)
          ·
            refine ⟨330668085344894699023651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 440890780459859598698201 330668085344894699023651)
            ·
              refine ⟨496002128017342048535477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 330668085344894699023651 496002128017342048535477)
              ·
                refine ⟨46500199501625817050201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 496002128017342048535477 46500199501625817050201)
                ·
                  refine ⟨34875149626219362787651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46500199501625817050201 34875149626219362787651)
                  ·
                    rfl

theorem cell20_76409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 5, 2].length) (baseStart_76409 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_76409 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_76409 prefixEnd_76409 := by exact prefixLift 76409
  have htrace : WordTrace (prefixWord ++ tailWord_76409) baseStart_76409 baseEnd_76409 := by
    simpa [prefixWord, tailWord_76409, baseEnd_76409] using wordTrace_append hprefix tailTrace_76409
  have hstable : (prefixWord ++ tailWord_76409).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76409).length < 2 ^ (prefixWord ++ tailWord_76409).sum := by decide
  have hdescent : baseEnd_76409 < baseStart_76409 := by decide
  rcases family_descends (prefixWord ++ tailWord_76409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76440 : List Nat := [2, 1, 2, 4, 1, 1, 5, 1, 3]
def baseStart_76440 : Nat := 118140960795 + 76440 * 2 ^ 59
def prefixEnd_76440 : Nat := 4983230072969 + 3 ^ 40 * 76440 * 2
def baseEnd_76440 : Nat := 34889298870921032754191

theorem tailTrace_76440 : CollatzResearch.WordTrace tailWord_76440 prefixEnd_76440 34889298870921032754191 := by
  unfold tailWord_76440
  simp only [CollatzResearch.WordTrace]
  refine ⟨1393997921539204878877387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1858663895385606505169849 1393997921539204878877387)
  ·
    refine ⟨2090996882308807318316081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1393997921539204878877387 2090996882308807318316081)
    ·
      refine ⟨1568247661731605488737061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2090996882308807318316081 1568247661731605488737061)
      ·
        refine ⟨294046436574676029138199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1568247661731605488737061 294046436574676029138199)
        ·
          refine ⟨441069654862014043707299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 294046436574676029138199 441069654862014043707299)
          ·
            refine ⟨661604482293021065560949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 441069654862014043707299 661604482293021065560949)
            ·
              refine ⟨62025420214970724896339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 661604482293021065560949 62025420214970724896339)
              ·
                refine ⟨93038130322456087344509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62025420214970724896339 93038130322456087344509)
                ·
                  refine ⟨34889298870921032754191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 93038130322456087344509 34889298870921032754191)
                  ·
                    rfl

theorem cell20_76440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 5, 1, 3].length) (baseStart_76440 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_76440 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_76440 prefixEnd_76440 := by exact prefixLift 76440
  have htrace : WordTrace (prefixWord ++ tailWord_76440) baseStart_76440 baseEnd_76440 := by
    simpa [prefixWord, tailWord_76440, baseEnd_76440] using wordTrace_append hprefix tailTrace_76440
  have hstable : (prefixWord ++ tailWord_76440).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76440).length < 2 ^ (prefixWord ++ tailWord_76440).sum := by decide
  have hdescent : baseEnd_76440 < baseStart_76440 := by decide
  rcases family_descends (prefixWord ++ tailWord_76440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76451 : List Nat := [1, 1, 1, 4, 1, 1, 2, 3, 6]
def baseStart_76451 : Nat := 118140960795 + 76451 * 2 ^ 59
def prefixEnd_76451 : Nat := 4983230072969 + 3 ^ 40 * 76451 * 2
def baseEnd_76451 : Nat := 34894319570653883387479

theorem tailTrace_76451 : CollatzResearch.WordTrace tailWord_76451 prefixEnd_76451 34894319570653883387479 := by
  unfold tailWord_76451
  simp only [CollatzResearch.WordTrace]
  refine ⟨2788397046038558636405207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1858931364025705757603471 2788397046038558636405207)
  ·
    refine ⟨4182595569057837954607811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2788397046038558636405207 4182595569057837954607811)
    ·
      refine ⟨6273893353586756931911717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4182595569057837954607811 6273893353586756931911717)
      ·
        refine ⟨1176355003797516924733447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6273893353586756931911717 1176355003797516924733447)
        ·
          refine ⟨1764532505696275387100171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1176355003797516924733447 1764532505696275387100171)
          ·
            refine ⟨2646798758544413080650257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1764532505696275387100171 2646798758544413080650257)
            ·
              refine ⟨1985099068908309810487693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2646798758544413080650257 1985099068908309810487693)
              ·
                refine ⟨744412150840616178932885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1985099068908309810487693 744412150840616178932885)
                ·
                  refine ⟨34894319570653883387479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 744412150840616178932885 34894319570653883387479)
                  ·
                    rfl

theorem cell20_76451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 6].length) (baseStart_76451 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_76451 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_76451 prefixEnd_76451 := by exact prefixLift 76451
  have htrace : WordTrace (prefixWord ++ tailWord_76451) baseStart_76451 baseEnd_76451 := by
    simpa [prefixWord, tailWord_76451, baseEnd_76451] using wordTrace_append hprefix tailTrace_76451
  have hstable : (prefixWord ++ tailWord_76451).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76451).length < 2 ^ (prefixWord ++ tailWord_76451).sum := by decide
  have hdescent : baseEnd_76451 < baseStart_76451 := by decide
  rcases family_descends (prefixWord ++ tailWord_76451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76461 : List Nat := [1, 5, 2, 1, 1, 2, 1, 2, 5]
def baseStart_76461 : Nat := 118140960795 + 76461 * 2 ^ 59
def prefixEnd_76461 : Nat := 4983230072969 + 3 ^ 40 * 76461 * 2
def baseEnd_76461 : Nat := 34898883843138293054105

theorem tailTrace_76461 : CollatzResearch.WordTrace tailWord_76461 prefixEnd_76461 34898883843138293054105 := by
  unfold tailWord_76461
  simp only [CollatzResearch.WordTrace]
  refine ⟨2788761776002330344269237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1859174517334886896179491 2788761776002330344269237)
  ·
    refine ⟨261446416500218469775241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2788761776002330344269237 261446416500218469775241)
    ·
      refine ⟨196084812375163852331431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 261446416500218469775241 196084812375163852331431)
      ·
        refine ⟨294127218562745778497147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196084812375163852331431 294127218562745778497147)
        ·
          refine ⟨441190827844118667745721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 294127218562745778497147 441190827844118667745721)
          ·
            refine ⟨330893120883089000809291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 441190827844118667745721 330893120883089000809291)
            ·
              refine ⟨496339681324633501213937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 330893120883089000809291 496339681324633501213937)
              ·
                refine ⟨372254760993475125910453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 496339681324633501213937 372254760993475125910453)
                ·
                  refine ⟨34898883843138293054105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 372254760993475125910453 34898883843138293054105)
                  ·
                    rfl

theorem cell20_76461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_76461 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_76461 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_76461 prefixEnd_76461 := by exact prefixLift 76461
  have htrace : WordTrace (prefixWord ++ tailWord_76461) baseStart_76461 baseEnd_76461 := by
    simpa [prefixWord, tailWord_76461, baseEnd_76461] using wordTrace_append hprefix tailTrace_76461
  have hstable : (prefixWord ++ tailWord_76461).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76461).length < 2 ^ (prefixWord ++ tailWord_76461).sum := by decide
  have hdescent : baseEnd_76461 < baseStart_76461 := by decide
  rcases family_descends (prefixWord ++ tailWord_76461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76481 : List Nat := [1, 2, 6, 2, 1, 2, 1, 1, 4]
def baseStart_76481 : Nat := 118140960795 + 76481 * 2 ^ 59
def prefixEnd_76481 : Nat := 4983230072969 + 3 ^ 40 * 76481 * 2
def baseEnd_76481 : Nat := 34908012388107112387357

theorem tailTrace_76481 : CollatzResearch.WordTrace tailWord_76481 prefixEnd_76481 34908012388107112387357 := by
  unfold tailWord_76481
  simp only [CollatzResearch.WordTrace]
  refine ⟨2789491235929873759997297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1859660823953249173331531 2789491235929873759997297)
  ·
    refine ⟨2092118426947405319997973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2789491235929873759997297 2092118426947405319997973)
    ·
      refine ⟨98068051263159624374905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 2092118426947405319997973 98068051263159624374905)
      ·
        refine ⟨73551038447369718281179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98068051263159624374905 73551038447369718281179)
        ·
          refine ⟨110326557671054577421769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73551038447369718281179 110326557671054577421769)
          ·
            refine ⟨82744918253290933066327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110326557671054577421769 82744918253290933066327)
            ·
              refine ⟨124117377379936399599491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82744918253290933066327 124117377379936399599491)
              ·
                refine ⟨186176066069904599399237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 124117377379936399599491 186176066069904599399237)
                ·
                  refine ⟨34908012388107112387357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 186176066069904599399237 34908012388107112387357)
                  ·
                    rfl

theorem cell20_76481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 1, 4].length) (baseStart_76481 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_76481 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_76481 prefixEnd_76481 := by exact prefixLift 76481
  have htrace : WordTrace (prefixWord ++ tailWord_76481) baseStart_76481 baseEnd_76481 := by
    simpa [prefixWord, tailWord_76481, baseEnd_76481] using wordTrace_append hprefix tailTrace_76481
  have hstable : (prefixWord ++ tailWord_76481).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76481).length < 2 ^ (prefixWord ++ tailWord_76481).sum := by decide
  have hdescent : baseEnd_76481 < baseStart_76481 := by decide
  rcases family_descends (prefixWord ++ tailWord_76481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76492 : List Nat := [2, 2, 1, 5, 1, 2, 2, 5]
def baseStart_76492 : Nat := 118140960795 + 76492 * 2 ^ 59
def prefixEnd_76492 : Nat := 4983230072969 + 3 ^ 40 * 76492 * 2
def baseEnd_76492 : Nat := 11637677695946654340215

theorem tailTrace_76492 : CollatzResearch.WordTrace tailWord_76492 prefixEnd_76492 11637677695946654340215 := by
  unfold tailWord_76492
  simp only [CollatzResearch.WordTrace]
  refine ⟨1394946219445011319323865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1859928292593348425765153 1394946219445011319323865)
  ·
    refine ⟨1046209664583758489492899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1394946219445011319323865 1046209664583758489492899)
    ·
      refine ⟨1569314496875637734239349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1046209664583758489492899 1569314496875637734239349)
      ·
        refine ⟨147123234082091037584939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1569314496875637734239349 147123234082091037584939)
        ·
          refine ⟨220684851123136556377409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147123234082091037584939 220684851123136556377409)
          ·
            refine ⟨165513638342352417283057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 220684851123136556377409 165513638342352417283057)
            ·
              refine ⟨124135228756764312962293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 165513638342352417283057 124135228756764312962293)
              ·
                refine ⟨11637677695946654340215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 124135228756764312962293 11637677695946654340215)
                ·
                  rfl

theorem cell20_76492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 5].length) (baseStart_76492 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_76492 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_76492 prefixEnd_76492 := by exact prefixLift 76492
  have htrace : WordTrace (prefixWord ++ tailWord_76492) baseStart_76492 baseEnd_76492 := by
    simpa [prefixWord, tailWord_76492, baseEnd_76492] using wordTrace_append hprefix tailTrace_76492
  have hstable : (prefixWord ++ tailWord_76492).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76492).length < 2 ^ (prefixWord ++ tailWord_76492).sum := by decide
  have hdescent : baseEnd_76492 < baseStart_76492 := by decide
  rcases family_descends (prefixWord ++ tailWord_76492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76513 : List Nat := [1, 2, 3, 1, 4, 1, 2, 6]
def baseStart_76513 : Nat := 118140960795 + 76513 * 2 ^ 59
def prefixEnd_76513 : Nat := 4983230072969 + 3 ^ 40 * 76513 * 2
def baseEnd_76513 : Nat := 11640872686685741106853

theorem tailTrace_76513 : CollatzResearch.WordTrace tailWord_76513 prefixEnd_76513 11640872686685741106853 := by
  unfold tailWord_76513
  simp only [CollatzResearch.WordTrace]
  refine ⟨2790658371813943225162193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1860438914542628816774795 2790658371813943225162193)
  ·
    refine ⟨2092993778860457418871645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2790658371813943225162193 2092993778860457418871645)
    ·
      refine ⟨784872667072671532076867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2092993778860457418871645 784872667072671532076867)
      ·
        refine ⟨1177309000609007298115301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 784872667072671532076867 1177309000609007298115301)
        ·
          refine ⟨220745437614188868396619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1177309000609007298115301 220745437614188868396619)
          ·
            refine ⟨331118156421283302594929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 220745437614188868396619 331118156421283302594929)
            ·
              refine ⟨248338617315962476946197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 331118156421283302594929 248338617315962476946197)
              ·
                refine ⟨11640872686685741106853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 248338617315962476946197 11640872686685741106853)
                ·
                  rfl

theorem cell20_76513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 6].length) (baseStart_76513 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_76513 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_76513 prefixEnd_76513 := by exact prefixLift 76513
  have htrace : WordTrace (prefixWord ++ tailWord_76513) baseStart_76513 baseEnd_76513 := by
    simpa [prefixWord, tailWord_76513, baseEnd_76513] using wordTrace_append hprefix tailTrace_76513
  have hstable : (prefixWord ++ tailWord_76513).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76513).length < 2 ^ (prefixWord ++ tailWord_76513).sum := by decide
  have hdescent : baseEnd_76513 < baseStart_76513 := by decide
  rcases family_descends (prefixWord ++ tailWord_76513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76532 : List Nat := [2, 6, 1, 1, 3, 1, 2, 2, 2]
def baseStart_76532 : Nat := 118140960795 + 76532 * 2 ^ 59
def prefixEnd_76532 : Nat := 4983230072969 + 3 ^ 40 * 76532 * 2
def baseEnd_76532 : Nat := 34931290177777601687149

theorem tailTrace_76532 : CollatzResearch.WordTrace tailWord_76532 prefixEnd_76532 34931290177777601687149 := by
  unfold tailWord_76532
  simp only [CollatzResearch.WordTrace]
  refine ⟨1395675679372554735051925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1860900905830072980069233 1395675679372554735051925)
  ·
    refine ⟨65422297470588503205559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 1395675679372554735051925 65422297470588503205559)
    ·
      refine ⟨98133446205882754808339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65422297470588503205559 98133446205882754808339)
      ·
        refine ⟨147200169308824132212509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98133446205882754808339 147200169308824132212509)
        ·
          refine ⟨55200063490809049579691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 147200169308824132212509 55200063490809049579691)
          ·
            refine ⟨82800095236213574369537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55200063490809049579691 82800095236213574369537)
            ·
              refine ⟨62100071427160180777153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82800095236213574369537 62100071427160180777153)
              ·
                refine ⟨46575053570370135582865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62100071427160180777153 46575053570370135582865)
                ·
                  refine ⟨34931290177777601687149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46575053570370135582865 34931290177777601687149)
                  ·
                    rfl

theorem cell20_76532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_76532 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_76532 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_76532 prefixEnd_76532 := by exact prefixLift 76532
  have htrace : WordTrace (prefixWord ++ tailWord_76532) baseStart_76532 baseEnd_76532 := by
    simpa [prefixWord, tailWord_76532, baseEnd_76532] using wordTrace_append hprefix tailTrace_76532
  have hstable : (prefixWord ++ tailWord_76532).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76532).length < 2 ^ (prefixWord ++ tailWord_76532).sum := by decide
  have hdescent : baseEnd_76532 < baseStart_76532 := by decide
  rcases family_descends (prefixWord ++ tailWord_76532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76540 : List Nat := [2, 2, 2, 1, 3, 2, 4, 2, 2]
def baseStart_76540 : Nat := 118140960795 + 76540 * 2 ^ 59
def prefixEnd_76540 : Nat := 4983230072969 + 3 ^ 40 * 76540 * 2
def baseEnd_76540 : Nat := 34934941595765129420449

theorem tailTrace_76540 : CollatzResearch.WordTrace tailWord_76540 prefixEnd_76540 34934941595765129420449 := by
  unfold tailWord_76540
  simp only [CollatzResearch.WordTrace]
  refine ⟨1395821571358063418197537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1861095428477417890930049 1395821571358063418197537)
  ·
    refine ⟨1046866178518547563648153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1395821571358063418197537 1046866178518547563648153)
    ·
      refine ⟨785149633888910672736115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1046866178518547563648153 785149633888910672736115)
      ·
        refine ⟨1177724450833366009104173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 785149633888910672736115 1177724450833366009104173)
        ·
          refine ⟨441646669062512253414065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1177724450833366009104173 441646669062512253414065)
          ·
            refine ⟨331235001796884190060549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 441646669062512253414065 331235001796884190060549)
            ·
              refine ⟨62106562836915785636353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 331235001796884190060549 62106562836915785636353)
              ·
                refine ⟨46579922127686839227265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62106562836915785636353 46579922127686839227265)
                ·
                  refine ⟨34934941595765129420449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46579922127686839227265 34934941595765129420449)
                  ·
                    rfl

theorem cell20_76540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 4, 2, 2].length) (baseStart_76540 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_76540 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_76540 prefixEnd_76540 := by exact prefixLift 76540
  have htrace : WordTrace (prefixWord ++ tailWord_76540) baseStart_76540 baseEnd_76540 := by
    simpa [prefixWord, tailWord_76540, baseEnd_76540] using wordTrace_append hprefix tailTrace_76540
  have hstable : (prefixWord ++ tailWord_76540).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76540).length < 2 ^ (prefixWord ++ tailWord_76540).sum := by decide
  have hdescent : baseEnd_76540 < baseStart_76540 := by decide
  rcases family_descends (prefixWord ++ tailWord_76540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76558 : List Nat := [4, 1, 1, 2, 1, 1, 1, 2, 7]
def baseStart_76558 : Nat := 118140960795 + 76558 * 2 ^ 59
def prefixEnd_76558 : Nat := 4983230072969 + 3 ^ 40 * 76558 * 2
def baseEnd_76558 : Nat := 34943157286237066820375

theorem tailTrace_76558 : CollatzResearch.WordTrace tailWord_76558 prefixEnd_76558 34943157286237066820375 := by
  unfold tailWord_76558
  simp only [CollatzResearch.WordTrace]
  refine ⟨349037457081364488818791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1861533104433943940366885 349037457081364488818791)
  ·
    refine ⟨523556185622046733228187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 349037457081364488818791 523556185622046733228187)
    ·
      refine ⟨785334278433070099842281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 523556185622046733228187 785334278433070099842281)
      ·
        refine ⟨589000708824802574881711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 785334278433070099842281 589000708824802574881711)
        ·
          refine ⟨883501063237203862322567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 589000708824802574881711 883501063237203862322567)
          ·
            refine ⟨1325251594855805793483851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 883501063237203862322567 1325251594855805793483851)
            ·
              refine ⟨1987877392283708690225777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1325251594855805793483851 1987877392283708690225777)
              ·
                refine ⟨1490908044212781517669333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1987877392283708690225777 1490908044212781517669333)
                ·
                  refine ⟨34943157286237066820375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1490908044212781517669333 34943157286237066820375)
                  ·
                    rfl

theorem cell20_76558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_76558 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_76558 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_76558 prefixEnd_76558 := by exact prefixLift 76558
  have htrace : WordTrace (prefixWord ++ tailWord_76558) baseStart_76558 baseEnd_76558 := by
    simpa [prefixWord, tailWord_76558, baseEnd_76558] using wordTrace_append hprefix tailTrace_76558
  have hstable : (prefixWord ++ tailWord_76558).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76558).length < 2 ^ (prefixWord ++ tailWord_76558).sum := by decide
  have hdescent : baseEnd_76558 < baseStart_76558 := by decide
  rcases family_descends (prefixWord ++ tailWord_76558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76578 : List Nat := [3, 3, 1, 1, 2, 3, 2, 3, 2]
def baseStart_76578 : Nat := 118140960795 + 76578 * 2 ^ 59
def prefixEnd_76578 : Nat := 4983230072969 + 3 ^ 40 * 76578 * 2
def baseEnd_76578 : Nat := 34952285831205886153627

theorem tailTrace_76578 : CollatzResearch.WordTrace tailWord_76578 prefixEnd_76578 34952285831205886153627 := by
  unfold tailWord_76578
  simp only [CollatzResearch.WordTrace]
  refine ⟨698257279144614831569597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1862019411052306217518925 698257279144614831569597)
  ·
    refine ⟨261846479679230561838599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 698257279144614831569597 261846479679230561838599)
    ·
      refine ⟨392769719518845842757899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261846479679230561838599 392769719518845842757899)
      ·
        refine ⟨589154579278268764136849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 392769719518845842757899 589154579278268764136849)
        ·
          refine ⟨441865934458701573102637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 589154579278268764136849 441865934458701573102637)
          ·
            refine ⟨165699725422013089913489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 441865934458701573102637 165699725422013089913489)
            ·
              refine ⟨124274794066509817435117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 165699725422013089913489 124274794066509817435117)
              ·
                refine ⟨46603047774941181538169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 124274794066509817435117 46603047774941181538169)
                ·
                  refine ⟨34952285831205886153627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46603047774941181538169 34952285831205886153627)
                  ·
                    rfl

theorem cell20_76578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 3, 2].length) (baseStart_76578 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_76578 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_76578 prefixEnd_76578 := by exact prefixLift 76578
  have htrace : WordTrace (prefixWord ++ tailWord_76578) baseStart_76578 baseEnd_76578 := by
    simpa [prefixWord, tailWord_76578, baseEnd_76578] using wordTrace_append hprefix tailTrace_76578
  have hstable : (prefixWord ++ tailWord_76578).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76578).length < 2 ^ (prefixWord ++ tailWord_76578).sum := by decide
  have hdescent : baseEnd_76578 < baseStart_76578 := by decide
  rcases family_descends (prefixWord ++ tailWord_76578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76620 : List Nat := [2, 2, 1, 3, 3, 1, 2, 2, 4]
def baseStart_76620 : Nat := 118140960795 + 76620 * 2 ^ 59
def prefixEnd_76620 : Nat := 4983230072969 + 3 ^ 40 * 76620 * 2
def baseEnd_76620 : Nat := 34971455775640406753455

theorem tailTrace_76620 : CollatzResearch.WordTrace tailWord_76620 prefixEnd_76620 34971455775640406753455 := by
  unfold tailWord_76620
  simp only [CollatzResearch.WordTrace]
  refine ⟨1397280491213150249653657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1863040654950866999538209 1397280491213150249653657)
  ·
    refine ⟨1047960368409862687240243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1397280491213150249653657 1047960368409862687240243)
    ·
      refine ⟨1571940552614794030860365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1047960368409862687240243 1571940552614794030860365)
      ·
        refine ⟨589477707230547761572637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1571940552614794030860365 589477707230547761572637)
        ·
          refine ⟨221054140211455410589739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 589477707230547761572637 221054140211455410589739)
          ·
            refine ⟨331581210317183115884609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221054140211455410589739 331581210317183115884609)
            ·
              refine ⟨248685907737887336913457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 331581210317183115884609 248685907737887336913457)
              ·
                refine ⟨186514430803415502685093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 248685907737887336913457 186514430803415502685093)
                ·
                  refine ⟨34971455775640406753455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 186514430803415502685093 34971455775640406753455)
                  ·
                    rfl

theorem cell20_76620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 2, 4].length) (baseStart_76620 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_76620 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_76620 prefixEnd_76620 := by exact prefixLift 76620
  have htrace : WordTrace (prefixWord ++ tailWord_76620) baseStart_76620 baseEnd_76620 := by
    simpa [prefixWord, tailWord_76620, baseEnd_76620] using wordTrace_append hprefix tailTrace_76620
  have hstable : (prefixWord ++ tailWord_76620).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76620).length < 2 ^ (prefixWord ++ tailWord_76620).sum := by decide
  have hdescent : baseEnd_76620 < baseStart_76620 := by decide
  rcases family_descends (prefixWord ++ tailWord_76620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76634 : List Nat := [3, 1, 1, 2, 1, 4, 1, 2, 5]
def baseStart_76634 : Nat := 118140960795 + 76634 * 2 ^ 59
def prefixEnd_76634 : Nat := 4983230072969 + 3 ^ 40 * 76634 * 2
def baseEnd_76634 : Nat := 34977845757118580286731

theorem tailTrace_76634 : CollatzResearch.WordTrace tailWord_76634 prefixEnd_76634 34977845757118580286731 := by
  unfold tailWord_76634
  simp only [CollatzResearch.WordTrace]
  refine ⟨698767901093895222579239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1863381069583720593544637 698767901093895222579239)
  ·
    refine ⟨1048151851640842833868859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 698767901093895222579239 1048151851640842833868859)
    ·
      refine ⟨1572227777461264250803289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1048151851640842833868859 1572227777461264250803289)
      ·
        refine ⟨1179170833095948188102467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1572227777461264250803289 1179170833095948188102467)
        ·
          refine ⟨1768756249643922282153701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1179170833095948188102467 1768756249643922282153701)
          ·
            refine ⟨331641796808235427903819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1768756249643922282153701 331641796808235427903819)
            ·
              refine ⟨497462695212353141855729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 331641796808235427903819 497462695212353141855729)
              ·
                refine ⟨373097021409264856391797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 497462695212353141855729 373097021409264856391797)
                ·
                  refine ⟨34977845757118580286731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 373097021409264856391797 34977845757118580286731)
                  ·
                    rfl

theorem cell20_76634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 2, 5].length) (baseStart_76634 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_76634 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_76634 prefixEnd_76634 := by exact prefixLift 76634
  have htrace : WordTrace (prefixWord ++ tailWord_76634) baseStart_76634 baseEnd_76634 := by
    simpa [prefixWord, tailWord_76634, baseEnd_76634] using wordTrace_append hprefix tailTrace_76634
  have hstable : (prefixWord ++ tailWord_76634).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76634).length < 2 ^ (prefixWord ++ tailWord_76634).sum := by decide
  have hdescent : baseEnd_76634 < baseStart_76634 := by decide
  rcases family_descends (prefixWord ++ tailWord_76634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76654 : List Nat := [4, 1, 2, 3, 2, 2, 1, 1, 4]
def baseStart_76654 : Nat := 118140960795 + 76654 * 2 ^ 59
def prefixEnd_76654 : Nat := 4983230072969 + 3 ^ 40 * 76654 * 2
def baseEnd_76654 : Nat := 34986974302087399619983

theorem tailTrace_76654 : CollatzResearch.WordTrace tailWord_76654 prefixEnd_76654 34986974302087399619983 := by
  unfold tailWord_76654
  simp only [CollatzResearch.WordTrace]
  refine ⟨349475133037890538255627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1863867376202082870696677 349475133037890538255627)
  ·
    refine ⟨524212699556835807383441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 349475133037890538255627 524212699556835807383441)
    ·
      refine ⟨393159524667626855537581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 524212699556835807383441 393159524667626855537581)
      ·
        refine ⟨147434821750360070826593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 393159524667626855537581 147434821750360070826593)
        ·
          refine ⟨110576116312770053119945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147434821750360070826593 110576116312770053119945)
          ·
            refine ⟨82932087234577539839959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110576116312770053119945 82932087234577539839959)
            ·
              refine ⟨124398130851866309759939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82932087234577539839959 124398130851866309759939)
              ·
                refine ⟨186597196277799464639909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 124398130851866309759939 186597196277799464639909)
                ·
                  refine ⟨34986974302087399619983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 186597196277799464639909 34986974302087399619983)
                  ·
                    rfl

theorem cell20_76654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 1, 4].length) (baseStart_76654 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_76654 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_76654 prefixEnd_76654 := by exact prefixLift 76654
  have htrace : WordTrace (prefixWord ++ tailWord_76654) baseStart_76654 baseEnd_76654 := by
    simpa [prefixWord, tailWord_76654, baseEnd_76654] using wordTrace_append hprefix tailTrace_76654
  have hstable : (prefixWord ++ tailWord_76654).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76654).length < 2 ^ (prefixWord ++ tailWord_76654).sum := by decide
  have hdescent : baseEnd_76654 < baseStart_76654 := by decide
  rcases family_descends (prefixWord ++ tailWord_76654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76658 : List Nat := [3, 2, 1, 2, 1, 1, 5, 1, 4]
def baseStart_76658 : Nat := 118140960795 + 76658 * 2 ^ 59
def prefixEnd_76658 : Nat := 4983230072969 + 3 ^ 40 * 76658 * 2
def baseEnd_76658 : Nat := 34988800011081163486633

theorem tailTrace_76658 : CollatzResearch.WordTrace tailWord_76658 prefixEnd_76658 34988800011081163486633 := by
  unfold tailWord_76658
  simp only [CollatzResearch.WordTrace]
  refine ⟨698986739072158247297657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1863964637525755326127085 698986739072158247297657)
  ·
    refine ⟨524240054304118685473243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 698986739072158247297657 524240054304118685473243)
    ·
      refine ⟨786360081456178028209865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 524240054304118685473243 786360081456178028209865)
      ·
        refine ⟨589770061092133521157399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 786360081456178028209865 589770061092133521157399)
        ·
          refine ⟨884655091638200281736099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 589770061092133521157399 884655091638200281736099)
          ·
            refine ⟨1326982637457300422604149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 884655091638200281736099 1326982637457300422604149)
            ·
              refine ⟨124404622261621914619139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1326982637457300422604149 124404622261621914619139)
              ·
                refine ⟨186606933392432871928709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 124404622261621914619139 186606933392432871928709)
                ·
                  refine ⟨34988800011081163486633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 186606933392432871928709 34988800011081163486633)
                  ·
                    rfl

theorem cell20_76658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_76658 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_76658 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_76658 prefixEnd_76658 := by exact prefixLift 76658
  have htrace : WordTrace (prefixWord ++ tailWord_76658) baseStart_76658 baseEnd_76658 := by
    simpa [prefixWord, tailWord_76658, baseEnd_76658] using wordTrace_append hprefix tailTrace_76658
  have hstable : (prefixWord ++ tailWord_76658).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76658).length < 2 ^ (prefixWord ++ tailWord_76658).sum := by decide
  have hdescent : baseEnd_76658 < baseStart_76658 := by decide
  rcases family_descends (prefixWord ++ tailWord_76658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76665 : List Nat := [1, 2, 1, 3, 2, 4, 2, 5]
def baseStart_76665 : Nat := 118140960795 + 76665 * 2 ^ 59
def prefixEnd_76665 : Nat := 4983230072969 + 3 ^ 40 * 76665 * 2
def baseEnd_76665 : Nat := 11663998333940083417757

theorem tailTrace_76665 : CollatzResearch.WordTrace tailWord_76665 prefixEnd_76665 11663998333940083417757 := by
  unfold tailWord_76665
  simp only [CollatzResearch.WordTrace]
  refine ⟨2796202267263273184695449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1864134844842182123130299 2796202267263273184695449)
  ·
    refine ⟨2097151700447454888521587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2796202267263273184695449 2097151700447454888521587)
    ·
      refine ⟨3145727550671182332782381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2097151700447454888521587 3145727550671182332782381)
      ·
        refine ⟨1179647831501693374793393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3145727550671182332782381 1179647831501693374793393)
        ·
          refine ⟨884735873626270031095045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1179647831501693374793393 884735873626270031095045)
          ·
            refine ⟨165887976304925630830321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 884735873626270031095045 165887976304925630830321)
            ·
              refine ⟨124415982228694223122741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 165887976304925630830321 124415982228694223122741)
              ·
                refine ⟨11663998333940083417757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 124415982228694223122741 11663998333940083417757)
                ·
                  rfl

theorem cell20_76665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 5].length) (baseStart_76665 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_76665 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_76665 prefixEnd_76665 := by exact prefixLift 76665
  have htrace : WordTrace (prefixWord ++ tailWord_76665) baseStart_76665 baseEnd_76665 := by
    simpa [prefixWord, tailWord_76665, baseEnd_76665] using wordTrace_append hprefix tailTrace_76665
  have hstable : (prefixWord ++ tailWord_76665).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76665).length < 2 ^ (prefixWord ++ tailWord_76665).sum := by decide
  have hdescent : baseEnd_76665 < baseStart_76665 := by decide
  rcases family_descends (prefixWord ++ tailWord_76665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76706 : List Nat := [3, 3, 1, 2, 2, 2, 2, 2, 3]
def baseStart_76706 : Nat := 118140960795 + 76706 * 2 ^ 59
def prefixEnd_76706 : Nat := 4983230072969 + 3 ^ 40 * 76706 * 2
def baseEnd_76706 : Nat := 35010708519006329886437

theorem tailTrace_76706 : CollatzResearch.WordTrace tailWord_76706 prefixEnd_76706 35010708519006329886437 := by
  unfold tailWord_76706
  simp only [CollatzResearch.WordTrace]
  refine ⟨699424415028684296734493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1865131773409824791291981 699424415028684296734493)
  ·
    refine ⟨262284155635756611275435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 699424415028684296734493 262284155635756611275435)
    ·
      refine ⟨393426233453634916913153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262284155635756611275435 393426233453634916913153)
      ·
        refine ⟨295069675090226187684865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 393426233453634916913153 295069675090226187684865)
        ·
          refine ⟨221302256317669640763649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 295069675090226187684865 221302256317669640763649)
          ·
            refine ⟨165976692238252230572737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 221302256317669640763649 165976692238252230572737)
            ·
              refine ⟨124482519178689172929553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 165976692238252230572737 124482519178689172929553)
              ·
                refine ⟨93361889384016879697165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 124482519178689172929553 93361889384016879697165)
                ·
                  refine ⟨35010708519006329886437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 93361889384016879697165 35010708519006329886437)
                  ·
                    rfl

theorem cell20_76706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_76706 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_76706 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_76706 prefixEnd_76706 := by exact prefixLift 76706
  have htrace : WordTrace (prefixWord ++ tailWord_76706) baseStart_76706 baseEnd_76706 := by
    simpa [prefixWord, tailWord_76706, baseEnd_76706] using wordTrace_append hprefix tailTrace_76706
  have hstable : (prefixWord ++ tailWord_76706).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76706).length < 2 ^ (prefixWord ++ tailWord_76706).sum := by decide
  have hdescent : baseEnd_76706 < baseStart_76706 := by decide
  rcases family_descends (prefixWord ++ tailWord_76706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76734 : List Nat := [4, 2, 1, 1, 1, 2, 3, 2, 4]
def baseStart_76734 : Nat := 118140960795 + 76734 * 2 ^ 59
def prefixEnd_76734 : Nat := 4983230072969 + 3 ^ 40 * 76734 * 2
def baseEnd_76734 : Nat := 35023488481962676952989

theorem tailTrace_76734 : CollatzResearch.WordTrace tailWord_76734 prefixEnd_76734 35023488481962676952989 := by
  unfold tailWord_76734
  simp only [CollatzResearch.WordTrace]
  refine ⟨349839863001662246119657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1865812602675531979304837 349839863001662246119657)
  ·
    refine ⟨262379897251246684589743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 349839863001662246119657 262379897251246684589743)
    ·
      refine ⟨393569845876870026884615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262379897251246684589743 393569845876870026884615)
      ·
        refine ⟨590354768815305040326923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 393569845876870026884615 590354768815305040326923)
        ·
          refine ⟨885532153222957560490385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 590354768815305040326923 885532153222957560490385)
          ·
            refine ⟨664149114917218170367789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 885532153222957560490385 664149114917218170367789)
            ·
              refine ⟨249055918093956813887921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 664149114917218170367789 249055918093956813887921)
              ·
                refine ⟨186791938570467610415941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 249055918093956813887921 186791938570467610415941)
                ·
                  refine ⟨35023488481962676952989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 186791938570467610415941 35023488481962676952989)
                  ·
                    rfl

theorem cell20_76734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_76734 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_76734 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_76734 prefixEnd_76734 := by exact prefixLift 76734
  have htrace : WordTrace (prefixWord ++ tailWord_76734) baseStart_76734 baseEnd_76734 := by
    simpa [prefixWord, tailWord_76734, baseEnd_76734] using wordTrace_append hprefix tailTrace_76734
  have hstable : (prefixWord ++ tailWord_76734).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76734).length < 2 ^ (prefixWord ++ tailWord_76734).sum := by decide
  have hdescent : baseEnd_76734 < baseStart_76734 := by decide
  rcases family_descends (prefixWord ++ tailWord_76734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76748 : List Nat := [2, 2, 1, 4, 1, 1, 2, 2, 5]
def baseStart_76748 : Nat := 118140960795 + 76748 * 2 ^ 59
def prefixEnd_76748 : Nat := 4983230072969 + 3 ^ 40 * 76748 * 2
def baseEnd_76748 : Nat := 35029878463440850486265

theorem tailTrace_76748 : CollatzResearch.WordTrace tailWord_76748 prefixEnd_76748 35029878463440850486265 := by
  unfold tailWord_76748
  simp only [CollatzResearch.WordTrace]
  refine ⟨1399614762981289179983449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1866153017308385573311265 1399614762981289179983449)
  ·
    refine ⟨1049711072235966884987587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1399614762981289179983449 1049711072235966884987587)
    ·
      refine ⟨1574566608353950327481381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1049711072235966884987587 1574566608353950327481381)
      ·
        refine ⟨295231239066365686402759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1574566608353950327481381 295231239066365686402759)
        ·
          refine ⟨442846858599548529604139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 295231239066365686402759 442846858599548529604139)
          ·
            refine ⟨664270287899322794406209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 442846858599548529604139 664270287899322794406209)
            ·
              refine ⟨498202715924492095804657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 664270287899322794406209 498202715924492095804657)
              ·
                refine ⟨373652036943369071853493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 498202715924492095804657 373652036943369071853493)
                ·
                  refine ⟨35029878463440850486265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 373652036943369071853493 35029878463440850486265)
                  ·
                    rfl

theorem cell20_76748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 2, 5].length) (baseStart_76748 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_76748 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_76748 prefixEnd_76748 := by exact prefixLift 76748
  have htrace : WordTrace (prefixWord ++ tailWord_76748) baseStart_76748 baseEnd_76748 := by
    simpa [prefixWord, tailWord_76748, baseEnd_76748] using wordTrace_append hprefix tailTrace_76748
  have hstable : (prefixWord ++ tailWord_76748).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76748).length < 2 ^ (prefixWord ++ tailWord_76748).sum := by decide
  have hdescent : baseEnd_76748 < baseStart_76748 := by decide
  rcases family_descends (prefixWord ++ tailWord_76748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76751 : List Nat := [1, 1, 2, 1, 1, 7, 2, 3, 2]
def baseStart_76751 : Nat := 118140960795 + 76751 * 2 ^ 59
def prefixEnd_76751 : Nat := 4983230072969 + 3 ^ 40 * 76751 * 2
def baseEnd_76751 : Nat := 35031247745186173386253

theorem tailTrace_76751 : CollatzResearch.WordTrace tailWord_76751 prefixEnd_76751 35031247745186173386253 := by
  unfold tailWord_76751
  simp only [CollatzResearch.WordTrace]
  refine ⟨2799338944951709872326107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1866225963301139914884071 2799338944951709872326107)
  ·
    refine ⟨4199008417427564808489161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2799338944951709872326107 4199008417427564808489161)
    ·
      refine ⟨3149256313070673606366871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4199008417427564808489161 3149256313070673606366871)
      ·
        refine ⟨4723884469606010409550307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3149256313070673606366871 4723884469606010409550307)
        ·
          refine ⟨7085826704409015614325461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4723884469606010409550307 7085826704409015614325461)
          ·
            refine ⟨166074063384586303460753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 7085826704409015614325461 166074063384586303460753)
            ·
              refine ⟨124555547538439727595565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 166074063384586303460753 124555547538439727595565)
              ·
                refine ⟨46708330326914897848337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 124555547538439727595565 46708330326914897848337)
                ·
                  refine ⟨35031247745186173386253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46708330326914897848337 35031247745186173386253)
                  ·
                    rfl

theorem cell20_76751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 3, 2].length) (baseStart_76751 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_76751 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_76751 prefixEnd_76751 := by exact prefixLift 76751
  have htrace : WordTrace (prefixWord ++ tailWord_76751) baseStart_76751 baseEnd_76751 := by
    simpa [prefixWord, tailWord_76751, baseEnd_76751] using wordTrace_append hprefix tailTrace_76751
  have hstable : (prefixWord ++ tailWord_76751).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76751).length < 2 ^ (prefixWord ++ tailWord_76751).sum := by decide
  have hdescent : baseEnd_76751 < baseStart_76751 := by decide
  rcases family_descends (prefixWord ++ tailWord_76751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76758 : List Nat := [5, 2, 1, 1, 2, 2, 7]
def baseStart_76758 : Nat := 118140960795 + 76758 * 2 ^ 59
def prefixEnd_76758 : Nat := 4983230072969 + 3 ^ 40 * 76758 * 2
def baseEnd_76758 : Nat := 3892715859547251128099

theorem tailTrace_76758 : CollatzResearch.WordTrace tailWord_76758 prefixEnd_76758 3892715859547251128099 := by
  unfold tailWord_76758
  simp only [CollatzResearch.WordTrace]
  refine ⟨174974640995396879239433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1866396170617566711887285 174974640995396879239433)
  ·
    refine ⟨131230980746547659429575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174974640995396879239433 131230980746547659429575)
    ·
      refine ⟨196846471119821489144363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131230980746547659429575 196846471119821489144363)
      ·
        refine ⟨295269706679732233716545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196846471119821489144363 295269706679732233716545)
        ·
          refine ⟨221452280009799175287409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 295269706679732233716545 221452280009799175287409)
          ·
            refine ⟨166089210007349381465557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 221452280009799175287409 166089210007349381465557)
            ·
              refine ⟨3892715859547251128099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 166089210007349381465557 3892715859547251128099)
              ·
                rfl

theorem cell20_76758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 7].length) (baseStart_76758 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_76758 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_76758 prefixEnd_76758 := by exact prefixLift 76758
  have htrace : WordTrace (prefixWord ++ tailWord_76758) baseStart_76758 baseEnd_76758 := by
    simpa [prefixWord, tailWord_76758, baseEnd_76758] using wordTrace_append hprefix tailTrace_76758
  have hstable : (prefixWord ++ tailWord_76758).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76758).length < 2 ^ (prefixWord ++ tailWord_76758).sum := by decide
  have hdescent : baseEnd_76758 < baseStart_76758 := by decide
  rcases family_descends (prefixWord ++ tailWord_76758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76765 : List Nat := [1, 4, 3, 1, 2, 2, 1, 1, 5]
def baseStart_76765 : Nat := 118140960795 + 76765 * 2 ^ 59
def prefixEnd_76765 : Nat := 4983230072969 + 3 ^ 40 * 76765 * 2
def baseEnd_76765 : Nat := 35037637726664346919529

theorem tailTrace_76765 : CollatzResearch.WordTrace tailWord_76765 prefixEnd_76765 35037637726664346919529 := by
  unfold tailWord_76765
  simp only [CollatzResearch.WordTrace]
  refine ⟨2799849566900990263335749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1866566377933993508890499 2799849566900990263335749)
  ·
    refine ⟨524971793793935674375453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2799849566900990263335749 524971793793935674375453)
    ·
      refine ⟨196864422672725877890795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 524971793793935674375453 196864422672725877890795)
      ·
        refine ⟨295296634009088816836193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196864422672725877890795 295296634009088816836193)
        ·
          refine ⟨221472475506816612627145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 295296634009088816836193 221472475506816612627145)
          ·
            refine ⟨166104356630112459470359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 221472475506816612627145 166104356630112459470359)
            ·
              refine ⟨249156534945168689205539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166104356630112459470359 249156534945168689205539)
              ·
                refine ⟨373734802417753033808309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 249156534945168689205539 373734802417753033808309)
                ·
                  refine ⟨35037637726664346919529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 373734802417753033808309 35037637726664346919529)
                  ·
                    rfl

theorem cell20_76765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_76765 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_76765 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_76765 prefixEnd_76765 := by exact prefixLift 76765
  have htrace : WordTrace (prefixWord ++ tailWord_76765) baseStart_76765 baseEnd_76765 := by
    simpa [prefixWord, tailWord_76765, baseEnd_76765] using wordTrace_append hprefix tailTrace_76765
  have hstable : (prefixWord ++ tailWord_76765).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76765).length < 2 ^ (prefixWord ++ tailWord_76765).sum := by decide
  have hdescent : baseEnd_76765 < baseStart_76765 := by decide
  rcases family_descends (prefixWord ++ tailWord_76765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76788 : List Nat := [2, 6, 2, 1, 1, 2, 2, 4]
def baseStart_76788 : Nat := 118140960795 + 76788 * 2 ^ 59
def prefixEnd_76788 : Nat := 4983230072969 + 3 ^ 40 * 76788 * 2
def baseEnd_76788 : Nat := 11682711851126163050923

theorem tailTrace_76788 : CollatzResearch.WordTrace tailWord_76788 prefixEnd_76788 11682711851126163050923 := by
  unfold tailWord_76788
  simp only [CollatzResearch.WordTrace]
  refine ⟨1400344222908832595711509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1867125630545110127615345 1400344222908832595711509)
  ·
    refine ⟨65641135448851527923977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 1400344222908832595711509 65641135448851527923977)
    ·
      refine ⟨49230851586638645942983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65641135448851527923977 49230851586638645942983)
      ·
        refine ⟨73846277379957968914475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49230851586638645942983 73846277379957968914475)
        ·
          refine ⟨110769416069936953371713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73846277379957968914475 110769416069936953371713)
          ·
            refine ⟨83077062052452715028785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110769416069936953371713 83077062052452715028785)
            ·
              refine ⟨62307796539339536271589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83077062052452715028785 62307796539339536271589)
              ·
                refine ⟨11682711851126163050923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62307796539339536271589 11682711851126163050923)
                ·
                  rfl

theorem cell20_76788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 2, 4].length) (baseStart_76788 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_76788 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_76788 prefixEnd_76788 := by exact prefixLift 76788
  have htrace : WordTrace (prefixWord ++ tailWord_76788) baseStart_76788 baseEnd_76788 := by
    simpa [prefixWord, tailWord_76788, baseEnd_76788] using wordTrace_append hprefix tailTrace_76788
  have hstable : (prefixWord ++ tailWord_76788).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76788).length < 2 ^ (prefixWord ++ tailWord_76788).sum := by decide
  have hdescent : baseEnd_76788 < baseStart_76788 := by decide
  rcases family_descends (prefixWord ++ tailWord_76788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76793 : List Nat := [1, 2, 1, 3, 1, 3, 1, 4, 4]
def baseStart_76793 : Nat := 118140960795 + 76793 * 2 ^ 59
def prefixEnd_76793 : Nat := 4983230072969 + 3 ^ 40 * 76793 * 2
def baseEnd_76793 : Nat := 35050417689620693986081

theorem tailTrace_76793 : CollatzResearch.WordTrace tailWord_76793 prefixEnd_76793 35050417689620693986081 := by
  unfold tailWord_76793
  simp only [CollatzResearch.WordTrace]
  refine ⟨2800870810799551045355033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1867247207199700696903355 2800870810799551045355033)
  ·
    refine ⟨2100653108099663284016275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2800870810799551045355033 2100653108099663284016275)
    ·
      refine ⟨3150979662149494926024413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2100653108099663284016275 3150979662149494926024413)
      ·
        refine ⟨1181617373306060597259155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3150979662149494926024413 1181617373306060597259155)
        ·
          refine ⟨1772426059959090895888733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1181617373306060597259155 1772426059959090895888733)
          ·
            refine ⟨664659772484659085958275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1772426059959090895888733 664659772484659085958275)
            ·
              refine ⟨996989658726988628937413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 664659772484659085958275 996989658726988628937413)
              ·
                refine ⟨186935561011310367925765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 996989658726988628937413 186935561011310367925765)
                ·
                  refine ⟨35050417689620693986081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 186935561011310367925765 35050417689620693986081)
                  ·
                    rfl

theorem cell20_76793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 4, 4].length) (baseStart_76793 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_76793 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_76793 prefixEnd_76793 := by exact prefixLift 76793
  have htrace : WordTrace (prefixWord ++ tailWord_76793) baseStart_76793 baseEnd_76793 := by
    simpa [prefixWord, tailWord_76793, baseEnd_76793] using wordTrace_append hprefix tailTrace_76793
  have hstable : (prefixWord ++ tailWord_76793).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76793).length < 2 ^ (prefixWord ++ tailWord_76793).sum := by decide
  have hdescent : baseEnd_76793 < baseStart_76793 := by decide
  rcases family_descends (prefixWord ++ tailWord_76793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76796 : List Nat := [2, 2, 2, 1, 2, 5, 2, 4]
def baseStart_76796 : Nat := 118140960795 + 76796 * 2 ^ 59
def prefixEnd_76796 : Nat := 4983230072969 + 3 ^ 40 * 76796 * 2
def baseEnd_76796 : Nat := 11683928990455338962023

theorem tailTrace_76796 : CollatzResearch.WordTrace tailWord_76796 prefixEnd_76796 11683928990455338962023 := by
  unfold tailWord_76796
  simp only [CollatzResearch.WordTrace]
  refine ⟨1400490114894341278857121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1867320153192455038476161 1400490114894341278857121)
  ·
    refine ⟨1050367586170755959142841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1400490114894341278857121 1050367586170755959142841)
    ·
      refine ⟨787775689628066969357131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1050367586170755959142841 787775689628066969357131)
      ·
        refine ⟨1181663534442100454035697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 787775689628066969357131 1181663534442100454035697)
        ·
          refine ⟨886247650831575340526773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1181663534442100454035697 886247650831575340526773)
          ·
            refine ⟨83085717265460188174385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 886247650831575340526773 83085717265460188174385)
            ·
              refine ⟨62314287949095141130789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83085717265460188174385 62314287949095141130789)
              ·
                refine ⟨11683928990455338962023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62314287949095141130789 11683928990455338962023)
                ·
                  rfl

theorem cell20_76796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 2, 4].length) (baseStart_76796 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_76796 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_76796 prefixEnd_76796 := by exact prefixLift 76796
  have htrace : WordTrace (prefixWord ++ tailWord_76796) baseStart_76796 baseEnd_76796 := by
    simpa [prefixWord, tailWord_76796, baseEnd_76796] using wordTrace_append hprefix tailTrace_76796
  have hstable : (prefixWord ++ tailWord_76796).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76796).length < 2 ^ (prefixWord ++ tailWord_76796).sum := by decide
  have hdescent : baseEnd_76796 < baseStart_76796 := by decide
  rcases family_descends (prefixWord ++ tailWord_76796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76802 : List Nat := [3, 4, 1, 3, 1, 2, 1, 3, 2]
def baseStart_76802 : Nat := 118140960795 + 76802 * 2 ^ 59
def prefixEnd_76802 : Nat := 4983230072969 + 3 ^ 40 * 76802 * 2
def baseEnd_76802 : Nat := 35054525534856662686045

theorem tailTrace_76802 : CollatzResearch.WordTrace tailWord_76802 prefixEnd_76802 35054525534856662686045 := by
  unfold tailWord_76802
  simp only [CollatzResearch.WordTrace]
  refine ⟨700299766941736395608165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1867466045177963721621773 700299766941736395608165)
  ·
    refine ⟨131306206301575574176531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 700299766941736395608165 131306206301575574176531)
    ·
      refine ⟨196959309452363361264797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131306206301575574176531 196959309452363361264797)
      ·
        refine ⟨73859741044636260474299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 196959309452363361264797 73859741044636260474299)
        ·
          refine ⟨110789611566954390711449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73859741044636260474299 110789611566954390711449)
          ·
            refine ⟨83092208675215793033587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110789611566954390711449 83092208675215793033587)
            ·
              refine ⟨124638313012823689550381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83092208675215793033587 124638313012823689550381)
              ·
                refine ⟨46739367379808883581393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 124638313012823689550381 46739367379808883581393)
                ·
                  refine ⟨35054525534856662686045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46739367379808883581393 35054525534856662686045)
                  ·
                    rfl

theorem cell20_76802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_76802 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_76802 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_76802 prefixEnd_76802 := by exact prefixLift 76802
  have htrace : WordTrace (prefixWord ++ tailWord_76802) baseStart_76802 baseEnd_76802 := by
    simpa [prefixWord, tailWord_76802, baseEnd_76802] using wordTrace_append hprefix tailTrace_76802
  have hstable : (prefixWord ++ tailWord_76802).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76802).length < 2 ^ (prefixWord ++ tailWord_76802).sum := by decide
  have hdescent : baseEnd_76802 < baseStart_76802 := by decide
  rcases family_descends (prefixWord ++ tailWord_76802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76824 : List Nat := [2, 1, 2, 3, 2, 2, 2, 1, 5]
def baseStart_76824 : Nat := 118140960795 + 76824 * 2 ^ 59
def prefixEnd_76824 : Nat := 4983230072969 + 3 ^ 40 * 76824 * 2
def baseEnd_76824 : Nat := 35064566934322363952621

theorem tailTrace_76824 : CollatzResearch.WordTrace tailWord_76824 prefixEnd_76824 35064566934322363952621 := by
  unfold tailWord_76824
  simp only [CollatzResearch.WordTrace]
  refine ⟨1401000736843621669866763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1868000982458162226489017 1401000736843621669866763)
  ·
    refine ⟨2101501105265432504800145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1401000736843621669866763 2101501105265432504800145)
    ·
      refine ⟨1576125828949074378600109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2101501105265432504800145 1576125828949074378600109)
      ·
        refine ⟨591047185855902891975041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1576125828949074378600109 591047185855902891975041)
        ·
          refine ⟨443285389391927168981281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 591047185855902891975041 443285389391927168981281)
          ·
            refine ⟨332464042043945376735961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 443285389391927168981281 332464042043945376735961)
            ·
              refine ⟨249348031532959032551971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 332464042043945376735961 249348031532959032551971)
              ·
                refine ⟨374022047299438548827957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 249348031532959032551971 374022047299438548827957)
                ·
                  refine ⟨35064566934322363952621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 374022047299438548827957 35064566934322363952621)
                  ·
                    rfl

theorem cell20_76824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 1, 5].length) (baseStart_76824 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_76824 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_76824 prefixEnd_76824 := by exact prefixLift 76824
  have htrace : WordTrace (prefixWord ++ tailWord_76824) baseStart_76824 baseEnd_76824 := by
    simpa [prefixWord, tailWord_76824, baseEnd_76824] using wordTrace_append hprefix tailTrace_76824
  have hstable : (prefixWord ++ tailWord_76824).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76824).length < 2 ^ (prefixWord ++ tailWord_76824).sum := by decide
  have hdescent : baseEnd_76824 < baseStart_76824 := by decide
  rcases family_descends (prefixWord ++ tailWord_76824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76882 : List Nat := [3, 2, 2, 1, 3, 1, 4, 2, 2]
def baseStart_76882 : Nat := 118140960795 + 76882 * 2 ^ 59
def prefixEnd_76882 : Nat := 4983230072969 + 3 ^ 40 * 76882 * 2
def baseEnd_76882 : Nat := 35091039714731940019051

theorem tailTrace_76882 : CollatzResearch.WordTrace tailWord_76882 prefixEnd_76882 35091039714731940019051 := by
  unfold tailWord_76882
  simp only [CollatzResearch.WordTrace]
  refine ⟨701029226869279811336225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1869411271651412830229933 701029226869279811336225)
  ·
    refine ⟨525771920151959858502169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 701029226869279811336225 525771920151959858502169)
    ·
      refine ⟨394328940113969893876627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 525771920151959858502169 394328940113969893876627)
      ·
        refine ⟨591493410170954840814941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 394328940113969893876627 591493410170954840814941)
        ·
          refine ⟨221810028814108065305603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 591493410170954840814941 221810028814108065305603)
          ·
            refine ⟨332715043221162097958405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221810028814108065305603 332715043221162097958405)
            ·
              refine ⟨62384070603967893367201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 332715043221162097958405 62384070603967893367201)
              ·
                refine ⟨46788052952975920025401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62384070603967893367201 46788052952975920025401)
                ·
                  refine ⟨35091039714731940019051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46788052952975920025401 35091039714731940019051)
                  ·
                    rfl

theorem cell20_76882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 4, 2, 2].length) (baseStart_76882 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_76882 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_76882 prefixEnd_76882 := by exact prefixLift 76882
  have htrace : WordTrace (prefixWord ++ tailWord_76882) baseStart_76882 baseEnd_76882 := by
    simpa [prefixWord, tailWord_76882, baseEnd_76882] using wordTrace_append hprefix tailTrace_76882
  have hstable : (prefixWord ++ tailWord_76882).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76882).length < 2 ^ (prefixWord ++ tailWord_76882).sum := by decide
  have hdescent : baseEnd_76882 < baseStart_76882 := by decide
  rcases family_descends (prefixWord ++ tailWord_76882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76910 : List Nat := [4, 1, 2, 2, 1, 3, 3, 4]
def baseStart_76910 : Nat := 118140960795 + 76910 * 2 ^ 59
def prefixEnd_76910 : Nat := 4983230072969 + 3 ^ 40 * 76910 * 2
def baseEnd_76910 : Nat := 11701273225896095695201

theorem tailTrace_76910 : CollatzResearch.WordTrace tailWord_76910 prefixEnd_76910 11701273225896095695201 := by
  unfold tailWord_76910
  simp only [CollatzResearch.WordTrace]
  refine ⟨350642268921960003420523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1870092100917120018242789 350642268921960003420523)
  ·
    refine ⟨525963403382940005130785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 350642268921960003420523 525963403382940005130785)
    ·
      refine ⟨394472552537205003848089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 525963403382940005130785 394472552537205003848089)
      ·
        refine ⟨295854414402903752886067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 394472552537205003848089 295854414402903752886067)
        ·
          refine ⟨443781621604355629329101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 295854414402903752886067 443781621604355629329101)
          ·
            refine ⟨166418108101633360998413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 443781621604355629329101 166418108101633360998413)
            ·
              refine ⟨62406790538112510374405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 166418108101633360998413 62406790538112510374405)
              ·
                refine ⟨11701273225896095695201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62406790538112510374405 11701273225896095695201)
                ·
                  rfl

theorem cell20_76910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 3, 4].length) (baseStart_76910 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_76910 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_76910 prefixEnd_76910 := by exact prefixLift 76910
  have htrace : WordTrace (prefixWord ++ tailWord_76910) baseStart_76910 baseEnd_76910 := by
    simpa [prefixWord, tailWord_76910, baseEnd_76910] using wordTrace_append hprefix tailTrace_76910
  have hstable : (prefixWord ++ tailWord_76910).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76910).length < 2 ^ (prefixWord ++ tailWord_76910).sum := by decide
  have hdescent : baseEnd_76910 < baseStart_76910 := by decide
  rcases family_descends (prefixWord ++ tailWord_76910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76938 : List Nat := [3, 1, 2, 3, 1, 1, 3, 1, 5]
def baseStart_76938 : Nat := 118140960795 + 76938 * 2 ^ 59
def prefixEnd_76938 : Nat := 4983230072969 + 3 ^ 40 * 76938 * 2
def baseEnd_76938 : Nat := 35116599640644634152155

theorem tailTrace_76938 : CollatzResearch.WordTrace tailWord_76938 prefixEnd_76938 35116599640644634152155 := by
  unfold tailWord_76938
  simp only [CollatzResearch.WordTrace]
  refine ⟨701539848818560202345867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1870772930182827206255645 701539848818560202345867)
  ·
    refine ⟨1052309773227840303518801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 701539848818560202345867 1052309773227840303518801)
    ·
      refine ⟨789232329920880227639101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1052309773227840303518801 789232329920880227639101)
      ·
        refine ⟨295962123720330085364663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 789232329920880227639101 295962123720330085364663)
        ·
          refine ⟨443943185580495128046995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 295962123720330085364663 443943185580495128046995)
          ·
            refine ⟨665914778370742692070493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 443943185580495128046995 665914778370742692070493)
            ·
              refine ⟨249718041889028509526435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 665914778370742692070493 249718041889028509526435)
              ·
                refine ⟨374577062833542764289653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 249718041889028509526435 374577062833542764289653)
                ·
                  refine ⟨35116599640644634152155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 374577062833542764289653 35116599640644634152155)
                  ·
                    rfl

theorem cell20_76938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 1, 5].length) (baseStart_76938 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_76938 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_76938 prefixEnd_76938 := by exact prefixLift 76938
  have htrace : WordTrace (prefixWord ++ tailWord_76938) baseStart_76938 baseEnd_76938 := by
    simpa [prefixWord, tailWord_76938, baseEnd_76938] using wordTrace_append hprefix tailTrace_76938
  have hstable : (prefixWord ++ tailWord_76938).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76938).length < 2 ^ (prefixWord ++ tailWord_76938).sum := by decide
  have hdescent : baseEnd_76938 < baseStart_76938 := by decide
  rcases family_descends (prefixWord ++ tailWord_76938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76982 : List Nat := [5, 1, 3, 2, 2, 1, 6]
def baseStart_76982 : Nat := 118140960795 + 76982 * 2 ^ 59
def prefixEnd_76982 : Nat := 4983230072969 + 3 ^ 40 * 76982 * 2
def baseEnd_76982 : Nat := 3904075826619559631701

theorem tailTrace_76982 : CollatzResearch.WordTrace tailWord_76982 prefixEnd_76982 3904075826619559631701 := by
  unfold tailWord_76982
  simp only [CollatzResearch.WordTrace]
  refine ⟨175485262944677270249075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1871842804743224215990133 175485262944677270249075)
  ·
    refine ⟨263227894417015905373613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175485262944677270249075 263227894417015905373613)
    ·
      refine ⟨98710460406380964515105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 263227894417015905373613 98710460406380964515105)
      ·
        refine ⟨74032845304785723386329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98710460406380964515105 74032845304785723386329)
        ·
          refine ⟨55524633978589292539747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74032845304785723386329 55524633978589292539747)
          ·
            refine ⟨83286950967883938809621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55524633978589292539747 83286950967883938809621)
            ·
              refine ⟨3904075826619559631701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 83286950967883938809621 3904075826619559631701)
              ·
                rfl

theorem cell20_76982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 6].length) (baseStart_76982 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_76982 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_76982 prefixEnd_76982 := by exact prefixLift 76982
  have htrace : WordTrace (prefixWord ++ tailWord_76982) baseStart_76982 baseEnd_76982 := by
    simpa [prefixWord, tailWord_76982, baseEnd_76982] using wordTrace_append hprefix tailTrace_76982
  have hstable : (prefixWord ++ tailWord_76982).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76982).length < 2 ^ (prefixWord ++ tailWord_76982).sum := by decide
  have hdescent : baseEnd_76982 < baseStart_76982 := by decide
  rcases family_descends (prefixWord ++ tailWord_76982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76993 : List Nat := [1, 2, 6, 1, 1, 1, 2, 1, 5]
def baseStart_76993 : Nat := 118140960795 + 76993 * 2 ^ 59
def prefixEnd_76993 : Nat := 4983230072969 + 3 ^ 40 * 76993 * 2
def baseEnd_76993 : Nat := 35141703139308887318597

theorem tailTrace_76993 : CollatzResearch.WordTrace tailWord_76993 prefixEnd_76993 35141703139308887318597 := by
  unfold tailWord_76993
  simp only [CollatzResearch.WordTrace]
  refine ⟨2808165410074985202635633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1872110273383323468423755 2808165410074985202635633)
  ·
    refine ⟨2106124057556238901976725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2808165410074985202635633 2106124057556238901976725)
    ·
      refine ⟨98724565197948698530159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 2106124057556238901976725 98724565197948698530159)
      ·
        refine ⟨148086847796923047795239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98724565197948698530159 148086847796923047795239)
        ·
          refine ⟨222130271695384571692859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148086847796923047795239 222130271695384571692859)
          ·
            refine ⟨333195407543076857539289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 222130271695384571692859 333195407543076857539289)
            ·
              refine ⟨249896555657307643154467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 333195407543076857539289 249896555657307643154467)
              ·
                refine ⟨374844833485961464731701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 249896555657307643154467 374844833485961464731701)
                ·
                  refine ⟨35141703139308887318597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 374844833485961464731701 35141703139308887318597)
                  ·
                    rfl

theorem cell20_76993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 1, 5].length) (baseStart_76993 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_76993 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_76993 prefixEnd_76993 := by exact prefixLift 76993
  have htrace : WordTrace (prefixWord ++ tailWord_76993) baseStart_76993 baseEnd_76993 := by
    simpa [prefixWord, tailWord_76993, baseEnd_76993] using wordTrace_append hprefix tailTrace_76993
  have hstable : (prefixWord ++ tailWord_76993).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76993).length < 2 ^ (prefixWord ++ tailWord_76993).sum := by decide
  have hdescent : baseEnd_76993 < baseStart_76993 := by decide
  rcases family_descends (prefixWord ++ tailWord_76993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76996 : List Nat := [2, 3, 3, 1, 4, 1, 1, 1, 4]
def baseStart_76996 : Nat := 118140960795 + 76996 * 2 ^ 59
def prefixEnd_76996 : Nat := 4983230072969 + 3 ^ 40 * 76996 * 2
def baseEnd_76996 : Nat := 35143072421054210218585

theorem tailTrace_76996 : CollatzResearch.WordTrace tailWord_76996 prefixEnd_76996 35143072421054210218585 := by
  unfold tailWord_76996
  simp only [CollatzResearch.WordTrace]
  refine ⟨1404137414532058357497421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1872183219376077809996561 1404137414532058357497421)
  ·
    refine ⟨526551530449521884061533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1404137414532058357497421 526551530449521884061533)
    ·
      refine ⟨197456823918570706523075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 526551530449521884061533 197456823918570706523075)
      ·
        refine ⟨296185235877856059784613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197456823918570706523075 296185235877856059784613)
        ·
          refine ⟨55534731727098011209615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 296185235877856059784613 55534731727098011209615)
          ·
            refine ⟨83302097590647016814423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55534731727098011209615 83302097590647016814423)
            ·
              refine ⟨124953146385970525221635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83302097590647016814423 124953146385970525221635)
              ·
                refine ⟨187429719578955787832453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 124953146385970525221635 187429719578955787832453)
                ·
                  refine ⟨35143072421054210218585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 187429719578955787832453 35143072421054210218585)
                  ·
                    rfl

theorem cell20_76996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 1, 4].length) (baseStart_76996 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_76996 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_76996 prefixEnd_76996 := by exact prefixLift 76996
  have htrace : WordTrace (prefixWord ++ tailWord_76996) baseStart_76996 baseEnd_76996 := by
    simpa [prefixWord, tailWord_76996, baseEnd_76996] using wordTrace_append hprefix tailTrace_76996
  have hstable : (prefixWord ++ tailWord_76996).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76996).length < 2 ^ (prefixWord ++ tailWord_76996).sum := by decide
  have hdescent : baseEnd_76996 < baseStart_76996 := by decide
  rcases family_descends (prefixWord ++ tailWord_76996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77000 : List Nat := [2, 1, 3, 1, 2, 1, 2, 6, 2]
def baseStart_77000 : Nat := 118140960795 + 77000 * 2 ^ 59
def prefixEnd_77000 : Nat := 4983230072969 + 3 ^ 40 * 77000 * 2
def baseEnd_77000 : Nat := 35144898130047974085235

theorem tailTrace_77000 : CollatzResearch.WordTrace tailWord_77000 prefixEnd_77000 35144898130047974085235 := by
  unfold tailWord_77000
  simp only [CollatzResearch.WordTrace]
  refine ⟨1404210360524812699070227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1872280480699750265426969 1404210360524812699070227)
  ·
    refine ⟨2106315540787219048605341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1404210360524812699070227 2106315540787219048605341)
    ·
      refine ⟨789868327795207143227003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2106315540787219048605341 789868327795207143227003)
      ·
        refine ⟨1184802491692810714840505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 789868327795207143227003 1184802491692810714840505)
        ·
          refine ⟨888601868769608036130379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1184802491692810714840505 888601868769608036130379)
          ·
            refine ⟨1332902803154412054195569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 888601868769608036130379 1332902803154412054195569)
            ·
              refine ⟨999677102365809040646677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1332902803154412054195569 999677102365809040646677)
              ·
                refine ⟨46859864173397298780313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 999677102365809040646677 46859864173397298780313)
                ·
                  refine ⟨35144898130047974085235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46859864173397298780313 35144898130047974085235)
                  ·
                    rfl

theorem cell20_77000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 6, 2].length) (baseStart_77000 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_77000 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_77000 prefixEnd_77000 := by exact prefixLift 77000
  have htrace : WordTrace (prefixWord ++ tailWord_77000) baseStart_77000 baseEnd_77000 := by
    simpa [prefixWord, tailWord_77000, baseEnd_77000] using wordTrace_append hprefix tailTrace_77000
  have hstable : (prefixWord ++ tailWord_77000).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77000).length < 2 ^ (prefixWord ++ tailWord_77000).sum := by decide
  have hdescent : baseEnd_77000 < baseStart_77000 := by decide
  rcases family_descends (prefixWord ++ tailWord_77000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77028 : List Nat := [2, 3, 1, 1, 1, 2, 4, 6]
def baseStart_77028 : Nat := 118140960795 + 77028 * 2 ^ 59
def prefixEnd_77028 : Nat := 4983230072969 + 3 ^ 40 * 77028 * 2
def baseEnd_77028 : Nat := 11719226031001440383929

theorem tailTrace_77028 : CollatzResearch.WordTrace tailWord_77028 prefixEnd_77028 11719226031001440383929 := by
  unfold tailWord_77028
  simp only [CollatzResearch.WordTrace]
  refine ⟨1404720982474093090079869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1872961309965457453439825 1404720982474093090079869)
  ·
    refine ⟨526770368427784908779951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1404720982474093090079869 526770368427784908779951)
    ·
      refine ⟨790155552641677363169927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 526770368427784908779951 790155552641677363169927)
      ·
        refine ⟨1185233328962516044754891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 790155552641677363169927 1185233328962516044754891)
        ·
          refine ⟨1777849993443774067132337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1185233328962516044754891 1777849993443774067132337)
          ·
            refine ⟨1333387495082830550349253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1777849993443774067132337 1333387495082830550349253)
            ·
              refine ⟨250010155328030728190485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1333387495082830550349253 250010155328030728190485)
              ·
                refine ⟨11719226031001440383929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 250010155328030728190485 11719226031001440383929)
                ·
                  rfl

theorem cell20_77028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 6].length) (baseStart_77028 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_77028 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_77028 prefixEnd_77028 := by exact prefixLift 77028
  have htrace : WordTrace (prefixWord ++ tailWord_77028) baseStart_77028 baseEnd_77028 := by
    simpa [prefixWord, tailWord_77028, baseEnd_77028] using wordTrace_append hprefix tailTrace_77028
  have hstable : (prefixWord ++ tailWord_77028).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77028).length < 2 ^ (prefixWord ++ tailWord_77028).sum := by decide
  have hdescent : baseEnd_77028 < baseStart_77028 := by decide
  rcases family_descends (prefixWord ++ tailWord_77028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77044 : List Nat := [2, 6, 1, 2, 1, 1, 2, 2, 3]
def baseStart_77044 : Nat := 118140960795 + 77044 * 2 ^ 59
def prefixEnd_77044 : Nat := 4983230072969 + 3 ^ 40 * 77044 * 2
def baseEnd_77044 : Nat := 35164980928979376618389

theorem tailTrace_77044 : CollatzResearch.WordTrace tailWord_77044 prefixEnd_77044 35164980928979376618389 := by
  unfold tailWord_77044
  simp only [CollatzResearch.WordTrace]
  refine ⟨1405012766445110456371093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1873350355260147275161457 1405012766445110456371093)
  ·
    refine ⟨65859973427114552642395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 1405012766445110456371093 65859973427114552642395)
    ·
      refine ⟨98789960140671828963593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65859973427114552642395 98789960140671828963593)
      ·
        refine ⟨74092470105503871722695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98789960140671828963593 74092470105503871722695)
        ·
          refine ⟨111138705158255807584043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74092470105503871722695 111138705158255807584043)
          ·
            refine ⟨166708057737383711376065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111138705158255807584043 166708057737383711376065)
            ·
              refine ⟨125031043303037783532049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 166708057737383711376065 125031043303037783532049)
              ·
                refine ⟨93773282477278337649037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 125031043303037783532049 93773282477278337649037)
                ·
                  refine ⟨35164980928979376618389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 93773282477278337649037 35164980928979376618389)
                  ·
                    rfl

theorem cell20_77044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_77044 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_77044 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_77044 prefixEnd_77044 := by exact prefixLift 77044
  have htrace : WordTrace (prefixWord ++ tailWord_77044) baseStart_77044 baseEnd_77044 := by
    simpa [prefixWord, tailWord_77044, baseEnd_77044] using wordTrace_append hprefix tailTrace_77044
  have hstable : (prefixWord ++ tailWord_77044).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77044).length < 2 ^ (prefixWord ++ tailWord_77044).sum := by decide
  have hdescent : baseEnd_77044 < baseStart_77044 := by decide
  rcases family_descends (prefixWord ++ tailWord_77044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77055 : List Nat := [1, 1, 2, 2, 1, 5, 4, 2, 2]
def baseStart_77055 : Nat := 118140960795 + 77055 * 2 ^ 59
def prefixEnd_77055 : Nat := 4983230072969 + 3 ^ 40 * 77055 * 2
def baseEnd_77055 : Nat := 35170001628712227251677

theorem tailTrace_77055 : CollatzResearch.WordTrace tailWord_77055 prefixEnd_77055 35170001628712227251677 := by
  unfold tailWord_77055
  simp only [CollatzResearch.WordTrace]
  refine ⟨2810426735850369791392619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1873617823900246527595079 2810426735850369791392619)
  ·
    refine ⟨4215640103775554687088929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2810426735850369791392619 4215640103775554687088929)
    ·
      refine ⟨3161730077831666015316697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4215640103775554687088929 3161730077831666015316697)
      ·
        refine ⟨2371297558373749511487523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3161730077831666015316697 2371297558373749511487523)
        ·
          refine ⟨3556946337560624267231285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2371297558373749511487523 3556946337560624267231285)
          ·
            refine ⟨333463719146308525052933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3556946337560624267231285 333463719146308525052933)
            ·
              refine ⟨62524447339932848447425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 333463719146308525052933 62524447339932848447425)
              ·
                refine ⟨46893335504949636335569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62524447339932848447425 46893335504949636335569)
                ·
                  refine ⟨35170001628712227251677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46893335504949636335569 35170001628712227251677)
                  ·
                    rfl

theorem cell20_77055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 4, 2, 2].length) (baseStart_77055 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_77055 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_77055 prefixEnd_77055 := by exact prefixLift 77055
  have htrace : WordTrace (prefixWord ++ tailWord_77055) baseStart_77055 baseEnd_77055 := by
    simpa [prefixWord, tailWord_77055, baseEnd_77055] using wordTrace_append hprefix tailTrace_77055
  have hstable : (prefixWord ++ tailWord_77055).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77055).length < 2 ^ (prefixWord ++ tailWord_77055).sum := by decide
  have hdescent : baseEnd_77055 < baseStart_77055 := by decide
  rcases family_descends (prefixWord ++ tailWord_77055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77093 : List Nat := [1, 3, 1, 2, 4, 2, 2, 3, 2]
def baseStart_77093 : Nat := 118140960795 + 77093 * 2 ^ 59
def prefixEnd_77093 : Nat := 4983230072969 + 3 ^ 40 * 77093 * 2
def baseEnd_77093 : Nat := 35187345864152983984855

theorem tailTrace_77093 : CollatzResearch.WordTrace tailWord_77093 prefixEnd_77093 35187345864152983984855 := by
  unfold tailWord_77093
  simp only [CollatzResearch.WordTrace]
  refine ⟨2811812709712702281275933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1874541806475134854183955 2811812709712702281275933)
  ·
    refine ⟨1054429766142263355478475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2811812709712702281275933 1054429766142263355478475)
    ·
      refine ⟨1581644649213395033217713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1054429766142263355478475 1581644649213395033217713)
      ·
        refine ⟨1186233486910046274913285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1581644649213395033217713 1186233486910046274913285)
        ·
          refine ⟨222418778795633676546241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1186233486910046274913285 222418778795633676546241)
          ·
            refine ⟨166814084096725257409681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 222418778795633676546241 166814084096725257409681)
            ·
              refine ⟨125110563072543943057261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 166814084096725257409681 125110563072543943057261)
              ·
                refine ⟨46916461152203978646473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 125110563072543943057261 46916461152203978646473)
                ·
                  refine ⟨35187345864152983984855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46916461152203978646473 35187345864152983984855)
                  ·
                    rfl

theorem cell20_77093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 3, 2].length) (baseStart_77093 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_77093 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_77093 prefixEnd_77093 := by exact prefixLift 77093
  have htrace : WordTrace (prefixWord ++ tailWord_77093) baseStart_77093 baseEnd_77093 := by
    simpa [prefixWord, tailWord_77093, baseEnd_77093] using wordTrace_append hprefix tailTrace_77093
  have hstable : (prefixWord ++ tailWord_77093).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77093).length < 2 ^ (prefixWord ++ tailWord_77093).sum := by decide
  have hdescent : baseEnd_77093 < baseStart_77093 := by decide
  rcases family_descends (prefixWord ++ tailWord_77093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77107 : List Nat := [1, 1, 1, 2, 5, 4, 1, 2, 3]
def baseStart_77107 : Nat := 118140960795 + 77107 * 2 ^ 59
def prefixEnd_77107 : Nat := 4983230072969 + 3 ^ 40 * 77107 * 2
def baseEnd_77107 : Nat := 35193735845631157518131

theorem tailTrace_77107 : CollatzResearch.WordTrace tailWord_77107 prefixEnd_77107 35193735845631157518131 := by
  unfold tailWord_77107
  simp only [CollatzResearch.WordTrace]
  refine ⟨2812323331661982672285575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1874882221107988448190383 2812323331661982672285575)
  ·
    refine ⟨4218484997492974008428363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2812323331661982672285575 4218484997492974008428363)
    ·
      refine ⟨6327727496239461012642545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4218484997492974008428363 6327727496239461012642545)
      ·
        refine ⟨4745795622179595759481909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6327727496239461012642545 4745795622179595759481909)
        ·
          refine ⟨444918339579337102451429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4745795622179595759481909 444918339579337102451429)
          ·
            refine ⟨83422188671125706709643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 444918339579337102451429 83422188671125706709643)
            ·
              refine ⟨125133283006688560064465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83422188671125706709643 125133283006688560064465)
              ·
                refine ⟨93849962255016420048349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 125133283006688560064465 93849962255016420048349)
                ·
                  refine ⟨35193735845631157518131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 93849962255016420048349 35193735845631157518131)
                  ·
                    rfl

theorem cell20_77107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 2, 3].length) (baseStart_77107 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_77107 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_77107 prefixEnd_77107 := by exact prefixLift 77107
  have htrace : WordTrace (prefixWord ++ tailWord_77107) baseStart_77107 baseEnd_77107 := by
    simpa [prefixWord, tailWord_77107, baseEnd_77107] using wordTrace_append hprefix tailTrace_77107
  have hstable : (prefixWord ++ tailWord_77107).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77107).length < 2 ^ (prefixWord ++ tailWord_77107).sum := by decide
  have hdescent : baseEnd_77107 < baseStart_77107 := by decide
  rcases family_descends (prefixWord ++ tailWord_77107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77110 : List Nat := [5, 1, 2, 3, 1, 1, 2, 1, 4]
def baseStart_77110 : Nat := 118140960795 + 77110 * 2 ^ 59
def prefixEnd_77110 : Nat := 4983230072969 + 3 ^ 40 * 77110 * 2
def baseEnd_77110 : Nat := 35195105127376480418119

theorem tailTrace_77110 : CollatzResearch.WordTrace tailWord_77110 prefixEnd_77110 35195105127376480418119 := by
  unfold tailWord_77110
  simp only [CollatzResearch.WordTrace]
  refine ⟨175777046915694636540299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1874955167100742789763189 175777046915694636540299)
  ·
    refine ⟨263665570373541954810449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175777046915694636540299 263665570373541954810449)
    ·
      refine ⟨197749177780156466107837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 263665570373541954810449 197749177780156466107837)
      ·
        refine ⟨74155941667558674790439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 197749177780156466107837 74155941667558674790439)
        ·
          refine ⟨111233912501338012185659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74155941667558674790439 111233912501338012185659)
          ·
            refine ⟨166850868752007018278489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111233912501338012185659 166850868752007018278489)
            ·
              refine ⟨125138151564005263708867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 166850868752007018278489 125138151564005263708867)
              ·
                refine ⟨187707227346007895563301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125138151564005263708867 187707227346007895563301)
                ·
                  refine ⟨35195105127376480418119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 187707227346007895563301 35195105127376480418119)
                  ·
                    rfl

theorem cell20_77110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_77110 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_77110 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_77110 prefixEnd_77110 := by exact prefixLift 77110
  have htrace : WordTrace (prefixWord ++ tailWord_77110) baseStart_77110 baseEnd_77110 := by
    simpa [prefixWord, tailWord_77110, baseEnd_77110] using wordTrace_append hprefix tailTrace_77110
  have hstable : (prefixWord ++ tailWord_77110).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77110).length < 2 ^ (prefixWord ++ tailWord_77110).sum := by decide
  have hdescent : baseEnd_77110 < baseStart_77110 := by decide
  rcases family_descends (prefixWord ++ tailWord_77110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77114 : List Nat := [3, 1, 1, 1, 4, 1, 1, 6, 2]
def baseStart_77114 : Nat := 118140960795 + 77114 * 2 ^ 59
def prefixEnd_77114 : Nat := 4983230072969 + 3 ^ 40 * 77114 * 2
def baseEnd_77114 : Nat := 35196930836370244284769

theorem tailTrace_77114 : CollatzResearch.WordTrace tailWord_77114 prefixEnd_77114 35196930836370244284769 := by
  unfold tailWord_77114
  simp only [CollatzResearch.WordTrace]
  refine ⟨703144660659155716947599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1875052428424415245193597 703144660659155716947599)
  ·
    refine ⟨1054716990988733575421399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 703144660659155716947599 1054716990988733575421399)
    ·
      refine ⟨1582075486483100363132099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1054716990988733575421399 1582075486483100363132099)
      ·
        refine ⟨2373113229724650544698149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1582075486483100363132099 2373113229724650544698149)
        ·
          refine ⟨444958730573371977130903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2373113229724650544698149 444958730573371977130903)
          ·
            refine ⟨667438095860057965696355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 444958730573371977130903 667438095860057965696355)
            ·
              refine ⟨1001157143790086948544533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 667438095860057965696355 1001157143790086948544533)
              ·
                refine ⟨46929241115160325713025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1001157143790086948544533 46929241115160325713025)
                ·
                  refine ⟨35196930836370244284769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46929241115160325713025 35196930836370244284769)
                  ·
                    rfl

theorem cell20_77114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 6, 2].length) (baseStart_77114 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_77114 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_77114 prefixEnd_77114 := by exact prefixLift 77114
  have htrace : WordTrace (prefixWord ++ tailWord_77114) baseStart_77114 baseEnd_77114 := by
    simpa [prefixWord, tailWord_77114, baseEnd_77114] using wordTrace_append hprefix tailTrace_77114
  have hstable : (prefixWord ++ tailWord_77114).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77114).length < 2 ^ (prefixWord ++ tailWord_77114).sum := by decide
  have hdescent : baseEnd_77114 < baseStart_77114 := by decide
  rcases family_descends (prefixWord ++ tailWord_77114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77159 : List Nat := [1, 1, 5, 1, 4, 2, 6]
def baseStart_77159 : Nat := 118140960795 + 77159 * 2 ^ 59
def prefixEnd_77159 : Nat := 4983230072969 + 3 ^ 40 * 77159 * 2
def baseEnd_77159 : Nat := 3913052229172231976065

theorem tailTrace_77159 : CollatzResearch.WordTrace tailWord_77159 prefixEnd_77159 3913052229172231976065 := by
  unfold tailWord_77159
  simp only [CollatzResearch.WordTrace]
  refine ⟨2814219927473595553178531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1876146618315730368785687 2814219927473595553178531)
  ·
    refine ⟨4221329891210393329767797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2814219927473595553178531 4221329891210393329767797)
    ·
      refine ⟨395749677300974374665731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4221329891210393329767797 395749677300974374665731)
      ·
        refine ⟨593624515951461561998597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 395749677300974374665731 593624515951461561998597)
        ·
          refine ⟨111304596740899042874737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 593624515951461561998597 111304596740899042874737)
          ·
            refine ⟨83478447555674282156053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111304596740899042874737 83478447555674282156053)
            ·
              refine ⟨3913052229172231976065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 83478447555674282156053 3913052229172231976065)
              ·
                rfl

theorem cell20_77159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 6].length) (baseStart_77159 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_77159 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_77159 prefixEnd_77159 := by exact prefixLift 77159
  have htrace : WordTrace (prefixWord ++ tailWord_77159) baseStart_77159 baseEnd_77159 := by
    simpa [prefixWord, tailWord_77159, baseEnd_77159] using wordTrace_append hprefix tailTrace_77159
  have hstable : (prefixWord ++ tailWord_77159).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77159).length < 2 ^ (prefixWord ++ tailWord_77159).sum := by decide
  have hdescent : baseEnd_77159 < baseStart_77159 := by decide
  rcases family_descends (prefixWord ++ tailWord_77159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77180 : List Nat := [2, 2, 2, 1, 1, 1, 6, 5]
def baseStart_77180 : Nat := 118140960795 + 77180 * 2 ^ 59
def prefixEnd_77180 : Nat := 4983230072969 + 3 ^ 40 * 77180 * 2
def baseEnd_77180 : Nat := 11742351678255782694833

theorem tailTrace_77180 : CollatzResearch.WordTrace tailWord_77180 prefixEnd_77180 11742351678255782694833 := by
  unfold tailWord_77180
  simp only [CollatzResearch.WordTrace]
  refine ⟨1407492930198758069846497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1876657240265010759795329 1407492930198758069846497)
  ·
    refine ⟨1055619697649068552384873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1407492930198758069846497 1055619697649068552384873)
    ·
      refine ⟨791714773236801414288655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1055619697649068552384873 791714773236801414288655)
      ·
        refine ⟨1187572159855202121432983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 791714773236801414288655 1187572159855202121432983)
        ·
          refine ⟨1781358239782803182149475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1187572159855202121432983 1781358239782803182149475)
          ·
            refine ⟨2672037359674204773224213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1781358239782803182149475 2672037359674204773224213)
            ·
              refine ⟨125251751234728348744885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2672037359674204773224213 125251751234728348744885)
              ·
                refine ⟨11742351678255782694833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 125251751234728348744885 11742351678255782694833)
                ·
                  rfl

theorem cell20_77180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 5].length) (baseStart_77180 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_77180 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_77180 prefixEnd_77180 := by exact prefixLift 77180
  have htrace : WordTrace (prefixWord ++ tailWord_77180) baseStart_77180 baseEnd_77180 := by
    simpa [prefixWord, tailWord_77180, baseEnd_77180] using wordTrace_append hprefix tailTrace_77180
  have hstable : (prefixWord ++ tailWord_77180).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77180).length < 2 ^ (prefixWord ++ tailWord_77180).sum := by decide
  have hdescent : baseEnd_77180 < baseStart_77180 := by decide
  rcases family_descends (prefixWord ++ tailWord_77180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77214 : List Nat := [4, 3, 1, 2, 3, 7]
def baseStart_77214 : Nat := 118140960795 + 77214 * 2 ^ 59
def prefixEnd_77214 : Nat := 4983230072969 + 3 ^ 40 * 77214 * 2
def baseEnd_77214 : Nat := 1305280502267197813001

theorem tailTrace_77214 : CollatzResearch.WordTrace tailWord_77214 prefixEnd_77214 1305280502267197813001 := by
  unfold tailWord_77214
  simp only [CollatzResearch.WordTrace]
  refine ⟨352028242784292493303837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1877483961516226630953797 352028242784292493303837)
  ·
    refine ⟨132010591044109684988939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 352028242784292493303837 132010591044109684988939)
    ·
      refine ⟨198015886566164527483409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132010591044109684988939 198015886566164527483409)
      ·
        refine ⟨148511914924623395612557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198015886566164527483409 148511914924623395612557)
        ·
          refine ⟨55691968096733773354709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 148511914924623395612557 55691968096733773354709)
          ·
            refine ⟨1305280502267197813001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 55691968096733773354709 1305280502267197813001)
            ·
              rfl

theorem cell20_77214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 7].length) (baseStart_77214 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_77214 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_77214 prefixEnd_77214 := by exact prefixLift 77214
  have htrace : WordTrace (prefixWord ++ tailWord_77214) baseStart_77214 baseEnd_77214 := by
    simpa [prefixWord, tailWord_77214, baseEnd_77214] using wordTrace_append hprefix tailTrace_77214
  have hstable : (prefixWord ++ tailWord_77214).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77214).length < 2 ^ (prefixWord ++ tailWord_77214).sum := by decide
  have hdescent : baseEnd_77214 < baseStart_77214 := by decide
  rcases family_descends (prefixWord ++ tailWord_77214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77218 : List Nat := [3, 3, 1, 2, 1, 10]
def baseStart_77218 : Nat := 118140960795 + 77218 * 2 ^ 59
def prefixEnd_77218 : Nat := 4983230072969 + 3 ^ 40 * 77218 * 2
def baseEnd_77218 : Nat := 1305348121118818696951

theorem tailTrace_77218 : CollatzResearch.WordTrace tailWord_77218 prefixEnd_77218 1305348121118818696951 := by
  unfold tailWord_77218
  simp only [CollatzResearch.WordTrace]
  refine ⟨704092958564962157394077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1877581222839899086384205 704092958564962157394077)
  ·
    refine ⟨264034859461860809022779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 704092958564962157394077 264034859461860809022779)
    ·
      refine ⟨396052289192791213534169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264034859461860809022779 396052289192791213534169)
      ·
        refine ⟨297039216894593410150627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 396052289192791213534169 297039216894593410150627)
        ·
          refine ⟨445558825341890115225941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 297039216894593410150627 445558825341890115225941)
          ·
            refine ⟨1305348121118818696951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 445558825341890115225941 1305348121118818696951)
            ·
              rfl

theorem cell20_77218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 10].length) (baseStart_77218 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_77218 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_77218 prefixEnd_77218 := by exact prefixLift 77218
  have htrace : WordTrace (prefixWord ++ tailWord_77218) baseStart_77218 baseEnd_77218 := by
    simpa [prefixWord, tailWord_77218, baseEnd_77218] using wordTrace_append hprefix tailTrace_77218
  have hstable : (prefixWord ++ tailWord_77218).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77218).length < 2 ^ (prefixWord ++ tailWord_77218).sum := by decide
  have hdescent : baseEnd_77218 < baseStart_77218 := by decide
  rcases family_descends (prefixWord ++ tailWord_77218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77224 : List Nat := [2, 1, 6, 1, 2, 1, 1, 4, 2]
def baseStart_77224 : Nat := 118140960795 + 77224 * 2 ^ 59
def prefixEnd_77224 : Nat := 4983230072969 + 3 ^ 40 * 77224 * 2
def baseEnd_77224 : Nat := 35247137833698750617653

theorem tailTrace_77224 : CollatzResearch.WordTrace tailWord_77224 prefixEnd_77224 35247137833698750617653 := by
  unfold tailWord_77224
  simp only [CollatzResearch.WordTrace]
  refine ⟨1408295336119055827147363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1877727114825407769529817 1408295336119055827147363)
  ·
    refine ⟨2112443004178583740721045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1408295336119055827147363 2112443004178583740721045)
    ·
      refine ⟨99020765820871112846299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 2112443004178583740721045 99020765820871112846299)
      ·
        refine ⟨148531148731306669269449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99020765820871112846299 148531148731306669269449)
        ·
          refine ⟨111398361548480001952087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148531148731306669269449 111398361548480001952087)
          ·
            refine ⟨167097542322720002928131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111398361548480001952087 167097542322720002928131)
            ·
              refine ⟨250646313484080004392197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 167097542322720002928131 250646313484080004392197)
              ·
                refine ⟨46996183778265000823537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 250646313484080004392197 46996183778265000823537)
                ·
                  refine ⟨35247137833698750617653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46996183778265000823537 35247137833698750617653)
                  ·
                    rfl

theorem cell20_77224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 4, 2].length) (baseStart_77224 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_77224 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_77224 prefixEnd_77224 := by exact prefixLift 77224
  have htrace : WordTrace (prefixWord ++ tailWord_77224) baseStart_77224 baseEnd_77224 := by
    simpa [prefixWord, tailWord_77224, baseEnd_77224] using wordTrace_append hprefix tailTrace_77224
  have hstable : (prefixWord ++ tailWord_77224).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77224).length < 2 ^ (prefixWord ++ tailWord_77224).sum := by decide
  have hdescent : baseEnd_77224 < baseStart_77224 := by decide
  rcases family_descends (prefixWord ++ tailWord_77224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77252 : List Nat := [2, 3, 3, 2, 1, 2, 3, 4]
def baseStart_77252 : Nat := 118140960795 + 77252 * 2 ^ 59
def prefixEnd_77252 : Nat := 4983230072969 + 3 ^ 40 * 77252 * 2
def baseEnd_77252 : Nat := 11753305932218365894735

theorem tailTrace_77252 : CollatzResearch.WordTrace tailWord_77252 prefixEnd_77252 11753305932218365894735 := by
  unfold tailWord_77252
  simp only [CollatzResearch.WordTrace]
  refine ⟨1408805958068336218157005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1878407944091114957542673 1408805958068336218157005)
  ·
    refine ⟨528302234275626081808877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1408805958068336218157005 528302234275626081808877)
    ·
      refine ⟨198113337853359780678329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 528302234275626081808877 198113337853359780678329)
      ·
        refine ⟨148585003390019835508747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198113337853359780678329 148585003390019835508747)
        ·
          refine ⟨222877505085029753263121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148585003390019835508747 222877505085029753263121)
          ·
            refine ⟨167158128813772314947341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 222877505085029753263121 167158128813772314947341)
            ·
              refine ⟨62684298305164618105253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 167158128813772314947341 62684298305164618105253)
              ·
                refine ⟨11753305932218365894735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62684298305164618105253 11753305932218365894735)
                ·
                  rfl

theorem cell20_77252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 3, 4].length) (baseStart_77252 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_77252 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_77252 prefixEnd_77252 := by exact prefixLift 77252
  have htrace : WordTrace (prefixWord ++ tailWord_77252) baseStart_77252 baseEnd_77252 := by
    simpa [prefixWord, tailWord_77252, baseEnd_77252] using wordTrace_append hprefix tailTrace_77252
  have hstable : (prefixWord ++ tailWord_77252).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77252).length < 2 ^ (prefixWord ++ tailWord_77252).sum := by decide
  have hdescent : baseEnd_77252 < baseStart_77252 := by decide
  rcases family_descends (prefixWord ++ tailWord_77252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77287 : List Nat := [1, 1, 5, 2, 1, 2, 1, 3, 4]
def baseStart_77287 : Nat := 118140960795 + 77287 * 2 ^ 59
def prefixEnd_77287 : Nat := 4983230072969 + 3 ^ 40 * 77287 * 2
def baseEnd_77287 : Nat := 35275892750350531517395

theorem tailTrace_77287 : CollatzResearch.WordTrace tailWord_77287 prefixEnd_77287 35275892750350531517395 := by
  unfold tailWord_77287
  simp only [CollatzResearch.WordTrace]
  refine ⟨2818888471009873413838115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1879258980673248942558743 2818888471009873413838115)
  ·
    refine ⟨4228332706514810120757173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2818888471009873413838115 4228332706514810120757173)
    ·
      refine ⟨396406191235763448820985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4228332706514810120757173 396406191235763448820985)
      ·
        refine ⟨297304643426822586615739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 396406191235763448820985 297304643426822586615739)
        ·
          refine ⟨445956965140233879923609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 297304643426822586615739 445956965140233879923609)
          ·
            refine ⟨334467723855175409942707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 445956965140233879923609 334467723855175409942707)
            ·
              refine ⟨501701585782763114914061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 334467723855175409942707 501701585782763114914061)
              ·
                refine ⟨188138094668536168092773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 501701585782763114914061 188138094668536168092773)
                ·
                  refine ⟨35275892750350531517395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 188138094668536168092773 35275892750350531517395)
                  ·
                    rfl

theorem cell20_77287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 3, 4].length) (baseStart_77287 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_77287 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_77287 prefixEnd_77287 := by exact prefixLift 77287
  have htrace : WordTrace (prefixWord ++ tailWord_77287) baseStart_77287 baseEnd_77287 := by
    simpa [prefixWord, tailWord_77287, baseEnd_77287] using wordTrace_append hprefix tailTrace_77287
  have hstable : (prefixWord ++ tailWord_77287).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77287).length < 2 ^ (prefixWord ++ tailWord_77287).sum := by decide
  have hdescent : baseEnd_77287 < baseStart_77287 := by decide
  rcases family_descends (prefixWord ++ tailWord_77287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77294 : List Nat := [4, 1, 2, 1, 2, 1, 2, 7]
def baseStart_77294 : Nat := 118140960795 + 77294 * 2 ^ 59
def prefixEnd_77294 : Nat := 4983230072969 + 3 ^ 40 * 77294 * 2
def baseEnd_77294 : Nat := 11759695913696539428011

theorem tailTrace_77294 : CollatzResearch.WordTrace tailWord_77294 prefixEnd_77294 11759695913696539428011 := by
  unfold tailWord_77294
  simp only [CollatzResearch.WordTrace]
  refine ⟨352392972748064201167867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1879429187989675739561957 352392972748064201167867)
  ·
    refine ⟨528589459122096301751801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 352392972748064201167867 528589459122096301751801)
    ·
      refine ⟨396442094341572226313851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 528589459122096301751801 396442094341572226313851)
      ·
        refine ⟨594663141512358339470777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 396442094341572226313851 594663141512358339470777)
        ·
          refine ⟨445997356134268754603083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 594663141512358339470777 445997356134268754603083)
          ·
            refine ⟨668996034201403131904625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 445997356134268754603083 668996034201403131904625)
            ·
              refine ⟨501747025651052348928469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 668996034201403131904625 501747025651052348928469)
              ·
                refine ⟨11759695913696539428011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 501747025651052348928469 11759695913696539428011)
                ·
                  rfl

theorem cell20_77294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 7].length) (baseStart_77294 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_77294 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_77294 prefixEnd_77294 := by exact prefixLift 77294
  have htrace : WordTrace (prefixWord ++ tailWord_77294) baseStart_77294 baseEnd_77294 := by
    simpa [prefixWord, tailWord_77294, baseEnd_77294] using wordTrace_append hprefix tailTrace_77294
  have hstable : (prefixWord ++ tailWord_77294).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77294).length < 2 ^ (prefixWord ++ tailWord_77294).sum := by decide
  have hdescent : baseEnd_77294 < baseStart_77294 := by decide
  rcases family_descends (prefixWord ++ tailWord_77294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77297 : List Nat := [1, 2, 2, 2, 3, 3, 3, 1, 3]
def baseStart_77297 : Nat := 118140960795 + 77297 * 2 ^ 59
def prefixEnd_77297 : Nat := 4983230072969 + 3 ^ 40 * 77297 * 2
def baseEnd_77297 : Nat := 35280457022834941184021

theorem tailTrace_77297 : CollatzResearch.WordTrace tailWord_77297 prefixEnd_77297 35280457022834941184021 := by
  unfold tailWord_77297
  simp only [CollatzResearch.WordTrace]
  refine ⟨2819253200973645121702145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1879502133982430081134763 2819253200973645121702145)
  ·
    refine ⟨2114439900730233841276609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2819253200973645121702145 2114439900730233841276609)
    ·
      refine ⟨1585829925547675380957457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2114439900730233841276609 1585829925547675380957457)
      ·
        refine ⟨1189372444160756535718093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1585829925547675380957457 1189372444160756535718093)
        ·
          refine ⟨446014666560283700894285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1189372444160756535718093 446014666560283700894285)
          ·
            refine ⟨167255499960106387835357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 446014666560283700894285 167255499960106387835357)
            ·
              refine ⟨62720812485039895438259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 167255499960106387835357 62720812485039895438259)
              ·
                refine ⟨94081218727559843157389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62720812485039895438259 94081218727559843157389)
                ·
                  refine ⟨35280457022834941184021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 94081218727559843157389 35280457022834941184021)
                  ·
                    rfl

theorem cell20_77297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 3, 1, 3].length) (baseStart_77297 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_77297 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_77297 prefixEnd_77297 := by exact prefixLift 77297
  have htrace : WordTrace (prefixWord ++ tailWord_77297) baseStart_77297 baseEnd_77297 := by
    simpa [prefixWord, tailWord_77297, baseEnd_77297] using wordTrace_append hprefix tailTrace_77297
  have hstable : (prefixWord ++ tailWord_77297).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77297).length < 2 ^ (prefixWord ++ tailWord_77297).sum := by decide
  have hdescent : baseEnd_77297 < baseStart_77297 := by decide
  rcases family_descends (prefixWord ++ tailWord_77297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77394 : List Nat := [3, 2, 2, 1, 2, 2, 1, 4, 3]
def baseStart_77394 : Nat := 118140960795 + 77394 * 2 ^ 59
def prefixEnd_77394 : Nat := 4983230072969 + 3 ^ 40 * 77394 * 2
def baseEnd_77394 : Nat := 35324730465933714950291

theorem tailTrace_77394 : CollatzResearch.WordTrace tailWord_77394 prefixEnd_77394 35324730465933714950291 := by
  unfold tailWord_77394
  simp only [CollatzResearch.WordTrace]
  refine ⟨705697770405557671995809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1881860721081487125322157 705697770405557671995809)
  ·
    refine ⟨529273327804168253996857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 705697770405557671995809 529273327804168253996857)
    ·
      refine ⟨396954995853126190497643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 529273327804168253996857 396954995853126190497643)
      ·
        refine ⟨595432493779689285746465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 396954995853126190497643 595432493779689285746465)
        ·
          refine ⟨446574370334766964309849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 595432493779689285746465 446574370334766964309849)
          ·
            refine ⟨334930777751075223232387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 446574370334766964309849 334930777751075223232387)
            ·
              refine ⟨502396166626612834848581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 334930777751075223232387 502396166626612834848581)
              ·
                refine ⟨94199281242489906534109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 502396166626612834848581 94199281242489906534109)
                ·
                  refine ⟨35324730465933714950291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 94199281242489906534109 35324730465933714950291)
                  ·
                    rfl

theorem cell20_77394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 4, 3].length) (baseStart_77394 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_77394 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_77394 prefixEnd_77394 := by exact prefixLift 77394
  have htrace : WordTrace (prefixWord ++ tailWord_77394) baseStart_77394 baseEnd_77394 := by
    simpa [prefixWord, tailWord_77394, baseEnd_77394] using wordTrace_append hprefix tailTrace_77394
  have hstable : (prefixWord ++ tailWord_77394).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77394).length < 2 ^ (prefixWord ++ tailWord_77394).sum := by decide
  have hdescent : baseEnd_77394 < baseStart_77394 := by decide
  rcases family_descends (prefixWord ++ tailWord_77394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77508 : List Nat := [2, 3, 3, 1, 1, 1, 2, 4, 3]
def baseStart_77508 : Nat := 118140960795 + 77508 * 2 ^ 59
def prefixEnd_77508 : Nat := 4983230072969 + 3 ^ 40 * 77508 * 2
def baseEnd_77508 : Nat := 35376763172255985149825

theorem tailTrace_77508 : CollatzResearch.WordTrace tailWord_77508 prefixEnd_77508 35376763172255985149825 := by
  unfold tailWord_77508
  simp only [CollatzResearch.WordTrace]
  refine ⟨1413474501604614078816589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1884632668806152105088785 1413474501604614078816589)
  ·
    refine ⟨530052938101730279556221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1413474501604614078816589 530052938101730279556221)
    ·
      refine ⟨198769851788148854833583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 530052938101730279556221 198769851788148854833583)
      ·
        refine ⟨298154777682223282250375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198769851788148854833583 298154777682223282250375)
        ·
          refine ⟨447232166523334923375563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 298154777682223282250375 447232166523334923375563)
          ·
            refine ⟨670848249785002385063345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 447232166523334923375563 670848249785002385063345)
            ·
              refine ⟨503136187338751788797509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 670848249785002385063345 503136187338751788797509)
              ·
                refine ⟨94338035126015960399533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 503136187338751788797509 94338035126015960399533)
                ·
                  refine ⟨35376763172255985149825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 94338035126015960399533 35376763172255985149825)
                  ·
                    rfl

theorem cell20_77508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 4, 3].length) (baseStart_77508 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_77508 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_77508 prefixEnd_77508 := by exact prefixLift 77508
  have htrace : WordTrace (prefixWord ++ tailWord_77508) baseStart_77508 baseEnd_77508 := by
    simpa [prefixWord, tailWord_77508, baseEnd_77508] using wordTrace_append hprefix tailTrace_77508
  have hstable : (prefixWord ++ tailWord_77508).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77508).length < 2 ^ (prefixWord ++ tailWord_77508).sum := by decide
  have hdescent : baseEnd_77508 < baseStart_77508 := by decide
  rcases family_descends (prefixWord ++ tailWord_77508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77515 : List Nat := [1, 1, 1, 1, 3, 2, 1, 8, 2]
def baseStart_77515 : Nat := 118140960795 + 77515 * 2 ^ 59
def prefixEnd_77515 : Nat := 4983230072969 + 3 ^ 40 * 77515 * 2
def baseEnd_77515 : Nat := 35379958162995071916463

theorem tailTrace_77515 : CollatzResearch.WordTrace tailWord_77515 prefixEnd_77515 35379958162995071916463 := by
  unfold tailWord_77515
  simp only [CollatzResearch.WordTrace]
  refine ⟨2827204314183868353137999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1884802876122578902091999 2827204314183868353137999)
  ·
    refine ⟨4240806471275802529706999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2827204314183868353137999 4240806471275802529706999)
    ·
      refine ⟨6361209706913703794560499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4240806471275802529706999 6361209706913703794560499)
      ·
        refine ⟨9541814560370555691840749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6361209706913703794560499 9541814560370555691840749)
        ·
          refine ⟨3578180460138958384440281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9541814560370555691840749 3578180460138958384440281)
          ·
            refine ⟨2683635345104218788330211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3578180460138958384440281 2683635345104218788330211)
            ·
              refine ⟨4025453017656328182495317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2683635345104218788330211 4025453017656328182495317)
              ·
                refine ⟨47173277550660095888617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4025453017656328182495317 47173277550660095888617)
                ·
                  refine ⟨35379958162995071916463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47173277550660095888617 35379958162995071916463)
                  ·
                    rfl

theorem cell20_77515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 8, 2].length) (baseStart_77515 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_77515 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_77515 prefixEnd_77515 := by exact prefixLift 77515
  have htrace : WordTrace (prefixWord ++ tailWord_77515) baseStart_77515 baseEnd_77515 := by
    simpa [prefixWord, tailWord_77515, baseEnd_77515] using wordTrace_append hprefix tailTrace_77515
  have hstable : (prefixWord ++ tailWord_77515).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77515).length < 2 ^ (prefixWord ++ tailWord_77515).sum := by decide
  have hdescent : baseEnd_77515 < baseStart_77515 := by decide
  rcases family_descends (prefixWord ++ tailWord_77515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77522 : List Nat := [3, 2, 2, 2, 2, 1, 1, 7]
def baseStart_77522 : Nat := 118140960795 + 77522 * 2 ^ 59
def prefixEnd_77522 : Nat := 4983230072969 + 3 ^ 40 * 77522 * 2
def baseEnd_77522 : Nat := 11794384384578052894367

theorem tailTrace_77522 : CollatzResearch.WordTrace tailWord_77522 prefixEnd_77522 11794384384578052894367 := by
  unfold tailWord_77522
  simp only [CollatzResearch.WordTrace]
  refine ⟨706864906289627137160705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1884973083439005699095213 706864906289627137160705)
  ·
    refine ⟨530148679717220352870529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 706864906289627137160705 530148679717220352870529)
    ·
      refine ⟨397611509787915264652897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 530148679717220352870529 397611509787915264652897)
      ·
        refine ⟨298208632340936448489673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 397611509787915264652897 298208632340936448489673)
        ·
          refine ⟨223656474255702336367255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 298208632340936448489673 223656474255702336367255)
          ·
            refine ⟨335484711383553504550883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223656474255702336367255 335484711383553504550883)
            ·
              refine ⟨503227067075330256826325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 335484711383553504550883 503227067075330256826325)
              ·
                refine ⟨11794384384578052894367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 503227067075330256826325 11794384384578052894367)
                ·
                  rfl

theorem cell20_77522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 7].length) (baseStart_77522 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_77522 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_77522 prefixEnd_77522 := by exact prefixLift 77522
  have htrace : WordTrace (prefixWord ++ tailWord_77522) baseStart_77522 baseEnd_77522 := by
    simpa [prefixWord, tailWord_77522, baseEnd_77522] using wordTrace_append hprefix tailTrace_77522
  have hstable : (prefixWord ++ tailWord_77522).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77522).length < 2 ^ (prefixWord ++ tailWord_77522).sum := by decide
  have hdescent : baseEnd_77522 < baseStart_77522 := by decide
  rcases family_descends (prefixWord ++ tailWord_77522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77536 : List Nat := [2, 1, 1, 3, 1, 2, 2, 4, 4]
def baseStart_77536 : Nat := 118140960795 + 77536 * 2 ^ 59
def prefixEnd_77536 : Nat := 4983230072969 + 3 ^ 40 * 77536 * 2
def baseEnd_77536 : Nat := 35389543135212332216377

theorem tailTrace_77536 : CollatzResearch.WordTrace tailWord_77536 prefixEnd_77536 35389543135212332216377 := by
  unfold tailWord_77536
  simp only [CollatzResearch.WordTrace]
  refine ⟨1413985123553894469826231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1885313498071859293101641 1413985123553894469826231)
  ·
    refine ⟨2120977685330841704739347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1413985123553894469826231 2120977685330841704739347)
    ·
      refine ⟨3181466527996262557109021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2120977685330841704739347 3181466527996262557109021)
      ·
        refine ⟨1193049947998598458915883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3181466527996262557109021 1193049947998598458915883)
        ·
          refine ⟨1789574921997897688373825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1193049947998598458915883 1789574921997897688373825)
          ·
            refine ⟨1342181191498423266280369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1789574921997897688373825 1342181191498423266280369)
            ·
              refine ⟨1006635893623817449710277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1342181191498423266280369 1006635893623817449710277)
              ·
                refine ⟨188744230054465771820677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1006635893623817449710277 188744230054465771820677)
                ·
                  refine ⟨35389543135212332216377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 188744230054465771820677 35389543135212332216377)
                  ·
                    rfl

theorem cell20_77536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 4, 4].length) (baseStart_77536 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_77536 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_77536 prefixEnd_77536 := by exact prefixLift 77536
  have htrace : WordTrace (prefixWord ++ tailWord_77536) baseStart_77536 baseEnd_77536 := by
    simpa [prefixWord, tailWord_77536, baseEnd_77536] using wordTrace_append hprefix tailTrace_77536
  have hstable : (prefixWord ++ tailWord_77536).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77536).length < 2 ^ (prefixWord ++ tailWord_77536).sum := by decide
  have hdescent : baseEnd_77536 < baseStart_77536 := by decide
  rcases family_descends (prefixWord ++ tailWord_77536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77567 : List Nat := [1, 1, 2, 2, 1, 3, 3, 4, 3]
def baseStart_77567 : Nat := 118140960795 + 77567 * 2 ^ 59
def prefixEnd_77567 : Nat := 4983230072969 + 3 ^ 40 * 77567 * 2
def baseEnd_77567 : Nat := 35403692379914002182917

theorem tailTrace_77567 : CollatzResearch.WordTrace tailWord_77567 prefixEnd_77567 35403692379914002182917 := by
  unfold tailWord_77567
  simp only [CollatzResearch.WordTrace]
  refine ⟨2829100909995481234030955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1886067273330320822687303 2829100909995481234030955)
  ·
    refine ⟨4243651364993221851046433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2829100909995481234030955 4243651364993221851046433)
    ·
      refine ⟨3182738523744916388284825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4243651364993221851046433 3182738523744916388284825)
      ·
        refine ⟨2387053892808687291213619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3182738523744916388284825 2387053892808687291213619)
        ·
          refine ⟨3580580839213030936820429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2387053892808687291213619 3580580839213030936820429)
          ·
            refine ⟨1342717814704886601307661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3580580839213030936820429 1342717814704886601307661)
            ·
              refine ⟨503519180514332475490373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1342717814704886601307661 503519180514332475490373)
              ·
                refine ⟨94409846346437339154445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 503519180514332475490373 94409846346437339154445)
                ·
                  refine ⟨35403692379914002182917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 94409846346437339154445 35403692379914002182917)
                  ·
                    rfl

theorem cell20_77567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 4, 3].length) (baseStart_77567 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_77567 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_77567 prefixEnd_77567 := by exact prefixLift 77567
  have htrace : WordTrace (prefixWord ++ tailWord_77567) baseStart_77567 baseEnd_77567 := by
    simpa [prefixWord, tailWord_77567, baseEnd_77567] using wordTrace_append hprefix tailTrace_77567
  have hstable : (prefixWord ++ tailWord_77567).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77567).length < 2 ^ (prefixWord ++ tailWord_77567).sum := by decide
  have hdescent : baseEnd_77567 < baseStart_77567 := by decide
  rcases family_descends (prefixWord ++ tailWord_77567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77591 : List Nat := [1, 1, 3, 4, 2, 2, 1, 2, 4]
def baseStart_77591 : Nat := 118140960795 + 77591 * 2 ^ 59
def prefixEnd_77591 : Nat := 4983230072969 + 3 ^ 40 * 77591 * 2
def baseEnd_77591 : Nat := 35414646633876585382819

theorem tailTrace_77591 : CollatzResearch.WordTrace tailWord_77591 prefixEnd_77591 35414646633876585382819 := by
  unfold tailWord_77591
  simp only [CollatzResearch.WordTrace]
  refine ⟨2829976261908533332904627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1886650841272355555269751 2829976261908533332904627)
  ·
    refine ⟨4244964392862799999356941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2829976261908533332904627 4244964392862799999356941)
    ·
      refine ⟨1591861647323549999758853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4244964392862799999356941 1591861647323549999758853)
      ·
        refine ⟨298474058873165624954785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1591861647323549999758853 298474058873165624954785)
        ·
          refine ⟨223855544154874218716089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 298474058873165624954785 223855544154874218716089)
          ·
            refine ⟨167891658116155664037067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 223855544154874218716089 167891658116155664037067)
            ·
              refine ⟨251837487174233496055601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 167891658116155664037067 251837487174233496055601)
              ·
                refine ⟨188878115380675122041701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 251837487174233496055601 188878115380675122041701)
                ·
                  refine ⟨35414646633876585382819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 188878115380675122041701 35414646633876585382819)
                  ·
                    rfl

theorem cell20_77591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 2, 4].length) (baseStart_77591 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_77591 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_77591 prefixEnd_77591 := by exact prefixLift 77591
  have htrace : WordTrace (prefixWord ++ tailWord_77591) baseStart_77591 baseEnd_77591 := by
    simpa [prefixWord, tailWord_77591, baseEnd_77591] using wordTrace_append hprefix tailTrace_77591
  have hstable : (prefixWord ++ tailWord_77591).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77591).length < 2 ^ (prefixWord ++ tailWord_77591).sum := by decide
  have hdescent : baseEnd_77591 < baseStart_77591 := by decide
  rcases family_descends (prefixWord ++ tailWord_77591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77608 : List Nat := [2, 1, 5, 1, 1, 2, 1, 5, 2]
def baseStart_77608 : Nat := 118140960795 + 77608 * 2 ^ 59
def prefixEnd_77608 : Nat := 4983230072969 + 3 ^ 40 * 77608 * 2
def baseEnd_77608 : Nat := 35422405897100081816083

theorem tailTrace_77608 : CollatzResearch.WordTrace tailWord_77608 prefixEnd_77608 35422405897100081816083 := by
  unfold tailWord_77608
  simp only [CollatzResearch.WordTrace]
  refine ⟨1415298151423472618136739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1887064201897963490848985 1415298151423472618136739)
  ·
    refine ⟨2122947227135208927205109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1415298151423472618136739 2122947227135208927205109)
    ·
      refine ⟨199026302543925836925479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2122947227135208927205109 199026302543925836925479)
      ·
        refine ⟨298539453815888755388219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199026302543925836925479 298539453815888755388219)
        ·
          refine ⟨447809180723833133082329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 298539453815888755388219 447809180723833133082329)
          ·
            refine ⟨335856885542874849811747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 447809180723833133082329 335856885542874849811747)
            ·
              refine ⟨503785328314312274717621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 335856885542874849811747 503785328314312274717621)
              ·
                refine ⟨47229874529466775754777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 503785328314312274717621 47229874529466775754777)
                ·
                  refine ⟨35422405897100081816083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47229874529466775754777 35422405897100081816083)
                  ·
                    rfl

theorem cell20_77608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 5, 2].length) (baseStart_77608 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_77608 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_77608 prefixEnd_77608 := by exact prefixLift 77608
  have htrace : WordTrace (prefixWord ++ tailWord_77608) baseStart_77608 baseEnd_77608 := by
    simpa [prefixWord, tailWord_77608, baseEnd_77608] using wordTrace_append hprefix tailTrace_77608
  have hstable : (prefixWord ++ tailWord_77608).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77608).length < 2 ^ (prefixWord ++ tailWord_77608).sum := by decide
  have hdescent : baseEnd_77608 < baseStart_77608 := by decide
  rcases family_descends (prefixWord ++ tailWord_77608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77629 : List Nat := [1, 4, 1, 4, 1, 1, 1, 3, 4]
def baseStart_77629 : Nat := 118140960795 + 77629 * 2 ^ 59
def prefixEnd_77629 : Nat := 4983230072969 + 3 ^ 40 * 77629 * 2
def baseEnd_77629 : Nat := 35431990869317342115997

theorem tailTrace_77629 : CollatzResearch.WordTrace tailWord_77629 prefixEnd_77629 35431990869317342115997 := by
  unfold tailWord_77629
  simp only [CollatzResearch.WordTrace]
  refine ⟨2831362235770865822787941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1887574823847243881858627 2831362235770865822787941)
  ·
    refine ⟨530880419207037341772739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2831362235770865822787941 530880419207037341772739)
    ·
      refine ⟨796320628810556012659109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 530880419207037341772739 796320628810556012659109)
      ·
        refine ⟨149310117901979252373583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 796320628810556012659109 149310117901979252373583)
        ·
          refine ⟨223965176852968878560375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149310117901979252373583 223965176852968878560375)
          ·
            refine ⟨335947765279453317840563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223965176852968878560375 335947765279453317840563)
            ·
              refine ⟨503921647919179976760845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 335947765279453317840563 503921647919179976760845)
              ·
                refine ⟨188970617969692491285317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 503921647919179976760845 188970617969692491285317)
                ·
                  refine ⟨35431990869317342115997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 188970617969692491285317 35431990869317342115997)
                  ·
                    rfl

theorem cell20_77629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_77629 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_77629 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_77629 prefixEnd_77629 := by exact prefixLift 77629
  have htrace : WordTrace (prefixWord ++ tailWord_77629) baseStart_77629 baseEnd_77629 := by
    simpa [prefixWord, tailWord_77629, baseEnd_77629] using wordTrace_append hprefix tailTrace_77629
  have hstable : (prefixWord ++ tailWord_77629).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77629).length < 2 ^ (prefixWord ++ tailWord_77629).sum := by decide
  have hdescent : baseEnd_77629 < baseStart_77629 := by decide
  rcases family_descends (prefixWord ++ tailWord_77629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77653 : List Nat := [1, 3, 2, 2, 2, 4, 2, 4]
def baseStart_77653 : Nat := 118140960795 + 77653 * 2 ^ 59
def prefixEnd_77653 : Nat := 4983230072969 + 3 ^ 40 * 77653 * 2
def baseEnd_77653 : Nat := 11814315041093308438633

theorem tailTrace_77653 : CollatzResearch.WordTrace tailWord_77653 prefixEnd_77653 11814315041093308438633 := by
  unfold tailWord_77653
  simp only [CollatzResearch.WordTrace]
  refine ⟨2832237587683917921661613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1888158391789278614441075 2832237587683917921661613)
  ·
    refine ⟨1062089095381469220623105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2832237587683917921661613 1062089095381469220623105)
    ·
      refine ⟨796566821536101915467329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1062089095381469220623105 796566821536101915467329)
      ·
        refine ⟨597425116152076436600497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 796566821536101915467329 597425116152076436600497)
        ·
          refine ⟨448068837114057327450373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 597425116152076436600497 448068837114057327450373)
          ·
            refine ⟨84012906958885748896945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 448068837114057327450373 84012906958885748896945)
            ·
              refine ⟨63009680219164311672709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84012906958885748896945 63009680219164311672709)
              ·
                refine ⟨11814315041093308438633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63009680219164311672709 11814315041093308438633)
                ·
                  rfl

theorem cell20_77653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 2, 4].length) (baseStart_77653 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_77653 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_77653 prefixEnd_77653 := by exact prefixLift 77653
  have htrace : WordTrace (prefixWord ++ tailWord_77653) baseStart_77653 baseEnd_77653 := by
    simpa [prefixWord, tailWord_77653, baseEnd_77653] using wordTrace_append hprefix tailTrace_77653
  have hstable : (prefixWord ++ tailWord_77653).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77653).length < 2 ^ (prefixWord ++ tailWord_77653).sum := by decide
  have hdescent : baseEnd_77653 < baseStart_77653 := by decide
  rcases family_descends (prefixWord ++ tailWord_77653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77657 : List Nat := [1, 2, 1, 2, 2, 3, 3, 6]
def baseStart_77657 : Nat := 118140960795 + 77657 * 2 ^ 59
def prefixEnd_77657 : Nat := 4983230072969 + 3 ^ 40 * 77657 * 2
def baseEnd_77657 : Nat := 11814923610757896394183

theorem tailTrace_77657 : CollatzResearch.WordTrace tailWord_77657 prefixEnd_77657 11814923610757896394183 := by
  unfold tailWord_77657
  simp only [CollatzResearch.WordTrace]
  refine ⟨2832383479669426604807225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1888255653112951069871483 2832383479669426604807225)
  ·
    refine ⟨2124287609752069953605419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2832383479669426604807225 2124287609752069953605419)
    ·
      refine ⟨3186431414628104930408129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2124287609752069953605419 3186431414628104930408129)
      ·
        refine ⟨2389823560971078697806097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3186431414628104930408129 2389823560971078697806097)
        ·
          refine ⟨1792367670728309023354573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2389823560971078697806097 1792367670728309023354573)
          ·
            refine ⟨672137876523115883757965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1792367670728309023354573 672137876523115883757965)
            ·
              refine ⟨252051703696168456409237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 672137876523115883757965 252051703696168456409237)
              ·
                refine ⟨11814923610757896394183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 252051703696168456409237 11814923610757896394183)
                ·
                  rfl

theorem cell20_77657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 6].length) (baseStart_77657 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_77657 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_77657 prefixEnd_77657 := by exact prefixLift 77657
  have htrace : WordTrace (prefixWord ++ tailWord_77657) baseStart_77657 baseEnd_77657 := by
    simpa [prefixWord, tailWord_77657, baseEnd_77657] using wordTrace_append hprefix tailTrace_77657
  have hstable : (prefixWord ++ tailWord_77657).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77657).length < 2 ^ (prefixWord ++ tailWord_77657).sum := by decide
  have hdescent : baseEnd_77657 < baseStart_77657 := by decide
  rcases family_descends (prefixWord ++ tailWord_77657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77681 : List Nat := [1, 2, 2, 2, 1, 3, 2, 4, 3]
def baseStart_77681 : Nat := 118140960795 + 77681 * 2 ^ 59
def prefixEnd_77681 : Nat := 4983230072969 + 3 ^ 40 * 77681 * 2
def baseEnd_77681 : Nat := 35455725086236272382451

theorem tailTrace_77681 : CollatzResearch.WordTrace tailWord_77681 prefixEnd_77681 35455725086236272382451 := by
  unfold tailWord_77681
  simp only [CollatzResearch.WordTrace]
  refine ⟨2833258831582478703680897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1888839221054985802453931 2833258831582478703680897)
  ·
    refine ⟨2124944123686859027760673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2833258831582478703680897 2124944123686859027760673)
    ·
      refine ⟨1593708092765144270820505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2124944123686859027760673 1593708092765144270820505)
      ·
        refine ⟨1195281069573858203115379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1593708092765144270820505 1195281069573858203115379)
        ·
          refine ⟨1792921604360787304673069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1195281069573858203115379 1792921604360787304673069)
          ·
            refine ⟨672345601635295239252401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1792921604360787304673069 672345601635295239252401)
            ·
              refine ⟨504259201226471429439301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 672345601635295239252401 504259201226471429439301)
              ·
                refine ⟨94548600229963393019869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 504259201226471429439301 94548600229963393019869)
                ·
                  refine ⟨35455725086236272382451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 94548600229963393019869 35455725086236272382451)
                  ·
                    rfl

theorem cell20_77681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 4, 3].length) (baseStart_77681 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_77681 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_77681 prefixEnd_77681 := by exact prefixLift 77681
  have htrace : WordTrace (prefixWord ++ tailWord_77681) baseStart_77681 baseEnd_77681 := by
    simpa [prefixWord, tailWord_77681, baseEnd_77681] using wordTrace_append hprefix tailTrace_77681
  have hstable : (prefixWord ++ tailWord_77681).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77681).length < 2 ^ (prefixWord ++ tailWord_77681).sum := by decide
  have hdescent : baseEnd_77681 < baseStart_77681 := by decide
  rcases family_descends (prefixWord ++ tailWord_77681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77694 : List Nat := [4, 2, 3, 1, 1, 1, 4, 1, 3]
def baseStart_77694 : Nat := 118140960795 + 77694 * 2 ^ 59
def prefixEnd_77694 : Nat := 4983230072969 + 3 ^ 40 * 77694 * 2
def baseEnd_77694 : Nat := 35461658640466004949065

theorem tailTrace_77694 : CollatzResearch.WordTrace tailWord_77694 prefixEnd_77694 35461658640466004949065 := by
  unfold tailWord_77694
  simp only [CollatzResearch.WordTrace]
  refine ⟨354216622566922740488017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1889155320356921282602757 354216622566922740488017)
  ·
    refine ⟨265662466925192055366013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 354216622566922740488017 265662466925192055366013)
    ·
      refine ⟨99623425096947020762255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 265662466925192055366013 99623425096947020762255)
      ·
        refine ⟨149435137645420531143383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99623425096947020762255 149435137645420531143383)
        ·
          refine ⟨224152706468130796715075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149435137645420531143383 224152706468130796715075)
          ·
            refine ⟨336229059702196195072613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224152706468130796715075 336229059702196195072613)
            ·
              refine ⟨63042948694161786576115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 336229059702196195072613 63042948694161786576115)
              ·
                refine ⟨94564423041242679864173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63042948694161786576115 94564423041242679864173)
                ·
                  refine ⟨35461658640466004949065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 94564423041242679864173 35461658640466004949065)
                  ·
                    rfl

theorem cell20_77694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_77694 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_77694 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_77694 prefixEnd_77694 := by exact prefixLift 77694
  have htrace : WordTrace (prefixWord ++ tailWord_77694) baseStart_77694 baseEnd_77694 := by
    simpa [prefixWord, tailWord_77694, baseEnd_77694] using wordTrace_append hprefix tailTrace_77694
  have hstable : (prefixWord ++ tailWord_77694).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77694).length < 2 ^ (prefixWord ++ tailWord_77694).sum := by decide
  have hdescent : baseEnd_77694 < baseStart_77694 := by decide
  rcases family_descends (prefixWord ++ tailWord_77694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77742 : List Nat := [4, 1, 5, 1, 2, 1, 1, 5]
def baseStart_77742 : Nat := 118140960795 + 77742 * 2 ^ 59
def prefixEnd_77742 : Nat := 4983230072969 + 3 ^ 40 * 77742 * 2
def baseEnd_77742 : Nat := 11827855716130390449623

theorem tailTrace_77742 : CollatzResearch.WordTrace tailWord_77742 prefixEnd_77742 11827855716130390449623 := by
  unfold tailWord_77742
  simp only [CollatzResearch.WordTrace]
  refine ⟨354435460545185765206435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1890322456240990747767653 354435460545185765206435)
  ·
    refine ⟨531653190817778647809653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 354435460545185765206435 531653190817778647809653)
    ·
      refine ⟨49842486639166748232155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 531653190817778647809653 49842486639166748232155)
      ·
        refine ⟨74763729958750122348233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49842486639166748232155 74763729958750122348233)
        ·
          refine ⟨56072797469062591761175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74763729958750122348233 56072797469062591761175)
          ·
            refine ⟨84109196203593887641763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56072797469062591761175 84109196203593887641763)
            ·
              refine ⟨126163794305390831462645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84109196203593887641763 126163794305390831462645)
              ·
                refine ⟨11827855716130390449623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 126163794305390831462645 11827855716130390449623)
                ·
                  rfl

theorem cell20_77742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 5].length) (baseStart_77742 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_77742 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_77742 prefixEnd_77742 := by exact prefixLift 77742
  have htrace : WordTrace (prefixWord ++ tailWord_77742) baseStart_77742 baseEnd_77742 := by
    simpa [prefixWord, tailWord_77742, baseEnd_77742] using wordTrace_append hprefix tailTrace_77742
  have hstable : (prefixWord ++ tailWord_77742).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77742).length < 2 ^ (prefixWord ++ tailWord_77742).sum := by decide
  have hdescent : baseEnd_77742 < baseStart_77742 := by decide
  rcases family_descends (prefixWord ++ tailWord_77742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77743 : List Nat := [1, 1, 2, 1, 2, 2, 5, 4, 2]
def baseStart_77743 : Nat := 118140960795 + 77743 * 2 ^ 59
def prefixEnd_77743 : Nat := 4983230072969 + 3 ^ 40 * 77743 * 2
def baseEnd_77743 : Nat := 35484023575639612315531

theorem tailTrace_77743 : CollatzResearch.WordTrace tailWord_77743 prefixEnd_77743 35484023575639612315531 := by
  unfold tailWord_77743
  simp only [CollatzResearch.WordTrace]
  refine ⟨2835520157357863292437883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1890346771571908861625255 2835520157357863292437883)
  ·
    refine ⟨4253280236036794938656825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2835520157357863292437883 4253280236036794938656825)
    ·
      refine ⟨3189960177027596203992619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4253280236036794938656825 3189960177027596203992619)
      ·
        refine ⟨4784940265541394305988929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3189960177027596203992619 4784940265541394305988929)
        ·
          refine ⟨3588705199156045729491697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4784940265541394305988929 3588705199156045729491697)
          ·
            refine ⟨2691528899367034297118773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3588705199156045729491697 2691528899367034297118773)
            ·
              refine ⟨252330834315659465354885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2691528899367034297118773 252330834315659465354885)
              ·
                refine ⟨47312031434186149754041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 252330834315659465354885 47312031434186149754041)
                ·
                  refine ⟨35484023575639612315531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47312031434186149754041 35484023575639612315531)
                  ·
                    rfl

theorem cell20_77743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 4, 2].length) (baseStart_77743 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_77743 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_77743 prefixEnd_77743 := by exact prefixLift 77743
  have htrace : WordTrace (prefixWord ++ tailWord_77743) baseStart_77743 baseEnd_77743 := by
    simpa [prefixWord, tailWord_77743, baseEnd_77743] using wordTrace_append hprefix tailTrace_77743
  have hstable : (prefixWord ++ tailWord_77743).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77743).length < 2 ^ (prefixWord ++ tailWord_77743).sum := by decide
  have hdescent : baseEnd_77743 < baseStart_77743 := by decide
  rcases family_descends (prefixWord ++ tailWord_77743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77795 : List Nat := [1, 1, 1, 6, 1, 3, 1, 1, 5]
def baseStart_77795 : Nat := 118140960795 + 77795 * 2 ^ 59
def prefixEnd_77795 : Nat := 4983230072969 + 3 ^ 40 * 77795 * 2
def baseEnd_77795 : Nat := 35507757792558542581985

theorem tailTrace_77795 : CollatzResearch.WordTrace tailWord_77795 prefixEnd_77795 35507757792558542581985 := by
  unfold tailWord_77795
  simp only [CollatzResearch.WordTrace]
  refine ⟨2837416753169476173330839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1891611168779650782220559 2837416753169476173330839)
  ·
    refine ⟨4256125129754214259996259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2837416753169476173330839 4256125129754214259996259)
    ·
      refine ⟨6384187694631321389994389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4256125129754214259996259 6384187694631321389994389)
      ·
        refine ⟨299258798185843190155987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 6384187694631321389994389 299258798185843190155987)
        ·
          refine ⟨448888197278764785233981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 299258798185843190155987 448888197278764785233981)
          ·
            refine ⟨168333073979536794462743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 448888197278764785233981 168333073979536794462743)
            ·
              refine ⟨252499610969305191694115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 168333073979536794462743 252499610969305191694115)
              ·
                refine ⟨378749416453957787541173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 252499610969305191694115 378749416453957787541173)
                ·
                  refine ⟨35507757792558542581985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 378749416453957787541173 35507757792558542581985)
                  ·
                    rfl

theorem cell20_77795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 1, 5].length) (baseStart_77795 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_77795 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_77795 prefixEnd_77795 := by exact prefixLift 77795
  have htrace : WordTrace (prefixWord ++ tailWord_77795) baseStart_77795 baseEnd_77795 := by
    simpa [prefixWord, tailWord_77795, baseEnd_77795] using wordTrace_append hprefix tailTrace_77795
  have hstable : (prefixWord ++ tailWord_77795).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77795).length < 2 ^ (prefixWord ++ tailWord_77795).sum := by decide
  have hdescent : baseEnd_77795 < baseStart_77795 := by decide
  rcases family_descends (prefixWord ++ tailWord_77795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77822 : List Nat := [4, 2, 2, 2, 1, 3, 2, 4]
def baseStart_77822 : Nat := 118140960795 + 77822 * 2 ^ 59
def prefixEnd_77822 : Nat := 4983230072969 + 3 ^ 40 * 77822 * 2
def baseEnd_77822 : Nat := 11840027109422149560625

theorem tailTrace_77822 : CollatzResearch.WordTrace tailWord_77822 prefixEnd_77822 11840027109422149560625 := by
  unfold tailWord_77822
  simp only [CollatzResearch.WordTrace]
  refine ⟨354800190508957473070465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1892267682714439856375813 354800190508957473070465)
  ·
    refine ⟨266100142881718104802849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 354800190508957473070465 266100142881718104802849)
    ·
      refine ⟨199575107161288578602137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 266100142881718104802849 199575107161288578602137)
      ·
        refine ⟨149681330370966433951603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199575107161288578602137 149681330370966433951603)
        ·
          refine ⟨224521995556449650927405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149681330370966433951603 224521995556449650927405)
          ·
            refine ⟨84195748333668619097777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 224521995556449650927405 84195748333668619097777)
            ·
              refine ⟨63146811250251464323333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84195748333668619097777 63146811250251464323333)
              ·
                refine ⟨11840027109422149560625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63146811250251464323333 11840027109422149560625)
                ·
                  rfl

theorem cell20_77822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 2, 4].length) (baseStart_77822 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_77822 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_77822 prefixEnd_77822 := by exact prefixLift 77822
  have htrace : WordTrace (prefixWord ++ tailWord_77822) baseStart_77822 baseEnd_77822 := by
    simpa [prefixWord, tailWord_77822, baseEnd_77822] using wordTrace_append hprefix tailTrace_77822
  have hstable : (prefixWord ++ tailWord_77822).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77822).length < 2 ^ (prefixWord ++ tailWord_77822).sum := by decide
  have hdescent : baseEnd_77822 < baseStart_77822 := by decide
  rcases family_descends (prefixWord ++ tailWord_77822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77853 : List Nat := [1, 4, 2, 2, 2, 2, 3, 2, 2]
def baseStart_77853 : Nat := 118140960795 + 77853 * 2 ^ 59
def prefixEnd_77853 : Nat := 4983230072969 + 3 ^ 40 * 77853 * 2
def baseEnd_77853 : Nat := 35534230572968118648415

theorem tailTrace_77853 : CollatzResearch.WordTrace tailWord_77853 prefixEnd_77853 35534230572968118648415 := by
  unfold tailWord_77853
  simp only [CollatzResearch.WordTrace]
  refine ⟨2839532186959352078942213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1893021457972901385961475 2839532186959352078942213)
  ·
    refine ⟨532412285054878514801665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2839532186959352078942213 532412285054878514801665)
    ·
      refine ⟨399309213791158886101249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 532412285054878514801665 399309213791158886101249)
      ·
        refine ⟨299481910343369164575937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 399309213791158886101249 299481910343369164575937)
        ·
          refine ⟨224611432757526873431953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 299481910343369164575937 224611432757526873431953)
          ·
            refine ⟨168458574568145155073965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 224611432757526873431953 168458574568145155073965)
            ·
              refine ⟨63171965463054433152737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 168458574568145155073965 63171965463054433152737)
              ·
                refine ⟨47378974097290824864553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63171965463054433152737 47378974097290824864553)
                ·
                  refine ⟨35534230572968118648415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47378974097290824864553 35534230572968118648415)
                  ·
                    rfl

theorem cell20_77853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 3, 2, 2].length) (baseStart_77853 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_77853 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_77853 prefixEnd_77853 := by exact prefixLift 77853
  have htrace : WordTrace (prefixWord ++ tailWord_77853) baseStart_77853 baseEnd_77853 := by
    simpa [prefixWord, tailWord_77853, baseEnd_77853] using wordTrace_append hprefix tailTrace_77853
  have hstable : (prefixWord ++ tailWord_77853).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77853).length < 2 ^ (prefixWord ++ tailWord_77853).sum := by decide
  have hdescent : baseEnd_77853 < baseStart_77853 := by decide
  rcases family_descends (prefixWord ++ tailWord_77853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77863 : List Nat := [1, 1, 7, 1, 3, 1, 2, 1, 3]
def baseStart_77863 : Nat := 118140960795 + 77863 * 2 ^ 59
def prefixEnd_77863 : Nat := 4983230072969 + 3 ^ 40 * 77863 * 2
def baseEnd_77863 : Nat := 35538794845452528315041

theorem tailTrace_77863 : CollatzResearch.WordTrace tailWord_77863 prefixEnd_77863 35538794845452528315041 := by
  unfold tailWord_77863
  simp only [CollatzResearch.WordTrace]
  refine ⟨2839896916923123786806243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1893264611282082524537495 2839896916923123786806243)
  ·
    refine ⟨4259845375384685680209365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2839896916923123786806243 4259845375384685680209365)
    ·
      refine ⟨99840125985578570629907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 4259845375384685680209365 99840125985578570629907)
      ·
        refine ⟨149760188978367855944861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99840125985578570629907 149760188978367855944861)
        ·
          refine ⟨56160070866887945979323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 149760188978367855944861 56160070866887945979323)
          ·
            refine ⟨84240106300331918968985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56160070866887945979323 84240106300331918968985)
            ·
              refine ⟨63180079725248939226739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84240106300331918968985 63180079725248939226739)
              ·
                refine ⟨94770119587873408840109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63180079725248939226739 94770119587873408840109)
                ·
                  refine ⟨35538794845452528315041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 94770119587873408840109 35538794845452528315041)
                  ·
                    rfl

theorem cell20_77863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 2, 1, 3].length) (baseStart_77863 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_77863 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_77863 prefixEnd_77863 := by exact prefixLift 77863
  have htrace : WordTrace (prefixWord ++ tailWord_77863) baseStart_77863 baseEnd_77863 := by
    simpa [prefixWord, tailWord_77863, baseEnd_77863] using wordTrace_append hprefix tailTrace_77863
  have hstable : (prefixWord ++ tailWord_77863).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77863).length < 2 ^ (prefixWord ++ tailWord_77863).sum := by decide
  have hdescent : baseEnd_77863 < baseStart_77863 := by decide
  rcases family_descends (prefixWord ++ tailWord_77863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77885 : List Nat := [1, 4, 1, 3, 1, 1, 1, 8]
def baseStart_77885 : Nat := 118140960795 + 77885 * 2 ^ 59
def prefixEnd_77885 : Nat := 4983230072969 + 3 ^ 40 * 77885 * 2
def baseEnd_77885 : Nat := 11849612081639409860539

theorem tailTrace_77885 : CollatzResearch.WordTrace tailWord_77885 prefixEnd_77885 11849612081639409860539 := by
  unfold tailWord_77885
  simp only [CollatzResearch.WordTrace]
  refine ⟨2840699322843421544107109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1893799548562281029404739 2840699322843421544107109)
  ·
    refine ⟨532631123033141539520083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2840699322843421544107109 532631123033141539520083)
    ·
      refine ⟨798946684549712309280125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 532631123033141539520083 798946684549712309280125)
      ·
        refine ⟨299605006706142115980047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 798946684549712309280125 299605006706142115980047)
        ·
          refine ⟨449407510059213173970071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 299605006706142115980047 449407510059213173970071)
          ·
            refine ⟨674111265088819760955107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 449407510059213173970071 674111265088819760955107)
            ·
              refine ⟨1011166897633229641432661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 674111265088819760955107 1011166897633229641432661)
              ·
                refine ⟨11849612081639409860539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1011166897633229641432661 11849612081639409860539)
                ·
                  rfl

theorem cell20_77885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 8].length) (baseStart_77885 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_77885 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_77885 prefixEnd_77885 := by exact prefixLift 77885
  have htrace : WordTrace (prefixWord ++ tailWord_77885) baseStart_77885 baseEnd_77885 := by
    simpa [prefixWord, tailWord_77885, baseEnd_77885] using wordTrace_append hprefix tailTrace_77885
  have hstable : (prefixWord ++ tailWord_77885).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77885).length < 2 ^ (prefixWord ++ tailWord_77885).sum := by decide
  have hdescent : baseEnd_77885 < baseStart_77885 := by decide
  rcases family_descends (prefixWord ++ tailWord_77885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77895 : List Nat := [1, 1, 4, 1, 3, 1, 2, 5, 2]
def baseStart_77895 : Nat := 118140960795 + 77895 * 2 ^ 59
def prefixEnd_77895 : Nat := 4983230072969 + 3 ^ 40 * 77895 * 2
def baseEnd_77895 : Nat := 35553400517402639248243

theorem tailTrace_77895 : CollatzResearch.WordTrace tailWord_77895 prefixEnd_77895 35553400517402639248243 := by
  unfold tailWord_77895
  simp only [CollatzResearch.WordTrace]
  refine ⟨2841064052807193251971139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1894042701871462167980759 2841064052807193251971139)
  ·
    refine ⟨4261596079210789877956709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2841064052807193251971139 4261596079210789877956709)
    ·
      refine ⟨799049264852023102116883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4261596079210789877956709 799049264852023102116883)
      ·
        refine ⟨1198573897278034653175325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 799049264852023102116883 1198573897278034653175325)
        ·
          refine ⟨449465211479262994940747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1198573897278034653175325 449465211479262994940747)
          ·
            refine ⟨674197817218894492411121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 449465211479262994940747 674197817218894492411121)
            ·
              refine ⟨505648362914170869308341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 674197817218894492411121 505648362914170869308341)
              ·
                refine ⟨47404534023203518997657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 505648362914170869308341 47404534023203518997657)
                ·
                  refine ⟨35553400517402639248243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47404534023203518997657 35553400517402639248243)
                  ·
                    rfl

theorem cell20_77895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 5, 2].length) (baseStart_77895 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_77895 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_77895 prefixEnd_77895 := by exact prefixLift 77895
  have htrace : WordTrace (prefixWord ++ tailWord_77895) baseStart_77895 baseEnd_77895 := by
    simpa [prefixWord, tailWord_77895, baseEnd_77895] using wordTrace_append hprefix tailTrace_77895
  have hstable : (prefixWord ++ tailWord_77895).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77895).length < 2 ^ (prefixWord ++ tailWord_77895).sum := by decide
  have hdescent : baseEnd_77895 < baseStart_77895 := by decide
  rcases family_descends (prefixWord ++ tailWord_77895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77899 : List Nat := [1, 1, 1, 1, 3, 1, 2, 4, 6]
def baseStart_77899 : Nat := 118140960795 + 77899 * 2 ^ 59
def prefixEnd_77899 : Nat := 4983230072969 + 3 ^ 40 * 77899 * 2
def baseEnd_77899 : Nat := 35555226226396403114893

theorem tailTrace_77899 : CollatzResearch.WordTrace tailWord_77899 prefixEnd_77899 35555226226396403114893 := by
  unfold tailWord_77899
  simp only [CollatzResearch.WordTrace]
  refine ⟨2841209944792701935116751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1894139963195134623411167 2841209944792701935116751)
  ·
    refine ⟨4261814917189052902675127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2841209944792701935116751 4261814917189052902675127)
    ·
      refine ⟨6392722375783579354012691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4261814917189052902675127 6392722375783579354012691)
      ·
        refine ⟨9589083563675369031019037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6392722375783579354012691 9589083563675369031019037)
        ·
          refine ⟨3595906336378263386632139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9589083563675369031019037 3595906336378263386632139)
          ·
            refine ⟨5393859504567395079948209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3595906336378263386632139 5393859504567395079948209)
            ·
              refine ⟨4045394628425546309961157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5393859504567395079948209 4045394628425546309961157)
              ·
                refine ⟨758511492829789933117717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4045394628425546309961157 758511492829789933117717)
                ·
                  refine ⟨35555226226396403114893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 758511492829789933117717 35555226226396403114893)
                  ·
                    rfl

theorem cell20_77899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 6].length) (baseStart_77899 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_77899 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_77899 prefixEnd_77899 := by exact prefixLift 77899
  have htrace : WordTrace (prefixWord ++ tailWord_77899) baseStart_77899 baseEnd_77899 := by
    simpa [prefixWord, tailWord_77899, baseEnd_77899] using wordTrace_append hprefix tailTrace_77899
  have hstable : (prefixWord ++ tailWord_77899).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77899).length < 2 ^ (prefixWord ++ tailWord_77899).sum := by decide
  have hdescent : baseEnd_77899 < baseStart_77899 := by decide
  rcases family_descends (prefixWord ++ tailWord_77899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77909 : List Nat := [1, 3, 2, 2, 1, 3, 1, 4, 3]
def baseStart_77909 : Nat := 118140960795 + 77909 * 2 ^ 59
def prefixEnd_77909 : Nat := 4983230072969 + 3 ^ 40 * 77909 * 2
def baseEnd_77909 : Nat := 35559790498880812781519

theorem tailTrace_77909 : CollatzResearch.WordTrace tailWord_77909 prefixEnd_77909 35559790498880812781519 := by
  unfold tailWord_77909
  simp only [CollatzResearch.WordTrace]
  refine ⟨2841574674756473642980781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1894383116504315761987187 2841574674756473642980781)
  ·
    refine ⟨1065590503033677616117793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2841574674756473642980781 1065590503033677616117793)
    ·
      refine ⟨799192877275258212088345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1065590503033677616117793 799192877275258212088345)
      ·
        refine ⟨599394657956443659066259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 799192877275258212088345 599394657956443659066259)
        ·
          refine ⟨899091986934665488599389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 599394657956443659066259 899091986934665488599389)
          ·
            refine ⟨337159495100499558224771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 899091986934665488599389 337159495100499558224771)
            ·
              refine ⟨505739242650749337337157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 337159495100499558224771 505739242650749337337157)
              ·
                refine ⟨94826107997015500750717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 505739242650749337337157 94826107997015500750717)
                ·
                  refine ⟨35559790498880812781519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 94826107997015500750717 35559790498880812781519)
                  ·
                    rfl

theorem cell20_77909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 4, 3].length) (baseStart_77909 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_77909 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_77909 prefixEnd_77909 := by exact prefixLift 77909
  have htrace : WordTrace (prefixWord ++ tailWord_77909) baseStart_77909 baseEnd_77909 := by
    simpa [prefixWord, tailWord_77909, baseEnd_77909] using wordTrace_append hprefix tailTrace_77909
  have hstable : (prefixWord ++ tailWord_77909).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77909).length < 2 ^ (prefixWord ++ tailWord_77909).sum := by decide
  have hdescent : baseEnd_77909 < baseStart_77909 := by decide
  rcases family_descends (prefixWord ++ tailWord_77909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77912 : List Nat := [2, 1, 2, 2, 1, 4, 4, 2, 2]
def baseStart_77912 : Nat := 118140960795 + 77912 * 2 ^ 59
def prefixEnd_77912 : Nat := 4983230072969 + 3 ^ 40 * 77912 * 2
def baseEnd_77912 : Nat := 35561159780626135681507

theorem tailTrace_77912 : CollatzResearch.WordTrace tailWord_77912 prefixEnd_77912 35561159780626135681507 := by
  unfold tailWord_77912
  simp only [CollatzResearch.WordTrace]
  refine ⟨1420842046872802577669995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1894456062497070103559993 1420842046872802577669995)
  ·
    refine ⟨2131263070309203866504993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1420842046872802577669995 2131263070309203866504993)
    ·
      refine ⟨1598447302731902899878745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2131263070309203866504993 1598447302731902899878745)
      ·
        refine ⟨1198835477048927174909059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1598447302731902899878745 1198835477048927174909059)
        ·
          refine ⟨1798253215573390762363589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1198835477048927174909059 1798253215573390762363589)
          ·
            refine ⟨337172477920010767943173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1798253215573390762363589 337172477920010767943173)
            ·
              refine ⟨63219839610002018989345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 337172477920010767943173 63219839610002018989345)
              ·
                refine ⟨47414879707501514242009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63219839610002018989345 47414879707501514242009)
                ·
                  refine ⟨35561159780626135681507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47414879707501514242009 35561159780626135681507)
                  ·
                    rfl

theorem cell20_77912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 4, 2, 2].length) (baseStart_77912 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_77912 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_77912 prefixEnd_77912 := by exact prefixLift 77912
  have htrace : WordTrace (prefixWord ++ tailWord_77912) baseStart_77912 baseEnd_77912 := by
    simpa [prefixWord, tailWord_77912, baseEnd_77912] using wordTrace_append hprefix tailTrace_77912
  have hstable : (prefixWord ++ tailWord_77912).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77912).length < 2 ^ (prefixWord ++ tailWord_77912).sum := by decide
  have hdescent : baseEnd_77912 < baseStart_77912 := by decide
  rcases family_descends (prefixWord ++ tailWord_77912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77923 : List Nat := [1, 1, 1, 5, 1, 1, 5, 5]
def baseStart_77923 : Nat := 118140960795 + 77923 * 2 ^ 59
def prefixEnd_77923 : Nat := 4983230072969 + 3 ^ 40 * 77923 * 2
def baseEnd_77923 : Nat := 11855393493452995438265

theorem tailTrace_77923 : CollatzResearch.WordTrace tailWord_77923 prefixEnd_77923 11855393493452995438265 := by
  unfold tailWord_77923
  simp only [CollatzResearch.WordTrace]
  refine ⟨2842085296705754033990423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1894723531137169355993615 2842085296705754033990423)
  ·
    refine ⟨4263127945058631050985635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2842085296705754033990423 4263127945058631050985635)
    ·
      refine ⟨6394691917587946576478453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4263127945058631050985635 6394691917587946576478453)
      ·
        refine ⟨599502367273869991544855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6394691917587946576478453 599502367273869991544855)
        ·
          refine ⟨899253550910804987317283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 599502367273869991544855 899253550910804987317283)
          ·
            refine ⟨1348880326366207480975925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 899253550910804987317283 1348880326366207480975925)
            ·
              refine ⟨126457530596831951341493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1348880326366207480975925 126457530596831951341493)
              ·
                refine ⟨11855393493452995438265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 126457530596831951341493 11855393493452995438265)
                ·
                  rfl

theorem cell20_77923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 5].length) (baseStart_77923 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_77923 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_77923 prefixEnd_77923 := by exact prefixLift 77923
  have htrace : WordTrace (prefixWord ++ tailWord_77923) baseStart_77923 baseEnd_77923 := by
    simpa [prefixWord, tailWord_77923, baseEnd_77923] using wordTrace_append hprefix tailTrace_77923
  have hstable : (prefixWord ++ tailWord_77923).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77923).length < 2 ^ (prefixWord ++ tailWord_77923).sum := by decide
  have hdescent : baseEnd_77923 < baseStart_77923 := by decide
  rcases family_descends (prefixWord ++ tailWord_77923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77968 : List Nat := [2, 1, 1, 1, 1, 1, 7, 1, 5]
def baseStart_77968 : Nat := 118140960795 + 77968 * 2 ^ 59
def prefixEnd_77968 : Nat := 4983230072969 + 3 ^ 40 * 77968 * 2
def baseEnd_77968 : Nat := 35586719706538829814611

theorem tailTrace_77968 : CollatzResearch.WordTrace tailWord_77968 prefixEnd_77968 35586719706538829814611 := by
  unfold tailWord_77968
  simp only [CollatzResearch.WordTrace]
  refine ⟨1421863290771363359689279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1895817721028484479585705 1421863290771363359689279)
  ·
    refine ⟨2132794936157045039533919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1421863290771363359689279 2132794936157045039533919)
    ·
      refine ⟨3199192404235567559300879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2132794936157045039533919 3199192404235567559300879)
      ·
        refine ⟨4798788606353351338951319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3199192404235567559300879 4798788606353351338951319)
        ·
          refine ⟨7198182909530027008426979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4798788606353351338951319 7198182909530027008426979)
          ·
            refine ⟨10797274364295040512640469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7198182909530027008426979 10797274364295040512640469)
            ·
              refine ⟨253061117913165012015011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 10797274364295040512640469 253061117913165012015011)
              ·
                refine ⟨379591676869747518022517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 253061117913165012015011 379591676869747518022517)
                ·
                  refine ⟨35586719706538829814611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 379591676869747518022517 35586719706538829814611)
                  ·
                    rfl

theorem cell20_77968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 1, 5].length) (baseStart_77968 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_77968 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_77968 prefixEnd_77968 := by exact prefixLift 77968
  have htrace : WordTrace (prefixWord ++ tailWord_77968) baseStart_77968 baseEnd_77968 := by
    simpa [prefixWord, tailWord_77968, baseEnd_77968] using wordTrace_append hprefix tailTrace_77968
  have hstable : (prefixWord ++ tailWord_77968).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77968).length < 2 ^ (prefixWord ++ tailWord_77968).sum := by decide
  have hdescent : baseEnd_77968 < baseStart_77968 := by decide
  rcases family_descends (prefixWord ++ tailWord_77968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78026 : List Nat := [3, 1, 2, 1, 3, 1, 5, 2, 2]
def baseStart_78026 : Nat := 118140960795 + 78026 * 2 ^ 59
def prefixEnd_78026 : Nat := 4983230072969 + 3 ^ 40 * 78026 * 2
def baseEnd_78026 : Nat := 35613192486948405881041

theorem tailTrace_78026 : CollatzResearch.WordTrace tailWord_78026 prefixEnd_78026 35613192486948405881041 := by
  unfold tailWord_78026
  simp only [CollatzResearch.WordTrace]
  refine ⟨711460503833150656247483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1897228010221735083326621 711460503833150656247483)
  ·
    refine ⟨1067190755749725984371225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 711460503833150656247483 1067190755749725984371225)
    ·
      refine ⟨800393066812294488278419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1067190755749725984371225 800393066812294488278419)
      ·
        refine ⟨1200589600218441732417629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 800393066812294488278419 1200589600218441732417629)
        ·
          refine ⟨450221100081915649656611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1200589600218441732417629 450221100081915649656611)
          ·
            refine ⟨675331650122873474484917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 450221100081915649656611 675331650122873474484917)
            ·
              refine ⟨63312342199019388232961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 675331650122873474484917 63312342199019388232961)
              ·
                refine ⟨47484256649264541174721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63312342199019388232961 47484256649264541174721)
                ·
                  refine ⟨35613192486948405881041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47484256649264541174721 35613192486948405881041)
                  ·
                    rfl

theorem cell20_78026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 5, 2, 2].length) (baseStart_78026 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_78026 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_78026 prefixEnd_78026 := by exact prefixLift 78026
  have htrace : WordTrace (prefixWord ++ tailWord_78026) baseStart_78026 baseEnd_78026 := by
    simpa [prefixWord, tailWord_78026, baseEnd_78026] using wordTrace_append hprefix tailTrace_78026
  have hstable : (prefixWord ++ tailWord_78026).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78026).length < 2 ^ (prefixWord ++ tailWord_78026).sum := by decide
  have hdescent : baseEnd_78026 < baseStart_78026 := by decide
  rcases family_descends (prefixWord ++ tailWord_78026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78040 : List Nat := [2, 1, 2, 2, 4, 1, 4, 1, 3]
def baseStart_78040 : Nat := 118140960795 + 78040 * 2 ^ 59
def prefixEnd_78040 : Nat := 4983230072969 + 3 ^ 40 * 78040 * 2
def baseEnd_78040 : Nat := 35619582468426579414317

theorem tailTrace_78040 : CollatzResearch.WordTrace tailWord_78040 prefixEnd_78040 35619582468426579414317 := by
  unfold tailWord_78040
  simp only [CollatzResearch.WordTrace]
  refine ⟨1423176318640941507999787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1897568424854588677333049 1423176318640941507999787)
  ·
    refine ⟨2134764477961412261999681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1423176318640941507999787 2134764477961412261999681)
    ·
      refine ⟨1601073358471059196499761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2134764477961412261999681 1601073358471059196499761)
      ·
        refine ⟨1200805018853294397374821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1601073358471059196499761 1200805018853294397374821)
        ·
          refine ⟨225150941034992699507779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1200805018853294397374821 225150941034992699507779)
          ·
            refine ⟨337726411552489049261669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225150941034992699507779 337726411552489049261669)
            ·
              refine ⟨63323702166091696736563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 337726411552489049261669 63323702166091696736563)
              ·
                refine ⟨94985553249137545104845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63323702166091696736563 94985553249137545104845)
                ·
                  refine ⟨35619582468426579414317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 94985553249137545104845 35619582468426579414317)
                  ·
                    rfl

theorem cell20_78040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 4, 1, 3].length) (baseStart_78040 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_78040 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_78040 prefixEnd_78040 := by exact prefixLift 78040
  have htrace : WordTrace (prefixWord ++ tailWord_78040) baseStart_78040 baseEnd_78040 := by
    simpa [prefixWord, tailWord_78040, baseEnd_78040] using wordTrace_append hprefix tailTrace_78040
  have hstable : (prefixWord ++ tailWord_78040).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78040).length < 2 ^ (prefixWord ++ tailWord_78040).sum := by decide
  have hdescent : baseEnd_78040 < baseStart_78040 := by decide
  rcases family_descends (prefixWord ++ tailWord_78040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78078 : List Nat := [4, 2, 2, 1, 1, 1, 4, 2, 3]
def baseStart_78078 : Nat := 118140960795 + 78078 * 2 ^ 59
def prefixEnd_78078 : Nat := 4983230072969 + 3 ^ 40 * 78078 * 2
def baseEnd_78078 : Nat := 35636926703867336147495

theorem tailTrace_78078 : CollatzResearch.WordTrace tailWord_78078 prefixEnd_78078 35636926703867336147495 := by
  unfold tailWord_78078
  simp only [CollatzResearch.WordTrace]
  refine ⟨355967326393026938235361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1898492407429477003921925 355967326393026938235361)
  ·
    refine ⟨266975494794770203676521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 355967326393026938235361 266975494794770203676521)
    ·
      refine ⟨200231621096077652757391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 266975494794770203676521 200231621096077652757391)
      ·
        refine ⟨300347431644116479136087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200231621096077652757391 300347431644116479136087)
        ·
          refine ⟨450521147466174718704131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 300347431644116479136087 450521147466174718704131)
          ·
            refine ⟨675781721199262078056197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 450521147466174718704131 675781721199262078056197)
            ·
              refine ⟨126709072724861639635537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 675781721199262078056197 126709072724861639635537)
              ·
                refine ⟨95031804543646229726653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 126709072724861639635537 95031804543646229726653)
                ·
                  refine ⟨35636926703867336147495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 95031804543646229726653 35636926703867336147495)
                  ·
                    rfl

theorem cell20_78078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_78078 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_78078 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_78078 prefixEnd_78078 := by exact prefixLift 78078
  have htrace : WordTrace (prefixWord ++ tailWord_78078) baseStart_78078 baseEnd_78078 := by
    simpa [prefixWord, tailWord_78078, baseEnd_78078] using wordTrace_append hprefix tailTrace_78078
  have hstable : (prefixWord ++ tailWord_78078).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78078).length < 2 ^ (prefixWord ++ tailWord_78078).sum := by decide
  have hdescent : baseEnd_78078 < baseStart_78078 := by decide
  rcases family_descends (prefixWord ++ tailWord_78078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78109 : List Nat := [1, 4, 2, 3, 2, 1, 3, 4]
def baseStart_78109 : Nat := 118140960795 + 78109 * 2 ^ 59
def prefixEnd_78109 : Nat := 4983230072969 + 3 ^ 40 * 78109 * 2
def baseEnd_78109 : Nat := 11883691982856335371345

theorem tailTrace_78109 : CollatzResearch.WordTrace tailWord_78109 prefixEnd_78109 11883691982856335371345 := by
  unfold tailWord_78109
  simp only [CollatzResearch.WordTrace]
  refine ⟨2848869274031907800261381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1899246182687938533507587 2848869274031907800261381)
  ·
    refine ⟨534162988880982712549009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2848869274031907800261381 534162988880982712549009)
    ·
      refine ⟨400622241660737034411757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 534162988880982712549009 400622241660737034411757)
      ·
        refine ⟨150233340622776387904409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 400622241660737034411757 150233340622776387904409)
        ·
          refine ⟨112675005467082290928307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150233340622776387904409 112675005467082290928307)
          ·
            refine ⟨169012508200623436392461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112675005467082290928307 169012508200623436392461)
            ·
              refine ⟨63379690575233788647173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 169012508200623436392461 63379690575233788647173)
              ·
                refine ⟨11883691982856335371345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63379690575233788647173 11883691982856335371345)
                ·
                  rfl

theorem cell20_78109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 3, 4].length) (baseStart_78109 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_78109 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_78109 prefixEnd_78109 := by exact prefixLift 78109
  have htrace : WordTrace (prefixWord ++ tailWord_78109) baseStart_78109 baseEnd_78109 := by
    simpa [prefixWord, tailWord_78109, baseEnd_78109] using wordTrace_append hprefix tailTrace_78109
  have hstable : (prefixWord ++ tailWord_78109).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78109).length < 2 ^ (prefixWord ++ tailWord_78109).sum := by decide
  have hdescent : baseEnd_78109 < baseStart_78109 := by decide
  rcases family_descends (prefixWord ++ tailWord_78109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78137 : List Nat := [1, 2, 1, 6, 1, 2, 1, 1, 5]
def baseStart_78137 : Nat := 118140960795 + 78137 * 2 ^ 59
def prefixEnd_78137 : Nat := 4983230072969 + 3 ^ 40 * 78137 * 2
def baseEnd_78137 : Nat := 35663855911525353180587

theorem tailTrace_78137 : CollatzResearch.WordTrace tailWord_78137 prefixEnd_78137 35663855911525353180587 := by
  unfold tailWord_78137
  simp only [CollatzResearch.WordTrace]
  refine ⟨2849890517930468582280665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1899927011953645721520443 2849890517930468582280665)
  ·
    refine ⟨2137417888447851436710499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2849890517930468582280665 2137417888447851436710499)
    ·
      refine ⟨3206126832671777155065749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2137417888447851436710499 3206126832671777155065749)
      ·
        refine ⟨150287195281489554143707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 3206126832671777155065749 150287195281489554143707)
        ·
          refine ⟨225430792922234331215561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150287195281489554143707 225430792922234331215561)
          ·
            refine ⟨169073094691675748411671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 225430792922234331215561 169073094691675748411671)
            ·
              refine ⟨253609642037513622617507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 169073094691675748411671 253609642037513622617507)
              ·
                refine ⟨380414463056270433926261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 253609642037513622617507 380414463056270433926261)
                ·
                  refine ⟨35663855911525353180587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 380414463056270433926261 35663855911525353180587)
                  ·
                    rfl

theorem cell20_78137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 1, 5].length) (baseStart_78137 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_78137 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_78137 prefixEnd_78137 := by exact prefixLift 78137
  have htrace : WordTrace (prefixWord ++ tailWord_78137) baseStart_78137 baseEnd_78137 := by
    simpa [prefixWord, tailWord_78137, baseEnd_78137] using wordTrace_append hprefix tailTrace_78137
  have hstable : (prefixWord ++ tailWord_78137).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78137).length < 2 ^ (prefixWord ++ tailWord_78137).sum := by decide
  have hdescent : baseEnd_78137 < baseStart_78137 := by decide
  rcases family_descends (prefixWord ++ tailWord_78137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78178 : List Nat := [3, 3, 2, 1, 1, 2, 3, 3, 2]
def baseStart_78178 : Nat := 118140960795 + 78178 * 2 ^ 59
def prefixEnd_78178 : Nat := 4983230072969 + 3 ^ 40 * 78178 * 2
def baseEnd_78178 : Nat := 35682569428711432813753

theorem tailTrace_78178 : CollatzResearch.WordTrace tailWord_78178 prefixEnd_78178 35682569428711432813753 := by
  unfold tailWord_78178
  simp only [CollatzResearch.WordTrace]
  refine ⟨712846477695483146130797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1900923940521288389682125 712846477695483146130797)
  ·
    refine ⟨267317429135806179799049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 712846477695483146130797 267317429135806179799049)
    ·
      refine ⟨200488071851854634849287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 267317429135806179799049 200488071851854634849287)
      ·
        refine ⟨300732107777781952273931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200488071851854634849287 300732107777781952273931)
        ·
          refine ⟨451098161666672928410897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 300732107777781952273931 451098161666672928410897)
          ·
            refine ⟨338323621250004696308173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 451098161666672928410897 338323621250004696308173)
            ·
              refine ⟨126871357968751761115565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 338323621250004696308173 126871357968751761115565)
              ·
                refine ⟨47576759238281910418337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 126871357968751761115565 47576759238281910418337)
                ·
                  refine ⟨35682569428711432813753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47576759238281910418337 35682569428711432813753)
                  ·
                    rfl

theorem cell20_78178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 3, 2].length) (baseStart_78178 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_78178 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_78178 prefixEnd_78178 := by exact prefixLift 78178
  have htrace : WordTrace (prefixWord ++ tailWord_78178) baseStart_78178 baseEnd_78178 := by
    simpa [prefixWord, tailWord_78178, baseEnd_78178] using wordTrace_append hprefix tailTrace_78178
  have hstable : (prefixWord ++ tailWord_78178).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78178).length < 2 ^ (prefixWord ++ tailWord_78178).sum := by decide
  have hdescent : baseEnd_78178 < baseStart_78178 := by decide
  rcases family_descends (prefixWord ++ tailWord_78178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78209 : List Nat := [1, 2, 4, 3, 1, 3, 2, 1, 3]
def baseStart_78209 : Nat := 118140960795 + 78209 * 2 ^ 59
def prefixEnd_78209 : Nat := 4983230072969 + 3 ^ 40 * 78209 * 2
def baseEnd_78209 : Nat := 35696718673413102780293

theorem tailTrace_78209 : CollatzResearch.WordTrace tailWord_78209 prefixEnd_78209 35696718673413102780293 := by
  unfold tailWord_78209
  simp only [CollatzResearch.WordTrace]
  refine ⟨2852516573669624878901681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1901677715779749919267787 2852516573669624878901681)
  ·
    refine ⟨2139387430252218659176261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2852516573669624878901681 2139387430252218659176261)
    ·
      refine ⟨401135143172290998595549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2139387430252218659176261 401135143172290998595549)
      ·
        refine ⟨150425678689609124473331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 401135143172290998595549 150425678689609124473331)
        ·
          refine ⟨225638518034413686709997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150425678689609124473331 225638518034413686709997)
          ·
            refine ⟨84614444262905132516249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 225638518034413686709997 84614444262905132516249)
            ·
              refine ⟨63460833197178849387187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84614444262905132516249 63460833197178849387187)
              ·
                refine ⟨95191249795768274080781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63460833197178849387187 95191249795768274080781)
                ·
                  refine ⟨35696718673413102780293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 95191249795768274080781 35696718673413102780293)
                  ·
                    rfl

theorem cell20_78209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 2, 1, 3].length) (baseStart_78209 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_78209 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_78209 prefixEnd_78209 := by exact prefixLift 78209
  have htrace : WordTrace (prefixWord ++ tailWord_78209) baseStart_78209 baseEnd_78209 := by
    simpa [prefixWord, tailWord_78209, baseEnd_78209] using wordTrace_append hprefix tailTrace_78209
  have hstable : (prefixWord ++ tailWord_78209).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78209).length < 2 ^ (prefixWord ++ tailWord_78209).sum := by decide
  have hdescent : baseEnd_78209 < baseStart_78209 := by decide
  rcases family_descends (prefixWord ++ tailWord_78209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78250 : List Nat := [3, 1, 6, 1, 1, 1, 1, 4, 2]
def baseStart_78250 : Nat := 118140960795 + 78250 * 2 ^ 59
def prefixEnd_78250 : Nat := 4983230072969 + 3 ^ 40 * 78250 * 2
def baseEnd_78250 : Nat := 35715432190599182413459

theorem tailTrace_78250 : CollatzResearch.WordTrace tailWord_78250 prefixEnd_78250 35715432190599182413459 := by
  unfold tailWord_78250
  simp only [CollatzResearch.WordTrace]
  refine ⟨713502991630272220286051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1902674644347392587429469 713502991630272220286051)
  ·
    refine ⟨1070254487445408330429077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 713502991630272220286051 1070254487445408330429077)
    ·
      refine ⟨50168179099003515488863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1070254487445408330429077 50168179099003515488863)
      ·
        refine ⟨75252268648505273233295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50168179099003515488863 75252268648505273233295)
        ·
          refine ⟨112878402972757909849943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75252268648505273233295 112878402972757909849943)
          ·
            refine ⟨169317604459136864774915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112878402972757909849943 169317604459136864774915)
            ·
              refine ⟨253976406688705297162373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 169317604459136864774915 253976406688705297162373)
              ·
                refine ⟨47620576254132243217945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 253976406688705297162373 47620576254132243217945)
                ·
                  refine ⟨35715432190599182413459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47620576254132243217945 35715432190599182413459)
                  ·
                    rfl

theorem cell20_78250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 4, 2].length) (baseStart_78250 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_78250 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_78250 prefixEnd_78250 := by exact prefixLift 78250
  have htrace : WordTrace (prefixWord ++ tailWord_78250) baseStart_78250 baseEnd_78250 := by
    simpa [prefixWord, tailWord_78250, baseEnd_78250] using wordTrace_append hprefix tailTrace_78250
  have hstable : (prefixWord ++ tailWord_78250).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78250).length < 2 ^ (prefixWord ++ tailWord_78250).sum := by decide
  have hdescent : baseEnd_78250 < baseStart_78250 := by decide
  rcases family_descends (prefixWord ++ tailWord_78250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78261 : List Nat := [1, 3, 3, 2, 4, 1, 1, 5]
def baseStart_78261 : Nat := 118140960795 + 78261 * 2 ^ 59
def prefixEnd_78261 : Nat := 4983230072969 + 3 ^ 40 * 78261 * 2
def baseEnd_78261 : Nat := 11906817630110677682249

theorem tailTrace_78261 : CollatzResearch.WordTrace tailWord_78261 prefixEnd_78261 11906817630110677682249 := by
  unfold tailWord_78261
  simp only [CollatzResearch.WordTrace]
  refine ⟨2854413169481237759794637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1902942112987491839863091 2854413169481237759794637)
  ·
    refine ⟨1070404938555464159922989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2854413169481237759794637 1070404938555464159922989)
    ·
      refine ⟨401401851958299059971121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1070404938555464159922989 401401851958299059971121)
      ·
        refine ⟨301051388968724294978341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 401401851958299059971121 301051388968724294978341)
        ·
          refine ⟨56447135431635805308439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 301051388968724294978341 56447135431635805308439)
          ·
            refine ⟨84670703147453707962659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56447135431635805308439 84670703147453707962659)
            ·
              refine ⟨127006054721180561943989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84670703147453707962659 127006054721180561943989)
              ·
                refine ⟨11906817630110677682249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 127006054721180561943989 11906817630110677682249)
                ·
                  rfl

theorem cell20_78261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 5].length) (baseStart_78261 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_78261 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_78261 prefixEnd_78261 := by exact prefixLift 78261
  have htrace : WordTrace (prefixWord ++ tailWord_78261) baseStart_78261 baseEnd_78261 := by
    simpa [prefixWord, tailWord_78261, baseEnd_78261] using wordTrace_append hprefix tailTrace_78261
  have hstable : (prefixWord ++ tailWord_78261).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78261).length < 2 ^ (prefixWord ++ tailWord_78261).sum := by decide
  have hdescent : baseEnd_78261 < baseStart_78261 := by decide
  rcases family_descends (prefixWord ++ tailWord_78261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78265 : List Nat := [1, 2, 1, 4, 3, 1, 3, 5]
def baseStart_78265 : Nat := 118140960795 + 78265 * 2 ^ 59
def prefixEnd_78265 : Nat := 4983230072969 + 3 ^ 40 * 78265 * 2
def baseEnd_78265 : Nat := 11907426199775265637799

theorem tailTrace_78265 : CollatzResearch.WordTrace tailWord_78265 prefixEnd_78265 11907426199775265637799 := by
  unfold tailWord_78265
  simp only [CollatzResearch.WordTrace]
  refine ⟨2854559061466746442940249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1903039374311164295293499 2854559061466746442940249)
  ·
    refine ⟨2140919296100059832205187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2854559061466746442940249 2140919296100059832205187)
    ·
      refine ⟨3211378944150089748307781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2140919296100059832205187 3211378944150089748307781)
      ·
        refine ⟨602133552028141827807709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3211378944150089748307781 602133552028141827807709)
        ·
          refine ⟨225800082010553185427891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 602133552028141827807709 225800082010553185427891)
          ·
            refine ⟨338700123015829778141837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225800082010553185427891 338700123015829778141837)
            ·
              refine ⟨127012546130936166803189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 338700123015829778141837 127012546130936166803189)
              ·
                refine ⟨11907426199775265637799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 127012546130936166803189 11907426199775265637799)
                ·
                  rfl

theorem cell20_78265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 5].length) (baseStart_78265 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_78265 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_78265 prefixEnd_78265 := by exact prefixLift 78265
  have htrace : WordTrace (prefixWord ++ tailWord_78265) baseStart_78265 baseEnd_78265 := by
    simpa [prefixWord, tailWord_78265, baseEnd_78265] using wordTrace_append hprefix tailTrace_78265
  have hstable : (prefixWord ++ tailWord_78265).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78265).length < 2 ^ (prefixWord ++ tailWord_78265).sum := by decide
  have hdescent : baseEnd_78265 < baseStart_78265 := by decide
  rcases family_descends (prefixWord ++ tailWord_78265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78279 : List Nat := [1, 1, 4, 1, 1, 4, 1, 1, 6]
def baseStart_78279 : Nat := 118140960795 + 78279 * 2 ^ 59
def prefixEnd_78279 : Nat := 4983230072969 + 3 ^ 40 * 78279 * 2
def baseEnd_78279 : Nat := 35728668580803970446673

theorem tailTrace_78279 : CollatzResearch.WordTrace tailWord_78279 prefixEnd_78279 35728668580803970446673 := by
  unfold tailWord_78279
  simp only [CollatzResearch.WordTrace]
  refine ⟨2855069683416026833949891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1903379788944017889299927 2855069683416026833949891)
  ·
    refine ⟨4282604525124040250924837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2855069683416026833949891 4282604525124040250924837)
    ·
      refine ⟨802988348460757547048407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4282604525124040250924837 802988348460757547048407)
      ·
        refine ⟨1204482522691136320572611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 802988348460757547048407 1204482522691136320572611)
        ·
          refine ⟨1806723784036704480858917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1204482522691136320572611 1806723784036704480858917)
          ·
            refine ⟨338760709506882090161047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1806723784036704480858917 338760709506882090161047)
            ·
              refine ⟨508141064260323135241571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 338760709506882090161047 508141064260323135241571)
              ·
                refine ⟨762211596390484702862357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 508141064260323135241571 762211596390484702862357)
                ·
                  refine ⟨35728668580803970446673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 762211596390484702862357 35728668580803970446673)
                  ·
                    rfl

theorem cell20_78279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 6].length) (baseStart_78279 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_78279 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_78279 prefixEnd_78279 := by exact prefixLift 78279
  have htrace : WordTrace (prefixWord ++ tailWord_78279) baseStart_78279 baseEnd_78279 := by
    simpa [prefixWord, tailWord_78279, baseEnd_78279] using wordTrace_append hprefix tailTrace_78279
  have hstable : (prefixWord ++ tailWord_78279).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78279).length < 2 ^ (prefixWord ++ tailWord_78279).sum := by decide
  have hdescent : baseEnd_78279 < baseStart_78279 := by decide
  rcases family_descends (prefixWord ++ tailWord_78279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78292 : List Nat := [2, 4, 1, 2, 2, 2, 2, 3, 2]
def baseStart_78292 : Nat := 118140960795 + 78292 * 2 ^ 59
def prefixEnd_78292 : Nat := 4983230072969 + 3 ^ 40 * 78292 * 2
def baseEnd_78292 : Nat := 35734602135033703013287

theorem tailTrace_78292 : CollatzResearch.WordTrace tailWord_78292 prefixEnd_78292 35734602135033703013287 := by
  unfold tailWord_78292
  simp only [CollatzResearch.WordTrace]
  refine ⟨1427771916184465027086565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1903695888245953369448753 1427771916184465027086565)
  ·
    refine ⟨267707234284587192578731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1427771916184465027086565 267707234284587192578731)
    ·
      refine ⟨401560851426880788868097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267707234284587192578731 401560851426880788868097)
      ·
        refine ⟨301170638570160591651073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 401560851426880788868097 301170638570160591651073)
        ·
          refine ⟨225877978927620443738305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 301170638570160591651073 225877978927620443738305)
          ·
            refine ⟨169408484195715332803729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 225877978927620443738305 169408484195715332803729)
            ·
              refine ⟨127056363146786499602797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169408484195715332803729 127056363146786499602797)
              ·
                refine ⟨47646136180044937351049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 127056363146786499602797 47646136180044937351049)
                ·
                  refine ⟨35734602135033703013287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47646136180044937351049 35734602135033703013287)
                  ·
                    rfl

theorem cell20_78292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 3, 2].length) (baseStart_78292 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_78292 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_78292 prefixEnd_78292 := by exact prefixLift 78292
  have htrace : WordTrace (prefixWord ++ tailWord_78292) baseStart_78292 baseEnd_78292 := by
    simpa [prefixWord, tailWord_78292, baseEnd_78292] using wordTrace_append hprefix tailTrace_78292
  have hstable : (prefixWord ++ tailWord_78292).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78292).length < 2 ^ (prefixWord ++ tailWord_78292).sum := by decide
  have hdescent : baseEnd_78292 < baseStart_78292 := by decide
  rcases family_descends (prefixWord ++ tailWord_78292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78331 : List Nat := [1, 1, 1, 1, 1, 3, 2, 1, 9]
def baseStart_78331 : Nat := 118140960795 + 78331 * 2 ^ 59
def prefixEnd_78331 : Nat := 4983230072969 + 3 ^ 40 * 78331 * 2
def baseEnd_78331 : Nat := 35752402797722900713127

theorem tailTrace_78331 : CollatzResearch.WordTrace tailWord_78331 prefixEnd_78331 35752402797722900713127 := by
  unfold tailWord_78331
  simp only [CollatzResearch.WordTrace]
  refine ⟨2856966279227639714842847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1904644186151759809895231 2856966279227639714842847)
  ·
    refine ⟨4285449418841459572264271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2856966279227639714842847 4285449418841459572264271)
    ·
      refine ⟨6428174128262189358396407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4285449418841459572264271 6428174128262189358396407)
      ·
        refine ⟨9642261192393284037594611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6428174128262189358396407 9642261192393284037594611)
        ·
          refine ⟨14463391788589926056391917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9642261192393284037594611 14463391788589926056391917)
          ·
            refine ⟨5423771920721222271146969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14463391788589926056391917 5423771920721222271146969)
            ·
              refine ⟨4067828940540916703360227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5423771920721222271146969 4067828940540916703360227)
              ·
                refine ⟨6101743410811375055040341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4067828940540916703360227 6101743410811375055040341)
                ·
                  refine ⟨35752402797722900713127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 6101743410811375055040341 35752402797722900713127)
                  ·
                    rfl

theorem cell20_78331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 9].length) (baseStart_78331 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_78331 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_78331 prefixEnd_78331 := by exact prefixLift 78331
  have htrace : WordTrace (prefixWord ++ tailWord_78331) baseStart_78331 baseEnd_78331 := by
    simpa [prefixWord, tailWord_78331, baseEnd_78331] using wordTrace_append hprefix tailTrace_78331
  have hstable : (prefixWord ++ tailWord_78331).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78331).length < 2 ^ (prefixWord ++ tailWord_78331).sum := by decide
  have hdescent : baseEnd_78331 < baseStart_78331 := by decide
  rcases family_descends (prefixWord ++ tailWord_78331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78341 : List Nat := [1, 3, 1, 1, 2, 2, 6, 4]
def baseStart_78341 : Nat := 118140960795 + 78341 * 2 ^ 59
def prefixEnd_78341 : Nat := 4983230072969 + 3 ^ 40 * 78341 * 2
def baseEnd_78341 : Nat := 11918989023402436793251

theorem tailTrace_78341 : CollatzResearch.WordTrace tailWord_78341 prefixEnd_78341 11918989023402436793251 := by
  unfold tailWord_78341
  simp only [CollatzResearch.WordTrace]
  refine ⟨2857331009191411422706877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1904887339460940948471251 2857331009191411422706877)
  ·
    refine ⟨1071499128446779283515079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2857331009191411422706877 1071499128446779283515079)
    ·
      refine ⟨1607248692670168925272619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1071499128446779283515079 1607248692670168925272619)
      ·
        refine ⟨2410873039005253387908929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1607248692670168925272619 2410873039005253387908929)
        ·
          refine ⟨1808154779253940040931697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2410873039005253387908929 1808154779253940040931697)
          ·
            refine ⟨1356116084440455030698773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1808154779253940040931697 1356116084440455030698773)
            ·
              refine ⟨63567941458146329564005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1356116084440455030698773 63567941458146329564005)
              ·
                refine ⟨11918989023402436793251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63567941458146329564005 11918989023402436793251)
                ·
                  rfl

theorem cell20_78341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 6, 4].length) (baseStart_78341 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_78341 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_78341 prefixEnd_78341 := by exact prefixLift 78341
  have htrace : WordTrace (prefixWord ++ tailWord_78341) baseStart_78341 baseEnd_78341 := by
    simpa [prefixWord, tailWord_78341, baseEnd_78341] using wordTrace_append hprefix tailTrace_78341
  have hstable : (prefixWord ++ tailWord_78341).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78341).length < 2 ^ (prefixWord ++ tailWord_78341).sum := by decide
  have hdescent : baseEnd_78341 < baseStart_78341 := by decide
  rcases family_descends (prefixWord ++ tailWord_78341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78348 : List Nat := [2, 2, 1, 2, 4, 1, 1, 2, 5]
def baseStart_78348 : Nat := 118140960795 + 78348 * 2 ^ 59
def prefixEnd_78348 : Nat := 4983230072969 + 3 ^ 40 * 78348 * 2
def baseEnd_78348 : Nat := 35760162060946397146391

theorem tailTrace_78348 : CollatzResearch.WordTrace tailWord_78348 prefixEnd_78348 35760162060946397146391 := by
  unfold tailWord_78348
  simp only [CollatzResearch.WordTrace]
  refine ⟨1428793160083025809105849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1905057546777367745474465 1428793160083025809105849)
  ·
    refine ⟨1071594870062269356829387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1428793160083025809105849 1071594870062269356829387)
    ·
      refine ⟨1607392305093404035244081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1071594870062269356829387 1607392305093404035244081)
      ·
        refine ⟨1205544228820053026433061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1607392305093404035244081 1205544228820053026433061)
        ·
          refine ⟨226039542903759942456199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1205544228820053026433061 226039542903759942456199)
          ·
            refine ⟨339059314355639913684299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 226039542903759942456199 339059314355639913684299)
            ·
              refine ⟨508588971533459870526449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 339059314355639913684299 508588971533459870526449)
              ·
                refine ⟨381441728650094902894837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 508588971533459870526449 381441728650094902894837)
                ·
                  refine ⟨35760162060946397146391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 381441728650094902894837 35760162060946397146391)
                  ·
                    rfl

theorem cell20_78348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 2, 5].length) (baseStart_78348 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_78348 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_78348 prefixEnd_78348 := by exact prefixLift 78348
  have htrace : WordTrace (prefixWord ++ tailWord_78348) baseStart_78348 baseEnd_78348 := by
    simpa [prefixWord, tailWord_78348, baseEnd_78348] using wordTrace_append hprefix tailTrace_78348
  have hstable : (prefixWord ++ tailWord_78348).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78348).length < 2 ^ (prefixWord ++ tailWord_78348).sum := by decide
  have hdescent : baseEnd_78348 < baseStart_78348 := by decide
  rcases family_descends (prefixWord ++ tailWord_78348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78362 : List Nat := [3, 1, 1, 3, 1, 1, 10]
def baseStart_78362 : Nat := 118140960795 + 78362 * 2 ^ 59
def prefixEnd_78362 : Nat := 4983230072969 + 3 ^ 40 * 78362 * 2
def baseEnd_78362 : Nat := 3974061338047174519963

theorem tailTrace_78362 : CollatzResearch.WordTrace tailWord_78362 prefixEnd_78362 3974061338047174519963 := by
  unfold tailWord_78362
  simp only [CollatzResearch.WordTrace]
  refine ⟨714524235528833002305335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1905397961410221339480893 714524235528833002305335)
  ·
    refine ⟨1071786353293249503458003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 714524235528833002305335 1071786353293249503458003)
    ·
      refine ⟨1607679529939874255187005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1071786353293249503458003 1607679529939874255187005)
      ·
        refine ⟨602879823727452845695127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1607679529939874255187005 602879823727452845695127)
        ·
          refine ⟨904319735591179268542691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 602879823727452845695127 904319735591179268542691)
          ·
            refine ⟨1356479603386768902814037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 904319735591179268542691 1356479603386768902814037)
            ·
              refine ⟨3974061338047174519963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1356479603386768902814037 3974061338047174519963)
              ·
                rfl

theorem cell20_78362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 10].length) (baseStart_78362 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_78362 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_78362 prefixEnd_78362 := by exact prefixLift 78362
  have htrace : WordTrace (prefixWord ++ tailWord_78362) baseStart_78362 baseEnd_78362 := by
    simpa [prefixWord, tailWord_78362, baseEnd_78362] using wordTrace_append hprefix tailTrace_78362
  have hstable : (prefixWord ++ tailWord_78362).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78362).length < 2 ^ (prefixWord ++ tailWord_78362).sum := by decide
  have hdescent : baseEnd_78362 < baseStart_78362 := by decide
  rcases family_descends (prefixWord ++ tailWord_78362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78368 : List Nat := [2, 1, 1, 6, 3, 1, 1, 1, 4]
def baseStart_78368 : Nat := 118140960795 + 78368 * 2 ^ 59
def prefixEnd_78368 : Nat := 4983230072969 + 3 ^ 40 * 78368 * 2
def baseEnd_78368 : Nat := 35769290605915216479643

theorem tailTrace_78368 : CollatzResearch.WordTrace tailWord_78368 prefixEnd_78368 35769290605915216479643 := by
  unfold tailWord_78368
  simp only [CollatzResearch.WordTrace]
  refine ⟨1429157890046797516969879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1905543853395730022626505 1429157890046797516969879)
  ·
    refine ⟨2143736835070196275454819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1429157890046797516969879 2143736835070196275454819)
    ·
      refine ⟨3215605252605294413182229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2143736835070196275454819 3215605252605294413182229)
      ·
        refine ⟨150731496215873175617917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 3215605252605294413182229 150731496215873175617917)
        ·
          refine ⟨56524311080952440856719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 150731496215873175617917 56524311080952440856719)
          ·
            refine ⟨84786466621428661285079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56524311080952440856719 84786466621428661285079)
            ·
              refine ⟨127179699932142991927619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84786466621428661285079 127179699932142991927619)
              ·
                refine ⟨190769549898214487891429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 127179699932142991927619 190769549898214487891429)
                ·
                  refine ⟨35769290605915216479643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 190769549898214487891429 35769290605915216479643)
                  ·
                    rfl

theorem cell20_78368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 1, 4].length) (baseStart_78368 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_78368 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_78368 prefixEnd_78368 := by exact prefixLift 78368
  have htrace : WordTrace (prefixWord ++ tailWord_78368) baseStart_78368 baseEnd_78368 := by
    simpa [prefixWord, tailWord_78368, baseEnd_78368] using wordTrace_append hprefix tailTrace_78368
  have hstable : (prefixWord ++ tailWord_78368).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78368).length < 2 ^ (prefixWord ++ tailWord_78368).sum := by decide
  have hdescent : baseEnd_78368 < baseStart_78368 := by decide
  rcases family_descends (prefixWord ++ tailWord_78368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78375 : List Nat := [1, 1, 7, 2, 1, 1, 2, 5]
def baseStart_78375 : Nat := 118140960795 + 78375 * 2 ^ 59
def prefixEnd_78375 : Nat := 4983230072969 + 3 ^ 40 * 78375 * 2
def baseEnd_78375 : Nat := 11924161865551434415427

theorem tailTrace_78375 : CollatzResearch.WordTrace tailWord_78375 prefixEnd_78375 11924161865551434415427 := by
  unfold tailWord_78375
  simp only [CollatzResearch.WordTrace]
  refine ⟨2858571091068235229444579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1905714060712156819629719 2858571091068235229444579)
  ·
    refine ⟨4287856636602352844166869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2858571091068235229444579 4287856636602352844166869)
    ·
      refine ⟨100496639920367644785161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 4287856636602352844166869 100496639920367644785161)
      ·
        refine ⟨75372479940275733588871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100496639920367644785161 75372479940275733588871)
        ·
          refine ⟨113058719910413600383307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75372479940275733588871 113058719910413600383307)
          ·
            refine ⟨169588079865620400574961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113058719910413600383307 169588079865620400574961)
            ·
              refine ⟨127191059899215300431221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169588079865620400574961 127191059899215300431221)
              ·
                refine ⟨11924161865551434415427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 127191059899215300431221 11924161865551434415427)
                ·
                  rfl

theorem cell20_78375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 5].length) (baseStart_78375 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_78375 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_78375 prefixEnd_78375 := by exact prefixLift 78375
  have htrace : WordTrace (prefixWord ++ tailWord_78375) baseStart_78375 baseEnd_78375 := by
    simpa [prefixWord, tailWord_78375, baseEnd_78375] using wordTrace_append hprefix tailTrace_78375
  have hstable : (prefixWord ++ tailWord_78375).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78375).length < 2 ^ (prefixWord ++ tailWord_78375).sum := by decide
  have hdescent : baseEnd_78375 < baseStart_78375 := by decide
  rcases family_descends (prefixWord ++ tailWord_78375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78382 : List Nat := [4, 1, 3, 1, 3, 1, 1, 3, 3]
def baseStart_78382 : Nat := 118140960795 + 78382 * 2 ^ 59
def prefixEnd_78382 : Nat := 4983230072969 + 3 ^ 40 * 78382 * 2
def baseEnd_78382 : Nat := 35775680587393390012919

theorem tailTrace_78382 : CollatzResearch.WordTrace tailWord_78382 prefixEnd_78382 35775680587393390012919 := by
  unfold tailWord_78382
  simp only [CollatzResearch.WordTrace]
  refine ⟨357353300255359428118675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1905884268028583616632933 357353300255359428118675)
  ·
    refine ⟨536029950383039142178013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 357353300255359428118675 536029950383039142178013)
    ·
      refine ⟨201011231393639678316755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 536029950383039142178013 201011231393639678316755)
      ·
        refine ⟨301516847090459517475133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201011231393639678316755 301516847090459517475133)
        ·
          refine ⟨113068817658922319053175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 301516847090459517475133 113068817658922319053175)
          ·
            refine ⟨169603226488383478579763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113068817658922319053175 169603226488383478579763)
            ·
              refine ⟨254404839732575217869645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 169603226488383478579763 254404839732575217869645)
              ·
                refine ⟨95401814899715706701117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 254404839732575217869645 95401814899715706701117)
                ·
                  refine ⟨35775680587393390012919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 95401814899715706701117 35775680587393390012919)
                  ·
                    rfl

theorem cell20_78382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 3, 3].length) (baseStart_78382 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_78382 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_78382 prefixEnd_78382 := by exact prefixLift 78382
  have htrace : WordTrace (prefixWord ++ tailWord_78382) baseStart_78382 baseEnd_78382 := by
    simpa [prefixWord, tailWord_78382, baseEnd_78382] using wordTrace_append hprefix tailTrace_78382
  have hstable : (prefixWord ++ tailWord_78382).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78382).length < 2 ^ (prefixWord ++ tailWord_78382).sum := by decide
  have hdescent : baseEnd_78382 < baseStart_78382 := by decide
  rcases family_descends (prefixWord ++ tailWord_78382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78393 : List Nat := [1, 2, 1, 5, 1, 1, 2, 1, 6]
def baseStart_78393 : Nat := 118140960795 + 78393 * 2 ^ 59
def prefixEnd_78393 : Nat := 4983230072969 + 3 ^ 40 * 78393 * 2
def baseEnd_78393 : Nat := 35780701287126240646207

theorem tailTrace_78393 : CollatzResearch.WordTrace tailWord_78393 prefixEnd_78393 35780701287126240646207 := by
  unfold tailWord_78393
  simp only [CollatzResearch.WordTrace]
  refine ⟨2859227605003024303599833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1906151736668682869066555 2859227605003024303599833)
  ·
    refine ⟨2144420703752268227699875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2859227605003024303599833 2144420703752268227699875)
    ·
      refine ⟨3216631055628402341549813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2144420703752268227699875 3216631055628402341549813)
      ·
        refine ⟨301559161465162719520295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3216631055628402341549813 301559161465162719520295)
        ·
          refine ⟨452338742197744079280443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 301559161465162719520295 452338742197744079280443)
          ·
            refine ⟨678508113296616118920665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 452338742197744079280443 678508113296616118920665)
            ·
              refine ⟨508881084972462089190499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 678508113296616118920665 508881084972462089190499)
              ·
                refine ⟨763321627458693133785749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 508881084972462089190499 763321627458693133785749)
                ·
                  refine ⟨35780701287126240646207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 763321627458693133785749 35780701287126240646207)
                  ·
                    rfl

theorem cell20_78393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 6].length) (baseStart_78393 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_78393 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_78393 prefixEnd_78393 := by exact prefixLift 78393
  have htrace : WordTrace (prefixWord ++ tailWord_78393) baseStart_78393 baseEnd_78393 := by
    simpa [prefixWord, tailWord_78393, baseEnd_78393] using wordTrace_append hprefix tailTrace_78393
  have hstable : (prefixWord ++ tailWord_78393).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78393).length < 2 ^ (prefixWord ++ tailWord_78393).sum := by decide
  have hdescent : baseEnd_78393 < baseStart_78393 := by decide
  rcases family_descends (prefixWord ++ tailWord_78393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78400 : List Nat := [2, 1, 1, 2, 2, 2, 4, 6]
def baseStart_78400 : Nat := 118140960795 + 78400 * 2 ^ 59
def prefixEnd_78400 : Nat := 4983230072969 + 3 ^ 40 * 78400 * 2
def baseEnd_78400 : Nat := 11927965425955109137615

theorem tailTrace_78400 : CollatzResearch.WordTrace tailWord_78400 prefixEnd_78400 11927965425955109137615 := by
  unfold tailWord_78400
  simp only [CollatzResearch.WordTrace]
  refine ⟨1429741457988832249552327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1906321943985109666069769 1429741457988832249552327)
  ·
    refine ⟨2144612186983248374328491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1429741457988832249552327 2144612186983248374328491)
    ·
      refine ⟨3216918280474872561492737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2144612186983248374328491 3216918280474872561492737)
      ·
        refine ⟨2412688710356154421119553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3216918280474872561492737 2412688710356154421119553)
        ·
          refine ⟨1809516532767115815839665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2412688710356154421119553 1809516532767115815839665)
          ·
            refine ⟨1357137399575336861879749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1809516532767115815839665 1357137399575336861879749)
            ·
              refine ⟨254463262420375661602453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1357137399575336861879749 254463262420375661602453)
              ·
                refine ⟨11927965425955109137615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 254463262420375661602453 11927965425955109137615)
                ·
                  rfl

theorem cell20_78400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 6].length) (baseStart_78400 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_78400 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_78400 prefixEnd_78400 := by exact prefixLift 78400
  have htrace : WordTrace (prefixWord ++ tailWord_78400) baseStart_78400 baseEnd_78400 := by
    simpa [prefixWord, tailWord_78400, baseEnd_78400] using wordTrace_append hprefix tailTrace_78400
  have hstable : (prefixWord ++ tailWord_78400).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78400).length < 2 ^ (prefixWord ++ tailWord_78400).sum := by decide
  have hdescent : baseEnd_78400 < baseStart_78400 := by decide
  rcases family_descends (prefixWord ++ tailWord_78400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78424 : List Nat := [2, 1, 2, 2, 1, 2, 3, 4, 3]
def baseStart_78424 : Nat := 118140960795 + 78424 * 2 ^ 59
def prefixEnd_78424 : Nat := 4983230072969 + 3 ^ 40 * 78424 * 2
def baseEnd_78424 : Nat := 35794850531827910612747

theorem tailTrace_78424 : CollatzResearch.WordTrace tailWord_78424 prefixEnd_78424 35794850531827910612747 := by
  unfold tailWord_78424
  simp only [CollatzResearch.WordTrace]
  refine ⟨1430179133945358298989163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1906905511927144398652217 1430179133945358298989163)
  ·
    refine ⟨2145268700918037448483745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1430179133945358298989163 2145268700918037448483745)
    ·
      refine ⟨1608951525688528086362809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2145268700918037448483745 1608951525688528086362809)
      ·
        refine ⟨1206713644266396064772107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1608951525688528086362809 1206713644266396064772107)
        ·
          refine ⟨1810070466399594097158161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1206713644266396064772107 1810070466399594097158161)
          ·
            refine ⟨1357552849799695572868621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1810070466399594097158161 1357552849799695572868621)
            ·
              refine ⟨509082318674885839825733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1357552849799695572868621 509082318674885839825733)
              ·
                refine ⟨95452934751541094967325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 509082318674885839825733 95452934751541094967325)
                ·
                  refine ⟨35794850531827910612747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 95452934751541094967325 35794850531827910612747)
                  ·
                    rfl

theorem cell20_78424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 4, 3].length) (baseStart_78424 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_78424 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_78424 prefixEnd_78424 := by exact prefixLift 78424
  have htrace : WordTrace (prefixWord ++ tailWord_78424) baseStart_78424 baseEnd_78424 := by
    simpa [prefixWord, tailWord_78424, baseEnd_78424] using wordTrace_append hprefix tailTrace_78424
  have hstable : (prefixWord ++ tailWord_78424).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78424).length < 2 ^ (prefixWord ++ tailWord_78424).sum := by decide
  have hdescent : baseEnd_78424 < baseStart_78424 := by decide
  rcases family_descends (prefixWord ++ tailWord_78424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78448 : List Nat := [2, 1, 1, 1, 7, 1, 1, 2, 4]
def baseStart_78448 : Nat := 118140960795 + 78448 * 2 ^ 59
def prefixEnd_78448 : Nat := 4983230072969 + 3 ^ 40 * 78448 * 2
def baseEnd_78448 : Nat := 35805804785790493812649

theorem tailTrace_78448 : CollatzResearch.WordTrace tailWord_78448 prefixEnd_78448 35805804785790493812649 := by
  unfold tailWord_78448
  simp only [CollatzResearch.WordTrace]
  refine ⟨1430616809901884348425999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1907489079869179131234665 1430616809901884348425999)
  ·
    refine ⟨2145925214852826522638999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1430616809901884348425999 2145925214852826522638999)
    ·
      refine ⟨3218887822279239783958499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2145925214852826522638999 3218887822279239783958499)
      ·
        refine ⟨4828331733418859675937749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3218887822279239783958499 4828331733418859675937749)
        ·
          refine ⟨113164025002004523654791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 4828331733418859675937749 113164025002004523654791)
          ·
            refine ⟨169746037503006785482187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113164025002004523654791 169746037503006785482187)
            ·
              refine ⟨254619056254510178223281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 169746037503006785482187 254619056254510178223281)
              ·
                refine ⟨190964292190882633667461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 254619056254510178223281 190964292190882633667461)
                ·
                  refine ⟨35805804785790493812649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 190964292190882633667461 35805804785790493812649)
                  ·
                    rfl

theorem cell20_78448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 2, 4].length) (baseStart_78448 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_78448 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_78448 prefixEnd_78448 := by exact prefixLift 78448
  have htrace : WordTrace (prefixWord ++ tailWord_78448) baseStart_78448 baseEnd_78448 := by
    simpa [prefixWord, tailWord_78448, baseEnd_78448] using wordTrace_append hprefix tailTrace_78448
  have hstable : (prefixWord ++ tailWord_78448).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78448).length < 2 ^ (prefixWord ++ tailWord_78448).sum := by decide
  have hdescent : baseEnd_78448 < baseStart_78448 := by decide
  rcases family_descends (prefixWord ++ tailWord_78448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78465 : List Nat := [1, 2, 4, 2, 1, 1, 4, 3, 2]
def baseStart_78465 : Nat := 118140960795 + 78465 * 2 ^ 59
def prefixEnd_78465 : Nat := 4983230072969 + 3 ^ 40 * 78465 * 2
def baseEnd_78465 : Nat := 35813564049013990245913

theorem tailTrace_78465 : CollatzResearch.WordTrace tailWord_78465 prefixEnd_78465 35813564049013990245913 := by
  unfold tailWord_78465
  simp only [CollatzResearch.WordTrace]
  refine ⟨2861853660742180600220849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1907902440494787066813899 2861853660742180600220849)
  ·
    refine ⟨2146390245556635450165637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2861853660742180600220849 2146390245556635450165637)
    ·
      refine ⟨402448171041869146906057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2146390245556635450165637 402448171041869146906057)
      ·
        refine ⟨301836128281401860179543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 402448171041869146906057 301836128281401860179543)
        ·
          refine ⟨452754192422102790269315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 301836128281401860179543 452754192422102790269315)
          ·
            refine ⟨679131288633154185403973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 452754192422102790269315 679131288633154185403973)
            ·
              refine ⟨127337116618716409763245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 679131288633154185403973 127337116618716409763245)
              ·
                refine ⟨47751418732018653661217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 127337116618716409763245 47751418732018653661217)
                ·
                  refine ⟨35813564049013990245913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47751418732018653661217 35813564049013990245913)
                  ·
                    rfl

theorem cell20_78465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 3, 2].length) (baseStart_78465 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_78465 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_78465 prefixEnd_78465 := by exact prefixLift 78465
  have htrace : WordTrace (prefixWord ++ tailWord_78465) baseStart_78465 baseEnd_78465 := by
    simpa [prefixWord, tailWord_78465, baseEnd_78465] using wordTrace_append hprefix tailTrace_78465
  have hstable : (prefixWord ++ tailWord_78465).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78465).length < 2 ^ (prefixWord ++ tailWord_78465).sum := by decide
  have hdescent : baseEnd_78465 < baseStart_78465 := by decide
  rcases family_descends (prefixWord ++ tailWord_78465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78483 : List Nat := [1, 1, 1, 2, 1, 2, 2, 5, 5]
def baseStart_78483 : Nat := 118140960795 + 78483 * 2 ^ 59
def prefixEnd_78483 : Nat := 4983230072969 + 3 ^ 40 * 78483 * 2
def baseEnd_78483 : Nat := 35821779739485927645839

theorem tailTrace_78483 : CollatzResearch.WordTrace tailWord_78483 prefixEnd_78483 35821779739485927645839 := by
  unfold tailWord_78483
  simp only [CollatzResearch.WordTrace]
  refine ⟨2862510174676969674376103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1908340116451313116250735 2862510174676969674376103)
  ·
    refine ⟨4293765262015454511564155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2862510174676969674376103 4293765262015454511564155)
    ·
      refine ⟨6440647893023181767346233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4293765262015454511564155 6440647893023181767346233)
      ·
        refine ⟨4830485919767386325509675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6440647893023181767346233 4830485919767386325509675)
        ·
          refine ⟨7245728879651079488264513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4830485919767386325509675 7245728879651079488264513)
          ·
            refine ⟨5434296659738309616198385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7245728879651079488264513 5434296659738309616198385)
            ·
              refine ⟨4075722494803732212148789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5434296659738309616198385 4075722494803732212148789)
              ·
                refine ⟨382098983887849894888949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4075722494803732212148789 382098983887849894888949)
                ·
                  refine ⟨35821779739485927645839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 382098983887849894888949 35821779739485927645839)
                  ·
                    rfl

theorem cell20_78483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 5, 5].length) (baseStart_78483 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_78483 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_78483 prefixEnd_78483 := by exact prefixLift 78483
  have htrace : WordTrace (prefixWord ++ tailWord_78483) baseStart_78483 baseEnd_78483 := by
    simpa [prefixWord, tailWord_78483, baseEnd_78483] using wordTrace_append hprefix tailTrace_78483
  have hstable : (prefixWord ++ tailWord_78483).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78483).length < 2 ^ (prefixWord ++ tailWord_78483).sum := by decide
  have hdescent : baseEnd_78483 < baseStart_78483 := by decide
  rcases family_descends (prefixWord ++ tailWord_78483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78496 : List Nat := [2, 1, 1, 4, 4, 1, 3, 1, 3]
def baseStart_78496 : Nat := 118140960795 + 78496 * 2 ^ 59
def prefixEnd_78496 : Nat := 4983230072969 + 3 ^ 40 * 78496 * 2
def baseEnd_78496 : Nat := 35827713293715660212453

theorem tailTrace_78496 : CollatzResearch.WordTrace tailWord_78496 prefixEnd_78496 35827713293715660212453 := by
  unfold tailWord_78496
  simp only [CollatzResearch.WordTrace]
  refine ⟨1431492161814936447299671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1908656215753248596399561 1431492161814936447299671)
  ·
    refine ⟨2147238242722404670949507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1431492161814936447299671 2147238242722404670949507)
    ·
      refine ⟨3220857364083607006424261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2147238242722404670949507 3220857364083607006424261)
      ·
        refine ⟨603910755765676313704549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3220857364083607006424261 603910755765676313704549)
        ·
          refine ⟨113233266706064308819603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 603910755765676313704549 113233266706064308819603)
          ·
            refine ⟨169849900059096463229405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113233266706064308819603 169849900059096463229405)
            ·
              refine ⟨63693712522161173711027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 169849900059096463229405 63693712522161173711027)
              ·
                refine ⟨95540568783241760566541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63693712522161173711027 95540568783241760566541)
                ·
                  refine ⟨35827713293715660212453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 95540568783241760566541 35827713293715660212453)
                  ·
                    rfl

theorem cell20_78496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 3, 1, 3].length) (baseStart_78496 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_78496 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_78496 prefixEnd_78496 := by exact prefixLift 78496
  have htrace : WordTrace (prefixWord ++ tailWord_78496) baseStart_78496 baseEnd_78496 := by
    simpa [prefixWord, tailWord_78496, baseEnd_78496] using wordTrace_append hprefix tailTrace_78496
  have hstable : (prefixWord ++ tailWord_78496).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78496).length < 2 ^ (prefixWord ++ tailWord_78496).sum := by decide
  have hdescent : baseEnd_78496 < baseStart_78496 := by decide
  rcases family_descends (prefixWord ++ tailWord_78496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78506 : List Nat := [3, 1, 5, 2, 1, 2, 2, 4]
def baseStart_78506 : Nat := 118140960795 + 78506 * 2 ^ 59
def prefixEnd_78506 : Nat := 4983230072969 + 3 ^ 40 * 78506 * 2
def baseEnd_78506 : Nat := 11944092522066689959693

theorem tailTrace_78506 : CollatzResearch.WordTrace tailWord_78506 prefixEnd_78506 11944092522066689959693 := by
  unfold tailWord_78506
  simp only [CollatzResearch.WordTrace]
  refine ⟨715837263398411150615843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1908899369062429734975581 715837263398411150615843)
  ·
    refine ⟨1073755895097616725923765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 715837263398411150615843 1073755895097616725923765)
    ·
      refine ⟨100664615165401568055353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1073755895097616725923765 100664615165401568055353)
      ·
        refine ⟨75498461374051176041515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100664615165401568055353 75498461374051176041515)
        ·
          refine ⟨113247692061076764062273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75498461374051176041515 113247692061076764062273)
          ·
            refine ⟨84935769045807573046705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113247692061076764062273 84935769045807573046705)
            ·
              refine ⟨63701826784355679785029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84935769045807573046705 63701826784355679785029)
              ·
                refine ⟨11944092522066689959693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63701826784355679785029 11944092522066689959693)
                ·
                  rfl

theorem cell20_78506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 2, 4].length) (baseStart_78506 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_78506 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_78506 prefixEnd_78506 := by exact prefixLift 78506
  have htrace : WordTrace (prefixWord ++ tailWord_78506) baseStart_78506 baseEnd_78506 := by
    simpa [prefixWord, tailWord_78506, baseEnd_78506] using wordTrace_append hprefix tailTrace_78506
  have hstable : (prefixWord ++ tailWord_78506).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78506).length < 2 ^ (prefixWord ++ tailWord_78506).sum := by decide
  have hdescent : baseEnd_78506 < baseStart_78506 := by decide
  rcases family_descends (prefixWord ++ tailWord_78506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78510 : List Nat := [4, 1, 4, 1, 1, 2, 1, 6]
def baseStart_78510 : Nat := 118140960795 + 78510 * 2 ^ 59
def prefixEnd_78510 : Nat := 4983230072969 + 3 ^ 40 * 78510 * 2
def baseEnd_78510 : Nat := 11944701091731277915243

theorem tailTrace_78510 : CollatzResearch.WordTrace tailWord_78510 prefixEnd_78510 11944701091731277915243 := by
  unfold tailWord_78510
  simp only [CollatzResearch.WordTrace]
  refine ⟨357936868197394160701123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1908996630386102190405989 357936868197394160701123)
  ·
    refine ⟨536905302296091241051685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 357936868197394160701123 536905302296091241051685)
    ·
      refine ⟨100669744180517107697191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 536905302296091241051685 100669744180517107697191)
      ·
        refine ⟨151004616270775661545787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100669744180517107697191 151004616270775661545787)
        ·
          refine ⟨226506924406163492318681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151004616270775661545787 226506924406163492318681)
          ·
            refine ⟨169880193304622619239011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 226506924406163492318681 169880193304622619239011)
            ·
              refine ⟨254820289956933928858517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 169880193304622619239011 254820289956933928858517)
              ·
                refine ⟨11944701091731277915243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 254820289956933928858517 11944701091731277915243)
                ·
                  rfl

theorem cell20_78510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 6].length) (baseStart_78510 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_78510 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_78510 prefixEnd_78510 := by exact prefixLift 78510
  have htrace : WordTrace (prefixWord ++ tailWord_78510) baseStart_78510 baseEnd_78510 := by
    simpa [prefixWord, tailWord_78510, baseEnd_78510] using wordTrace_append hprefix tailTrace_78510
  have hstable : (prefixWord ++ tailWord_78510).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78510).length < 2 ^ (prefixWord ++ tailWord_78510).sum := by decide
  have hdescent : baseEnd_78510 < baseStart_78510 := by decide
  rcases family_descends (prefixWord ++ tailWord_78510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78538 : List Nat := [3, 1, 2, 1, 4, 1, 2, 1, 5]
def baseStart_78538 : Nat := 118140960795 + 78538 * 2 ^ 59
def prefixEnd_78538 : Nat := 4983230072969 + 3 ^ 40 * 78538 * 2
def baseEnd_78538 : Nat := 35846883238150180812281

theorem tailTrace_78538 : CollatzResearch.WordTrace tailWord_78538 prefixEnd_78538 35846883238150180812281 := by
  unfold tailWord_78538
  simp only [CollatzResearch.WordTrace]
  refine ⟨716129047369428516907067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1909677459651809378418845 716129047369428516907067)
  ·
    refine ⟨1074193571054142775360601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 716129047369428516907067 1074193571054142775360601)
    ·
      refine ⟨805645178290607081520451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1074193571054142775360601 805645178290607081520451)
      ·
        refine ⟨1208467767435910622280677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 805645178290607081520451 1208467767435910622280677)
        ·
          refine ⟨226587706394233241677627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1208467767435910622280677 226587706394233241677627)
          ·
            refine ⟨339881559591349862516441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 226587706394233241677627 339881559591349862516441)
            ·
              refine ⟨254911169693512396887331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 339881559591349862516441 254911169693512396887331)
              ·
                refine ⟨382366754540268595330997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 254911169693512396887331 382366754540268595330997)
                ·
                  refine ⟨35846883238150180812281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 382366754540268595330997 35846883238150180812281)
                  ·
                    rfl

theorem cell20_78538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 1, 5].length) (baseStart_78538 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_78538 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_78538 prefixEnd_78538 := by exact prefixLift 78538
  have htrace : WordTrace (prefixWord ++ tailWord_78538) baseStart_78538 baseEnd_78538 := by
    simpa [prefixWord, tailWord_78538, baseEnd_78538] using wordTrace_append hprefix tailTrace_78538
  have hstable : (prefixWord ++ tailWord_78538).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78538).length < 2 ^ (prefixWord ++ tailWord_78538).sum := by decide
  have hdescent : baseEnd_78538 < baseStart_78538 := by decide
  rcases family_descends (prefixWord ++ tailWord_78538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78548 : List Nat := [2, 4, 1, 3, 2, 1, 2, 5]
def baseStart_78548 : Nat := 118140960795 + 78548 * 2 ^ 59
def prefixEnd_78548 : Nat := 4983230072969 + 3 ^ 40 * 78548 * 2
def baseEnd_78548 : Nat := 11950482503544863492969

theorem tailTrace_78548 : CollatzResearch.WordTrace tailWord_78548 prefixEnd_78548 11950482503544863492969 := by
  unfold tailWord_78548
  simp only [CollatzResearch.WordTrace]
  refine ⟨1432440459720742887746149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1909920612960990516994865 1432440459720742887746149)
  ·
    refine ⟨268582586197639291452403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1432440459720742887746149 268582586197639291452403)
    ·
      refine ⟨402873879296458937178605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268582586197639291452403 402873879296458937178605)
      ·
        refine ⟨151077704736172101441977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 402873879296458937178605 151077704736172101441977)
        ·
          refine ⟨113308278552129076081483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151077704736172101441977 113308278552129076081483)
          ·
            refine ⟨169962417828193614122225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113308278552129076081483 169962417828193614122225)
            ·
              refine ⟨127471813371145210591669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169962417828193614122225 127471813371145210591669)
              ·
                refine ⟨11950482503544863492969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 127471813371145210591669 11950482503544863492969)
                ·
                  rfl

theorem cell20_78548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 5].length) (baseStart_78548 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_78548 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_78548 prefixEnd_78548 := by exact prefixLift 78548
  have htrace : WordTrace (prefixWord ++ tailWord_78548) baseStart_78548 baseEnd_78548 := by
    simpa [prefixWord, tailWord_78548, baseEnd_78548] using wordTrace_append hprefix tailTrace_78548
  have hstable : (prefixWord ++ tailWord_78548).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78548).length < 2 ^ (prefixWord ++ tailWord_78548).sum := by decide
  have hdescent : baseEnd_78548 < baseStart_78548 := by decide
  rcases family_descends (prefixWord ++ tailWord_78548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78552 : List Nat := [2, 1, 2, 2, 3, 2, 1, 7]
def baseStart_78552 : Nat := 118140960795 + 78552 * 2 ^ 59
def prefixEnd_78552 : Nat := 4983230072969 + 3 ^ 40 * 78552 * 2
def baseEnd_78552 : Nat := 11951091073209451448519

theorem tailTrace_78552 : CollatzResearch.WordTrace tailWord_78552 prefixEnd_78552 11951091073209451448519 := by
  unfold tailWord_78552
  simp only [CollatzResearch.WordTrace]
  refine ⟨1432513405713497229318955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1910017874284662972425273 1432513405713497229318955)
  ·
    refine ⟨2148770108570245843978433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1432513405713497229318955 2148770108570245843978433)
    ·
      refine ⟨1611577581427684382983825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2148770108570245843978433 1611577581427684382983825)
      ·
        refine ⟨1208683186070763287237869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1611577581427684382983825 1208683186070763287237869)
        ·
          refine ⟨453256194776536232714201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1208683186070763287237869 453256194776536232714201)
          ·
            refine ⟨339942146082402174535651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 453256194776536232714201 339942146082402174535651)
            ·
              refine ⟨509913219123603261803477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 339942146082402174535651 509913219123603261803477)
              ·
                refine ⟨11951091073209451448519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 509913219123603261803477 11951091073209451448519)
                ·
                  rfl

theorem cell20_78552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 7].length) (baseStart_78552 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_78552 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_78552 prefixEnd_78552 := by exact prefixLift 78552
  have htrace : WordTrace (prefixWord ++ tailWord_78552) baseStart_78552 baseEnd_78552 := by
    simpa [prefixWord, tailWord_78552, baseEnd_78552] using wordTrace_append hprefix tailTrace_78552
  have hstable : (prefixWord ++ tailWord_78552).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78552).length < 2 ^ (prefixWord ++ tailWord_78552).sum := by decide
  have hdescent : baseEnd_78552 < baseStart_78552 := by decide
  rcases family_descends (prefixWord ++ tailWord_78552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78597 : List Nat := [1, 3, 1, 1, 2, 1, 1, 5, 5]
def baseStart_78597 : Nat := 118140960795 + 78597 * 2 ^ 59
def prefixEnd_78597 : Nat := 4983230072969 + 3 ^ 40 * 78597 * 2
def baseEnd_78597 : Nat := 35873812445808197845373

theorem tailTrace_78597 : CollatzResearch.WordTrace tailWord_78597 prefixEnd_78597 35873812445808197845373 := by
  unfold tailWord_78597
  simp only [CollatzResearch.WordTrace]
  refine ⟨2866668096263967144026045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1911112064175978096017363 2866668096263967144026045)
  ·
    refine ⟨1075000536098987679009767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2866668096263967144026045 1075000536098987679009767)
    ·
      refine ⟨1612500804148481518514651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1075000536098987679009767 1612500804148481518514651)
      ·
        refine ⟨2418751206222722277771977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1612500804148481518514651 2418751206222722277771977)
        ·
          refine ⟨1814063404667041708328983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2418751206222722277771977 1814063404667041708328983)
          ·
            refine ⟨2721095107000562562493475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1814063404667041708328983 2721095107000562562493475)
            ·
              refine ⟨4081642660500843843740213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2721095107000562562493475 4081642660500843843740213)
              ·
                refine ⟨382653999421954110350645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4081642660500843843740213 382653999421954110350645)
                ·
                  refine ⟨35873812445808197845373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 382653999421954110350645 35873812445808197845373)
                  ·
                    rfl

theorem cell20_78597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 5, 5].length) (baseStart_78597 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_78597 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_78597 prefixEnd_78597 := by exact prefixLift 78597
  have htrace : WordTrace (prefixWord ++ tailWord_78597) baseStart_78597 baseEnd_78597 := by
    simpa [prefixWord, tailWord_78597, baseEnd_78597] using wordTrace_append hprefix tailTrace_78597
  have hstable : (prefixWord ++ tailWord_78597).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78597).length < 2 ^ (prefixWord ++ tailWord_78597).sum := by decide
  have hdescent : baseEnd_78597 < baseStart_78597 := by decide
  rcases family_descends (prefixWord ++ tailWord_78597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78659 : List Nat := [1, 1, 1, 3, 1, 4, 4, 1, 4]
def baseStart_78659 : Nat := 118140960795 + 78659 * 2 ^ 59
def prefixEnd_78659 : Nat := 4983230072969 + 3 ^ 40 * 78659 * 2
def baseEnd_78659 : Nat := 35902110935211537778453

theorem tailTrace_78659 : CollatzResearch.WordTrace tailWord_78659 prefixEnd_78659 35902110935211537778453 := by
  unfold tailWord_78659
  simp only [CollatzResearch.WordTrace]
  refine ⟨2868929422039351732783031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1912619614692901155188687 2868929422039351732783031)
  ·
    refine ⟨4303394133059027599174547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2868929422039351732783031 4303394133059027599174547)
    ·
      refine ⟨6455091199588541398761821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4303394133059027599174547 6455091199588541398761821)
      ·
        refine ⟨2420659199845703024535683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6455091199588541398761821 2420659199845703024535683)
        ·
          refine ⟨3630988799768554536803525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2420659199845703024535683 3630988799768554536803525)
          ·
            refine ⟨680810399956603975650661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3630988799768554536803525 680810399956603975650661)
            ·
              refine ⟨127651949991863245434499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 680810399956603975650661 127651949991863245434499)
              ·
                refine ⟨191477924987794868151749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 127651949991863245434499 191477924987794868151749)
                ·
                  refine ⟨35902110935211537778453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 191477924987794868151749 35902110935211537778453)
                  ·
                    rfl

theorem cell20_78659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 1, 4].length) (baseStart_78659 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_78659 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_78659 prefixEnd_78659 := by exact prefixLift 78659
  have htrace : WordTrace (prefixWord ++ tailWord_78659) baseStart_78659 baseEnd_78659 := by
    simpa [prefixWord, tailWord_78659, baseEnd_78659] using wordTrace_append hprefix tailTrace_78659
  have hstable : (prefixWord ++ tailWord_78659).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78659).length < 2 ^ (prefixWord ++ tailWord_78659).sum := by decide
  have hdescent : baseEnd_78659 < baseStart_78659 := by decide
  rcases family_descends (prefixWord ++ tailWord_78659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78759 : List Nat := [1, 1, 6, 1, 4, 7]
def baseStart_78759 : Nat := 118140960795 + 78759 * 2 ^ 59
def prefixEnd_78759 : Nat := 4983230072969 + 3 ^ 40 * 78759 * 2
def baseEnd_78759 : Nat := 1331398283705764238693

theorem tailTrace_78759 : CollatzResearch.WordTrace tailWord_78759 prefixEnd_78759 1331398283705764238693 := by
  unfold tailWord_78759
  simp only [CollatzResearch.WordTrace]
  refine ⟨2872576721677068811423331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1915051147784712540948887 2872576721677068811423331)
  ·
    refine ⟨4308865082515603217134997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2872576721677068811423331 4308865082515603217134997)
    ·
      refine ⟨201978050742918900803203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 4308865082515603217134997 201978050742918900803203)
      ·
        refine ⟨302967076114378351204805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201978050742918900803203 302967076114378351204805)
        ·
          refine ⟨56806326771445940850901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 302967076114378351204805 56806326771445940850901)
          ·
            refine ⟨1331398283705764238693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 56806326771445940850901 1331398283705764238693)
            ·
              rfl

theorem cell20_78759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 7].length) (baseStart_78759 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_78759 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_78759 prefixEnd_78759 := by exact prefixLift 78759
  have htrace : WordTrace (prefixWord ++ tailWord_78759) baseStart_78759 baseEnd_78759 := by
    simpa [prefixWord, tailWord_78759, baseEnd_78759] using wordTrace_append hprefix tailTrace_78759
  have hstable : (prefixWord ++ tailWord_78759).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78759).length < 2 ^ (prefixWord ++ tailWord_78759).sum := by decide
  have hdescent : baseEnd_78759 < baseStart_78759 := by decide
  rcases family_descends (prefixWord ++ tailWord_78759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78769 : List Nat := [1, 2, 2, 4, 3, 1, 1, 4, 2]
def baseStart_78769 : Nat := 118140960795 + 78769 * 2 ^ 59
def prefixEnd_78769 : Nat := 4983230072969 + 3 ^ 40 * 78769 * 2
def baseEnd_78769 : Nat := 35952317932540044111337

theorem tailTrace_78769 : CollatzResearch.WordTrace tailWord_78769 prefixEnd_78769 35952317932540044111337 := by
  unfold tailWord_78769
  simp only [CollatzResearch.WordTrace]
  refine ⟨2872941451640840519287361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1915294301093893679524907 2872941451640840519287361)
  ·
    refine ⟨2154706088730630389465521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2872941451640840519287361 2154706088730630389465521)
    ·
      refine ⟨1616029566547972792099141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2154706088730630389465521 1616029566547972792099141)
      ·
        refine ⟨303005543727744898518589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1616029566547972792099141 303005543727744898518589)
        ·
          refine ⟨113627078897904336944471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 303005543727744898518589 113627078897904336944471)
          ·
            refine ⟨170440618346856505416707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113627078897904336944471 170440618346856505416707)
            ·
              refine ⟨255660927520284758125061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170440618346856505416707 255660927520284758125061)
              ·
                refine ⟨47936423910053392148449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 255660927520284758125061 47936423910053392148449)
                ·
                  refine ⟨35952317932540044111337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47936423910053392148449 35952317932540044111337)
                  ·
                    rfl

theorem cell20_78769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 4, 2].length) (baseStart_78769 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_78769 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_78769 prefixEnd_78769 := by exact prefixLift 78769
  have htrace : WordTrace (prefixWord ++ tailWord_78769) baseStart_78769 baseEnd_78769 := by
    simpa [prefixWord, tailWord_78769, baseEnd_78769] using wordTrace_append hprefix tailTrace_78769
  have hstable : (prefixWord ++ tailWord_78769).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78769).length < 2 ^ (prefixWord ++ tailWord_78769).sum := by decide
  have hdescent : baseEnd_78769 < baseStart_78769 := by decide
  rcases family_descends (prefixWord ++ tailWord_78769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78773 : List Nat := [1, 3, 3, 2, 1, 1, 2, 3, 4]
def baseStart_78773 : Nat := 118140960795 + 78773 * 2 ^ 59
def prefixEnd_78773 : Nat := 4983230072969 + 3 ^ 40 * 78773 * 2
def baseEnd_78773 : Nat := 35954143641533807977987

theorem tailTrace_78773 : CollatzResearch.WordTrace tailWord_78773 prefixEnd_78773 35954143641533807977987 := by
  unfold tailWord_78773
  simp only [CollatzResearch.WordTrace]
  refine ⟨2873087343626349202432973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1915391562417566134955315 2873087343626349202432973)
  ·
    refine ⟨1077407753859880950912365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2873087343626349202432973 1077407753859880950912365)
    ·
      refine ⟨404027907697455356592137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1077407753859880950912365 404027907697455356592137)
      ·
        refine ⟨303020930773091517444103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 404027907697455356592137 303020930773091517444103)
        ·
          refine ⟨454531396159637276166155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 303020930773091517444103 454531396159637276166155)
          ·
            refine ⟨681797094239455914249233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 454531396159637276166155 681797094239455914249233)
            ·
              refine ⟨511347820679591935686925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 681797094239455914249233 511347820679591935686925)
              ·
                refine ⟨191755432754846975882597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 511347820679591935686925 191755432754846975882597)
                ·
                  refine ⟨35954143641533807977987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 191755432754846975882597 35954143641533807977987)
                  ·
                    rfl

theorem cell20_78773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 3, 4].length) (baseStart_78773 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_78773 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_78773 prefixEnd_78773 := by exact prefixLift 78773
  have htrace : WordTrace (prefixWord ++ tailWord_78773) baseStart_78773 baseEnd_78773 := by
    simpa [prefixWord, tailWord_78773, baseEnd_78773] using wordTrace_append hprefix tailTrace_78773
  have hstable : (prefixWord ++ tailWord_78773).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78773).length < 2 ^ (prefixWord ++ tailWord_78773).sum := by decide
  have hdescent : baseEnd_78773 < baseStart_78773 := by decide
  rcases family_descends (prefixWord ++ tailWord_78773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78821 : List Nat := [1, 3, 1, 6, 1, 1, 1, 1, 5]
def baseStart_78821 : Nat := 118140960795 + 78821 * 2 ^ 59
def prefixEnd_78821 : Nat := 4983230072969 + 3 ^ 40 * 78821 * 2
def baseEnd_78821 : Nat := 35976052149458974377791

theorem tailTrace_78821 : CollatzResearch.WordTrace tailWord_78821 prefixEnd_78821 35976052149458974377791 := by
  unfold tailWord_78821
  simp only [CollatzResearch.WordTrace]
  refine ⟨2874838047452453400180317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1916558698301635600120211 2874838047452453400180317)
  ·
    refine ⟨1078064267794670025067619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2874838047452453400180317 1078064267794670025067619)
    ·
      refine ⟨1617096401692005037601429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1078064267794670025067619 1617096401692005037601429)
      ·
        refine ⟨75801393829312736137567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 1617096401692005037601429 75801393829312736137567)
        ·
          refine ⟨113702090743969104206351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75801393829312736137567 113702090743969104206351)
          ·
            refine ⟨170553136115953656309527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113702090743969104206351 170553136115953656309527)
            ·
              refine ⟨255829704173930484464291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170553136115953656309527 255829704173930484464291)
              ·
                refine ⟨383744556260895726696437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 255829704173930484464291 383744556260895726696437)
                ·
                  refine ⟨35976052149458974377791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 383744556260895726696437 35976052149458974377791)
                  ·
                    rfl

theorem cell20_78821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 1, 5].length) (baseStart_78821 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_78821 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_78821 prefixEnd_78821 := by exact prefixLift 78821
  have htrace : WordTrace (prefixWord ++ tailWord_78821) baseStart_78821 baseEnd_78821 := by
    simpa [prefixWord, tailWord_78821, baseEnd_78821] using wordTrace_append hprefix tailTrace_78821
  have hstable : (prefixWord ++ tailWord_78821).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78821).length < 2 ^ (prefixWord ++ tailWord_78821).sum := by decide
  have hdescent : baseEnd_78821 < baseStart_78821 := by decide
  rcases family_descends (prefixWord ++ tailWord_78821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
