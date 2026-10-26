import V185TrunkScan23Chunk1344

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7965168 : List Nat := [2, 1, 1, 1, 3, 3, 2, 3, 1, 3, 3]
def baseStart_7965168 : Nat := 118140960795 + 7965168 * 2 ^ 59
def prefixEnd_7965168 : Nat := 4983230072969 + 3 ^ 40 * 7965168 * 2
def baseEnd_7965168 : Nat := 4089959677811397477268865

theorem tailTrace_7965168 : CollatzResearch.WordTrace tailWord_7965168 prefixEnd_7965168 4089959677811397477268865 := by
  unfold tailWord_7965168
  simp only [CollatzResearch.WordTrace]
  refine ⟨145256771803782076618560079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193675695738376102158080105 145256771803782076618560079)
  ·
    refine ⟨217885157705673114927840119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145256771803782076618560079 217885157705673114927840119)
    ·
      refine ⟨326827736558509672391760179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217885157705673114927840119 326827736558509672391760179)
      ·
        refine ⟨490241604837764508587640269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326827736558509672391760179 490241604837764508587640269)
        ·
          refine ⟨183840601814161690720365101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 490241604837764508587640269 183840601814161690720365101)
          ·
            refine ⟨68940225680310634020136913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183840601814161690720365101 68940225680310634020136913)
            ·
              refine ⟨51705169260232975515102685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68940225680310634020136913 51705169260232975515102685)
              ·
                refine ⟨19389438472587365818163507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51705169260232975515102685 19389438472587365818163507)
                ·
                  refine ⟨29084157708881048727245261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19389438472587365818163507 29084157708881048727245261)
                  ·
                    refine ⟨10906559140830393272716973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29084157708881048727245261 10906559140830393272716973)
                    ·
                      refine ⟨4089959677811397477268865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10906559140830393272716973 4089959677811397477268865)
                      ·
                        rfl

theorem cell23_7965168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 3, 1, 3, 3].length) (baseStart_7965168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7965168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7965168 prefixEnd_7965168 := by exact prefixLift 7965168
  have htrace : WordTrace (prefixWord ++ tailWord_7965168) baseStart_7965168 baseEnd_7965168 := by
    simpa [prefixWord, tailWord_7965168, baseEnd_7965168] using wordTrace_append hprefix tailTrace_7965168
  have hstable : (prefixWord ++ tailWord_7965168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7965168).length < 2 ^ (prefixWord ++ tailWord_7965168).sum := by decide
  have hdescent : baseEnd_7965168 < baseStart_7965168 := by decide
  rcases family_descends (prefixWord ++ tailWord_7965168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7965185 : List Nat := [1, 2, 4, 1, 3, 2, 1, 2, 1, 3, 3]
def baseStart_7965185 : Nat := 118140960795 + 7965185 * 2 ^ 59
def prefixEnd_7965185 : Nat := 4983230072969 + 3 ^ 40 * 7965185 * 2
def baseEnd_7965185 : Nat := 4089968406982523910756287

theorem tailTrace_7965185 : CollatzResearch.WordTrace tailWord_7965185 prefixEnd_7965185 4089968406982523910756287 := by
  unfold tailWord_7965185
  simp only [CollatzResearch.WordTrace]
  refine ⟨290514163648502565140489009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193676109099001710093659339 290514163648502565140489009)
  ·
    refine ⟨217885622736376923855366757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290514163648502565140489009 217885622736376923855366757)
    ·
      refine ⟨40853554263070673222881267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 217885622736376923855366757 40853554263070673222881267)
      ·
        refine ⟨61280331394606009834321901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40853554263070673222881267 61280331394606009834321901)
        ·
          refine ⟨22980124272977253687870713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61280331394606009834321901 22980124272977253687870713)
          ·
            refine ⟨17235093204732940265903035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22980124272977253687870713 17235093204732940265903035)
            ·
              refine ⟨25852639807099410398854553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17235093204732940265903035 25852639807099410398854553)
              ·
                refine ⟨19389479855324557799140915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25852639807099410398854553 19389479855324557799140915)
                ·
                  refine ⟨29084219782986836698711373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19389479855324557799140915 29084219782986836698711373)
                  ·
                    refine ⟨10906582418620063762016765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29084219782986836698711373 10906582418620063762016765)
                    ·
                      refine ⟨4089968406982523910756287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10906582418620063762016765 4089968406982523910756287)
                      ·
                        rfl

theorem cell23_7965185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 2, 1, 3, 3].length) (baseStart_7965185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7965185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7965185 prefixEnd_7965185 := by exact prefixLift 7965185
  have htrace : WordTrace (prefixWord ++ tailWord_7965185) baseStart_7965185 baseEnd_7965185 := by
    simpa [prefixWord, tailWord_7965185, baseEnd_7965185] using wordTrace_append hprefix tailTrace_7965185
  have hstable : (prefixWord ++ tailWord_7965185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7965185).length < 2 ^ (prefixWord ++ tailWord_7965185).sum := by decide
  have hdescent : baseEnd_7965185 < baseStart_7965185 := by decide
  rcases family_descends (prefixWord ++ tailWord_7965185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7965208 : List Nat := [2, 1, 2, 3, 3, 1, 1, 1, 2, 3, 4]
def baseStart_7965208 : Nat := 118140960795 + 7965208 * 2 ^ 59
def prefixEnd_7965208 : Nat := 4983230072969 + 3 ^ 40 * 7965208 * 2
def baseEnd_7965208 : Nat := 4089980217037577320768681

theorem tailTrace_7965208 : CollatzResearch.WordTrace tailWord_7965208 prefixEnd_7965208 4089980217037577320768681 := by
  unfold tailWord_7965208
  simp only [CollatzResearch.WordTrace]
  refine ⟨145257501263709620034288139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193676668351612826712384185 145257501263709620034288139)
  ·
    refine ⟨217886251895564430051432209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145257501263709620034288139 217886251895564430051432209)
    ·
      refine ⟨163414688921673322538574157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217886251895564430051432209 163414688921673322538574157)
      ·
        refine ⟨61280508345627495951965309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163414688921673322538574157 61280508345627495951965309)
        ·
          refine ⟨22980190629610310981986991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61280508345627495951965309 22980190629610310981986991)
          ·
            refine ⟨34470285944415466472980487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22980190629610310981986991 34470285944415466472980487)
            ·
              refine ⟨51705428916623199709470731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34470285944415466472980487 51705428916623199709470731)
              ·
                refine ⟨77558143374934799564206097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51705428916623199709470731 77558143374934799564206097)
                ·
                  refine ⟨58168607531201099673154573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77558143374934799564206097 58168607531201099673154573)
                  ·
                    refine ⟨21813227824200412377432965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58168607531201099673154573 21813227824200412377432965)
                    ·
                      refine ⟨4089980217037577320768681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21813227824200412377432965 4089980217037577320768681)
                      ·
                        rfl

theorem cell23_7965208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_7965208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7965208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7965208 prefixEnd_7965208 := by exact prefixLift 7965208
  have htrace : WordTrace (prefixWord ++ tailWord_7965208) baseStart_7965208 baseEnd_7965208 := by
    simpa [prefixWord, tailWord_7965208, baseEnd_7965208] using wordTrace_append hprefix tailTrace_7965208
  have hstable : (prefixWord ++ tailWord_7965208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7965208).length < 2 ^ (prefixWord ++ tailWord_7965208).sum := by decide
  have hdescent : baseEnd_7965208 < baseStart_7965208 := by decide
  rcases family_descends (prefixWord ++ tailWord_7965208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7965246 : List Nat := [4, 2, 1, 4, 1, 1, 1, 3, 1, 3, 2]
def baseStart_7965246 : Nat := 118140960795 + 7965246 * 2 ^ 59
def prefixEnd_7965246 : Nat := 4983230072969 + 3 ^ 40 * 7965246 * 2
def baseEnd_7965246 : Nat := 4089999729302448172093507

theorem tailTrace_7965246 : CollatzResearch.WordTrace tailWord_7965246 prefixEnd_7965246 4089999729302448172093507 := by
  unfold tailWord_7965246
  simp only [CollatzResearch.WordTrace]
  refine ⟨36314548562660196569807449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193677592334187715038973061 36314548562660196569807449)
  ·
    refine ⟨27235911421995147427355587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36314548562660196569807449 27235911421995147427355587)
    ·
      refine ⟨40853867132992721141033381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27235911421995147427355587 40853867132992721141033381)
      ·
        refine ⟨7660100087436135213943759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40853867132992721141033381 7660100087436135213943759)
        ·
          refine ⟨11490150131154202820915639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7660100087436135213943759 11490150131154202820915639)
          ·
            refine ⟨17235225196731304231373459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11490150131154202820915639 17235225196731304231373459)
            ·
              refine ⟨25852837795096956347060189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17235225196731304231373459 25852837795096956347060189)
              ·
                refine ⟨9694814173161358630147571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25852837795096956347060189 9694814173161358630147571)
                ·
                  refine ⟨14542221259742037945221357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9694814173161358630147571 14542221259742037945221357)
                  ·
                    refine ⟨5453332972403264229458009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14542221259742037945221357 5453332972403264229458009)
                    ·
                      refine ⟨4089999729302448172093507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5453332972403264229458009 4089999729302448172093507)
                      ·
                        rfl

theorem cell23_7965246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_7965246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7965246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7965246 prefixEnd_7965246 := by exact prefixLift 7965246
  have htrace : WordTrace (prefixWord ++ tailWord_7965246) baseStart_7965246 baseEnd_7965246 := by
    simpa [prefixWord, tailWord_7965246, baseEnd_7965246] using wordTrace_append hprefix tailTrace_7965246
  have hstable : (prefixWord ++ tailWord_7965246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7965246).length < 2 ^ (prefixWord ++ tailWord_7965246).sum := by decide
  have hdescent : baseEnd_7965246 < baseStart_7965246 := by decide
  rcases family_descends (prefixWord ++ tailWord_7965246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7965265 : List Nat := [1, 2, 2, 1, 3, 3, 2, 4, 5]
def baseStart_7965265 : Nat := 118140960795 + 7965265 * 2 ^ 59
def prefixEnd_7965265 : Nat := 4983230072969 + 3 ^ 40 * 7965265 * 2
def baseEnd_7965265 : Nat := 454445498381653733083991

theorem tailTrace_7965265 : CollatzResearch.WordTrace tailWord_7965265 prefixEnd_7965265 454445498381653733083991 := by
  unfold tailWord_7965265
  simp only [CollatzResearch.WordTrace]
  refine ⟨290517081488212738803401249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193678054325475159202267499 290517081488212738803401249)
  ·
    refine ⟨217887811116159554102550937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290517081488212738803401249 217887811116159554102550937)
    ·
      refine ⟨163415858337119665576913203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217887811116159554102550937 163415858337119665576913203)
      ·
        refine ⟨245123787505679498365369805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163415858337119665576913203 245123787505679498365369805)
        ·
          refine ⟨91921420314629811887013677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 245123787505679498365369805 91921420314629811887013677)
          ·
            refine ⟨34470532617986179457630129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91921420314629811887013677 34470532617986179457630129)
            ·
              refine ⟨25852899463489634593222597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34470532617986179457630129 25852899463489634593222597)
              ·
                refine ⟨4847418649404306486229237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25852899463489634593222597 4847418649404306486229237)
                ·
                  refine ⟨454445498381653733083991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4847418649404306486229237 454445498381653733083991)
                  ·
                    rfl

theorem cell23_7965265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 4, 5].length) (baseStart_7965265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7965265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7965265 prefixEnd_7965265 := by exact prefixLift 7965265
  have htrace : WordTrace (prefixWord ++ tailWord_7965265) baseStart_7965265 baseEnd_7965265 := by
    simpa [prefixWord, tailWord_7965265, baseEnd_7965265] using wordTrace_append hprefix tailTrace_7965265
  have hstable : (prefixWord ++ tailWord_7965265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7965265).length < 2 ^ (prefixWord ++ tailWord_7965265).sum := by decide
  have hdescent : baseEnd_7965265 < baseStart_7965265 := by decide
  rcases family_descends (prefixWord ++ tailWord_7965265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7965276 : List Nat := [2, 2, 4, 1, 4, 1, 1, 1, 1, 4, 2]
def baseStart_7965276 : Nat := 118140960795 + 7965276 * 2 ^ 59
def prefixEnd_7965276 : Nat := 4983230072969 + 3 ^ 40 * 7965276 * 2
def baseEnd_7965276 : Nat := 4090015133722083054718369

theorem tailTrace_7965276 : CollatzResearch.WordTrace tailWord_7965276 prefixEnd_7965276 4090015133722083054718369 := by
  unfold tailWord_7965276
  simp only [CollatzResearch.WordTrace]
  refine ⟨145258741345586443841025841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193678321794115258454701121 145258741345586443841025841)
  ·
    refine ⟨108944056009189832880769381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145258741345586443841025841 108944056009189832880769381)
    ·
      refine ⟨20427010501723093665144259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108944056009189832880769381 20427010501723093665144259)
      ·
        refine ⟨30640515752584640497716389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20427010501723093665144259 30640515752584640497716389)
        ·
          refine ⟨5745096703609620093321823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30640515752584640497716389 5745096703609620093321823)
          ·
            refine ⟨8617645055414430139982735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5745096703609620093321823 8617645055414430139982735)
            ·
              refine ⟨12926467583121645209974103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8617645055414430139982735 12926467583121645209974103)
              ·
                refine ⟨19389701374682467814961155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12926467583121645209974103 19389701374682467814961155)
                ·
                  refine ⟨29084552062023701722441733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19389701374682467814961155 29084552062023701722441733)
                  ·
                    refine ⟨5453353511629444072957825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29084552062023701722441733 5453353511629444072957825)
                    ·
                      refine ⟨4090015133722083054718369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5453353511629444072957825 4090015133722083054718369)
                      ·
                        rfl

theorem cell23_7965276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 1, 1, 4, 2].length) (baseStart_7965276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7965276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7965276 prefixEnd_7965276 := by exact prefixLift 7965276
  have htrace : WordTrace (prefixWord ++ tailWord_7965276) baseStart_7965276 baseEnd_7965276 := by
    simpa [prefixWord, tailWord_7965276, baseEnd_7965276] using wordTrace_append hprefix tailTrace_7965276
  have hstable : (prefixWord ++ tailWord_7965276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7965276).length < 2 ^ (prefixWord ++ tailWord_7965276).sum := by decide
  have hdescent : baseEnd_7965276 < baseStart_7965276 := by decide
  rcases family_descends (prefixWord ++ tailWord_7965276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7965315 : List Nat := [1, 1, 1, 3, 3, 1, 2, 1, 4, 4, 2]
def baseStart_7965315 : Nat := 118140960795 + 7965315 * 2 ^ 59
def prefixEnd_7965315 : Nat := 4983230072969 + 3 ^ 40 * 7965315 * 2
def baseEnd_7965315 : Nat := 4090035159467608402130689

theorem tailTrace_7965315 : CollatzResearch.WordTrace tailWord_7965315 prefixEnd_7965315 4090035159467608402130689 := by
  unfold tailWord_7965315
  simp only [CollatzResearch.WordTrace]
  refine ⟨290518905138031597342721399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193679270092021064895147599 290518905138031597342721399)
  ·
    refine ⟨435778357707047396014082099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290518905138031597342721399 435778357707047396014082099)
    ·
      refine ⟨653667536560571094021123149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435778357707047396014082099 653667536560571094021123149)
      ·
        refine ⟨245125326210214160257921181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 653667536560571094021123149 245125326210214160257921181)
        ·
          refine ⟨91921997328830310096720443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 245125326210214160257921181 91921997328830310096720443)
          ·
            refine ⟨137882995993245465145080665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91921997328830310096720443 137882995993245465145080665)
            ·
              refine ⟨103412246994934098858810499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137882995993245465145080665 103412246994934098858810499)
              ·
                refine ⟨155118370492401148288215749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103412246994934098858810499 155118370492401148288215749)
                ·
                  refine ⟨29084694467325215304040453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 155118370492401148288215749 29084694467325215304040453)
                  ·
                    refine ⟨5453380212623477869507585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29084694467325215304040453 5453380212623477869507585)
                    ·
                      refine ⟨4090035159467608402130689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5453380212623477869507585 4090035159467608402130689)
                      ·
                        rfl

theorem cell23_7965315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 4, 4, 2].length) (baseStart_7965315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7965315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7965315 prefixEnd_7965315 := by exact prefixLift 7965315
  have htrace : WordTrace (prefixWord ++ tailWord_7965315) baseStart_7965315 baseEnd_7965315 := by
    simpa [prefixWord, tailWord_7965315, baseEnd_7965315] using wordTrace_append hprefix tailTrace_7965315
  have hstable : (prefixWord ++ tailWord_7965315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7965315).length < 2 ^ (prefixWord ++ tailWord_7965315).sum := by decide
  have hdescent : baseEnd_7965315 < baseStart_7965315 := by decide
  rcases family_descends (prefixWord ++ tailWord_7965315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7965335 : List Nat := [1, 1, 3, 3, 2, 1, 1, 2, 4, 2, 3]
def baseStart_7965335 : Nat := 118140960795 + 7965335 * 2 ^ 59
def prefixEnd_7965335 : Nat := 4983230072969 + 3 ^ 40 * 7965335 * 2
def baseEnd_7965335 : Nat := 4090045429080698323880597

theorem tailTrace_7965335 : CollatzResearch.WordTrace tailWord_7965335 prefixEnd_7965335 4090045429080698323880597 := by
  unfold tailWord_7965335
  simp only [CollatzResearch.WordTrace]
  refine ⟨290519634597959140758449459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193679756398639427172299639 290519634597959140758449459)
  ·
    refine ⟨435779451896938711137674189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290519634597959140758449459 435779451896938711137674189)
    ·
      refine ⟨163417294461352016676627821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 435779451896938711137674189 163417294461352016676627821)
      ·
        refine ⟨61281485423007006253735433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163417294461352016676627821 61281485423007006253735433)
        ·
          refine ⟨45961114067255254690301575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61281485423007006253735433 45961114067255254690301575)
          ·
            refine ⟨68941671100882882035452363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45961114067255254690301575 68941671100882882035452363)
            ·
              refine ⟨103412506651324323053178545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68941671100882882035452363 103412506651324323053178545)
              ·
                refine ⟨77559379988493242289883909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103412506651324323053178545 77559379988493242289883909)
                ·
                  refine ⟨14542383747842482929353233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77559379988493242289883909 14542383747842482929353233)
                  ·
                    refine ⟨10906787810881862197014925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14542383747842482929353233 10906787810881862197014925)
                    ·
                      refine ⟨4090045429080698323880597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10906787810881862197014925 4090045429080698323880597)
                      ·
                        rfl

theorem cell23_7965335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 4, 2, 3].length) (baseStart_7965335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7965335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7965335 prefixEnd_7965335 := by exact prefixLift 7965335
  have htrace : WordTrace (prefixWord ++ tailWord_7965335) baseStart_7965335 baseEnd_7965335 := by
    simpa [prefixWord, tailWord_7965335, baseEnd_7965335] using wordTrace_append hprefix tailTrace_7965335
  have hstable : (prefixWord ++ tailWord_7965335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7965335).length < 2 ^ (prefixWord ++ tailWord_7965335).sum := by decide
  have hdescent : baseEnd_7965335 < baseStart_7965335 := by decide
  rcases family_descends (prefixWord ++ tailWord_7965335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7965342 : List Nat := [4, 3, 1, 1, 1, 1, 2, 1, 5, 4]
def baseStart_7965342 : Nat := 118140960795 + 7965342 * 2 ^ 59
def prefixEnd_7965342 : Nat := 4983230072969 + 3 ^ 40 * 7965342 * 2
def baseEnd_7965342 : Nat := 1363349674481759932164355

theorem tailTrace_7965342 : CollatzResearch.WordTrace tailWord_7965342 prefixEnd_7965342 1363349674481759932164355 := by
  unfold tailWord_7965342
  simp only [CollatzResearch.WordTrace]
  refine ⟨36314986238616722619244285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193679926605955853969302853 36314986238616722619244285)
  ·
    refine ⟨13618119839481270982216607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36314986238616722619244285 13618119839481270982216607)
    ·
      refine ⟨20427179759221906473324911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13618119839481270982216607 20427179759221906473324911)
      ·
        refine ⟨30640769638832859709987367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20427179759221906473324911 30640769638832859709987367)
        ·
          refine ⟨45961154458249289564981051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30640769638832859709987367 45961154458249289564981051)
          ·
            refine ⟨68941731687373934347471577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45961154458249289564981051 68941731687373934347471577)
            ·
              refine ⟨51706298765530450760603683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68941731687373934347471577 51706298765530450760603683)
              ·
                refine ⟨77559448148295676140905525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51706298765530450760603683 77559448148295676140905525)
                ·
                  refine ⟨7271198263902719638209893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77559448148295676140905525 7271198263902719638209893)
                  ·
                    refine ⟨1363349674481759932164355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7271198263902719638209893 1363349674481759932164355)
                    ·
                      rfl

theorem cell23_7965342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_7965342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7965342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7965342 prefixEnd_7965342 := by exact prefixLift 7965342
  have htrace : WordTrace (prefixWord ++ tailWord_7965342) baseStart_7965342 baseEnd_7965342 := by
    simpa [prefixWord, tailWord_7965342, baseEnd_7965342] using wordTrace_append hprefix tailTrace_7965342
  have hstable : (prefixWord ++ tailWord_7965342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7965342).length < 2 ^ (prefixWord ++ tailWord_7965342).sum := by decide
  have hdescent : baseEnd_7965342 < baseStart_7965342 := by decide
  rcases family_descends (prefixWord ++ tailWord_7965342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7965376 : List Nat := [2, 1, 1, 2, 4, 4, 2, 2, 1, 4]
def baseStart_7965376 : Nat := 118140960795 + 7965376 * 2 ^ 59
def prefixEnd_7965376 : Nat := 4983230072969 + 3 ^ 40 * 7965376 * 2
def baseEnd_7965376 : Nat := 1363355493929177554489303

theorem tailTrace_7965376 : CollatzResearch.WordTrace tailWord_7965376 prefixEnd_7965376 1363355493929177554489303 := by
  unfold tailWord_7965376
  simp only [CollatzResearch.WordTrace]
  refine ⟨145260564995405302380345991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193680753327207069840461321 145260564995405302380345991)
  ·
    refine ⟨217890847493107953570518987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145260564995405302380345991 217890847493107953570518987)
    ·
      refine ⟨326836271239661930355778481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217890847493107953570518987 326836271239661930355778481)
      ·
        refine ⟨245127203429746447766833861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 326836271239661930355778481 245127203429746447766833861)
        ·
          refine ⟨45961350643077458956281349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 245127203429746447766833861 45961350643077458956281349)
          ·
            refine ⟨8617753245577023554302753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45961350643077458956281349 8617753245577023554302753)
            ·
              refine ⟨6463314934182767665727065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8617753245577023554302753 6463314934182767665727065)
              ·
                refine ⟨4847486200637075749295299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6463314934182767665727065 4847486200637075749295299)
                ·
                  refine ⟨7271229300955613623942949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4847486200637075749295299 7271229300955613623942949)
                  ·
                    refine ⟨1363355493929177554489303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7271229300955613623942949 1363355493929177554489303)
                    ·
                      rfl

theorem cell23_7965376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 2, 2, 1, 4].length) (baseStart_7965376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7965376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7965376 prefixEnd_7965376 := by exact prefixLift 7965376
  have htrace : WordTrace (prefixWord ++ tailWord_7965376) baseStart_7965376 baseEnd_7965376 := by
    simpa [prefixWord, tailWord_7965376, baseEnd_7965376] using wordTrace_append hprefix tailTrace_7965376
  have hstable : (prefixWord ++ tailWord_7965376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7965376).length < 2 ^ (prefixWord ++ tailWord_7965376).sum := by decide
  have hdescent : baseEnd_7965376 < baseStart_7965376 := by decide
  rcases family_descends (prefixWord ++ tailWord_7965376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7965409 : List Nat := [1, 2, 3, 1, 4, 1, 3, 1, 2, 3, 2]
def baseStart_7965409 : Nat := 118140960795 + 7965409 * 2 ^ 59
def prefixEnd_7965409 : Nat := 4983230072969 + 3 ^ 40 * 7965409 * 2
def baseEnd_7965409 : Nat := 4090083426649131034355257

theorem tailTrace_7965409 : CollatzResearch.WordTrace tailWord_7965409 prefixEnd_7965409 4090083426649131034355257 := by
  unfold tailWord_7965409
  simp only [CollatzResearch.WordTrace]
  refine ⟨290522333599691051396643281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193681555733127367597762187 290522333599691051396643281)
  ·
    refine ⟨217891750199768288547482461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290522333599691051396643281 217891750199768288547482461)
    ·
      refine ⟨81709406324913108205305923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217891750199768288547482461 81709406324913108205305923)
      ·
        refine ⟨122564109487369662307958885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81709406324913108205305923 122564109487369662307958885)
        ·
          refine ⟨22980770528881811682742291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122564109487369662307958885 22980770528881811682742291)
          ·
            refine ⟨34471155793322717524113437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22980770528881811682742291 34471155793322717524113437)
            ·
              refine ⟨12926683422496019071542539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34471155793322717524113437 12926683422496019071542539)
              ·
                refine ⟨19390025133744028607313809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12926683422496019071542539 19390025133744028607313809)
                ·
                  refine ⟨14542518850308021455485357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19390025133744028607313809 14542518850308021455485357)
                  ·
                    refine ⟨5453444568865508045807009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14542518850308021455485357 5453444568865508045807009)
                    ·
                      refine ⟨4090083426649131034355257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5453444568865508045807009 4090083426649131034355257)
                      ·
                        rfl

theorem cell23_7965409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 1, 2, 3, 2].length) (baseStart_7965409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7965409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7965409 prefixEnd_7965409 := by exact prefixLift 7965409
  have htrace : WordTrace (prefixWord ++ tailWord_7965409) baseStart_7965409 baseEnd_7965409 := by
    simpa [prefixWord, tailWord_7965409, baseEnd_7965409] using wordTrace_append hprefix tailTrace_7965409
  have hstable : (prefixWord ++ tailWord_7965409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7965409).length < 2 ^ (prefixWord ++ tailWord_7965409).sum := by decide
  have hdescent : baseEnd_7965409 < baseStart_7965409 := by decide
  rcases family_descends (prefixWord ++ tailWord_7965409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7965425 : List Nat := [1, 2, 2, 2, 2, 2, 2, 3, 1, 1, 5]
def baseStart_7965425 : Nat := 118140960795 + 7965425 * 2 ^ 59
def prefixEnd_7965425 : Nat := 4983230072969 + 3 ^ 40 * 7965425 * 2
def baseEnd_7965425 : Nat := 4090091642339602971755183

theorem tailTrace_7965425 : CollatzResearch.WordTrace tailWord_7965425 prefixEnd_7965425 4090091642339602971755183 := by
  unfold tailWord_7965425
  simp only [CollatzResearch.WordTrace]
  refine ⟨290522917167633086129225729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193681944778422057419483819 290522917167633086129225729)
  ·
    refine ⟨217892187875724814596919297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290522917167633086129225729 217892187875724814596919297)
    ·
      refine ⟨163419140906793610947689473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217892187875724814596919297 163419140906793610947689473)
      ·
        refine ⟨122564355680095208210767105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163419140906793610947689473 122564355680095208210767105)
        ·
          refine ⟨91923266760071406158075329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122564355680095208210767105 91923266760071406158075329)
          ·
            refine ⟨68942450070053554618556497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91923266760071406158075329 68942450070053554618556497)
            ·
              refine ⟨51706837552540165963917373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68942450070053554618556497 51706837552540165963917373)
              ·
                refine ⟨19390064082202562236469015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51706837552540165963917373 19390064082202562236469015)
                ·
                  refine ⟨29085096123303843354703523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19390064082202562236469015 29085096123303843354703523)
                  ·
                    refine ⟨43627644184955765032055285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29085096123303843354703523 43627644184955765032055285)
                    ·
                      refine ⟨4090091642339602971755183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43627644184955765032055285 4090091642339602971755183)
                      ·
                        rfl

theorem cell23_7965425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 1, 1, 5].length) (baseStart_7965425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7965425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7965425 prefixEnd_7965425 := by exact prefixLift 7965425
  have htrace : WordTrace (prefixWord ++ tailWord_7965425) baseStart_7965425 baseEnd_7965425 := by
    simpa [prefixWord, tailWord_7965425, baseEnd_7965425] using wordTrace_append hprefix tailTrace_7965425
  have hstable : (prefixWord ++ tailWord_7965425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7965425).length < 2 ^ (prefixWord ++ tailWord_7965425).sum := by decide
  have hdescent : baseEnd_7965425 < baseStart_7965425 := by decide
  rcases family_descends (prefixWord ++ tailWord_7965425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7965442 : List Nat := [3, 4, 1, 1, 1, 2, 1, 1, 3, 1, 5]
def baseStart_7965442 : Nat := 118140960795 + 7965442 * 2 ^ 59
def prefixEnd_7965442 : Nat := 4983230072969 + 3 ^ 40 * 7965442 * 2
def baseEnd_7965442 : Nat := 4090100371510729405242605

theorem tailTrace_7965442 : CollatzResearch.WordTrace tailWord_7965442 prefixEnd_7965442 4090100371510729405242605 := by
  unfold tailWord_7965442
  simp only [CollatzResearch.WordTrace]
  refine ⟨72630884302142874508148645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193682358139047665355063053 72630884302142874508148645)
  ·
    refine ⟨13618290806651788970277871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72630884302142874508148645 13618290806651788970277871)
    ·
      refine ⟨20427436209977683455416807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13618290806651788970277871 20427436209977683455416807)
      ·
        refine ⟨30641154314966525183125211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20427436209977683455416807 30641154314966525183125211)
        ·
          refine ⟨45961731472449787774687817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30641154314966525183125211 45961731472449787774687817)
          ·
            refine ⟨34471298604337340831015863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45961731472449787774687817 34471298604337340831015863)
            ·
              refine ⟨51706947906506011246523795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34471298604337340831015863 51706947906506011246523795)
              ·
                refine ⟨77560421859759016869785693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51706947906506011246523795 77560421859759016869785693)
                ·
                  refine ⟨29085158197409631326169635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77560421859759016869785693 29085158197409631326169635)
                  ·
                    refine ⟨43627737296114446989254453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29085158197409631326169635 43627737296114446989254453)
                    ·
                      refine ⟨4090100371510729405242605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43627737296114446989254453 4090100371510729405242605)
                      ·
                        rfl

theorem cell23_7965442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_7965442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7965442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7965442 prefixEnd_7965442 := by exact prefixLift 7965442
  have htrace : WordTrace (prefixWord ++ tailWord_7965442) baseStart_7965442 baseEnd_7965442 := by
    simpa [prefixWord, tailWord_7965442, baseEnd_7965442] using wordTrace_append hprefix tailTrace_7965442
  have hstable : (prefixWord ++ tailWord_7965442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7965442).length < 2 ^ (prefixWord ++ tailWord_7965442).sum := by decide
  have hdescent : baseEnd_7965442 < baseStart_7965442 := by decide
  rcases family_descends (prefixWord ++ tailWord_7965442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7965489 : List Nat := [1, 2, 2, 3, 2, 1, 2, 4, 2, 1, 3]
def baseStart_7965489 : Nat := 118140960795 + 7965489 * 2 ^ 59
def prefixEnd_7965489 : Nat := 4983230072969 + 3 ^ 40 * 7965489 * 2
def baseEnd_7965489 : Nat := 4090124505101490721354889

theorem tailTrace_7965489 : CollatzResearch.WordTrace tailWord_7965489 prefixEnd_7965489 4090124505101490721354889 := by
  unfold tailWord_7965489
  simp only [CollatzResearch.WordTrace]
  refine ⟨290525251439401225059555521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193683500959600816706370347 290525251439401225059555521)
  ·
    refine ⟨217893938579550918794666641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290525251439401225059555521 217893938579550918794666641)
    ·
      refine ⟨163420453934663189095999981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217893938579550918794666641 163420453934663189095999981)
      ·
        refine ⟨61282670225498695910999993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163420453934663189095999981 61282670225498695910999993)
        ·
          refine ⟨45962002669124021933249995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61282670225498695910999993 45962002669124021933249995)
          ·
            refine ⟨68943004003686032899874993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45962002669124021933249995 68943004003686032899874993)
            ·
              refine ⟨51707253002764524674906245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68943004003686032899874993 51707253002764524674906245)
              ·
                refine ⟨9695109938018348376544921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51707253002764524674906245 9695109938018348376544921)
                ·
                  refine ⟨7271332453513761282408691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9695109938018348376544921 7271332453513761282408691)
                  ·
                    refine ⟨10906998680270641923613037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7271332453513761282408691 10906998680270641923613037)
                    ·
                      refine ⟨4090124505101490721354889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10906998680270641923613037 4090124505101490721354889)
                      ·
                        rfl

theorem cell23_7965489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 4, 2, 1, 3].length) (baseStart_7965489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7965489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7965489 prefixEnd_7965489 := by exact prefixLift 7965489
  have htrace : WordTrace (prefixWord ++ tailWord_7965489) baseStart_7965489 baseEnd_7965489 := by
    simpa [prefixWord, tailWord_7965489, baseEnd_7965489] using wordTrace_append hprefix tailTrace_7965489
  have hstable : (prefixWord ++ tailWord_7965489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7965489).length < 2 ^ (prefixWord ++ tailWord_7965489).sum := by decide
  have hdescent : baseEnd_7965489 < baseStart_7965489 := by decide
  rcases family_descends (prefixWord ++ tailWord_7965489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7965495 : List Nat := [1, 1, 3, 1, 2, 1, 4, 1, 2, 3, 4]
def baseStart_7965495 : Nat := 118140960795 + 7965495 * 2 ^ 59
def prefixEnd_7965495 : Nat := 4983230072969 + 3 ^ 40 * 7965495 * 2
def baseEnd_7965495 : Nat := 4090127585985417697879861

theorem tailTrace_7965495 : CollatzResearch.WordTrace tailWord_7965495 prefixEnd_7965495 4090127585985417697879861 := by
  unfold tailWord_7965495
  simp only [CollatzResearch.WordTrace]
  refine ⟨290525470277379488084273939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193683646851586325389515959 290525470277379488084273939)
  ·
    refine ⟨435788205416069232126410909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290525470277379488084273939 435788205416069232126410909)
    ·
      refine ⟨163420577031025962047404091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 435788205416069232126410909 163420577031025962047404091)
      ·
        refine ⟨245130865546538943071106137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163420577031025962047404091 245130865546538943071106137)
        ·
          refine ⟨183848149159904207303329603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245130865546538943071106137 183848149159904207303329603)
          ·
            refine ⟨275772223739856310954994405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183848149159904207303329603 275772223739856310954994405)
            ·
              refine ⟨51707291951223058304061451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 275772223739856310954994405 51707291951223058304061451)
              ·
                refine ⟨77560937926834587456092177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51707291951223058304061451 77560937926834587456092177)
                ·
                  refine ⟨58170703445125940592069133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77560937926834587456092177 58170703445125940592069133)
                  ·
                    refine ⟨21814013791922227722025925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58170703445125940592069133 21814013791922227722025925)
                    ·
                      refine ⟨4090127585985417697879861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21814013791922227722025925 4090127585985417697879861)
                      ·
                        rfl

theorem cell23_7965495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 2, 3, 4].length) (baseStart_7965495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7965495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7965495 prefixEnd_7965495 := by exact prefixLift 7965495
  have htrace : WordTrace (prefixWord ++ tailWord_7965495) baseStart_7965495 baseEnd_7965495 := by
    simpa [prefixWord, tailWord_7965495, baseEnd_7965495] using wordTrace_append hprefix tailTrace_7965495
  have hstable : (prefixWord ++ tailWord_7965495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7965495).length < 2 ^ (prefixWord ++ tailWord_7965495).sum := by decide
  have hdescent : baseEnd_7965495 < baseStart_7965495 := by decide
  rcases family_descends (prefixWord ++ tailWord_7965495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7965510 : List Nat := [6, 1, 1, 2, 2, 2, 1, 2, 1, 2, 3]
def baseStart_7965510 : Nat := 118140960795 + 7965510 * 2 ^ 59
def prefixEnd_7965510 : Nat := 4983230072969 + 3 ^ 40 * 7965510 * 2
def baseEnd_7965510 : Nat := 4090135288195235139192293

theorem tailTrace_7965510 : CollatzResearch.WordTrace tailWord_7965510 prefixEnd_7965510 4090135288195235139192293 := by
  unfold tailWord_7965510
  simp only [CollatzResearch.WordTrace]
  refine ⟨9078938042885160801439687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 193684011581550097097379989 9078938042885160801439687)
  ·
    refine ⟨13618407064327741202159531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9078938042885160801439687 13618407064327741202159531)
    ·
      refine ⟨20427610596491611803239297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13618407064327741202159531 20427610596491611803239297)
      ·
        refine ⟨15320707947368708852429473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20427610596491611803239297 15320707947368708852429473)
        ·
          refine ⟨11490530960526531639322105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15320707947368708852429473 11490530960526531639322105)
          ·
            refine ⟨8617898220394898729491579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11490530960526531639322105 8617898220394898729491579)
            ·
              refine ⟨12926847330592348094237369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8617898220394898729491579 12926847330592348094237369)
              ·
                refine ⟨9695135497944261070678027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12926847330592348094237369 9695135497944261070678027)
                ·
                  refine ⟨14542703246916391606017041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9695135497944261070678027 14542703246916391606017041)
                  ·
                    refine ⟨10907027435187293704512781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14542703246916391606017041 10907027435187293704512781)
                    ·
                      refine ⟨4090135288195235139192293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10907027435187293704512781 4090135288195235139192293)
                      ·
                        rfl

theorem cell23_7965510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_7965510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7965510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7965510 prefixEnd_7965510 := by exact prefixLift 7965510
  have htrace : WordTrace (prefixWord ++ tailWord_7965510) baseStart_7965510 baseEnd_7965510 := by
    simpa [prefixWord, tailWord_7965510, baseEnd_7965510] using wordTrace_append hprefix tailTrace_7965510
  have hstable : (prefixWord ++ tailWord_7965510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7965510).length < 2 ^ (prefixWord ++ tailWord_7965510).sum := by decide
  have hdescent : baseEnd_7965510 < baseStart_7965510 := by decide
  rcases family_descends (prefixWord ++ tailWord_7965510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7965516 : List Nat := [2, 2, 1, 3, 3, 1, 3, 2, 1, 3, 2]
def baseStart_7965516 : Nat := 118140960795 + 7965516 * 2 ^ 59
def prefixEnd_7965516 : Nat := 4983230072969 + 3 ^ 40 * 7965516 * 2
def baseEnd_7965516 : Nat := 4090138369079162115717265

theorem tailTrace_7965516 : CollatzResearch.WordTrace tailWord_7965516 prefixEnd_7965516 4090138369079162115717265 := by
  unfold tailWord_7965516
  simp only [CollatzResearch.WordTrace]
  refine ⟨145263118105151704335394201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193684157473535605780525601 145263118105151704335394201)
  ·
    refine ⟨108947338578863778251545651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145263118105151704335394201 108947338578863778251545651)
    ·
      refine ⟨163421007868295667377318477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108947338578863778251545651 163421007868295667377318477)
      ·
        refine ⟨61282877950610875266494429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163421007868295667377318477 61282877950610875266494429)
        ·
          refine ⟨22981079231479078224935411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61282877950610875266494429 22981079231479078224935411)
          ·
            refine ⟨34471618847218617337403117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22981079231479078224935411 34471618847218617337403117)
            ·
              refine ⟨12926857067706981501526169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34471618847218617337403117 12926857067706981501526169)
              ·
                refine ⟨9695142800780236126144627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12926857067706981501526169 9695142800780236126144627)
                ·
                  refine ⟨14542714201170354189216941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9695142800780236126144627 14542714201170354189216941)
                  ·
                    refine ⟨5453517825438882820956353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14542714201170354189216941 5453517825438882820956353)
                    ·
                      refine ⟨4090138369079162115717265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5453517825438882820956353 4090138369079162115717265)
                      ·
                        rfl

theorem cell23_7965516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 2, 1, 3, 2].length) (baseStart_7965516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7965516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7965516 prefixEnd_7965516 := by exact prefixLift 7965516
  have htrace : WordTrace (prefixWord ++ tailWord_7965516) baseStart_7965516 baseEnd_7965516 := by
    simpa [prefixWord, tailWord_7965516, baseEnd_7965516] using wordTrace_append hprefix tailTrace_7965516
  have hstable : (prefixWord ++ tailWord_7965516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7965516).length < 2 ^ (prefixWord ++ tailWord_7965516).sum := by decide
  have hdescent : baseEnd_7965516 < baseStart_7965516 := by decide
  rcases family_descends (prefixWord ++ tailWord_7965516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7965529 : List Nat := [1, 2, 1, 2, 2, 5, 1, 2, 1, 4, 2]
def baseStart_7965529 : Nat := 118140960795 + 7965529 * 2 ^ 59
def prefixEnd_7965529 : Nat := 4983230072969 + 3 ^ 40 * 7965529 * 2
def baseEnd_7965529 : Nat := 4090145044327670564854705

theorem tailTrace_7965529 : CollatzResearch.WordTrace tailWord_7965529 prefixEnd_7965529 4090145044327670564854705 := by
  unfold tailWord_7965529
  simp only [CollatzResearch.WordTrace]
  refine ⟨290526710359256311891011641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193684473572837541260674427 290526710359256311891011641)
  ·
    refine ⟨217895032769442233918258731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290526710359256311891011641 217895032769442233918258731)
    ·
      refine ⟨326842549154163350877388097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217895032769442233918258731 326842549154163350877388097)
      ·
        refine ⟨245131911865622513158041073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 326842549154163350877388097 245131911865622513158041073)
        ·
          refine ⟨183848933899216884868530805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245131911865622513158041073 183848933899216884868530805)
          ·
            refine ⟨17235837553051582956424763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 183848933899216884868530805 17235837553051582956424763)
            ·
              refine ⟨25853756329577374434637145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17235837553051582956424763 25853756329577374434637145)
              ·
                refine ⟨19390317247183030825977859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25853756329577374434637145 19390317247183030825977859)
                ·
                  refine ⟨29085475870774546238966789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19390317247183030825977859 29085475870774546238966789)
                  ·
                    refine ⟨5453526725770227419806273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29085475870774546238966789 5453526725770227419806273)
                    ·
                      refine ⟨4090145044327670564854705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5453526725770227419806273 4090145044327670564854705)
                      ·
                        rfl

theorem cell23_7965529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 2, 1, 4, 2].length) (baseStart_7965529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7965529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7965529 prefixEnd_7965529 := by exact prefixLift 7965529
  have htrace : WordTrace (prefixWord ++ tailWord_7965529) baseStart_7965529 baseEnd_7965529 := by
    simpa [prefixWord, tailWord_7965529, baseEnd_7965529] using wordTrace_append hprefix tailTrace_7965529
  have hstable : (prefixWord ++ tailWord_7965529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7965529).length < 2 ^ (prefixWord ++ tailWord_7965529).sum := by decide
  have hdescent : baseEnd_7965529 < baseStart_7965529 := by decide
  rcases family_descends (prefixWord ++ tailWord_7965529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7965612 : List Nat := [2, 2, 1, 1, 1, 1, 2, 2, 7, 4]
def baseStart_7965612 : Nat := 118140960795 + 7965612 * 2 ^ 59
def prefixEnd_7965612 : Nat := 4983230072969 + 3 ^ 40 * 7965612 * 2
def baseEnd_7965612 : Nat := 1363395887740664580038941

theorem tailTrace_7965612 : CollatzResearch.WordTrace tailWord_7965612 prefixEnd_7965612 1363395887740664580038941 := by
  unfold tailWord_7965612
  simp only [CollatzResearch.WordTrace]
  refine ⟨145264868808977808533141545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193686491745303744710855393 145264868808977808533141545)
  ·
    refine ⟨108948651606733356399856159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145264868808977808533141545 108948651606733356399856159)
    ·
      refine ⟨163422977410100034599784239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108948651606733356399856159 163422977410100034599784239)
      ·
        refine ⟨245134466115150051899676359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163422977410100034599784239 245134466115150051899676359)
        ·
          refine ⟨367701699172725077849514539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245134466115150051899676359 367701699172725077849514539)
          ·
            refine ⟨551552548759087616774271809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 367701699172725077849514539 551552548759087616774271809)
            ·
              refine ⟨413664411569315712580703857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 551552548759087616774271809 413664411569315712580703857)
              ·
                refine ⟨310248308676986784435527893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 413664411569315712580703857 310248308676986784435527893)
                ·
                  refine ⟨7271444734616877760207685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 310248308676986784435527893 7271444734616877760207685)
                  ·
                    refine ⟨1363395887740664580038941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7271444734616877760207685 1363395887740664580038941)
                    ·
                      rfl

theorem cell23_7965612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 4].length) (baseStart_7965612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7965612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7965612 prefixEnd_7965612 := by exact prefixLift 7965612
  have htrace : WordTrace (prefixWord ++ tailWord_7965612) baseStart_7965612 baseEnd_7965612 := by
    simpa [prefixWord, tailWord_7965612, baseEnd_7965612] using wordTrace_append hprefix tailTrace_7965612
  have hstable : (prefixWord ++ tailWord_7965612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7965612).length < 2 ^ (prefixWord ++ tailWord_7965612).sum := by decide
  have hdescent : baseEnd_7965612 < baseStart_7965612 := by decide
  rcases family_descends (prefixWord ++ tailWord_7965612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7965663 : List Nat := [1, 1, 2, 3, 6, 1, 1, 1, 3, 4]
def baseStart_7965663 : Nat := 118140960795 + 7965663 * 2 ^ 59
def prefixEnd_7965663 : Nat := 4983230072969 + 3 ^ 40 * 7965663 * 2
def baseEnd_7965663 : Nat := 1363404616911791013526363

theorem tailTrace_7965663 : CollatzResearch.WordTrace tailWord_7965663 prefixEnd_7965663 1363404616911791013526363 := by
  unfold tailWord_7965663
  simp only [CollatzResearch.WordTrace]
  refine ⟨290531597740770852776389643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193687731827180568517593095 290531597740770852776389643)
  ·
    refine ⟨435797396611156279164584465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290531597740770852776389643 435797396611156279164584465)
    ·
      refine ⟨326848047458367209373438349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 435797396611156279164584465 326848047458367209373438349)
      ·
        refine ⟨122568017796887703515039381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 326848047458367209373438349 122568017796887703515039381)
        ·
          refine ⟨5745375834229111102267471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 122568017796887703515039381 5745375834229111102267471)
          ·
            refine ⟨8618063751343666653401207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5745375834229111102267471 8618063751343666653401207)
            ·
              refine ⟨12927095627015499980101811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8618063751343666653401207 12927095627015499980101811)
              ·
                refine ⟨19390643440523249970152717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12927095627015499980101811 19390643440523249970152717)
                ·
                  refine ⟨7271491290196218738807269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19390643440523249970152717 7271491290196218738807269)
                  ·
                    refine ⟨1363404616911791013526363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7271491290196218738807269 1363404616911791013526363)
                    ·
                      rfl

theorem cell23_7965663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 1, 3, 4].length) (baseStart_7965663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7965663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7965663 prefixEnd_7965663 := by exact prefixLift 7965663
  have htrace : WordTrace (prefixWord ++ tailWord_7965663) baseStart_7965663 baseEnd_7965663 := by
    simpa [prefixWord, tailWord_7965663, baseEnd_7965663] using wordTrace_append hprefix tailTrace_7965663
  have hstable : (prefixWord ++ tailWord_7965663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7965663).length < 2 ^ (prefixWord ++ tailWord_7965663).sum := by decide
  have hdescent : baseEnd_7965663 < baseStart_7965663 := by decide
  rcases family_descends (prefixWord ++ tailWord_7965663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7965703 : List Nat := [1, 1, 4, 3, 1, 1, 2, 5, 1, 1, 3]
def baseStart_7965703 : Nat := 118140960795 + 7965703 * 2 ^ 59
def prefixEnd_7965703 : Nat := 4983230072969 + 3 ^ 40 * 7965703 * 2
def baseEnd_7965703 : Nat := 4090234389961552884078905

theorem tailTrace_7965703 : CollatzResearch.WordTrace tailWord_7965703 prefixEnd_7965703 4090234389961552884078905 := by
  unfold tailWord_7965703
  simp only [CollatzResearch.WordTrace]
  refine ⟨290533056660625939607845763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193688704440417293071897175 290533056660625939607845763)
  ·
    refine ⟨435799584990938909411768645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290533056660625939607845763 435799584990938909411768645)
    ·
      refine ⟨81712422185801045514706621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 435799584990938909411768645 81712422185801045514706621)
      ·
        refine ⟨30642158319675392068014983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81712422185801045514706621 30642158319675392068014983)
        ·
          refine ⟨45963237479513088102022475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30642158319675392068014983 45963237479513088102022475)
          ·
            refine ⟨68944856219269632153033713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45963237479513088102022475 68944856219269632153033713)
            ·
              refine ⟨51708642164452224114775285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68944856219269632153033713 51708642164452224114775285)
              ·
                refine ⟨4847685202917396010760183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51708642164452224114775285 4847685202917396010760183)
                ·
                  refine ⟨7271527804376094016140275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4847685202917396010760183 7271527804376094016140275)
                  ·
                    refine ⟨10907291706564141024210413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7271527804376094016140275 10907291706564141024210413)
                    ·
                      refine ⟨4090234389961552884078905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10907291706564141024210413 4090234389961552884078905)
                      ·
                        rfl

theorem cell23_7965703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 5, 1, 1, 3].length) (baseStart_7965703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7965703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7965703 prefixEnd_7965703 := by exact prefixLift 7965703
  have htrace : WordTrace (prefixWord ++ tailWord_7965703) baseStart_7965703 baseEnd_7965703 := by
    simpa [prefixWord, tailWord_7965703, baseEnd_7965703] using wordTrace_append hprefix tailTrace_7965703
  have hstable : (prefixWord ++ tailWord_7965703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7965703).length < 2 ^ (prefixWord ++ tailWord_7965703).sum := by decide
  have hdescent : baseEnd_7965703 < baseStart_7965703 := by decide
  rcases family_descends (prefixWord ++ tailWord_7965703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7965720 : List Nat := [2, 1, 2, 3, 2, 2, 4, 2, 1, 1, 3]
def baseStart_7965720 : Nat := 118140960795 + 7965720 * 2 ^ 59
def prefixEnd_7965720 : Nat := 4983230072969 + 3 ^ 40 * 7965720 * 2
def baseEnd_7965720 : Nat := 4090243119132679317566327

theorem tailTrace_7965720 : CollatzResearch.WordTrace tailWord_7965720 prefixEnd_7965720 4090243119132679317566327 := by
  unfold tailWord_7965720
  simp only [CollatzResearch.WordTrace]
  refine ⟨145266838350782175755607307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193689117801042901007476409 145266838350782175755607307)
  ·
    refine ⟨217900257526173263633410961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145266838350782175755607307 217900257526173263633410961)
    ·
      refine ⟨163425193144629947725058221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217900257526173263633410961 163425193144629947725058221)
      ·
        refine ⟨61284447429236230396896833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163425193144629947725058221 61284447429236230396896833)
        ·
          refine ⟨45963335571927172797672625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61284447429236230396896833 45963335571927172797672625)
          ·
            refine ⟨34472501678945379598254469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45963335571927172797672625 34472501678945379598254469)
            ·
              refine ⟨6463594064802258674672713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34472501678945379598254469 6463594064802258674672713)
              ·
                refine ⟨4847695548601694006004535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6463594064802258674672713 4847695548601694006004535)
                ·
                  refine ⟨7271543322902541009006803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4847695548601694006004535 7271543322902541009006803)
                  ·
                    refine ⟨10907314984353811513510205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7271543322902541009006803 10907314984353811513510205)
                    ·
                      refine ⟨4090243119132679317566327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10907314984353811513510205 4090243119132679317566327)
                      ·
                        rfl

theorem cell23_7965720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 4, 2, 1, 1, 3].length) (baseStart_7965720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7965720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7965720 prefixEnd_7965720 := by exact prefixLift 7965720
  have htrace : WordTrace (prefixWord ++ tailWord_7965720) baseStart_7965720 baseEnd_7965720 := by
    simpa [prefixWord, tailWord_7965720, baseEnd_7965720] using wordTrace_append hprefix tailTrace_7965720
  have hstable : (prefixWord ++ tailWord_7965720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7965720).length < 2 ^ (prefixWord ++ tailWord_7965720).sum := by decide
  have hdescent : baseEnd_7965720 < baseStart_7965720 := by decide
  rcases family_descends (prefixWord ++ tailWord_7965720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7965739 : List Nat := [1, 1, 1, 1, 2, 1, 8, 1, 1, 2, 4]
def baseStart_7965739 : Nat := 118140960795 + 7965739 * 2 ^ 59
def prefixEnd_7965739 : Nat := 4983230072969 + 3 ^ 40 * 7965739 * 2
def baseEnd_7965739 : Nat := 4090252875265114743228739

theorem tailTrace_7965739 : CollatzResearch.WordTrace tailWord_7965739 prefixEnd_7965739 4090252875265114743228739 := by
  unfold tailWord_7965739
  simp only [CollatzResearch.WordTrace]
  refine ⟨290534369688495517756156271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193689579792330345170770847 290534369688495517756156271)
  ·
    refine ⟨435801554532743276634234407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290534369688495517756156271 435801554532743276634234407)
    ·
      refine ⟨653702331799114914951351611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435801554532743276634234407 653702331799114914951351611)
      ·
        refine ⟨980553497698672372427027417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 653702331799114914951351611 980553497698672372427027417)
        ·
          refine ⟨735415123274004279320270563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 980553497698672372427027417 735415123274004279320270563)
          ·
            refine ⟨1103122684911006418980405845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 735415123274004279320270563 1103122684911006418980405845)
            ·
              refine ⟨12927218963800856472426631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1103122684911006418980405845 12927218963800856472426631)
              ·
                refine ⟨19390828445701284708639947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12927218963800856472426631 19390828445701284708639947)
                ·
                  refine ⟨29086242668551927062959921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19390828445701284708639947 29086242668551927062959921)
                  ·
                    refine ⟨21814682001413945297219941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29086242668551927062959921 21814682001413945297219941)
                    ·
                      refine ⟨4090252875265114743228739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21814682001413945297219941 4090252875265114743228739)
                      ·
                        rfl

theorem cell23_7965739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 1, 1, 2, 4].length) (baseStart_7965739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7965739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7965739 prefixEnd_7965739 := by exact prefixLift 7965739
  have htrace : WordTrace (prefixWord ++ tailWord_7965739) baseStart_7965739 baseEnd_7965739 := by
    simpa [prefixWord, tailWord_7965739, baseEnd_7965739] using wordTrace_append hprefix tailTrace_7965739
  have hstable : (prefixWord ++ tailWord_7965739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7965739).length < 2 ^ (prefixWord ++ tailWord_7965739).sum := by decide
  have hdescent : baseEnd_7965739 < baseStart_7965739 := by decide
  rcases family_descends (prefixWord ++ tailWord_7965739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7965746 : List Nat := [3, 2, 1, 1, 2, 2, 2, 4, 1, 2, 3]
def baseStart_7965746 : Nat := 118140960795 + 7965746 * 2 ^ 59
def prefixEnd_7965746 : Nat := 4983230072969 + 3 ^ 40 * 7965746 * 2
def baseEnd_7965746 : Nat := 4090256469629696215841207

theorem tailTrace_7965746 : CollatzResearch.WordTrace tailWord_7965746 prefixEnd_7965746 4090256469629696215841207 := by
  unfold tailWord_7965746
  simp only [CollatzResearch.WordTrace]
  refine ⟨72633656249867539487915273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193689749999646771967774061 72633656249867539487915273)
  ·
    refine ⟨54475242187400654615936455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72633656249867539487915273 54475242187400654615936455)
    ·
      refine ⟨81712863281100981923904683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54475242187400654615936455 81712863281100981923904683)
      ·
        refine ⟨122569294921651472885857025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81712863281100981923904683 122569294921651472885857025)
        ·
          refine ⟨91926971191238604664392769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122569294921651472885857025 91926971191238604664392769)
          ·
            refine ⟨68945228393428953498294577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91926971191238604664392769 68945228393428953498294577)
            ·
              refine ⟨51708921295071715123720933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68945228393428953498294577 51708921295071715123720933)
              ·
                refine ⟨9695422742825946585697675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51708921295071715123720933 9695422742825946585697675)
                ·
                  refine ⟨14543134114238919878546513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9695422742825946585697675 14543134114238919878546513)
                  ·
                    refine ⟨10907350585679189908909885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14543134114238919878546513 10907350585679189908909885)
                    ·
                      refine ⟨4090256469629696215841207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10907350585679189908909885 4090256469629696215841207)
                      ·
                        rfl

theorem cell23_7965746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 4, 1, 2, 3].length) (baseStart_7965746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7965746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7965746 prefixEnd_7965746 := by exact prefixLift 7965746
  have htrace : WordTrace (prefixWord ++ tailWord_7965746) baseStart_7965746 baseEnd_7965746 := by
    simpa [prefixWord, tailWord_7965746, baseEnd_7965746] using wordTrace_append hprefix tailTrace_7965746
  have hstable : (prefixWord ++ tailWord_7965746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7965746).length < 2 ^ (prefixWord ++ tailWord_7965746).sum := by decide
  have hdescent : baseEnd_7965746 < baseStart_7965746 := by decide
  rcases family_descends (prefixWord ++ tailWord_7965746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7965760 : List Nat := [2, 1, 1, 2, 2, 3, 4, 3, 1, 2, 2]
def baseStart_7965760 : Nat := 118140960795 + 7965760 * 2 ^ 59
def prefixEnd_7965760 : Nat := 4983230072969 + 3 ^ 40 * 7965760 * 2
def baseEnd_7965760 : Nat := 4090263658358859161066143

theorem tailTrace_7965760 : CollatzResearch.WordTrace tailWord_7965760 prefixEnd_7965760 4090263658358859161066143 := by
  unfold tailWord_7965760
  simp only [CollatzResearch.WordTrace]
  refine ⟨145267567810709719171335367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193690090414279625561780489 145267567810709719171335367)
  ·
    refine ⟨217901351716064578757003051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145267567810709719171335367 217901351716064578757003051)
    ·
      refine ⟨326852027574096868135504577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217901351716064578757003051 326852027574096868135504577)
      ·
        refine ⟨245139020680572651101628433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 326852027574096868135504577 245139020680572651101628433)
        ·
          refine ⟨183854265510429488326221325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245139020680572651101628433 183854265510429488326221325)
          ·
            refine ⟨68945349566411058122332997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183854265510429488326221325 68945349566411058122332997)
            ·
              refine ⟨12927253043702073397937437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68945349566411058122332997 12927253043702073397937437)
              ·
                refine ⟨4847719891388277524226539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12927253043702073397937437 4847719891388277524226539)
                ·
                  refine ⟨7271579837082416286339809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4847719891388277524226539 7271579837082416286339809)
                  ·
                    refine ⟨5453684877811812214754857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7271579837082416286339809 5453684877811812214754857)
                    ·
                      refine ⟨4090263658358859161066143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5453684877811812214754857 4090263658358859161066143)
                      ·
                        rfl

theorem cell23_7965760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 3, 1, 2, 2].length) (baseStart_7965760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7965760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7965760 prefixEnd_7965760 := by exact prefixLift 7965760
  have htrace : WordTrace (prefixWord ++ tailWord_7965760) baseStart_7965760 baseEnd_7965760 := by
    simpa [prefixWord, tailWord_7965760, baseEnd_7965760] using wordTrace_append hprefix tailTrace_7965760
  have hstable : (prefixWord ++ tailWord_7965760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7965760).length < 2 ^ (prefixWord ++ tailWord_7965760).sum := by decide
  have hdescent : baseEnd_7965760 < baseStart_7965760 := by decide
  rcases family_descends (prefixWord ++ tailWord_7965760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7965766 : List Nat := [6, 1, 1, 1, 1, 3, 10]
def baseStart_7965766 : Nat := 118140960795 + 7965766 * 2 ^ 59
def prefixEnd_7965766 : Nat := 4983230072969 + 3 ^ 40 * 7965766 * 2
def baseEnd_7965766 : Nat := 50497120237565260957915

theorem tailTrace_7965766 : CollatzResearch.WordTrace tailWord_7965766 prefixEnd_7965766 50497120237565260957915 := by
  unfold tailWord_7965766
  simp only [CollatzResearch.WordTrace]
  refine ⟨9079229826856178167730911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 193690236306265134244926101 9079229826856178167730911)
  ·
    refine ⟨13618844740284267251596367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9079229826856178167730911 13618844740284267251596367)
    ·
      refine ⟨20428267110426400877394551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13618844740284267251596367 20428267110426400877394551)
      ·
        refine ⟨30642400665639601316091827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20428267110426400877394551 30642400665639601316091827)
        ·
          refine ⟨45963600998459401974137741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30642400665639601316091827 45963600998459401974137741)
          ·
            refine ⟨17236350374422275740301653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45963600998459401974137741 17236350374422275740301653)
            ·
              refine ⟨50497120237565260957915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17236350374422275740301653 50497120237565260957915)
              ·
                rfl

theorem cell23_7965766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 10].length) (baseStart_7965766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7965766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7965766 prefixEnd_7965766 := by exact prefixLift 7965766
  have htrace : WordTrace (prefixWord ++ tailWord_7965766) baseStart_7965766 baseEnd_7965766 := by
    simpa [prefixWord, tailWord_7965766, baseEnd_7965766] using wordTrace_append hprefix tailTrace_7965766
  have hstable : (prefixWord ++ tailWord_7965766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7965766).length < 2 ^ (prefixWord ++ tailWord_7965766).sum := by decide
  have hdescent : baseEnd_7965766 < baseStart_7965766 := by decide
  rcases family_descends (prefixWord ++ tailWord_7965766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7965786 : List Nat := [3, 1, 1, 2, 1, 1, 2, 4, 3, 3, 2]
def baseStart_7965786 : Nat := 118140960795 + 7965786 * 2 ^ 59
def prefixEnd_7965786 : Nat := 4983230072969 + 3 ^ 40 * 7965786 * 2
def baseEnd_7965786 : Nat := 4090277008855876059341023

theorem tailTrace_7965786 : CollatzResearch.WordTrace tailWord_7965786 prefixEnd_7965786 4090277008855876059341023 := by
  unfold tailWord_7965786
  simp only [CollatzResearch.WordTrace]
  refine ⟨72634020979831311195779303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193690722612883496522078141 72634020979831311195779303)
  ·
    refine ⟨108951031469746966793668955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72634020979831311195779303 108951031469746966793668955)
    ·
      refine ⟨163426547204620450190503433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108951031469746966793668955 163426547204620450190503433)
      ·
        refine ⟨122569910403465337642877575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163426547204620450190503433 122569910403465337642877575)
        ·
          refine ⟨183854865605198006464316363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122569910403465337642877575 183854865605198006464316363)
          ·
            refine ⟨275782298407797009696474545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183854865605198006464316363 275782298407797009696474545)
            ·
              refine ⟨206836723805847757272355909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 275782298407797009696474545 206836723805847757272355909)
              ·
                refine ⟨38781885713596454488566733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 206836723805847757272355909 38781885713596454488566733)
                ·
                  refine ⟨14543207142598670433212525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38781885713596454488566733 14543207142598670433212525)
                  ·
                    refine ⟨5453702678474501412454697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14543207142598670433212525 5453702678474501412454697)
                    ·
                      refine ⟨4090277008855876059341023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5453702678474501412454697 4090277008855876059341023)
                      ·
                        rfl

theorem cell23_7965786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 4, 3, 3, 2].length) (baseStart_7965786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7965786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7965786 prefixEnd_7965786 := by exact prefixLift 7965786
  have htrace : WordTrace (prefixWord ++ tailWord_7965786) baseStart_7965786 baseEnd_7965786 := by
    simpa [prefixWord, tailWord_7965786, baseEnd_7965786] using wordTrace_append hprefix tailTrace_7965786
  have hstable : (prefixWord ++ tailWord_7965786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7965786).length < 2 ^ (prefixWord ++ tailWord_7965786).sum := by decide
  have hdescent : baseEnd_7965786 < baseStart_7965786 := by decide
  rcases family_descends (prefixWord ++ tailWord_7965786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7965790 : List Nat := [4, 4, 1, 1, 1, 1, 3, 1, 1, 2, 4]
def baseStart_7965790 : Nat := 118140960795 + 7965790 * 2 ^ 59
def prefixEnd_7965790 : Nat := 4983230072969 + 3 ^ 40 * 7965790 * 2
def baseEnd_7965790 : Nat := 4090279062778494043691005

theorem tailTrace_7965790 : CollatzResearch.WordTrace tailWord_7965790 prefixEnd_7965790 4090279062778494043691005 := by
  unfold tailWord_7965790
  simp only [CollatzResearch.WordTrace]
  refine ⟨36317028726413844183282853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193690819874207168977508549 36317028726413844183282853)
  ·
    refine ⟨6809442886202595784365535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36317028726413844183282853 6809442886202595784365535)
    ·
      refine ⟨10214164329303893676548303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6809442886202595784365535 10214164329303893676548303)
      ·
        refine ⟨15321246493955840514822455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10214164329303893676548303 15321246493955840514822455)
        ·
          refine ⟨22981869740933760772233683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15321246493955840514822455 22981869740933760772233683)
          ·
            refine ⟨34472804611400641158350525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22981869740933760772233683 34472804611400641158350525)
            ·
              refine ⟨12927301729275240434381447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34472804611400641158350525 12927301729275240434381447)
              ·
                refine ⟨19390952593912860651572171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12927301729275240434381447 19390952593912860651572171)
                ·
                  refine ⟨29086428890869290977358257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19390952593912860651572171 29086428890869290977358257)
                  ·
                    refine ⟨21814821668151968233018693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29086428890869290977358257 21814821668151968233018693)
                    ·
                      refine ⟨4090279062778494043691005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21814821668151968233018693 4090279062778494043691005)
                      ·
                        rfl

theorem cell23_7965790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_7965790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7965790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7965790 prefixEnd_7965790 := by exact prefixLift 7965790
  have htrace : WordTrace (prefixWord ++ tailWord_7965790) baseStart_7965790 baseEnd_7965790 := by
    simpa [prefixWord, tailWord_7965790, baseEnd_7965790] using wordTrace_append hprefix tailTrace_7965790
  have hstable : (prefixWord ++ tailWord_7965790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7965790).length < 2 ^ (prefixWord ++ tailWord_7965790).sum := by decide
  have hdescent : baseEnd_7965790 < baseStart_7965790 := by decide
  rcases family_descends (prefixWord ++ tailWord_7965790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7965800 : List Nat := [2, 1, 4, 4, 2, 1, 2, 7]
def baseStart_7965800 : Nat := 118140960795 + 7965800 * 2 ^ 59
def prefixEnd_7965800 : Nat := 4983230072969 + 3 ^ 40 * 7965800 * 2
def baseEnd_7965800 : Nat := 151492007317964407576517

theorem tailTrace_7965800 : CollatzResearch.WordTrace tailWord_7965800 prefixEnd_7965800 151492007317964407576517 := by
  unfold tailWord_7965800
  simp only [CollatzResearch.WordTrace]
  refine ⟨145268297270637262587063427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193691063027516350116084569 145268297270637262587063427)
  ·
    refine ⟨217902445905955893880595141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145268297270637262587063427 217902445905955893880595141)
    ·
      refine ⟨40856708607366730102611589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 217902445905955893880595141 40856708607366730102611589)
      ·
        refine ⟨7660632863881261894239673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40856708607366730102611589 7660632863881261894239673)
        ·
          refine ⟨5745474647910946420679755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7660632863881261894239673 5745474647910946420679755)
          ·
            refine ⟨8618211971866419631019633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5745474647910946420679755 8618211971866419631019633)
            ·
              refine ⟨6463658978899814723264725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8618211971866419631019633 6463658978899814723264725)
              ·
                refine ⟨151492007317964407576517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6463658978899814723264725 151492007317964407576517)
                ·
                  rfl

theorem cell23_7965800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 2, 7].length) (baseStart_7965800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7965800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7965800 prefixEnd_7965800 := by exact prefixLift 7965800
  have htrace : WordTrace (prefixWord ++ tailWord_7965800) baseStart_7965800 baseEnd_7965800 := by
    simpa [prefixWord, tailWord_7965800, baseEnd_7965800] using wordTrace_append hprefix tailTrace_7965800
  have hstable : (prefixWord ++ tailWord_7965800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7965800).length < 2 ^ (prefixWord ++ tailWord_7965800).sum := by decide
  have hdescent : baseEnd_7965800 < baseStart_7965800 := by decide
  rcases family_descends (prefixWord ++ tailWord_7965800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7965816 : List Nat := [2, 1, 2, 1, 1, 1, 4, 4, 1, 4, 2]
def baseStart_7965816 : Nat := 118140960795 + 7965816 * 2 ^ 59
def prefixEnd_7965816 : Nat := 4983230072969 + 3 ^ 40 * 7965816 * 2
def baseEnd_7965816 : Nat := 4090292413275510941965885

theorem tailTrace_7965816 : CollatzResearch.WordTrace tailWord_7965816 prefixEnd_7965816 4090292413275510941965885 := by
  unfold tailWord_7965816
  simp only [CollatzResearch.WordTrace]
  refine ⟨145268589054608279953354651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193691452072811039937806201 145268589054608279953354651)
  ·
    refine ⟨217902883581912419930031977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145268589054608279953354651 217902883581912419930031977)
    ·
      refine ⟨163427162686434314947523983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217902883581912419930031977 163427162686434314947523983)
      ·
        refine ⟨245140744029651472421285975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163427162686434314947523983 245140744029651472421285975)
        ·
          refine ⟨367711116044477208631928963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245140744029651472421285975 367711116044477208631928963)
          ·
            refine ⟨551566674066715812947893445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 367711116044477208631928963 551566674066715812947893445)
            ·
              refine ⟨103418751387509214927730021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 551566674066715812947893445 103418751387509214927730021)
              ·
                refine ⟨19391015885157977798949379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103418751387509214927730021 19391015885157977798949379)
                ·
                  refine ⟨29086523827736966698424069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19391015885157977798949379 29086523827736966698424069)
                  ·
                    refine ⟨5453723217700681255954513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29086523827736966698424069 5453723217700681255954513)
                    ·
                      refine ⟨4090292413275510941965885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5453723217700681255954513 4090292413275510941965885)
                      ·
                        rfl

theorem cell23_7965816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 4, 1, 4, 2].length) (baseStart_7965816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7965816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7965816 prefixEnd_7965816 := by exact prefixLift 7965816
  have htrace : WordTrace (prefixWord ++ tailWord_7965816) baseStart_7965816 baseEnd_7965816 := by
    simpa [prefixWord, tailWord_7965816, baseEnd_7965816] using wordTrace_append hprefix tailTrace_7965816
  have hstable : (prefixWord ++ tailWord_7965816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7965816).length < 2 ^ (prefixWord ++ tailWord_7965816).sum := by decide
  have hdescent : baseEnd_7965816 < baseStart_7965816 := by decide
  rcases family_descends (prefixWord ++ tailWord_7965816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7965833 : List Nat := [1, 2, 1, 1, 4, 3, 2, 1, 4, 2, 2]
def baseStart_7965833 : Nat := 118140960795 + 7965833 * 2 ^ 59
def prefixEnd_7965833 : Nat := 4983230072969 + 3 ^ 40 * 7965833 * 2
def baseEnd_7965833 : Nat := 4090301142446637375453307

theorem tailTrace_7965833 : CollatzResearch.WordTrace tailWord_7965833 prefixEnd_7965833 4090301142446637375453307 := by
  unfold tailWord_7965833
  simp only [CollatzResearch.WordTrace]
  refine ⟨290537798150154971810078153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193691865433436647873385435 290537798150154971810078153)
  ·
    refine ⟨217903348612616228857558615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290537798150154971810078153 217903348612616228857558615)
    ·
      refine ⟨326855022918924343286337923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217903348612616228857558615 326855022918924343286337923)
      ·
        refine ⟨490282534378386514929506885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326855022918924343286337923 490282534378386514929506885)
        ·
          refine ⟨91927975195947471549282541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 490282534378386514929506885 91927975195947471549282541)
          ·
            refine ⟨34472990698480301830980953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91927975195947471549282541 34472990698480301830980953)
            ·
              refine ⟨25854743023860226373235715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34472990698480301830980953 25854743023860226373235715)
              ·
                refine ⟨38782114535790339559853573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25854743023860226373235715 38782114535790339559853573)
                ·
                  refine ⟨7271646475460688667472545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38782114535790339559853573 7271646475460688667472545)
                  ·
                    refine ⟨5453734856595516500604409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7271646475460688667472545 5453734856595516500604409)
                    ·
                      refine ⟨4090301142446637375453307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5453734856595516500604409 4090301142446637375453307)
                      ·
                        rfl

theorem cell23_7965833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 1, 4, 2, 2].length) (baseStart_7965833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7965833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7965833 prefixEnd_7965833 := by exact prefixLift 7965833
  have htrace : WordTrace (prefixWord ++ tailWord_7965833) baseStart_7965833 baseEnd_7965833 := by
    simpa [prefixWord, tailWord_7965833, baseEnd_7965833] using wordTrace_append hprefix tailTrace_7965833
  have hstable : (prefixWord ++ tailWord_7965833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7965833).length < 2 ^ (prefixWord ++ tailWord_7965833).sum := by decide
  have hdescent : baseEnd_7965833 < baseStart_7965833 := by decide
  rcases family_descends (prefixWord ++ tailWord_7965833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7965879 : List Nat := [1, 1, 3, 1, 4, 1, 1, 1, 3, 2, 5]
def baseStart_7965879 : Nat := 118140960795 + 7965879 * 2 ^ 59
def prefixEnd_7965879 : Nat := 4983230072969 + 3 ^ 40 * 7965879 * 2
def baseEnd_7965879 : Nat := 4090324762556744195478095

theorem tailTrace_7965879 : CollatzResearch.WordTrace tailWord_7965879 prefixEnd_7965879 4090324762556744195478095 := by
  unfold tailWord_7965879
  simp only [CollatzResearch.WordTrace]
  refine ⟨290539475907988321666252691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193692983938658881110835127 290539475907988321666252691)
  ·
    refine ⟨435809213861982482499379037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290539475907988321666252691 435809213861982482499379037)
    ·
      refine ⟨163428455198243430937267139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 435809213861982482499379037 163428455198243430937267139)
      ·
        refine ⟨245142682797365146405900709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163428455198243430937267139 245142682797365146405900709)
        ·
          refine ⟨45964253024505964951106383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 245142682797365146405900709 45964253024505964951106383)
          ·
            refine ⟨68946379536758947426659575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45964253024505964951106383 68946379536758947426659575)
            ·
              refine ⟨103419569305138421139989363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68946379536758947426659575 103419569305138421139989363)
              ·
                refine ⟨155129353957707631709984045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103419569305138421139989363 155129353957707631709984045)
                ·
                  refine ⟨58173507734140361891244017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 155129353957707631709984045 58173507734140361891244017)
                  ·
                    refine ⟨43630130800605271418433013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58173507734140361891244017 43630130800605271418433013)
                    ·
                      refine ⟨4090324762556744195478095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43630130800605271418433013 4090324762556744195478095)
                      ·
                        rfl

theorem cell23_7965879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 3, 2, 5].length) (baseStart_7965879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7965879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7965879 prefixEnd_7965879 := by exact prefixLift 7965879
  have htrace : WordTrace (prefixWord ++ tailWord_7965879) baseStart_7965879 baseEnd_7965879 := by
    simpa [prefixWord, tailWord_7965879, baseEnd_7965879] using wordTrace_append hprefix tailTrace_7965879
  have hstable : (prefixWord ++ tailWord_7965879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7965879).length < 2 ^ (prefixWord ++ tailWord_7965879).sum := by decide
  have hdescent : baseEnd_7965879 < baseStart_7965879 := by decide
  rcases family_descends (prefixWord ++ tailWord_7965879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7965906 : List Nat := [3, 2, 2, 2, 1, 1, 2, 2, 1, 3, 4]
def baseStart_7965906 : Nat := 118140960795 + 7965906 * 2 ^ 59
def prefixEnd_7965906 : Nat := 4983230072969 + 3 ^ 40 * 7965906 * 2
def baseEnd_7965906 : Nat := 4090338626534415589840471

theorem tailTrace_7965906 : CollatzResearch.WordTrace tailWord_7965906 prefixEnd_7965906 4090338626534415589840471 := by
  unfold tailWord_7965906
  simp only [CollatzResearch.WordTrace]
  refine ⟨72635115169722626319371393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193693640452593670184990381 72635115169722626319371393)
  ·
    refine ⟨54476336377291969739528545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72635115169722626319371393 54476336377291969739528545)
    ·
      refine ⟨40857252282968977304646409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54476336377291969739528545 40857252282968977304646409)
      ·
        refine ⟨30642939212226732978484807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40857252282968977304646409 30642939212226732978484807)
        ·
          refine ⟨45964408818340099467727211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30642939212226732978484807 45964408818340099467727211)
          ·
            refine ⟨68946613227510149201590817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45964408818340099467727211 68946613227510149201590817)
            ·
              refine ⟨51709959920632611901193113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68946613227510149201590817 51709959920632611901193113)
              ·
                refine ⟨38782469940474458925894835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51709959920632611901193113 38782469940474458925894835)
                ·
                  refine ⟨58173704910711688388842253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38782469940474458925894835 58173704910711688388842253)
                  ·
                    refine ⟨21815139341516883145815845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58173704910711688388842253 21815139341516883145815845)
                    ·
                      refine ⟨4090338626534415589840471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21815139341516883145815845 4090338626534415589840471)
                      ·
                        rfl

theorem cell23_7965906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_7965906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7965906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7965906 prefixEnd_7965906 := by exact prefixLift 7965906
  have htrace : WordTrace (prefixWord ++ tailWord_7965906) baseStart_7965906 baseEnd_7965906 := by
    simpa [prefixWord, tailWord_7965906, baseEnd_7965906] using wordTrace_append hprefix tailTrace_7965906
  have hstable : (prefixWord ++ tailWord_7965906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7965906).length < 2 ^ (prefixWord ++ tailWord_7965906).sum := by decide
  have hdescent : baseEnd_7965906 < baseStart_7965906 := by decide
  rcases family_descends (prefixWord ++ tailWord_7965906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7965950 : List Nat := [4, 2, 2, 1, 1, 3, 2, 1, 3, 4]
def baseStart_7965950 : Nat := 118140960795 + 7965950 * 2 ^ 59
def prefixEnd_7965950 : Nat := 4983230072969 + 3 ^ 40 * 7965950 * 2
def baseEnd_7965950 : Nat := 1363453739894404472563423

theorem tailTrace_7965950 : CollatzResearch.WordTrace tailWord_7965950 prefixEnd_7965950 1363453739894404472563423 := by
  unfold tailWord_7965950
  simp only [CollatzResearch.WordTrace]
  refine ⟨36317758186341387599010913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193694710327154067194724869 36317758186341387599010913)
  ·
    refine ⟨27238318639756040699258185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36317758186341387599010913 27238318639756040699258185)
    ·
      refine ⟨20428738979817030524443639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27238318639756040699258185 20428738979817030524443639)
      ·
        refine ⟨30643108469725545786665459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20428738979817030524443639 30643108469725545786665459)
        ·
          refine ⟨45964662704588318679998189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30643108469725545786665459 45964662704588318679998189)
          ·
            refine ⟨17236748514220619504999321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45964662704588318679998189 17236748514220619504999321)
            ·
              refine ⟨12927561385665464628749491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17236748514220619504999321 12927561385665464628749491)
              ·
                refine ⟨19391342078498196943124237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12927561385665464628749491 19391342078498196943124237)
                ·
                  refine ⟨7271753279436823853671589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19391342078498196943124237 7271753279436823853671589)
                  ·
                    refine ⟨1363453739894404472563423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7271753279436823853671589 1363453739894404472563423)
                    ·
                      rfl

theorem cell23_7965950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_7965950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7965950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7965950 prefixEnd_7965950 := by exact prefixLift 7965950
  have htrace : WordTrace (prefixWord ++ tailWord_7965950) baseStart_7965950 baseEnd_7965950 := by
    simpa [prefixWord, tailWord_7965950, baseEnd_7965950] using wordTrace_append hprefix tailTrace_7965950
  have hstable : (prefixWord ++ tailWord_7965950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7965950).length < 2 ^ (prefixWord ++ tailWord_7965950).sum := by decide
  have hdescent : baseEnd_7965950 < baseStart_7965950 := by decide
  rcases family_descends (prefixWord ++ tailWord_7965950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7965963 : List Nat := [1, 1, 1, 1, 5, 4, 3, 1, 6]
def baseStart_7965963 : Nat := 118140960795 + 7965963 * 2 ^ 59
def prefixEnd_7965963 : Nat := 4983230072969 + 3 ^ 40 * 7965963 * 2
def baseEnd_7965963 : Nat := 454485321659080207425301

theorem tailTrace_7965963 : CollatzResearch.WordTrace tailWord_7965963 prefixEnd_7965963 454485321659080207425301 := by
  unfold tailWord_7965963
  simp only [CollatzResearch.WordTrace]
  refine ⟨290542539639684004012310543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193695026426456002674873695 290542539639684004012310543)
  ·
    refine ⟨435813809459526006018465815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290542539639684004012310543 435813809459526006018465815)
    ·
      refine ⟨653720714189289009027698723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435813809459526006018465815 653720714189289009027698723)
      ·
        refine ⟨980581071283933513541548085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 653720714189289009027698723 980581071283933513541548085)
        ·
          refine ⟨91929475432868766894520133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 980581071283933513541548085 91929475432868766894520133)
          ·
            refine ⟨17236776643662893792722525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91929475432868766894520133 17236776643662893792722525)
            ·
              refine ⟨6463791241373585172270947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17236776643662893792722525 6463791241373585172270947)
              ·
                refine ⟨9695686862060377758406421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6463791241373585172270947 9695686862060377758406421)
                ·
                  refine ⟨454485321659080207425301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9695686862060377758406421 454485321659080207425301)
                  ·
                    rfl

theorem cell23_7965963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 3, 1, 6].length) (baseStart_7965963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7965963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7965963 prefixEnd_7965963 := by exact prefixLift 7965963
  have htrace : WordTrace (prefixWord ++ tailWord_7965963) baseStart_7965963 baseEnd_7965963 := by
    simpa [prefixWord, tailWord_7965963, baseEnd_7965963] using wordTrace_append hprefix tailTrace_7965963
  have hstable : (prefixWord ++ tailWord_7965963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7965963).length < 2 ^ (prefixWord ++ tailWord_7965963).sum := by decide
  have hdescent : baseEnd_7965963 < baseStart_7965963 := by decide
  rcases family_descends (prefixWord ++ tailWord_7965963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7965984 : List Nat := [2, 1, 1, 5, 4, 1, 1, 3, 1, 4]
def baseStart_7965984 : Nat := 118140960795 + 7965984 * 2 ^ 59
def prefixEnd_7965984 : Nat := 4983230072969 + 3 ^ 40 * 7965984 * 2
def baseEnd_7965984 : Nat := 1363459559341822094888371

theorem tailTrace_7965984 : CollatzResearch.WordTrace tailWord_7965984 prefixEnd_7965984 1363459559341822094888371 := by
  unfold tailWord_7965984
  simp only [CollatzResearch.WordTrace]
  refine ⟨145271652786303962299412503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193695537048405283065883337 145271652786303962299412503)
  ·
    refine ⟨217907479179455943449118755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145271652786303962299412503 217907479179455943449118755)
    ·
      refine ⟨326861218769183915173678133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217907479179455943449118755 326861218769183915173678133)
      ·
        refine ⟨30643239259610992047532325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 326861218769183915173678133 30643239259610992047532325)
        ·
          refine ⟨5745607361177061008912311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30643239259610992047532325 5745607361177061008912311)
          ·
            refine ⟨8618411041765591513368467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5745607361177061008912311 8618411041765591513368467)
            ·
              refine ⟨12927616562648387270052701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8618411041765591513368467 12927616562648387270052701)
              ·
                refine ⟨4847856210993145226269763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12927616562648387270052701 4847856210993145226269763)
                ·
                  refine ⟨7271784316489717839404645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4847856210993145226269763 7271784316489717839404645)
                  ·
                    refine ⟨1363459559341822094888371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7271784316489717839404645 1363459559341822094888371)
                    ·
                      rfl

theorem cell23_7965984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 3, 1, 4].length) (baseStart_7965984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7965984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7965984 prefixEnd_7965984 := by exact prefixLift 7965984
  have htrace : WordTrace (prefixWord ++ tailWord_7965984) baseStart_7965984 baseEnd_7965984 := by
    simpa [prefixWord, tailWord_7965984, baseEnd_7965984] using wordTrace_append hprefix tailTrace_7965984
  have hstable : (prefixWord ++ tailWord_7965984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7965984).length < 2 ^ (prefixWord ++ tailWord_7965984).sum := by decide
  have hdescent : baseEnd_7965984 < baseStart_7965984 := by decide
  rcases family_descends (prefixWord ++ tailWord_7965984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7965996 : List Nat := [2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 4]
def baseStart_7965996 : Nat := 118140960795 + 7965996 * 2 ^ 59
def prefixEnd_7965996 : Nat := 4983230072969 + 3 ^ 40 * 7965996 * 2
def baseEnd_7965996 : Nat := 4090384839793320237715057

theorem tailTrace_7965996 : CollatzResearch.WordTrace tailWord_7965996 prefixEnd_7965996 4090384839793320237715057 := by
  unfold tailWord_7965996
  simp only [CollatzResearch.WordTrace]
  refine ⟨145271871624282225324130921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193695828832376300432174561 145271871624282225324130921)
  ·
    refine ⟨108953903718211668993098191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145271871624282225324130921 108953903718211668993098191)
    ·
      refine ⟨163430855577317503489647287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108953903718211668993098191 163430855577317503489647287)
      ·
        refine ⟨245146283365976255234470931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163430855577317503489647287 245146283365976255234470931)
        ·
          refine ⟨367719425048964382851706397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245146283365976255234470931 367719425048964382851706397)
          ·
            refine ⟨137894784393361643569389899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 367719425048964382851706397 137894784393361643569389899)
            ·
              refine ⟨206842176590042465354084849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137894784393361643569389899 206842176590042465354084849)
              ·
                refine ⟨155131632442531849015563637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 206842176590042465354084849 155131632442531849015563637)
                ·
                  refine ⟨14543590541487360845209091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 155131632442531849015563637 14543590541487360845209091)
                  ·
                    refine ⟨21815385812231041267813637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14543590541487360845209091 21815385812231041267813637)
                    ·
                      refine ⟨4090384839793320237715057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21815385812231041267813637 4090384839793320237715057)
                      ·
                        rfl

theorem cell23_7965996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 4].length) (baseStart_7965996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7965996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7965996 prefixEnd_7965996 := by exact prefixLift 7965996
  have htrace : WordTrace (prefixWord ++ tailWord_7965996) baseStart_7965996 baseEnd_7965996 := by
    simpa [prefixWord, tailWord_7965996, baseEnd_7965996] using wordTrace_append hprefix tailTrace_7965996
  have hstable : (prefixWord ++ tailWord_7965996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7965996).length < 2 ^ (prefixWord ++ tailWord_7965996).sum := by decide
  have hdescent : baseEnd_7965996 < baseStart_7965996 := by decide
  rcases family_descends (prefixWord ++ tailWord_7965996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7966016 : List Nat := [2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 5]
def baseStart_7966016 : Nat := 118140960795 + 7966016 * 2 ^ 59
def prefixEnd_7966016 : Nat := 4983230072969 + 3 ^ 40 * 7966016 * 2
def baseEnd_7966016 : Nat := 4090395109406410159464965

theorem tailTrace_7966016 : CollatzResearch.WordTrace tailWord_7966016 prefixEnd_7966016 4090395109406410159464965 := by
  unfold tailWord_7966016
  simp only [CollatzResearch.WordTrace]
  refine ⟨145272236354245997031994951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193696315138994662709326601 145272236354245997031994951)
  ·
    refine ⟨217908354531368995547992427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145272236354245997031994951 217908354531368995547992427)
    ·
      refine ⟨326862531797053493321988641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217908354531368995547992427 326862531797053493321988641)
      ·
        refine ⟨245146898847790119991491481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 326862531797053493321988641 245146898847790119991491481)
        ·
          refine ⟨183860174135842589993618611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245146898847790119991491481 183860174135842589993618611)
          ·
            refine ⟨275790261203763884990427917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183860174135842589993618611 275790261203763884990427917)
            ·
              refine ⟨103421347951411456871410469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 275790261203763884990427917 103421347951411456871410469)
              ·
                refine ⟨19391502740889648163389463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103421347951411456871410469 19391502740889648163389463)
                ·
                  refine ⟨29087254111334472245084195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19391502740889648163389463 29087254111334472245084195)
                  ·
                    refine ⟨43630881167001708367626293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29087254111334472245084195 43630881167001708367626293)
                    ·
                      refine ⟨4090395109406410159464965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43630881167001708367626293 4090395109406410159464965)
                      ·
                        rfl

theorem cell23_7966016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 5].length) (baseStart_7966016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7966016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7966016 prefixEnd_7966016 := by exact prefixLift 7966016
  have htrace : WordTrace (prefixWord ++ tailWord_7966016) baseStart_7966016 baseEnd_7966016 := by
    simpa [prefixWord, tailWord_7966016, baseEnd_7966016] using wordTrace_append hprefix tailTrace_7966016
  have hstable : (prefixWord ++ tailWord_7966016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7966016).length < 2 ^ (prefixWord ++ tailWord_7966016).sum := by decide
  have hdescent : baseEnd_7966016 < baseStart_7966016 := by decide
  rcases family_descends (prefixWord ++ tailWord_7966016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7966026 : List Nat := [3, 1, 2, 1, 1, 1, 1, 2, 5, 2, 4]
def baseStart_7966026 : Nat := 118140960795 + 7966026 * 2 ^ 59
def prefixEnd_7966026 : Nat := 4983230072969 + 3 ^ 40 * 7966026 * 2
def baseEnd_7966026 : Nat := 4090400244212955120339919

theorem tailTrace_7966026 : CollatzResearch.WordTrace tailWord_7966026 prefixEnd_7966026 4090400244212955120339919 := by
  unfold tailWord_7966026
  simp only [CollatzResearch.WordTrace]
  refine ⟨72636209359613941442963483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193696558292303843847902621 72636209359613941442963483)
  ·
    refine ⟨108954314039420912164445225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72636209359613941442963483 108954314039420912164445225)
    ·
      refine ⟨81715735529565684123333919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108954314039420912164445225 81715735529565684123333919)
      ·
        refine ⟨122573603294348526185000879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81715735529565684123333919 122573603294348526185000879)
        ·
          refine ⟨183860404941522789277501319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122573603294348526185000879 183860404941522789277501319)
          ·
            refine ⟨275790607412284183916251979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183860404941522789277501319 275790607412284183916251979)
            ·
              refine ⟨413685911118426275874377969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275790607412284183916251979 413685911118426275874377969)
              ·
                refine ⟨310264433338819706905783477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 413685911118426275874377969 310264433338819706905783477)
                ·
                  refine ⟨29087290625514347522417201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 310264433338819706905783477 29087290625514347522417201)
                  ·
                    refine ⟨21815467969135760641812901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29087290625514347522417201 21815467969135760641812901)
                    ·
                      refine ⟨4090400244212955120339919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21815467969135760641812901 4090400244212955120339919)
                      ·
                        rfl

theorem cell23_7966026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 5, 2, 4].length) (baseStart_7966026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7966026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7966026 prefixEnd_7966026 := by exact prefixLift 7966026
  have htrace : WordTrace (prefixWord ++ tailWord_7966026) baseStart_7966026 baseEnd_7966026 := by
    simpa [prefixWord, tailWord_7966026, baseEnd_7966026] using wordTrace_append hprefix tailTrace_7966026
  have hstable : (prefixWord ++ tailWord_7966026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7966026).length < 2 ^ (prefixWord ++ tailWord_7966026).sum := by decide
  have hdescent : baseEnd_7966026 < baseStart_7966026 := by decide
  rcases family_descends (prefixWord ++ tailWord_7966026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7966030 : List Nat := [4, 1, 1, 1, 1, 1, 4, 1, 5, 2, 2]
def baseStart_7966030 : Nat := 118140960795 + 7966030 * 2 ^ 59
def prefixEnd_7966030 : Nat := 4983230072969 + 3 ^ 40 * 7966030 * 2
def baseEnd_7966030 : Nat := 4090402298135573104689901

theorem tailTrace_7966030 : CollatzResearch.WordTrace tailWord_7966030 prefixEnd_7966030 4090402298135573104689901 := by
  unfold tailWord_7966030
  simp only [CollatzResearch.WordTrace]
  refine ⟨36318122916305159306874943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193696655553627516303333029 36318122916305159306874943)
  ·
    refine ⟨54477184374457738960312415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36318122916305159306874943 54477184374457738960312415)
    ·
      refine ⟨81715776561686608440468623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54477184374457738960312415 81715776561686608440468623)
      ·
        refine ⟨122573664842529912660702935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81715776561686608440468623 122573664842529912660702935)
        ·
          refine ⟨183860497263794868991054403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122573664842529912660702935 183860497263794868991054403)
          ·
            refine ⟨275790745895692303486581605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183860497263794868991054403 275790745895692303486581605)
            ·
              refine ⟨51710764855442306903734051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 275790745895692303486581605 51710764855442306903734051)
              ·
                refine ⟨77566147283163460355601077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51710764855442306903734051 77566147283163460355601077)
                ·
                  refine ⟨7271826307796574408337601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77566147283163460355601077 7271826307796574408337601)
                  ·
                    refine ⟨5453869730847430806253201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7271826307796574408337601 5453869730847430806253201)
                    ·
                      refine ⟨4090402298135573104689901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5453869730847430806253201 4090402298135573104689901)
                      ·
                        rfl

theorem cell23_7966030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 5, 2, 2].length) (baseStart_7966030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7966030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7966030 prefixEnd_7966030 := by exact prefixLift 7966030
  have htrace : WordTrace (prefixWord ++ tailWord_7966030) baseStart_7966030 baseEnd_7966030 := by
    simpa [prefixWord, tailWord_7966030, baseEnd_7966030] using wordTrace_append hprefix tailTrace_7966030
  have hstable : (prefixWord ++ tailWord_7966030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7966030).length < 2 ^ (prefixWord ++ tailWord_7966030).sum := by decide
  have hdescent : baseEnd_7966030 < baseStart_7966030 := by decide
  rcases family_descends (prefixWord ++ tailWord_7966030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7966033 : List Nat := [1, 2, 2, 1, 4, 1, 3, 1, 3, 2, 3]
def baseStart_7966033 : Nat := 118140960795 + 7966033 * 2 ^ 59
def prefixEnd_7966033 : Nat := 4983230072969 + 3 ^ 40 * 7966033 * 2
def baseEnd_7966033 : Nat := 4090403838577536592952387

theorem tailTrace_7966033 : CollatzResearch.WordTrace tailWord_7966033 prefixEnd_7966033 4090403838577536592952387 := by
  unfold tailWord_7966033
  simp only [CollatzResearch.WordTrace]
  refine ⟨290545092749430405967358753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193696728499620270644905835 290545092749430405967358753)
  ·
    refine ⟨217908819562072804475519065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290545092749430405967358753 217908819562072804475519065)
    ·
      refine ⟨163431614671554603356639299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217908819562072804475519065 163431614671554603356639299)
      ·
        refine ⟨245147422007331905034958949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163431614671554603356639299 245147422007331905034958949)
        ·
          refine ⟨45965141626374732194054803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 245147422007331905034958949 45965141626374732194054803)
          ·
            refine ⟨68947712439562098291082205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45965141626374732194054803 68947712439562098291082205)
            ·
              refine ⟨25855392164835786859155827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68947712439562098291082205 25855392164835786859155827)
              ·
                refine ⟨38783088247253680288733741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25855392164835786859155827 38783088247253680288733741)
                ·
                  refine ⟨14543658092720130108275153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38783088247253680288733741 14543658092720130108275153)
                  ·
                    refine ⟨10907743569540097581206365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14543658092720130108275153 10907743569540097581206365)
                    ·
                      refine ⟨4090403838577536592952387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10907743569540097581206365 4090403838577536592952387)
                      ·
                        rfl

theorem cell23_7966033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 1, 3, 2, 3].length) (baseStart_7966033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7966033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7966033 prefixEnd_7966033 := by exact prefixLift 7966033
  have htrace : WordTrace (prefixWord ++ tailWord_7966033) baseStart_7966033 baseEnd_7966033 := by
    simpa [prefixWord, tailWord_7966033, baseEnd_7966033] using wordTrace_append hprefix tailTrace_7966033
  have hstable : (prefixWord ++ tailWord_7966033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7966033).length < 2 ^ (prefixWord ++ tailWord_7966033).sum := by decide
  have hdescent : baseEnd_7966033 < baseStart_7966033 := by decide
  rcases family_descends (prefixWord ++ tailWord_7966033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7966036 : List Nat := [2, 4, 1, 1, 2, 1, 1, 11]
def baseStart_7966036 : Nat := 118140960795 + 7966036 * 2 ^ 59
def prefixEnd_7966036 : Nat := 4983230072969 + 3 ^ 40 * 7966036 * 2
def baseEnd_7966036 : Nat := 151496495519240743748699

theorem tailTrace_7966036 : CollatzResearch.WordTrace tailWord_7966036 prefixEnd_7966036 151496495519240743748699 := by
  unfold tailWord_7966036
  simp only [CollatzResearch.WordTrace]
  refine ⟨145272601084209768739858981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193696801445613024986478641 145272601084209768739858981)
  ·
    refine ⟨27238612703289331638723559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145272601084209768739858981 27238612703289331638723559)
    ·
      refine ⟨40857919054933997458085339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27238612703289331638723559 40857919054933997458085339)
      ·
        refine ⟨61286878582400996187128009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40857919054933997458085339 61286878582400996187128009)
        ·
          refine ⟨45965158936800747140346007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61286878582400996187128009 45965158936800747140346007)
          ·
            refine ⟨68947738405201120710519011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45965158936800747140346007 68947738405201120710519011)
            ·
              refine ⟨103421607607801681065778517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68947738405201120710519011 103421607607801681065778517)
              ·
                refine ⟨151496495519240743748699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 103421607607801681065778517 151496495519240743748699)
                ·
                  rfl

theorem cell23_7966036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 11].length) (baseStart_7966036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7966036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7966036 prefixEnd_7966036 := by exact prefixLift 7966036
  have htrace : WordTrace (prefixWord ++ tailWord_7966036) baseStart_7966036 baseEnd_7966036 := by
    simpa [prefixWord, tailWord_7966036, baseEnd_7966036] using wordTrace_append hprefix tailTrace_7966036
  have hstable : (prefixWord ++ tailWord_7966036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7966036).length < 2 ^ (prefixWord ++ tailWord_7966036).sum := by decide
  have hdescent : baseEnd_7966036 < baseStart_7966036 := by decide
  rcases family_descends (prefixWord ++ tailWord_7966036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7966047 : List Nat := [1, 1, 2, 3, 1, 2, 1, 7, 1, 2, 2]
def baseStart_7966047 : Nat := 118140960795 + 7966047 * 2 ^ 59
def prefixEnd_7966047 : Nat := 4983230072969 + 3 ^ 40 * 7966047 * 2
def baseEnd_7966047 : Nat := 4090411027306699538177323

theorem tailTrace_7966047 : CollatzResearch.WordTrace tailWord_7966047 prefixEnd_7966047 4090411027306699538177323 := by
  unfold tailWord_7966047
  simp only [CollatzResearch.WordTrace]
  refine ⟨290545603371379686358368395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193697068914253124238912263 290545603371379686358368395)
  ·
    refine ⟨435818405057069529537552593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290545603371379686358368395 435818405057069529537552593)
    ·
      refine ⟨326863803792802147153164445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 435818405057069529537552593 326863803792802147153164445)
      ·
        refine ⟨122573926422300805182436667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 326863803792802147153164445 122573926422300805182436667)
        ·
          refine ⟨183860889633451207773655001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122573926422300805182436667 183860889633451207773655001)
          ·
            refine ⟨137895667225088405830241251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183860889633451207773655001 137895667225088405830241251)
            ·
              refine ⟨206843500837632608745361877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137895667225088405830241251 206843500837632608745361877)
              ·
                refine ⟨4847894550882014267469419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 206843500837632608745361877 4847894550882014267469419)
                ·
                  refine ⟨7271841826323021401204129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4847894550882014267469419 7271841826323021401204129)
                  ·
                    refine ⟨5453881369742266050903097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7271841826323021401204129 5453881369742266050903097)
                    ·
                      refine ⟨4090411027306699538177323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5453881369742266050903097 4090411027306699538177323)
                      ·
                        rfl

theorem cell23_7966047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 7, 1, 2, 2].length) (baseStart_7966047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7966047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7966047 prefixEnd_7966047 := by exact prefixLift 7966047
  have htrace : WordTrace (prefixWord ++ tailWord_7966047) baseStart_7966047 baseEnd_7966047 := by
    simpa [prefixWord, tailWord_7966047, baseEnd_7966047] using wordTrace_append hprefix tailTrace_7966047
  have hstable : (prefixWord ++ tailWord_7966047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7966047).length < 2 ^ (prefixWord ++ tailWord_7966047).sum := by decide
  have hdescent : baseEnd_7966047 < baseStart_7966047 := by decide
  rcases family_descends (prefixWord ++ tailWord_7966047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7966058 : List Nat := [3, 1, 3, 3, 3, 1, 2, 2, 1, 1, 3]
def baseStart_7966058 : Nat := 118140960795 + 7966058 * 2 ^ 59
def prefixEnd_7966058 : Nat := 4983230072969 + 3 ^ 40 * 7966058 * 2
def baseEnd_7966058 : Nat := 4090416675593898995139773

theorem tailTrace_7966058 : CollatzResearch.WordTrace tailWord_7966058 prefixEnd_7966058 4090416675593898995139773 := by
  unfold tailWord_7966058
  simp only [CollatzResearch.WordTrace]
  refine ⟨72636501143584958809254707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193697336382893223491345885 72636501143584958809254707)
  ·
    refine ⟨108954751715377438213882061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72636501143584958809254707 108954751715377438213882061)
    ·
      refine ⟨40858031893266539330205773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108954751715377438213882061 40858031893266539330205773)
      ·
        refine ⟨15321761959974952248827165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40858031893266539330205773 15321761959974952248827165)
        ·
          refine ⟨5745660734990607093310187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15321761959974952248827165 5745660734990607093310187)
          ·
            refine ⟨8618491102485910639965281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5745660734990607093310187 8618491102485910639965281)
            ·
              refine ⟨6463868326864432979973961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8618491102485910639965281 6463868326864432979973961)
              ·
                refine ⟨4847901245148324734980471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6463868326864432979973961 4847901245148324734980471)
                ·
                  refine ⟨7271851867722487102470707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4847901245148324734980471 7271851867722487102470707)
                  ·
                    refine ⟨10907777801583730653706061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7271851867722487102470707 10907777801583730653706061)
                    ·
                      refine ⟨4090416675593898995139773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10907777801583730653706061 4090416675593898995139773)
                      ·
                        rfl

theorem cell23_7966058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_7966058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7966058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7966058 prefixEnd_7966058 := by exact prefixLift 7966058
  have htrace : WordTrace (prefixWord ++ tailWord_7966058) baseStart_7966058 baseEnd_7966058 := by
    simpa [prefixWord, tailWord_7966058, baseEnd_7966058] using wordTrace_append hprefix tailTrace_7966058
  have hstable : (prefixWord ++ tailWord_7966058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7966058).length < 2 ^ (prefixWord ++ tailWord_7966058).sum := by decide
  have hdescent : baseEnd_7966058 < baseStart_7966058 := by decide
  rcases family_descends (prefixWord ++ tailWord_7966058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7966066 : List Nat := [3, 2, 1, 2, 1, 2, 1, 1, 1, 9]
def baseStart_7966066 : Nat := 118140960795 + 7966066 * 2 ^ 59
def prefixEnd_7966066 : Nat := 4983230072969 + 3 ^ 40 * 7966066 * 2
def baseEnd_7966066 : Nat := 1363473594479711654613245

theorem tailTrace_7966066 : CollatzResearch.WordTrace tailWord_7966066 prefixEnd_7966066 1363473594479711654613245 := by
  unfold tailWord_7966066
  simp only [CollatzResearch.WordTrace]
  refine ⟨72636574089577713150827513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193697530905540568402206701 72636574089577713150827513)
  ·
    refine ⟨54477430567183284863120635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72636574089577713150827513 54477430567183284863120635)
    ·
      refine ⟨81716145850774927294680953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54477430567183284863120635 81716145850774927294680953)
      ·
        refine ⟨61287109388081195471010715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81716145850774927294680953 61287109388081195471010715)
        ·
          refine ⟨91930664082121793206516073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61287109388081195471010715 91930664082121793206516073)
          ·
            refine ⟨68947998061591344904887055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91930664082121793206516073 68947998061591344904887055)
            ·
              refine ⟨103421997092387017357330583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68947998061591344904887055 103421997092387017357330583)
              ·
                refine ⟨155132995638580526035995875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103421997092387017357330583 155132995638580526035995875)
                ·
                  refine ⟨232699493457870789053993813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 155132995638580526035995875 232699493457870789053993813)
                  ·
                    refine ⟨1363473594479711654613245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 232699493457870789053993813 1363473594479711654613245)
                    ·
                      rfl

theorem cell23_7966066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 1, 9].length) (baseStart_7966066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7966066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7966066 prefixEnd_7966066 := by exact prefixLift 7966066
  have htrace : WordTrace (prefixWord ++ tailWord_7966066) baseStart_7966066 baseEnd_7966066 := by
    simpa [prefixWord, tailWord_7966066, baseEnd_7966066] using wordTrace_append hprefix tailTrace_7966066
  have hstable : (prefixWord ++ tailWord_7966066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7966066).length < 2 ^ (prefixWord ++ tailWord_7966066).sum := by decide
  have hdescent : baseEnd_7966066 < baseStart_7966066 := by decide
  rcases family_descends (prefixWord ++ tailWord_7966066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7966098 : List Nat := [3, 2, 3, 3, 1, 1, 2, 3, 1, 2, 2]
def baseStart_7966098 : Nat := 118140960795 + 7966098 * 2 ^ 59
def prefixEnd_7966098 : Nat := 4983230072969 + 3 ^ 40 * 7966098 * 2
def baseEnd_7966098 : Nat := 4090437214820078838639589

theorem tailTrace_7966098 : CollatzResearch.WordTrace tailWord_7966098 prefixEnd_7966098 4090437214820078838639589 := by
  unfold tailWord_7966098
  simp only [CollatzResearch.WordTrace]
  refine ⟨72636865873548730517118737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193698308996129948045649965 72636865873548730517118737)
  ·
    refine ⟨54477649405161547887839053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72636865873548730517118737 54477649405161547887839053)
    ·
      refine ⟨20429118526935580457939645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54477649405161547887839053 20429118526935580457939645)
      ·
        refine ⟨7660919447600842671727367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20429118526935580457939645 7660919447600842671727367)
        ·
          refine ⟨11491379171401264007591051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7660919447600842671727367 11491379171401264007591051)
          ·
            refine ⟨17237068757101896011386577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11491379171401264007591051 17237068757101896011386577)
            ·
              refine ⟨12927801567826422008539933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17237068757101896011386577 12927801567826422008539933)
              ·
                refine ⟨4847925587934908253202475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12927801567826422008539933 4847925587934908253202475)
                ·
                  refine ⟨7271888381902362379803713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4847925587934908253202475 7271888381902362379803713)
                  ·
                    refine ⟨5453916286426771784852785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7271888381902362379803713 5453916286426771784852785)
                    ·
                      refine ⟨4090437214820078838639589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5453916286426771784852785 4090437214820078838639589)
                      ·
                        rfl

theorem cell23_7966098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_7966098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7966098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7966098 prefixEnd_7966098 := by exact prefixLift 7966098
  have htrace : WordTrace (prefixWord ++ tailWord_7966098) baseStart_7966098 baseEnd_7966098 := by
    simpa [prefixWord, tailWord_7966098, baseEnd_7966098] using wordTrace_append hprefix tailTrace_7966098
  have hstable : (prefixWord ++ tailWord_7966098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7966098).length < 2 ^ (prefixWord ++ tailWord_7966098).sum := by decide
  have hdescent : baseEnd_7966098 < baseStart_7966098 := by decide
  rcases family_descends (prefixWord ++ tailWord_7966098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7966114 : List Nat := [3, 3, 1, 2, 1, 4, 1, 2, 2, 1, 3]
def baseStart_7966114 : Nat := 118140960795 + 7966114 * 2 ^ 59
def prefixEnd_7966114 : Nat := 4983230072969 + 3 ^ 40 * 7966114 * 2
def baseEnd_7966114 : Nat := 4090445430510550776039515

theorem tailTrace_7966114 : CollatzResearch.WordTrace tailWord_7966114 prefixEnd_7966114 4090445430510550776039515 := by
  unfold tailWord_7966114
  simp only [CollatzResearch.WordTrace]
  refine ⟨72637011765534239200264349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193698698041424637867371597 72637011765534239200264349)
  ·
    refine ⟨27238879412075339700099131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72637011765534239200264349 27238879412075339700099131)
    ·
      refine ⟨40858319118113009550148697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27238879412075339700099131 40858319118113009550148697)
      ·
        refine ⟨30643739338584757162611523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40858319118113009550148697 30643739338584757162611523)
        ·
          refine ⟨45965609007877135743917285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30643739338584757162611523 45965609007877135743917285)
          ·
            refine ⟨8618551688976962951984491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45965609007877135743917285 8618551688976962951984491)
            ·
              refine ⟨12927827533465444427976737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8618551688976962951984491 12927827533465444427976737)
              ·
                refine ⟨9695870650099083320982553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12927827533465444427976737 9695870650099083320982553)
                ·
                  refine ⟨7271902987574312490736915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9695870650099083320982553 7271902987574312490736915)
                  ·
                    refine ⟨10907854481361468736105373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7271902987574312490736915 10907854481361468736105373)
                    ·
                      refine ⟨4090445430510550776039515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10907854481361468736105373 4090445430510550776039515)
                      ·
                        rfl

theorem cell23_7966114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_7966114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7966114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7966114 prefixEnd_7966114 := by exact prefixLift 7966114
  have htrace : WordTrace (prefixWord ++ tailWord_7966114) baseStart_7966114 baseEnd_7966114 := by
    simpa [prefixWord, tailWord_7966114, baseEnd_7966114] using wordTrace_append hprefix tailTrace_7966114
  have hstable : (prefixWord ++ tailWord_7966114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7966114).length < 2 ^ (prefixWord ++ tailWord_7966114).sum := by decide
  have hdescent : baseEnd_7966114 < baseStart_7966114 := by decide
  rcases family_descends (prefixWord ++ tailWord_7966114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7966177 : List Nat := [1, 2, 3, 1, 2, 4, 3, 2, 5]
def baseStart_7966177 : Nat := 118140960795 + 7966177 * 2 ^ 59
def prefixEnd_7966177 : Nat := 4983230072969 + 3 ^ 40 * 7966177 * 2
def baseEnd_7966177 : Nat := 454497531087976003283525

theorem tailTrace_7966177 : CollatzResearch.WordTrace tailWord_7966177 prefixEnd_7966177 454497531087976003283525 := by
  unfold tailWord_7966177
  simp only [CollatzResearch.WordTrace]
  refine ⟨290550344860908718560600785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193700229907272479040400523 290550344860908718560600785)
  ·
    refine ⟨217912758645681538920450589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290550344860908718560600785 217912758645681538920450589)
    ·
      refine ⟨81717284492130577095168971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217912758645681538920450589 81717284492130577095168971)
      ·
        refine ⟨122575926738195865642753457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81717284492130577095168971 122575926738195865642753457)
        ·
          refine ⟨91931945053646899232065093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122575926738195865642753457 91931945053646899232065093)
          ·
            refine ⟨17237239697558793606012205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91931945053646899232065093 17237239697558793606012205)
            ·
              refine ⟨6463964886584547602254577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17237239697558793606012205 6463964886584547602254577)
              ·
                refine ⟨4847973664938410701690933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6463964886584547602254577 4847973664938410701690933)
                ·
                  refine ⟨454497531087976003283525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4847973664938410701690933 454497531087976003283525)
                  ·
                    rfl

theorem cell23_7966177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 3, 2, 5].length) (baseStart_7966177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7966177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7966177 prefixEnd_7966177 := by exact prefixLift 7966177
  have htrace : WordTrace (prefixWord ++ tailWord_7966177) baseStart_7966177 baseEnd_7966177 := by
    simpa [prefixWord, tailWord_7966177, baseEnd_7966177] using wordTrace_append hprefix tailTrace_7966177
  have hstable : (prefixWord ++ tailWord_7966177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7966177).length < 2 ^ (prefixWord ++ tailWord_7966177).sum := by decide
  have hdescent : baseEnd_7966177 < baseStart_7966177 := by decide
  rcases family_descends (prefixWord ++ tailWord_7966177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7966183 : List Nat := [1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 7]
def baseStart_7966183 : Nat := 118140960795 + 7966183 * 2 ^ 59
def prefixEnd_7966183 : Nat := 4983230072969 + 3 ^ 40 * 7966183 * 2
def baseEnd_7966183 : Nat := 4090480860675711006076697

theorem tailTrace_7966183 : CollatzResearch.WordTrace tailWord_7966183 prefixEnd_7966183 4090480860675711006076697 := by
  unfold tailWord_7966183
  simp only [CollatzResearch.WordTrace]
  refine ⟨290550563698886981585319203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193700375799257987723546135 290550563698886981585319203)
  ·
    refine ⟨435825845548330472377978805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290550563698886981585319203 435825845548330472377978805)
    ·
      refine ⟨40858673020155981785435513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 435825845548330472377978805 40858673020155981785435513)
      ·
        refine ⟨30644004765116986339076635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40858673020155981785435513 30644004765116986339076635)
        ·
          refine ⟨45966007147675479508614953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30644004765116986339076635 45966007147675479508614953)
          ·
            refine ⟨34474505360756609631461215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45966007147675479508614953 34474505360756609631461215)
            ·
              refine ⟨51711758041134914447191823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34474505360756609631461215 51711758041134914447191823)
              ·
                refine ⟨77567637061702371670787735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51711758041134914447191823 77567637061702371670787735)
                ·
                  refine ⟨116351455592553557506181603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77567637061702371670787735 116351455592553557506181603)
                  ·
                    refine ⟨174527183388830336259272405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 116351455592553557506181603 174527183388830336259272405)
                    ·
                      refine ⟨4090480860675711006076697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 174527183388830336259272405 4090480860675711006076697)
                      ·
                        rfl

theorem cell23_7966183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_7966183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7966183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7966183 prefixEnd_7966183 := by exact prefixLift 7966183
  have htrace : WordTrace (prefixWord ++ tailWord_7966183) baseStart_7966183 baseEnd_7966183 := by
    simpa [prefixWord, tailWord_7966183, baseEnd_7966183] using wordTrace_append hprefix tailTrace_7966183
  have hstable : (prefixWord ++ tailWord_7966183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7966183).length < 2 ^ (prefixWord ++ tailWord_7966183).sum := by decide
  have hdescent : baseEnd_7966183 < baseStart_7966183 := by decide
  rcases family_descends (prefixWord ++ tailWord_7966183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7966228 : List Nat := [2, 4, 3, 1, 3, 1, 2, 2, 5]
def baseStart_7966228 : Nat := 118140960795 + 7966228 * 2 ^ 59
def prefixEnd_7966228 : Nat := 4983230072969 + 3 ^ 40 * 7966228 * 2
def baseEnd_7966228 : Nat := 454500440811684814445999

theorem tailTrace_7966228 : CollatzResearch.WordTrace tailWord_7966228 prefixEnd_7966228 454500440811684814445999 := by
  unfold tailWord_7966228
  simp only [CollatzResearch.WordTrace]
  refine ⟨145276102491861977135353669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193701469989149302847138225 145276102491861977135353669)
  ·
    refine ⟨27239269217224120712878813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145276102491861977135353669 27239269217224120712878813)
    ·
      refine ⟨10214725956459045267329555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27239269217224120712878813 10214725956459045267329555)
      ·
        refine ⟨15322088934688567900994333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10214725956459045267329555 15322088934688567900994333)
        ·
          refine ⟨5745783350508212962872875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15322088934688567900994333 5745783350508212962872875)
          ·
            refine ⟨8618675025762319444309313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5745783350508212962872875 8618675025762319444309313)
            ·
              refine ⟨6464006269321739583231985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8618675025762319444309313 6464006269321739583231985)
              ·
                refine ⟨4848004701991304687423989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6464006269321739583231985 4848004701991304687423989)
                ·
                  refine ⟨454500440811684814445999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4848004701991304687423989 454500440811684814445999)
                  ·
                    rfl

theorem cell23_7966228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 2, 2, 5].length) (baseStart_7966228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7966228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7966228 prefixEnd_7966228 := by exact prefixLift 7966228
  have htrace : WordTrace (prefixWord ++ tailWord_7966228) baseStart_7966228 baseEnd_7966228 := by
    simpa [prefixWord, tailWord_7966228, baseEnd_7966228] using wordTrace_append hprefix tailTrace_7966228
  have hstable : (prefixWord ++ tailWord_7966228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7966228).length < 2 ^ (prefixWord ++ tailWord_7966228).sum := by decide
  have hdescent : baseEnd_7966228 < baseStart_7966228 := by decide
  rcases family_descends (prefixWord ++ tailWord_7966228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7966250 : List Nat := [3, 1, 4, 1, 1, 1, 1, 5, 6]
def baseStart_7966250 : Nat := 118140960795 + 7966250 * 2 ^ 59
def prefixEnd_7966250 : Nat := 4983230072969 + 3 ^ 40 * 7966250 * 2
def baseEnd_7966250 : Nat := 454501695986618027104321

theorem tailTrace_7966250 : CollatzResearch.WordTrace tailWord_7966250 prefixEnd_7966250 454501695986618027104321 := by
  unfold tailWord_7966250
  simp only [CollatzResearch.WordTrace]
  refine ⟨72638251847411063007002051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193702004926429501352005469 72638251847411063007002051)
  ·
    refine ⟨108957377771116594510503077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72638251847411063007002051 108957377771116594510503077)
    ·
      refine ⟨20429508332084361470719327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108957377771116594510503077 20429508332084361470719327)
      ·
        refine ⟨30644262498126542206078991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20429508332084361470719327 30644262498126542206078991)
        ·
          refine ⟨45966393747189813309118487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30644262498126542206078991 45966393747189813309118487)
          ·
            refine ⟨68949590620784719963677731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45966393747189813309118487 68949590620784719963677731)
            ·
              refine ⟨103424385931177079945516597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68949590620784719963677731 103424385931177079945516597)
              ·
                refine ⟨9696036181047851244892181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 103424385931177079945516597 9696036181047851244892181)
                ·
                  refine ⟨454501695986618027104321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9696036181047851244892181 454501695986618027104321)
                  ·
                    rfl

theorem cell23_7966250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 5, 6].length) (baseStart_7966250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7966250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7966250 prefixEnd_7966250 := by exact prefixLift 7966250
  have htrace : WordTrace (prefixWord ++ tailWord_7966250) baseStart_7966250 baseEnd_7966250 := by
    simpa [prefixWord, tailWord_7966250, baseEnd_7966250] using wordTrace_append hprefix tailTrace_7966250
  have hstable : (prefixWord ++ tailWord_7966250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7966250).length < 2 ^ (prefixWord ++ tailWord_7966250).sum := by decide
  have hdescent : baseEnd_7966250 < baseStart_7966250 := by decide
  rcases family_descends (prefixWord ++ tailWord_7966250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7966301 : List Nat := [1, 4, 4, 2, 1, 1, 3, 1, 6]
def baseStart_7966301 : Nat := 118140960795 + 7966301 * 2 ^ 59
def prefixEnd_7966301 : Nat := 4983230072969 + 3 ^ 40 * 7966301 * 2
def baseEnd_7966301 : Nat := 454504605710326838266795

theorem tailTrace_7966301 : CollatzResearch.WordTrace tailWord_7966301 prefixEnd_7966301 454504605710326838266795 := by
  unfold tailWord_7966301
  simp only [CollatzResearch.WordTrace]
  refine ⟨290554867512459487738114757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193703245008306325158743171 290554867512459487738114757)
  ·
    refine ⟨54479037658586153950896517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 290554867512459487738114757 54479037658586153950896517)
    ·
      refine ⟨10214819560984903865793097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54479037658586153950896517 10214819560984903865793097)
      ·
        refine ⟨7661114670738677899344823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10214819560984903865793097 7661114670738677899344823)
        ·
          refine ⟨11491672006108016849017235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7661114670738677899344823 11491672006108016849017235)
          ·
            refine ⟨17237508009162025273525853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11491672006108016849017235 17237508009162025273525853)
            ·
              refine ⟨6464065503435759477572195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17237508009162025273525853 6464065503435759477572195)
              ·
                refine ⟨9696098255153639216358293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6464065503435759477572195 9696098255153639216358293)
                ·
                  refine ⟨454504605710326838266795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9696098255153639216358293 454504605710326838266795)
                  ·
                    rfl

theorem cell23_7966301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 3, 1, 6].length) (baseStart_7966301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7966301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7966301 prefixEnd_7966301 := by exact prefixLift 7966301
  have htrace : WordTrace (prefixWord ++ tailWord_7966301) baseStart_7966301 baseEnd_7966301 := by
    simpa [prefixWord, tailWord_7966301, baseEnd_7966301] using wordTrace_append hprefix tailTrace_7966301
  have hstable : (prefixWord ++ tailWord_7966301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7966301).length < 2 ^ (prefixWord ++ tailWord_7966301).sum := by decide
  have hdescent : baseEnd_7966301 < baseStart_7966301 := by decide
  rcases family_descends (prefixWord ++ tailWord_7966301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7966337 : List Nat := [1, 2, 4, 2, 1, 3, 2, 1, 1, 1, 5]
def baseStart_7966337 : Nat := 118140960795 + 7966337 * 2 ^ 59
def prefixEnd_7966337 : Nat := 4983230072969 + 3 ^ 40 * 7966337 * 2
def baseEnd_7966337 : Nat := 4090559936696503403550989

theorem tailTrace_7966337 : CollatzResearch.WordTrace tailWord_7966337 prefixEnd_7966337 4090559936696503403550989 := by
  unfold tailWord_7966337
  simp only [CollatzResearch.WordTrace]
  refine ⟨290556180540329065886425265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193704120360219377257616843 290556180540329065886425265)
  ·
    refine ⟨217917135405246799414818949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290556180540329065886425265 217917135405246799414818949)
    ·
      refine ⟨40859462888483774890278553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 217917135405246799414818949 40859462888483774890278553)
      ·
        refine ⟨30644597166362831167708915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40859462888483774890278553 30644597166362831167708915)
        ·
          refine ⟨45966895749544246751563373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30644597166362831167708915 45966895749544246751563373)
          ·
            refine ⟨17237585906079092531836265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45966895749544246751563373 17237585906079092531836265)
            ·
              refine ⟨12928189429559319398877199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17237585906079092531836265 12928189429559319398877199)
              ·
                refine ⟨19392284144338979098315799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12928189429559319398877199 19392284144338979098315799)
                ·
                  refine ⟨29088426216508468647473699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19392284144338979098315799 29088426216508468647473699)
                  ·
                    refine ⟨43632639324762702971210549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29088426216508468647473699 43632639324762702971210549)
                    ·
                      refine ⟨4090559936696503403550989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43632639324762702971210549 4090559936696503403550989)
                      ·
                        rfl

theorem cell23_7966337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_7966337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7966337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7966337 prefixEnd_7966337 := by exact prefixLift 7966337
  have htrace : WordTrace (prefixWord ++ tailWord_7966337) baseStart_7966337 baseEnd_7966337 := by
    simpa [prefixWord, tailWord_7966337, baseEnd_7966337] using wordTrace_append hprefix tailTrace_7966337
  have hstable : (prefixWord ++ tailWord_7966337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7966337).length < 2 ^ (prefixWord ++ tailWord_7966337).sum := by decide
  have hdescent : baseEnd_7966337 < baseStart_7966337 := by decide
  rcases family_descends (prefixWord ++ tailWord_7966337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7966363 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 7]
def baseStart_7966363 : Nat := 118140960795 + 7966363 * 2 ^ 59
def prefixEnd_7966363 : Nat := 4983230072969 + 3 ^ 40 * 7966363 * 2
def baseEnd_7966363 : Nat := 4090573287193520301825869

theorem tailTrace_7966363 : CollatzResearch.WordTrace tailWord_7966363 prefixEnd_7966363 4090573287193520301825869 := by
  unfold tailWord_7966363
  simp only [CollatzResearch.WordTrace]
  refine ⟨290557128838234872326871743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193704752558823248217914495 290557128838234872326871743)
  ·
    refine ⟨435835693257352308490307615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290557128838234872326871743 435835693257352308490307615)
    ·
      refine ⟨653753539886028462735461423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435835693257352308490307615 653753539886028462735461423)
      ·
        refine ⟨980630309829042694103192135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 653753539886028462735461423 980630309829042694103192135)
        ·
          refine ⟨1470945464743564041154788203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 980630309829042694103192135 1470945464743564041154788203)
          ·
            refine ⟨2206418197115346061732182305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1470945464743564041154788203 2206418197115346061732182305)
            ·
              refine ⟨1654813647836509546299136729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2206418197115346061732182305 1654813647836509546299136729)
              ·
                refine ⟨1241110235877382159724352547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1654813647836509546299136729 1241110235877382159724352547)
                ·
                  refine ⟨1861665353816073239586528821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1241110235877382159724352547 1861665353816073239586528821)
                  ·
                    refine ⟨174531126920256866211237077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1861665353816073239586528821 174531126920256866211237077)
                    ·
                      refine ⟨4090573287193520301825869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 174531126920256866211237077 4090573287193520301825869)
                      ·
                        rfl

theorem cell23_7966363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 7].length) (baseStart_7966363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7966363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7966363 prefixEnd_7966363 := by exact prefixLift 7966363
  have htrace : WordTrace (prefixWord ++ tailWord_7966363) baseStart_7966363 baseEnd_7966363 := by
    simpa [prefixWord, tailWord_7966363, baseEnd_7966363] using wordTrace_append hprefix tailTrace_7966363
  have hstable : (prefixWord ++ tailWord_7966363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7966363).length < 2 ^ (prefixWord ++ tailWord_7966363).sum := by decide
  have hdescent : baseEnd_7966363 < baseStart_7966363 := by decide
  rcases family_descends (prefixWord ++ tailWord_7966363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7966400 : List Nat := [2, 1, 1, 2, 4, 1, 2, 2, 2, 6]
def baseStart_7966400 : Nat := 118140960795 + 7966400 * 2 ^ 59
def prefixEnd_7966400 : Nat := 4983230072969 + 3 ^ 40 * 7966400 * 2
def baseEnd_7966400 : Nat := 1363530761992578885687733

theorem tailTrace_7966400 : CollatzResearch.WordTrace tailWord_7966400 prefixEnd_7966400 1363530761992578885687733 := by
  unfold tailWord_7966400
  simp only [CollatzResearch.WordTrace]
  refine ⟨145279239169550413822984327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193705652226067218430645769 145279239169550413822984327)
  ·
    refine ⟨217918858754325620734476491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145279239169550413822984327 217918858754325620734476491)
    ·
      refine ⟨326878288131488431101714737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217918858754325620734476491 326878288131488431101714737)
      ·
        refine ⟨245158716098616323326286053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 326878288131488431101714737 245158716098616323326286053)
        ·
          refine ⟨45967259268490560623678635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 245158716098616323326286053 45967259268490560623678635)
          ·
            refine ⟨68950888902735840935517953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45967259268490560623678635 68950888902735840935517953)
            ·
              refine ⟨51713166677051880701638465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68950888902735840935517953 51713166677051880701638465)
              ·
                refine ⟨38784875007788910526228849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51713166677051880701638465 38784875007788910526228849)
                ·
                  refine ⟨29088656255841682894671637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38784875007788910526228849 29088656255841682894671637)
                  ·
                    refine ⟨1363530761992578885687733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29088656255841682894671637 1363530761992578885687733)
                    ·
                      rfl

theorem cell23_7966400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 2, 2, 6].length) (baseStart_7966400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7966400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7966400 prefixEnd_7966400 := by exact prefixLift 7966400
  have htrace : WordTrace (prefixWord ++ tailWord_7966400) baseStart_7966400 baseEnd_7966400 := by
    simpa [prefixWord, tailWord_7966400, baseEnd_7966400] using wordTrace_append hprefix tailTrace_7966400
  have hstable : (prefixWord ++ tailWord_7966400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7966400).length < 2 ^ (prefixWord ++ tailWord_7966400).sum := by decide
  have hdescent : baseEnd_7966400 < baseStart_7966400 := by decide
  rcases family_descends (prefixWord ++ tailWord_7966400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7966407 : List Nat := [1, 1, 4, 1, 1, 1, 3, 2, 3, 4, 2]
def baseStart_7966407 : Nat := 118140960795 + 7966407 * 2 ^ 59
def prefixEnd_7966407 : Nat := 4983230072969 + 3 ^ 40 * 7966407 * 2
def baseEnd_7966407 : Nat := 4090595880342318129675667

theorem tailTrace_7966407 : CollatzResearch.WordTrace tailWord_7966407 prefixEnd_7966407 4090595880342318129675667 := by
  unfold tailWord_7966407
  simp only [CollatzResearch.WordTrace]
  refine ⟨290558733650075467841473475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193705822433383645227648983 290558733650075467841473475)
  ·
    refine ⟨435838100475113201762210213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290558733650075467841473475 435838100475113201762210213)
    ·
      refine ⟨81719643839083725330414415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 435838100475113201762210213 81719643839083725330414415)
      ·
        refine ⟨122579465758625587995621623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81719643839083725330414415 122579465758625587995621623)
        ·
          refine ⟨183869198637938381993432435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122579465758625587995621623 183869198637938381993432435)
          ·
            refine ⟨275803797956907572990148653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183869198637938381993432435 275803797956907572990148653)
            ·
              refine ⟨103426424233840339871305745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 275803797956907572990148653 103426424233840339871305745)
              ·
                refine ⟨77569818175380254903479309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103426424233840339871305745 77569818175380254903479309)
                ·
                  refine ⟨29088681815767595588804741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77569818175380254903479309 29088681815767595588804741)
                  ·
                    refine ⟨5454127840456424172900889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29088681815767595588804741 5454127840456424172900889)
                    ·
                      refine ⟨4090595880342318129675667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5454127840456424172900889 4090595880342318129675667)
                      ·
                        rfl

theorem cell23_7966407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 3, 4, 2].length) (baseStart_7966407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7966407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7966407 prefixEnd_7966407 := by exact prefixLift 7966407
  have htrace : WordTrace (prefixWord ++ tailWord_7966407) baseStart_7966407 baseEnd_7966407 := by
    simpa [prefixWord, tailWord_7966407, baseEnd_7966407] using wordTrace_append hprefix tailTrace_7966407
  have hstable : (prefixWord ++ tailWord_7966407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7966407).length < 2 ^ (prefixWord ++ tailWord_7966407).sum := by decide
  have hdescent : baseEnd_7966407 < baseStart_7966407 := by decide
  rcases family_descends (prefixWord ++ tailWord_7966407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7966424 : List Nat := [2, 1, 2, 2, 3, 1, 4, 1, 1, 4, 2]
def baseStart_7966424 : Nat := 118140960795 + 7966424 * 2 ^ 59
def prefixEnd_7966424 : Nat := 4983230072969 + 3 ^ 40 * 7966424 * 2
def baseEnd_7966424 : Nat := 4090604609513444563163089

theorem tailTrace_7966424 : CollatzResearch.WordTrace tailWord_7966424 prefixEnd_7966424 4090604609513444563163089 := by
  unfold tailWord_7966424
  simp only [CollatzResearch.WordTrace]
  refine ⟨145279676845506939872421163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193706235794009253163228217 145279676845506939872421163)
  ·
    refine ⟨217919515268260409808631745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145279676845506939872421163 217919515268260409808631745)
    ·
      refine ⟨163439636451195307356473809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217919515268260409808631745 163439636451195307356473809)
      ·
        refine ⟨122579727338396480517355357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163439636451195307356473809 122579727338396480517355357)
        ·
          refine ⟨45967397751898680194008259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122579727338396480517355357 45967397751898680194008259)
          ·
            refine ⟨68951096627848020291012389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45967397751898680194008259 68951096627848020291012389)
            ·
              refine ⟨12928330617721503804564823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68951096627848020291012389 12928330617721503804564823)
              ·
                refine ⟨19392495926582255706847235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12928330617721503804564823 19392495926582255706847235)
                ·
                  refine ⟨29088743889873383560270853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19392495926582255706847235 29088743889873383560270853)
                  ·
                    refine ⟨5454139479351259417550785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29088743889873383560270853 5454139479351259417550785)
                    ·
                      refine ⟨4090604609513444563163089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5454139479351259417550785 4090604609513444563163089)
                      ·
                        rfl

theorem cell23_7966424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 1, 1, 4, 2].length) (baseStart_7966424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7966424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7966424 prefixEnd_7966424 := by exact prefixLift 7966424
  have htrace : WordTrace (prefixWord ++ tailWord_7966424) baseStart_7966424 baseEnd_7966424 := by
    simpa [prefixWord, tailWord_7966424, baseEnd_7966424] using wordTrace_append hprefix tailTrace_7966424
  have hstable : (prefixWord ++ tailWord_7966424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7966424).length < 2 ^ (prefixWord ++ tailWord_7966424).sum := by decide
  have hdescent : baseEnd_7966424 < baseStart_7966424 := by decide
  rcases family_descends (prefixWord ++ tailWord_7966424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7966467 : List Nat := [1, 1, 1, 3, 2, 2, 2, 1, 1, 7, 2]
def baseStart_7966467 : Nat := 118140960795 + 7966467 * 2 ^ 59
def prefixEnd_7966467 : Nat := 4983230072969 + 3 ^ 40 * 7966467 * 2
def baseEnd_7966467 : Nat := 4090626689181587894925391

theorem tailTrace_7966467 : CollatzResearch.WordTrace tailWord_7966467 prefixEnd_7966467 4090626689181587894925391 := by
  unfold tailWord_7966467
  simp only [CollatzResearch.WordTrace]
  refine ⟨290560922029858098088657655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193707281353238732059105103 290560922029858098088657655)
  ·
    refine ⟨435841383044787147132986483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290560922029858098088657655 435841383044787147132986483)
    ·
      refine ⟨653762074567180720699479725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435841383044787147132986483 653762074567180720699479725)
      ·
        refine ⟨245160777962692770262304897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 653762074567180720699479725 245160777962692770262304897)
        ·
          refine ⟨183870583472019577696728673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245160777962692770262304897 183870583472019577696728673)
          ·
            refine ⟨137902937604014683272546505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183870583472019577696728673 137902937604014683272546505)
            ·
              refine ⟨103427203203011012454409879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137902937604014683272546505 103427203203011012454409879)
              ·
                refine ⟨155140804804516518681614819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103427203203011012454409879 155140804804516518681614819)
                ·
                  refine ⟨232711207206774778022422229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 155140804804516518681614819 232711207206774778022422229)
                  ·
                    refine ⟨5454168918908783859900521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 232711207206774778022422229 5454168918908783859900521)
                    ·
                      refine ⟨4090626689181587894925391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5454168918908783859900521 4090626689181587894925391)
                      ·
                        rfl

theorem cell23_7966467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 7, 2].length) (baseStart_7966467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7966467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7966467 prefixEnd_7966467 := by exact prefixLift 7966467
  have htrace : WordTrace (prefixWord ++ tailWord_7966467) baseStart_7966467 baseEnd_7966467 := by
    simpa [prefixWord, tailWord_7966467, baseEnd_7966467] using wordTrace_append hprefix tailTrace_7966467
  have hstable : (prefixWord ++ tailWord_7966467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7966467).length < 2 ^ (prefixWord ++ tailWord_7966467).sum := by decide
  have hdescent : baseEnd_7966467 < baseStart_7966467 := by decide
  rcases family_descends (prefixWord ++ tailWord_7966467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7966497 : List Nat := [1, 2, 3, 2, 1, 3, 2, 1, 1, 3, 4]
def baseStart_7966497 : Nat := 118140960795 + 7966497 * 2 ^ 59
def prefixEnd_7966497 : Nat := 4983230072969 + 3 ^ 40 * 7966497 * 2
def baseEnd_7966497 : Nat := 4090642093601222777550253

theorem tailTrace_7966497 : CollatzResearch.WordTrace tailWord_7966497 prefixEnd_7966497 4090642093601222777550253 := by
  unfold tailWord_7966497
  simp only [CollatzResearch.WordTrace]
  refine ⟨290562016219749413212249745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193708010813166275474833163 290562016219749413212249745)
  ·
    refine ⟨217921512164812059909187309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290562016219749413212249745 217921512164812059909187309)
    ·
      refine ⟨81720567061804522465945241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217921512164812059909187309 81720567061804522465945241)
      ·
        refine ⟨61290425296353391849458931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81720567061804522465945241 61290425296353391849458931)
        ·
          refine ⟨91935637944530087774188397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61290425296353391849458931 91935637944530087774188397)
          ·
            refine ⟨34475864229198782915320649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91935637944530087774188397 34475864229198782915320649)
            ·
              refine ⟨25856898171899087186490487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34475864229198782915320649 25856898171899087186490487)
              ·
                refine ⟨38785347257848630779735731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25856898171899087186490487 38785347257848630779735731)
                ·
                  refine ⟨58178020886772946169603597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38785347257848630779735731 58178020886772946169603597)
                  ·
                    refine ⟨21816757832539854813601349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58178020886772946169603597 21816757832539854813601349)
                    ·
                      refine ⟨4090642093601222777550253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21816757832539854813601349 4090642093601222777550253)
                      ·
                        rfl

theorem cell23_7966497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_7966497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7966497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7966497 prefixEnd_7966497 := by exact prefixLift 7966497
  have htrace : WordTrace (prefixWord ++ tailWord_7966497) baseStart_7966497 baseEnd_7966497 := by
    simpa [prefixWord, tailWord_7966497, baseEnd_7966497] using wordTrace_append hprefix tailTrace_7966497
  have hstable : (prefixWord ++ tailWord_7966497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7966497).length < 2 ^ (prefixWord ++ tailWord_7966497).sum := by decide
  have hdescent : baseEnd_7966497 < baseStart_7966497 := by decide
  rcases family_descends (prefixWord ++ tailWord_7966497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7966514 : List Nat := [3, 2, 1, 1, 3, 3, 1, 2, 2, 1, 4]
def baseStart_7966514 : Nat := 118140960795 + 7966514 * 2 ^ 59
def prefixEnd_7966514 : Nat := 4983230072969 + 3 ^ 40 * 7966514 * 2
def baseEnd_7966514 : Nat := 4090650822772349211037675

theorem tailTrace_7966514 : CollatzResearch.WordTrace tailWord_7966514 prefixEnd_7966514 4090650822772349211037675 := by
  unfold tailWord_7966514
  simp only [CollatzResearch.WordTrace]
  refine ⟨72640659065171956278904649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193708424173791883410412397 72640659065171956278904649)
  ·
    refine ⟨54480494298878967209178487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72640659065171956278904649 54480494298878967209178487)
    ·
      refine ⟨81720741448318450813767731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54480494298878967209178487 81720741448318450813767731)
      ·
        refine ⟨122581112172477676220651597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81720741448318450813767731 122581112172477676220651597)
        ·
          refine ⟨45967917064679128582744349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122581112172477676220651597 45967917064679128582744349)
          ·
            refine ⟨17237968899254673218529131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45967917064679128582744349 17237968899254673218529131)
            ·
              refine ⟨25856953348882009827793697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17237968899254673218529131 25856953348882009827793697)
              ·
                refine ⟨19392715011661507370845273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25856953348882009827793697 19392715011661507370845273)
                ·
                  refine ⟨14544536258746130528133955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19392715011661507370845273 14544536258746130528133955)
                  ·
                    refine ⟨21816804388119195792200933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14544536258746130528133955 21816804388119195792200933)
                    ·
                      refine ⟨4090650822772349211037675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21816804388119195792200933 4090650822772349211037675)
                      ·
                        rfl

theorem cell23_7966514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 2, 2, 1, 4].length) (baseStart_7966514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7966514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7966514 prefixEnd_7966514 := by exact prefixLift 7966514
  have htrace : WordTrace (prefixWord ++ tailWord_7966514) baseStart_7966514 baseEnd_7966514 := by
    simpa [prefixWord, tailWord_7966514, baseEnd_7966514] using wordTrace_append hprefix tailTrace_7966514
  have hstable : (prefixWord ++ tailWord_7966514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7966514).length < 2 ^ (prefixWord ++ tailWord_7966514).sum := by decide
  have hdescent : baseEnd_7966514 < baseStart_7966514 := by decide
  rcases family_descends (prefixWord ++ tailWord_7966514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7966524 : List Nat := [2, 2, 2, 2, 1, 1, 5, 1, 3, 4]
def baseStart_7966524 : Nat := 118140960795 + 7966524 * 2 ^ 59
def prefixEnd_7966524 : Nat := 4983230072969 + 3 ^ 40 * 7966524 * 2
def baseEnd_7966524 : Nat := 1363551985859631390637543

theorem tailTrace_7966524 : CollatzResearch.WordTrace tailWord_7966524 prefixEnd_7966524 1363551985859631390637543 := by
  unfold tailWord_7966524
  simp only [CollatzResearch.WordTrace]
  refine ⟨145281500495325798411741313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193708667327101064548988417 145281500495325798411741313)
  ·
    refine ⟨108961125371494348808805985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145281500495325798411741313 108961125371494348808805985)
    ·
      refine ⟨81720844028620761606604489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108961125371494348808805985 81720844028620761606604489)
      ·
        refine ⟨61290633021465571204953367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81720844028620761606604489 61290633021465571204953367)
        ·
          refine ⟨91935949532198356807430051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61290633021465571204953367 91935949532198356807430051)
          ·
            refine ⟨137903924298297535211145077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91935949532198356807430051 137903924298297535211145077)
            ·
              refine ⟨12928492902965393926044851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 137903924298297535211145077 12928492902965393926044851)
              ·
                refine ⟨19392739354448090889067277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12928492902965393926044851 19392739354448090889067277)
                ·
                  refine ⟨7272277257918034083400229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19392739354448090889067277 7272277257918034083400229)
                  ·
                    refine ⟨1363551985859631390637543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7272277257918034083400229 1363551985859631390637543)
                    ·
                      rfl

theorem cell23_7966524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 1, 3, 4].length) (baseStart_7966524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7966524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7966524 prefixEnd_7966524 := by exact prefixLift 7966524
  have htrace : WordTrace (prefixWord ++ tailWord_7966524) baseStart_7966524 baseEnd_7966524 := by
    simpa [prefixWord, tailWord_7966524, baseEnd_7966524] using wordTrace_append hprefix tailTrace_7966524
  have hstable : (prefixWord ++ tailWord_7966524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7966524).length < 2 ^ (prefixWord ++ tailWord_7966524).sum := by decide
  have hdescent : baseEnd_7966524 < baseStart_7966524 := by decide
  rcases family_descends (prefixWord ++ tailWord_7966524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7966537 : List Nat := [1, 2, 1, 1, 2, 4, 3, 3, 6]
def baseStart_7966537 : Nat := 118140960795 + 7966537 * 2 ^ 59
def prefixEnd_7966537 : Nat := 4983230072969 + 3 ^ 40 * 7966537 * 2
def baseEnd_7966537 : Nat := 454518070314155846783341

theorem tailTrace_7966537 : CollatzResearch.WordTrace tailWord_7966537 prefixEnd_7966537 454518070314155846783341 := by
  unfold tailWord_7966537
  simp only [CollatzResearch.WordTrace]
  refine ⟨290563475139604500043705865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193708983426403000029137243 290563475139604500043705865)
  ·
    refine ⟨217922606354703375032779399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290563475139604500043705865 217922606354703375032779399)
    ·
      refine ⟨326883909532055062549169099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217922606354703375032779399 326883909532055062549169099)
      ·
        refine ⟨490325864298082593823753649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326883909532055062549169099 490325864298082593823753649)
        ·
          refine ⟨367744398223561945367815237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 490325864298082593823753649 367744398223561945367815237)
          ·
            refine ⟨68952074666917864756465357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 367744398223561945367815237 68952074666917864756465357)
            ·
              refine ⟨25857028000094199283674509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68952074666917864756465357 25857028000094199283674509)
              ·
                refine ⟨9696385500035324731377941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25857028000094199283674509 9696385500035324731377941)
                ·
                  refine ⟨454518070314155846783341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9696385500035324731377941 454518070314155846783341)
                  ·
                    rfl

theorem cell23_7966537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 3, 6].length) (baseStart_7966537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7966537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7966537 prefixEnd_7966537 := by exact prefixLift 7966537
  have htrace : WordTrace (prefixWord ++ tailWord_7966537) baseStart_7966537 baseEnd_7966537 := by
    simpa [prefixWord, tailWord_7966537, baseEnd_7966537] using wordTrace_append hprefix tailTrace_7966537
  have hstable : (prefixWord ++ tailWord_7966537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7966537).length < 2 ^ (prefixWord ++ tailWord_7966537).sum := by decide
  have hdescent : baseEnd_7966537 < baseStart_7966537 := by decide
  rcases family_descends (prefixWord ++ tailWord_7966537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7966551 : List Nat := [1, 1, 3, 2, 5, 1, 2, 1, 2, 2, 3]
def baseStart_7966551 : Nat := 118140960795 + 7966551 * 2 ^ 59
def prefixEnd_7966551 : Nat := 4983230072969 + 3 ^ 40 * 7966551 * 2
def baseEnd_7966551 : Nat := 4090669821556565566275005

theorem tailTrace_7966551 : CollatzResearch.WordTrace tailWord_7966551 prefixEnd_7966551 4090669821556565566275005 := by
  unfold tailWord_7966551
  simp only [CollatzResearch.WordTrace]
  refine ⟨290563985761553780434715507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193709323841035853623143671 290563985761553780434715507)
  ·
    refine ⟨435845978642330670652073261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290563985761553780434715507 435845978642330670652073261)
    ·
      refine ⟨163442241990874001494527473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 435845978642330670652073261 163442241990874001494527473)
      ·
        refine ⟨122581681493155501120895605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163442241990874001494527473 122581681493155501120895605)
        ·
          refine ⟨11492032639983328230083963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 122581681493155501120895605 11492032639983328230083963)
          ·
            refine ⟨17238048959974992345125945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11492032639983328230083963 17238048959974992345125945)
            ·
              refine ⟨12928536719981244258844459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17238048959974992345125945 12928536719981244258844459)
              ·
                refine ⟨19392805079971866388266689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12928536719981244258844459 19392805079971866388266689)
                ·
                  refine ⟨14544603809978899791200017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19392805079971866388266689 14544603809978899791200017)
                  ·
                    refine ⟨10908452857484174843400013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14544603809978899791200017 10908452857484174843400013)
                    ·
                      refine ⟨4090669821556565566275005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10908452857484174843400013 4090669821556565566275005)
                      ·
                        rfl

theorem cell23_7966551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 1, 2, 2, 3].length) (baseStart_7966551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7966551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7966551 prefixEnd_7966551 := by exact prefixLift 7966551
  have htrace : WordTrace (prefixWord ++ tailWord_7966551) baseStart_7966551 baseEnd_7966551 := by
    simpa [prefixWord, tailWord_7966551, baseEnd_7966551] using wordTrace_append hprefix tailTrace_7966551
  have hstable : (prefixWord ++ tailWord_7966551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7966551).length < 2 ^ (prefixWord ++ tailWord_7966551).sum := by decide
  have hdescent : baseEnd_7966551 < baseStart_7966551 := by decide
  rcases family_descends (prefixWord ++ tailWord_7966551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7966581 : List Nat := [1, 3, 4, 1, 1, 1, 2, 3, 3, 1, 3]
def baseStart_7966581 : Nat := 118140960795 + 7966581 * 2 ^ 59
def prefixEnd_7966581 : Nat := 4983230072969 + 3 ^ 40 * 7966581 * 2
def baseEnd_7966581 : Nat := 4090685225976200448899867

theorem tailTrace_7966581 : CollatzResearch.WordTrace tailWord_7966581 prefixEnd_7966581 4090685225976200448899867 := by
  unfold tailWord_7966581
  simp only [CollatzResearch.WordTrace]
  refine ⟨290565079951445095558307597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193710053300963397038871731 290565079951445095558307597)
  ·
    refine ⟨108961904981791910834365349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290565079951445095558307597 108961904981791910834365349)
    ·
      refine ⟨20430357184085983281443503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108961904981791910834365349 20430357184085983281443503)
      ·
        refine ⟨30645535776128974922165255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20430357184085983281443503 30645535776128974922165255)
        ·
          refine ⟨45968303664193462383247883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30645535776128974922165255 45968303664193462383247883)
          ·
            refine ⟨68952455496290193574871825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45968303664193462383247883 68952455496290193574871825)
            ·
              refine ⟨51714341622217645181153869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68952455496290193574871825 51714341622217645181153869)
              ·
                refine ⟨19392878108331616942932701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51714341622217645181153869 19392878108331616942932701)
                ·
                  refine ⟨7272329290624356353599763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19392878108331616942932701 7272329290624356353599763)
                  ·
                    refine ⟨10908493935936534530399645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7272329290624356353599763 10908493935936534530399645)
                    ·
                      refine ⟨4090685225976200448899867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10908493935936534530399645 4090685225976200448899867)
                      ·
                        rfl

theorem cell23_7966581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_7966581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7966581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7966581 prefixEnd_7966581 := by exact prefixLift 7966581
  have htrace : WordTrace (prefixWord ++ tailWord_7966581) baseStart_7966581 baseEnd_7966581 := by
    simpa [prefixWord, tailWord_7966581, baseEnd_7966581] using wordTrace_append hprefix tailTrace_7966581
  have hstable : (prefixWord ++ tailWord_7966581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7966581).length < 2 ^ (prefixWord ++ tailWord_7966581).sum := by decide
  have hdescent : baseEnd_7966581 < baseStart_7966581 := by decide
  rcases family_descends (prefixWord ++ tailWord_7966581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7966604 : List Nat := [2, 2, 1, 2, 1, 2, 1, 6, 1, 1, 4]
def baseStart_7966604 : Nat := 118140960795 + 7966604 * 2 ^ 59
def prefixEnd_7966604 : Nat := 4983230072969 + 3 ^ 40 * 7966604 * 2
def baseEnd_7966604 : Nat := 4090697036031253858912261

theorem tailTrace_7966604 : CollatzResearch.WordTrace tailWord_7966604 prefixEnd_7966604 4090697036031253858912261 := by
  unfold tailWord_7966604
  simp only [CollatzResearch.WordTrace]
  refine ⟨145282959415180885243197433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193710612553574513657596577 145282959415180885243197433)
  ·
    refine ⟨108962219561385663932398075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145282959415180885243197433 108962219561385663932398075)
    ·
      refine ⟨163443329342078495898597113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108962219561385663932398075 163443329342078495898597113)
      ·
        refine ⟨122582497006558871923947835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163443329342078495898597113 122582497006558871923947835)
        ·
          refine ⟨183873745509838307885921753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122582497006558871923947835 183873745509838307885921753)
          ·
            refine ⟨137905309132378730914441315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183873745509838307885921753 137905309132378730914441315)
            ·
              refine ⟨206857963698568096371661973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137905309132378730914441315 206857963698568096371661973)
              ·
                refine ⟨9696467048370379517421655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 206857963698568096371661973 9696467048370379517421655)
                ·
                  refine ⟨14544700572555569276132483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9696467048370379517421655 14544700572555569276132483)
                  ·
                    refine ⟨21817050858833353914198725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14544700572555569276132483 21817050858833353914198725)
                    ·
                      refine ⟨4090697036031253858912261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21817050858833353914198725 4090697036031253858912261)
                      ·
                        rfl

theorem cell23_7966604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 6, 1, 1, 4].length) (baseStart_7966604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7966604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7966604 prefixEnd_7966604 := by exact prefixLift 7966604
  have htrace : WordTrace (prefixWord ++ tailWord_7966604) baseStart_7966604 baseEnd_7966604 := by
    simpa [prefixWord, tailWord_7966604, baseEnd_7966604] using wordTrace_append hprefix tailTrace_7966604
  have hstable : (prefixWord ++ tailWord_7966604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7966604).length < 2 ^ (prefixWord ++ tailWord_7966604).sum := by decide
  have hdescent : baseEnd_7966604 < baseStart_7966604 := by decide
  rcases family_descends (prefixWord ++ tailWord_7966604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7966618 : List Nat := [3, 1, 1, 4, 2, 3, 2, 1, 1, 5]
def baseStart_7966618 : Nat := 118140960795 + 7966618 * 2 ^ 59
def prefixEnd_7966618 : Nat := 4983230072969 + 3 ^ 40 * 7966618 * 2
def baseEnd_7966618 : Nat := 1363568074920138934712399

theorem tailTrace_7966618 : CollatzResearch.WordTrace tailWord_7966618 prefixEnd_7966618 1363568074920138934712399 := by
  unfold tailWord_7966618
  simp only [CollatzResearch.WordTrace]
  refine ⟨72641607363077762719351127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193710952968207367251603005 72641607363077762719351127)
  ·
    refine ⟨108962411044616644079026691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72641607363077762719351127 108962411044616644079026691)
    ·
      refine ⟨163443616566924966118540037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108962411044616644079026691 163443616566924966118540037)
      ·
        refine ⟨30645678106298431147226257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 163443616566924966118540037 30645678106298431147226257)
        ·
          refine ⟨22984258579723823360419693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30645678106298431147226257 22984258579723823360419693)
          ·
            refine ⟨8619096967396433760157385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22984258579723823360419693 8619096967396433760157385)
            ·
              refine ⟨6464322725547325320118039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8619096967396433760157385 6464322725547325320118039)
              ·
                refine ⟨9696484088320987980177059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6464322725547325320118039 9696484088320987980177059)
                ·
                  refine ⟨14544726132481481970265589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9696484088320987980177059 14544726132481481970265589)
                  ·
                    refine ⟨1363568074920138934712399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14544726132481481970265589 1363568074920138934712399)
                    ·
                      rfl

theorem cell23_7966618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 2, 1, 1, 5].length) (baseStart_7966618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7966618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7966618 prefixEnd_7966618 := by exact prefixLift 7966618
  have htrace : WordTrace (prefixWord ++ tailWord_7966618) baseStart_7966618 baseEnd_7966618 := by
    simpa [prefixWord, tailWord_7966618, baseEnd_7966618] using wordTrace_append hprefix tailTrace_7966618
  have hstable : (prefixWord ++ tailWord_7966618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7966618).length < 2 ^ (prefixWord ++ tailWord_7966618).sum := by decide
  have hdescent : baseEnd_7966618 < baseStart_7966618 := by decide
  rcases family_descends (prefixWord ++ tailWord_7966618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7966621 : List Nat := [1, 4, 2, 1, 2, 3, 1, 3, 1, 1, 4]
def baseStart_7966621 : Nat := 118140960795 + 7966621 * 2 ^ 59
def prefixEnd_7966621 : Nat := 4983230072969 + 3 ^ 40 * 7966621 * 2
def baseEnd_7966621 : Nat := 4090705765202380292399683

theorem tailTrace_7966621 : CollatzResearch.WordTrace tailWord_7966621 prefixEnd_7966621 4090705765202380292399683 := by
  unfold tailWord_7966621
  simp only [CollatzResearch.WordTrace]
  refine ⟨290566538871300182389763717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193711025914200121593175811 290566538871300182389763717)
  ·
    refine ⟨54481226038368784198080697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 290566538871300182389763717 54481226038368784198080697)
    ·
      refine ⟨40860919528776588148560523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54481226038368784198080697 40860919528776588148560523)
      ·
        refine ⟨61291379293164882222840785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40860919528776588148560523 61291379293164882222840785)
        ·
          refine ⟨45968534469873661667130589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61291379293164882222840785 45968534469873661667130589)
          ·
            refine ⟨17238200426202623125173971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45968534469873661667130589 17238200426202623125173971)
            ·
              refine ⟨25857300639303934687760957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17238200426202623125173971 25857300639303934687760957)
              ·
                refine ⟨9696487739738975507910359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25857300639303934687760957 9696487739738975507910359)
                ·
                  refine ⟨14544731609608463261865539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9696487739738975507910359 14544731609608463261865539)
                  ·
                    refine ⟨21817097414412694892798309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14544731609608463261865539 21817097414412694892798309)
                    ·
                      refine ⟨4090705765202380292399683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21817097414412694892798309 4090705765202380292399683)
                      ·
                        rfl

theorem cell23_7966621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 3, 1, 1, 4].length) (baseStart_7966621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7966621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7966621 prefixEnd_7966621 := by exact prefixLift 7966621
  have htrace : WordTrace (prefixWord ++ tailWord_7966621) baseStart_7966621 baseEnd_7966621 := by
    simpa [prefixWord, tailWord_7966621, baseEnd_7966621] using wordTrace_append hprefix tailTrace_7966621
  have hstable : (prefixWord ++ tailWord_7966621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7966621).length < 2 ^ (prefixWord ++ tailWord_7966621).sum := by decide
  have hdescent : baseEnd_7966621 < baseStart_7966621 := by decide
  rcases family_descends (prefixWord ++ tailWord_7966621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7966631 : List Nat := [1, 1, 6, 1, 2, 2, 1, 1, 4, 4]
def baseStart_7966631 : Nat := 118140960795 + 7966631 * 2 ^ 59
def prefixEnd_7966631 : Nat := 4983230072969 + 3 ^ 40 * 7966631 * 2
def baseEnd_7966631 : Nat := 1363570300002975084424879

theorem tailTrace_7966631 : CollatzResearch.WordTrace tailWord_7966631 prefixEnd_7966631 1363570300002975084424879 := by
  unfold tailWord_7966631
  simp only [CollatzResearch.WordTrace]
  refine ⟨290566903601263954097627747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193711269067509302731751831 290566903601263954097627747)
  ·
    refine ⟨435850355401895931146441621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290566903601263954097627747 435850355401895931146441621)
    ·
      refine ⟨20430485409463871772489451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 435850355401895931146441621 20430485409463871772489451)
      ·
        refine ⟨30645728114195807658734177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20430485409463871772489451 30645728114195807658734177)
        ·
          refine ⟨22984296085646855744050633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30645728114195807658734177 22984296085646855744050633)
          ·
            refine ⟨17238222064235141808037975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22984296085646855744050633 17238222064235141808037975)
            ·
              refine ⟨25857333096352712712056963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17238222064235141808037975 25857333096352712712056963)
              ·
                refine ⟨38785999644529069068085445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25857333096352712712056963 38785999644529069068085445)
                ·
                  refine ⟨7272374933349200450266021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38785999644529069068085445 7272374933349200450266021)
                  ·
                    refine ⟨1363570300002975084424879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7272374933349200450266021 1363570300002975084424879)
                    ·
                      rfl

theorem cell23_7966631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_7966631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7966631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7966631 prefixEnd_7966631 := by exact prefixLift 7966631
  have htrace : WordTrace (prefixWord ++ tailWord_7966631) baseStart_7966631 baseEnd_7966631 := by
    simpa [prefixWord, tailWord_7966631, baseEnd_7966631] using wordTrace_append hprefix tailTrace_7966631
  have hstable : (prefixWord ++ tailWord_7966631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7966631).length < 2 ^ (prefixWord ++ tailWord_7966631).sum := by decide
  have hdescent : baseEnd_7966631 < baseStart_7966631 := by decide
  rcases family_descends (prefixWord ++ tailWord_7966631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7966667 : List Nat := [1, 1, 1, 1, 3, 4, 1, 1, 1, 4, 5]
def baseStart_7966667 : Nat := 118140960795 + 7966667 * 2 ^ 59
def prefixEnd_7966667 : Nat := 4983230072969 + 3 ^ 40 * 7966667 * 2
def baseEnd_7966667 : Nat := 4090729385312487112424471

theorem tailTrace_7966667 : CollatzResearch.WordTrace tailWord_7966667 prefixEnd_7966667 4090729385312487112424471 := by
  unfold tailWord_7966667
  simp only [CollatzResearch.WordTrace]
  refine ⟨290568216629133532245938255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193712144419422354830625503 290568216629133532245938255)
  ·
    refine ⟨435852324943700298368907383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290568216629133532245938255 435852324943700298368907383)
    ·
      refine ⟨653778487415550447553361075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435852324943700298368907383 653778487415550447553361075)
      ·
        refine ⟨980667731123325671330041613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 653778487415550447553361075 980667731123325671330041613)
        ·
          refine ⟨367750399171247126748765605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 980667731123325671330041613 367750399171247126748765605)
          ·
            refine ⟨68953199844608836265393551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 367750399171247126748765605 68953199844608836265393551)
            ·
              refine ⟨103429799766913254398090327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68953199844608836265393551 103429799766913254398090327)
              ·
                refine ⟨155144699650369881597135491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103429799766913254398090327 155144699650369881597135491)
                ·
                  refine ⟨232717049475554822395703237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 155144699650369881597135491 232717049475554822395703237)
                  ·
                    refine ⟨43634446776666529199194357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 232717049475554822395703237 43634446776666529199194357)
                    ·
                      refine ⟨4090729385312487112424471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43634446776666529199194357 4090729385312487112424471)
                      ·
                        rfl

theorem cell23_7966667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 4, 5].length) (baseStart_7966667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7966667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7966667 prefixEnd_7966667 := by exact prefixLift 7966667
  have htrace : WordTrace (prefixWord ++ tailWord_7966667) baseStart_7966667 baseEnd_7966667 := by
    simpa [prefixWord, tailWord_7966667, baseEnd_7966667] using wordTrace_append hprefix tailTrace_7966667
  have hstable : (prefixWord ++ tailWord_7966667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7966667).length < 2 ^ (prefixWord ++ tailWord_7966667).sum := by decide
  have hdescent : baseEnd_7966667 < baseStart_7966667 := by decide
  rcases family_descends (prefixWord ++ tailWord_7966667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7966678 : List Nat := [5, 2, 1, 1, 4, 1, 9]
def baseStart_7966678 : Nat := 118140960795 + 7966678 * 2 ^ 59
def prefixEnd_7966678 : Nat := 4983230072969 + 3 ^ 40 * 7966678 * 2
def baseEnd_7966678 : Nat := 50502901649378846535641

theorem tailTrace_7966678 : CollatzResearch.WordTrace tailWord_7966678 prefixEnd_7966678 50502901649378846535641 := by
  unfold tailWord_7966678
  simp only [CollatzResearch.WordTrace]
  refine ⟨18160538614505855070286793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 193712411888062454083059125 18160538614505855070286793)
  ·
    refine ⟨13620403960879391302715095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18160538614505855070286793 13620403960879391302715095)
    ·
      refine ⟨20430605941319086954072643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13620403960879391302715095 20430605941319086954072643)
      ·
        refine ⟨30645908911978630431108965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20430605941319086954072643 30645908911978630431108965)
        ·
          refine ⟨5746107920995993205832931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30645908911978630431108965 5746107920995993205832931)
          ·
            refine ⟨8619161881493989808749397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5746107920995993205832931 8619161881493989808749397)
            ·
              refine ⟨50502901649378846535641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8619161881493989808749397 50502901649378846535641)
              ·
                rfl

theorem cell23_7966678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 9].length) (baseStart_7966678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7966678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7966678 prefixEnd_7966678 := by exact prefixLift 7966678
  have htrace : WordTrace (prefixWord ++ tailWord_7966678) baseStart_7966678 baseEnd_7966678 := by
    simpa [prefixWord, tailWord_7966678, baseEnd_7966678] using wordTrace_append hprefix tailTrace_7966678
  have hstable : (prefixWord ++ tailWord_7966678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7966678).length < 2 ^ (prefixWord ++ tailWord_7966678).sum := by decide
  have hdescent : baseEnd_7966678 < baseStart_7966678 := by decide
  rcases family_descends (prefixWord ++ tailWord_7966678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7966707 : List Nat := [1, 1, 1, 2, 2, 2, 1, 2, 2, 3, 6]
def baseStart_7966707 : Nat := 118140960795 + 7966707 * 2 ^ 59
def prefixEnd_7966707 : Nat := 4983230072969 + 3 ^ 40 * 7966707 * 2
def baseEnd_7966707 : Nat := 4090749924538666955924287

theorem tailTrace_7966707 : CollatzResearch.WordTrace tailWord_7966707 prefixEnd_7966707 4090749924538666955924287 := by
  unfold tailWord_7966707
  simp only [CollatzResearch.WordTrace]
  refine ⟨290569675548988619077394375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193713117032659079384929583 290569675548988619077394375)
  ·
    refine ⟨435854513323482928616091563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290569675548988619077394375 435854513323482928616091563)
    ·
      refine ⟨653781769985224392924137345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435854513323482928616091563 653781769985224392924137345)
      ·
        refine ⟨490336327488918294693103009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 653781769985224392924137345 490336327488918294693103009)
        ·
          refine ⟨367752245616688721019827257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 490336327488918294693103009 367752245616688721019827257)
          ·
            refine ⟨275814184212516540764870443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 367752245616688721019827257 275814184212516540764870443)
            ·
              refine ⟨413721276318774811147305665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275814184212516540764870443 413721276318774811147305665)
              ·
                refine ⟨310290957239081108360479249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 413721276318774811147305665 310290957239081108360479249)
                ·
                  refine ⟨232718217929310831270359437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 310290957239081108360479249 232718217929310831270359437)
                  ·
                    refine ⟨87269331723491561726384789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 232718217929310831270359437 87269331723491561726384789)
                    ·
                      refine ⟨4090749924538666955924287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87269331723491561726384789 4090749924538666955924287)
                      ·
                        rfl

theorem cell23_7966707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 3, 6].length) (baseStart_7966707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7966707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7966707 prefixEnd_7966707 := by exact prefixLift 7966707
  have htrace : WordTrace (prefixWord ++ tailWord_7966707) baseStart_7966707 baseEnd_7966707 := by
    simpa [prefixWord, tailWord_7966707, baseEnd_7966707] using wordTrace_append hprefix tailTrace_7966707
  have hstable : (prefixWord ++ tailWord_7966707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7966707).length < 2 ^ (prefixWord ++ tailWord_7966707).sum := by decide
  have hdescent : baseEnd_7966707 < baseStart_7966707 := by decide
  rcases family_descends (prefixWord ++ tailWord_7966707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7966726 : List Nat := [6, 2, 1, 2, 1, 1, 3, 1, 1, 2, 3]
def baseStart_7966726 : Nat := 118140960795 + 7966726 * 2 ^ 59
def prefixEnd_7966726 : Nat := 4983230072969 + 3 ^ 40 * 7966726 * 2
def baseEnd_7966726 : Nat := 4090759680671102381586701

theorem tailTrace_7966726 : CollatzResearch.WordTrace tailWord_7966726 prefixEnd_7966726 4090759680671102381586701 := by
  unfold tailWord_7966726
  simp only [CollatzResearch.WordTrace]
  refine ⟨9080324016747493291323001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 193713579023946523548224021 9080324016747493291323001)
  ·
    refine ⟨6810243012560619968492251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9080324016747493291323001 6810243012560619968492251)
    ·
      refine ⟨10215364518840929952738377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6810243012560619968492251 10215364518840929952738377)
      ·
        refine ⟨7661523389130697464553783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10215364518840929952738377 7661523389130697464553783)
        ·
          refine ⟨11492285083696046196830675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7661523389130697464553783 11492285083696046196830675)
          ·
            refine ⟨17238427625544069295246013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11492285083696046196830675 17238427625544069295246013)
            ·
              refine ⟨6464410359579025985717255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17238427625544069295246013 6464410359579025985717255)
              ·
                refine ⟨9696615539368538978575883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6464410359579025985717255 9696615539368538978575883)
                ·
                  refine ⟨14544923309052808467863825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9696615539368538978575883 14544923309052808467863825)
                  ·
                    refine ⟨10908692481789606350897869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14544923309052808467863825 10908692481789606350897869)
                    ·
                      refine ⟨4090759680671102381586701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10908692481789606350897869 4090759680671102381586701)
                      ·
                        rfl

theorem cell23_7966726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_7966726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7966726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7966726 prefixEnd_7966726 := by exact prefixLift 7966726
  have htrace : WordTrace (prefixWord ++ tailWord_7966726) baseStart_7966726 baseEnd_7966726 := by
    simpa [prefixWord, tailWord_7966726, baseEnd_7966726] using wordTrace_append hprefix tailTrace_7966726
  have hstable : (prefixWord ++ tailWord_7966726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7966726).length < 2 ^ (prefixWord ++ tailWord_7966726).sum := by decide
  have hdescent : baseEnd_7966726 < baseStart_7966726 := by decide
  rcases family_descends (prefixWord ++ tailWord_7966726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7966751 : List Nat := [1, 1, 2, 4, 1, 2, 3, 4, 5]
def baseStart_7966751 : Nat := 118140960795 + 7966751 * 2 ^ 59
def prefixEnd_7966751 : Nat := 4983230072969 + 3 ^ 40 * 7966751 * 2
def baseEnd_7966751 : Nat := 454530279743051642641565

theorem tailTrace_7966751 : CollatzResearch.WordTrace tailWord_7966751 prefixEnd_7966751 454530279743051642641565 := by
  unfold tailWord_7966751
  simp only [CollatzResearch.WordTrace]
  refine ⟨290571280360829214591996107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193714186907219476394664071 290571280360829214591996107)
  ·
    refine ⟨435856920541243821887994161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290571280360829214591996107 435856920541243821887994161)
    ·
      refine ⟨326892690405932866415995621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 435856920541243821887994161 326892690405932866415995621)
      ·
        refine ⟨61292379451112412452999179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 326892690405932866415995621 61292379451112412452999179)
        ·
          refine ⟨91938569176668618679498769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61292379451112412452999179 91938569176668618679498769)
          ·
            refine ⟨68953926882501464009624077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91938569176668618679498769 68953926882501464009624077)
            ·
              refine ⟨25857722580938049003609029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68953926882501464009624077 25857722580938049003609029)
              ·
                refine ⟨4848322983925884188176693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25857722580938049003609029 4848322983925884188176693)
                ·
                  refine ⟨454530279743051642641565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4848322983925884188176693 454530279743051642641565)
                  ·
                    rfl

theorem cell23_7966751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 4, 5].length) (baseStart_7966751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7966751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7966751 prefixEnd_7966751 := by exact prefixLift 7966751
  have htrace : WordTrace (prefixWord ++ tailWord_7966751) baseStart_7966751 baseEnd_7966751 := by
    simpa [prefixWord, tailWord_7966751, baseEnd_7966751] using wordTrace_append hprefix tailTrace_7966751
  have hstable : (prefixWord ++ tailWord_7966751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7966751).length < 2 ^ (prefixWord ++ tailWord_7966751).sum := by decide
  have hdescent : baseEnd_7966751 < baseStart_7966751 := by decide
  rcases family_descends (prefixWord ++ tailWord_7966751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7966821 : List Nat := [1, 3, 1, 3, 2, 2, 1, 2, 1, 4, 3]
def baseStart_7966821 : Nat := 118140960795 + 7966821 * 2 ^ 59
def prefixEnd_7966821 : Nat := 4983230072969 + 3 ^ 40 * 7966821 * 2
def baseEnd_7966821 : Nat := 4090808461333279509898763

theorem tailTrace_7966821 : CollatzResearch.WordTrace tailWord_7966821 prefixEnd_7966821 4090808461333279509898763 := by
  unfold tailWord_7966821
  simp only [CollatzResearch.WordTrace]
  refine ⟨290573833470575616547044317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193715888980383744364696211 290573833470575616547044317)
  ·
    refine ⟨108965187551465856205141619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290573833470575616547044317 108965187551465856205141619)
    ·
      refine ⟨163447781327198784307712429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108965187551465856205141619 163447781327198784307712429)
      ·
        refine ⟨61292917997699544115392161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163447781327198784307712429 61292917997699544115392161)
        ·
          refine ⟨45969688498274658086544121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61292917997699544115392161 45969688498274658086544121)
          ·
            refine ⟨34477266373705993564908091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45969688498274658086544121 34477266373705993564908091)
            ·
              refine ⟨51715899560558990347362137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34477266373705993564908091 51715899560558990347362137)
              ·
                refine ⟨38786924670419242760521603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51715899560558990347362137 38786924670419242760521603)
                ·
                  refine ⟨58180387005628864140782405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38786924670419242760521603 58180387005628864140782405)
                  ·
                    refine ⟨10908822563555412026396701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58180387005628864140782405 10908822563555412026396701)
                    ·
                      refine ⟨4090808461333279509898763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10908822563555412026396701 4090808461333279509898763)
                      ·
                        rfl

theorem cell23_7966821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 2, 1, 4, 3].length) (baseStart_7966821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7966821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7966821 prefixEnd_7966821 := by exact prefixLift 7966821
  have htrace : WordTrace (prefixWord ++ tailWord_7966821) baseStart_7966821 baseEnd_7966821 := by
    simpa [prefixWord, tailWord_7966821, baseEnd_7966821] using wordTrace_append hprefix tailTrace_7966821
  have hstable : (prefixWord ++ tailWord_7966821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7966821).length < 2 ^ (prefixWord ++ tailWord_7966821).sum := by decide
  have hdescent : baseEnd_7966821 < baseStart_7966821 := by decide
  rcases family_descends (prefixWord ++ tailWord_7966821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7966838 : List Nat := [5, 1, 1, 2, 1, 2, 2, 1, 1, 4, 3]
def baseStart_7966838 : Nat := 118140960795 + 7966838 * 2 ^ 59
def prefixEnd_7966838 : Nat := 4983230072969 + 3 ^ 40 * 7966838 * 2
def baseEnd_7966838 : Nat := 4090817190504405943386185

theorem tailTrace_7966838 : CollatzResearch.WordTrace tailWord_7966838 prefixEnd_7966838 4090817190504405943386185 := by
  unfold tailWord_7966838
  simp only [CollatzResearch.WordTrace]
  refine ⟨18160903344469626778150823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 193716302341009352300275445 18160903344469626778150823)
  ·
    refine ⟨27241355016704440167226235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18160903344469626778150823 27241355016704440167226235)
    ·
      refine ⟨40862032525056660250839353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27241355016704440167226235 40862032525056660250839353)
      ·
        refine ⟨30646524393792495188129515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40862032525056660250839353 30646524393792495188129515)
        ·
          refine ⟨45969786590688742782194273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30646524393792495188129515 45969786590688742782194273)
          ·
            refine ⟨34477339943016557086645705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45969786590688742782194273 34477339943016557086645705)
            ·
              refine ⟨25858004957262417814984279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34477339943016557086645705 25858004957262417814984279)
              ·
                refine ⟨38787007435893626722476419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25858004957262417814984279 38787007435893626722476419)
                ·
                  refine ⟨58180511153840440083714629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38787007435893626722476419 58180511153840440083714629)
                  ·
                    refine ⟨10908845841345082515696493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58180511153840440083714629 10908845841345082515696493)
                    ·
                      refine ⟨4090817190504405943386185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10908845841345082515696493 4090817190504405943386185)
                      ·
                        rfl

theorem cell23_7966838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_7966838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7966838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7966838 prefixEnd_7966838 := by exact prefixLift 7966838
  have htrace : WordTrace (prefixWord ++ tailWord_7966838) baseStart_7966838 baseEnd_7966838 := by
    simpa [prefixWord, tailWord_7966838, baseEnd_7966838] using wordTrace_append hprefix tailTrace_7966838
  have hstable : (prefixWord ++ tailWord_7966838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7966838).length < 2 ^ (prefixWord ++ tailWord_7966838).sum := by decide
  have hdescent : baseEnd_7966838 < baseStart_7966838 := by decide
  rcases family_descends (prefixWord ++ tailWord_7966838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7966845 : List Nat := [1, 4, 1, 1, 3, 2, 3, 3, 1, 4]
def baseStart_7966845 : Nat := 118140960795 + 7966845 * 2 ^ 59
def prefixEnd_7966845 : Nat := 4983230072969 + 3 ^ 40 * 7966845 * 2
def baseEnd_7966845 : Nat := 1363606928289662471999551

theorem tailTrace_7966845 : CollatzResearch.WordTrace tailWord_7966845 prefixEnd_7966845 1363606928289662471999551 := by
  unfold tailWord_7966845
  simp only [CollatzResearch.WordTrace]
  refine ⟨290574708822488668645917989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193716472548325779097278659 290574708822488668645917989)
  ·
    refine ⟨54482757904216625371109623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 290574708822488668645917989 54482757904216625371109623)
    ·
      refine ⟨81724136856324938056664435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54482757904216625371109623 81724136856324938056664435)
      ·
        refine ⟨122586205284487407084996653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81724136856324938056664435 122586205284487407084996653)
        ·
          refine ⟨45969826981682777656873745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122586205284487407084996653 45969826981682777656873745)
          ·
            refine ⟨34477370236262083242655309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45969826981682777656873745 34477370236262083242655309)
            ·
              refine ⟨12929013838598281215995741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34477370236262083242655309 12929013838598281215995741)
              ·
                refine ⟨4848380189474355455998403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12929013838598281215995741 4848380189474355455998403)
                ·
                  refine ⟨7272570284211533183997605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4848380189474355455998403 7272570284211533183997605)
                  ·
                    refine ⟨1363606928289662471999551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7272570284211533183997605 1363606928289662471999551)
                    ·
                      rfl

theorem cell23_7966845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 3, 1, 4].length) (baseStart_7966845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7966845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7966845 prefixEnd_7966845 := by exact prefixLift 7966845
  have htrace : WordTrace (prefixWord ++ tailWord_7966845) baseStart_7966845 baseEnd_7966845 := by
    simpa [prefixWord, tailWord_7966845, baseEnd_7966845] using wordTrace_append hprefix tailTrace_7966845
  have hstable : (prefixWord ++ tailWord_7966845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7966845).length < 2 ^ (prefixWord ++ tailWord_7966845).sum := by decide
  have hdescent : baseEnd_7966845 < baseStart_7966845 := by decide
  rcases family_descends (prefixWord ++ tailWord_7966845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7966862 : List Nat := [4, 1, 1, 3, 4, 1, 1, 1, 3, 4]
def baseStart_7966862 : Nat := 118140960795 + 7966862 * 2 ^ 59
def prefixEnd_7966862 : Nat := 4983230072969 + 3 ^ 40 * 7966862 * 2
def baseEnd_7966862 : Nat := 1363609838013371283162025

theorem tailTrace_7966862 : CollatzResearch.WordTrace tailWord_7966862 prefixEnd_7966862 1363609838013371283162025 := by
  unfold tailWord_7966862
  simp only [CollatzResearch.WordTrace]
  refine ⟨36321916107928385068660855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193716885908951387032857893 36321916107928385068660855)
  ·
    refine ⟨54482874161892577602991283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36321916107928385068660855 54482874161892577602991283)
    ·
      refine ⟨81724311242838866404486925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54482874161892577602991283 81724311242838866404486925)
      ·
        refine ⟨30646616716064574901682597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81724311242838866404486925 30646616716064574901682597)
        ·
          refine ⟨5746240634262107794065487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30646616716064574901682597 5746240634262107794065487)
          ·
            refine ⟨8619360951393161691098231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5746240634262107794065487 8619360951393161691098231)
            ·
              refine ⟨12929041427089742536647347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8619360951393161691098231 12929041427089742536647347)
              ·
                refine ⟨19393562140634613804971021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12929041427089742536647347 19393562140634613804971021)
                ·
                  refine ⟨7272585802737980176864133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19393562140634613804971021 7272585802737980176864133)
                  ·
                    refine ⟨1363609838013371283162025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7272585802737980176864133 1363609838013371283162025)
                    ·
                      rfl

theorem cell23_7966862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 1, 3, 4].length) (baseStart_7966862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7966862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7966862 prefixEnd_7966862 := by exact prefixLift 7966862
  have htrace : WordTrace (prefixWord ++ tailWord_7966862) baseStart_7966862 baseEnd_7966862 := by
    simpa [prefixWord, tailWord_7966862, baseEnd_7966862] using wordTrace_append hprefix tailTrace_7966862
  have hstable : (prefixWord ++ tailWord_7966862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7966862).length < 2 ^ (prefixWord ++ tailWord_7966862).sum := by decide
  have hdescent : baseEnd_7966862 < baseStart_7966862 := by decide
  rcases family_descends (prefixWord ++ tailWord_7966862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7966959 : List Nat := [1, 1, 2, 1, 6, 2, 2, 3, 1, 2, 2]
def baseStart_7966959 : Nat := 118140960795 + 7966959 * 2 ^ 59
def prefixEnd_7966959 : Nat := 4983230072969 + 3 ^ 40 * 7966959 * 2
def baseEnd_7966959 : Nat := 4090879321663599969973129

theorem tailTrace_7966959 : CollatzResearch.WordTrace tailWord_7966959 prefixEnd_7966959 4090879321663599969973129 := by
  unfold tailWord_7966959
  simp only [CollatzResearch.WordTrace]
  refine ⟨290578866744075666115567931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193719244496050444077045287 290578866744075666115567931)
  ·
    refine ⟨435868300116113499173351897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290578866744075666115567931 435868300116113499173351897)
    ·
      refine ⟨326901225087085124380013923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 435868300116113499173351897 326901225087085124380013923)
      ·
        refine ⟨490351837630627686570020885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326901225087085124380013923 490351837630627686570020885)
        ·
          refine ⟨22985242388935672807969729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 490351837630627686570020885 22985242388935672807969729)
          ·
            refine ⟨17238931791701754605977297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22985242388935672807969729 17238931791701754605977297)
            ·
              refine ⟨12929198843776315954482973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17238931791701754605977297 12929198843776315954482973)
              ·
                refine ⟨4848449566416118482931115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12929198843776315954482973 4848449566416118482931115)
                ·
                  refine ⟨7272674349624177724396673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4848449566416118482931115 7272674349624177724396673)
                  ·
                    refine ⟨5454505762218133293297505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7272674349624177724396673 5454505762218133293297505)
                    ·
                      refine ⟨4090879321663599969973129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5454505762218133293297505 4090879321663599969973129)
                      ·
                        rfl

theorem cell23_7966959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 3, 1, 2, 2].length) (baseStart_7966959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7966959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7966959 prefixEnd_7966959 := by exact prefixLift 7966959
  have htrace : WordTrace (prefixWord ++ tailWord_7966959) baseStart_7966959 baseEnd_7966959 := by
    simpa [prefixWord, tailWord_7966959, baseEnd_7966959] using wordTrace_append hprefix tailTrace_7966959
  have hstable : (prefixWord ++ tailWord_7966959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7966959).length < 2 ^ (prefixWord ++ tailWord_7966959).sum := by decide
  have hdescent : baseEnd_7966959 < baseStart_7966959 := by decide
  rcases family_descends (prefixWord ++ tailWord_7966959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7966962 : List Nat := [3, 2, 1, 3, 2, 1, 4, 1, 1, 2, 3]
def baseStart_7966962 : Nat := 118140960795 + 7966962 * 2 ^ 59
def prefixEnd_7966962 : Nat := 4983230072969 + 3 ^ 40 * 7966962 * 2
def baseEnd_7966962 : Nat := 4090880862105563458235615

theorem tailTrace_7966962 : CollatzResearch.WordTrace tailWord_7966962 prefixEnd_7966962 4090880862105563458235615 := by
  unfold tailWord_7966962
  simp only [CollatzResearch.WordTrace]
  refine ⟨72644744040766199406981785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193719317442043198418618093 72644744040766199406981785)
  ·
    refine ⟨54483558030574649555236339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72644744040766199406981785 54483558030574649555236339)
    ·
      refine ⟨81725337045861974332854509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54483558030574649555236339 81725337045861974332854509)
      ·
        refine ⟨30647001392198240374820441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81725337045861974332854509 30647001392198240374820441)
        ·
          refine ⟨22985251044148680281115331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30647001392198240374820441 22985251044148680281115331)
          ·
            refine ⟨34477876566223020421672997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22985251044148680281115331 34477876566223020421672997)
            ·
              refine ⟨6464601856166816329063687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34477876566223020421672997 6464601856166816329063687)
              ·
                refine ⟨9696902784250224493595531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6464601856166816329063687 9696902784250224493595531)
                ·
                  refine ⟨14545354176375336740393297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9696902784250224493595531 14545354176375336740393297)
                  ·
                    refine ⟨10909015632281502555294973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14545354176375336740393297 10909015632281502555294973)
                    ·
                      refine ⟨4090880862105563458235615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10909015632281502555294973 4090880862105563458235615)
                      ·
                        rfl

theorem cell23_7966962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 4, 1, 1, 2, 3].length) (baseStart_7966962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7966962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7966962 prefixEnd_7966962 := by exact prefixLift 7966962
  have htrace : WordTrace (prefixWord ++ tailWord_7966962) baseStart_7966962 baseEnd_7966962 := by
    simpa [prefixWord, tailWord_7966962, baseEnd_7966962] using wordTrace_append hprefix tailTrace_7966962
  have hstable : (prefixWord ++ tailWord_7966962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7966962).length < 2 ^ (prefixWord ++ tailWord_7966962).sum := by decide
  have hdescent : baseEnd_7966962 < baseStart_7966962 := by decide
  rcases family_descends (prefixWord ++ tailWord_7966962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7966981 : List Nat := [1, 3, 1, 1, 2, 1, 2, 3, 2, 3, 4]
def baseStart_7966981 : Nat := 118140960795 + 7966981 * 2 ^ 59
def prefixEnd_7966981 : Nat := 4983230072969 + 3 ^ 40 * 7966981 * 2
def baseEnd_7966981 : Nat := 4090890618237998883898027

theorem tailTrace_7966981 : CollatzResearch.WordTrace tailWord_7966981 prefixEnd_7966981 4090890618237998883898027 := by
  unfold tailWord_7966981
  simp only [CollatzResearch.WordTrace]
  refine ⟨290579669149995963872868797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193719779433330642581912531 290579669149995963872868797)
  ·
    refine ⟨108967375931248486452325799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290579669149995963872868797 108967375931248486452325799)
    ·
      refine ⟨163451063896872729678488699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108967375931248486452325799 163451063896872729678488699)
      ·
        refine ⟨245176595845309094517733049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163451063896872729678488699 245176595845309094517733049)
        ·
          refine ⟨183882446883981820888299787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245176595845309094517733049 183882446883981820888299787)
          ·
            refine ⟨275823670325972731332449681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183882446883981820888299787 275823670325972731332449681)
            ·
              refine ⟨206867752744479548499337261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 275823670325972731332449681 206867752744479548499337261)
              ·
                refine ⟨77575407279179830687251473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 206867752744479548499337261 77575407279179830687251473)
                ·
                  refine ⟨58181555459384873015438605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77575407279179830687251473 58181555459384873015438605)
                  ·
                    refine ⟨21818083297269327380789477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58181555459384873015438605 21818083297269327380789477)
                    ·
                      refine ⟨4090890618237998883898027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21818083297269327380789477 4090890618237998883898027)
                      ·
                        rfl

theorem cell23_7966981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 2, 3, 4].length) (baseStart_7966981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7966981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7966981 prefixEnd_7966981 := by exact prefixLift 7966981
  have htrace : WordTrace (prefixWord ++ tailWord_7966981) baseStart_7966981 baseEnd_7966981 := by
    simpa [prefixWord, tailWord_7966981, baseEnd_7966981] using wordTrace_append hprefix tailTrace_7966981
  have hstable : (prefixWord ++ tailWord_7966981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7966981).length < 2 ^ (prefixWord ++ tailWord_7966981).sum := by decide
  have hdescent : baseEnd_7966981 < baseStart_7966981 := by decide
  rcases family_descends (prefixWord ++ tailWord_7966981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7967048 : List Nat := [2, 1, 3, 1, 1, 2, 2, 3, 2, 3, 3]
def baseStart_7967048 : Nat := 118140960795 + 7967048 * 2 ^ 59
def prefixEnd_7967048 : Nat := 4983230072969 + 3 ^ 40 * 7967048 * 2
def baseEnd_7967048 : Nat := 4090925021441850121760219

theorem tailTrace_7967048 : CollatzResearch.WordTrace tailWord_7967048 prefixEnd_7967048 4090925021441850121760219 := by
  unfold tailWord_7967048
  simp only [CollatzResearch.WordTrace]
  refine ⟨145291056420376617157778899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193721408560502156210371865 145291056420376617157778899)
  ·
    refine ⟨217936584630564925736668349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145291056420376617157778899 217936584630564925736668349)
    ·
      refine ⟨81726219236461847151250631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217936584630564925736668349 81726219236461847151250631)
      ·
        refine ⟨122589328854692770726875947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81726219236461847151250631 122589328854692770726875947)
        ·
          refine ⟨183883993282039156090313921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122589328854692770726875947 183883993282039156090313921)
          ·
            refine ⟨137912994961529367067735441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183883993282039156090313921 137912994961529367067735441)
            ·
              refine ⟨103434746221147025300801581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137912994961529367067735441 103434746221147025300801581)
              ·
                refine ⟨38788029832930134487800593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103434746221147025300801581 38788029832930134487800593)
                ·
                  refine ⟨29091022374697600865850445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38788029832930134487800593 29091022374697600865850445)
                  ·
                    refine ⟨10909133390511600324693917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29091022374697600865850445 10909133390511600324693917)
                    ·
                      refine ⟨4090925021441850121760219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10909133390511600324693917 4090925021441850121760219)
                      ·
                        rfl

theorem cell23_7967048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 3, 2, 3, 3].length) (baseStart_7967048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7967048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7967048 prefixEnd_7967048 := by exact prefixLift 7967048
  have htrace : WordTrace (prefixWord ++ tailWord_7967048) baseStart_7967048 baseEnd_7967048 := by
    simpa [prefixWord, tailWord_7967048, baseEnd_7967048] using wordTrace_append hprefix tailTrace_7967048
  have hstable : (prefixWord ++ tailWord_7967048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7967048).length < 2 ^ (prefixWord ++ tailWord_7967048).sum := by decide
  have hdescent : baseEnd_7967048 < baseStart_7967048 := by decide
  rcases family_descends (prefixWord ++ tailWord_7967048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7967051 : List Nat := [1, 1, 1, 1, 3, 1, 1, 6, 1, 7]
def baseStart_7967051 : Nat := 118140960795 + 7967051 * 2 ^ 59
def prefixEnd_7967051 : Nat := 4983230072969 + 3 ^ 40 * 7967051 * 2
def baseEnd_7967051 : Nat := 1363642187294604536674235

theorem tailTrace_7967051 : CollatzResearch.WordTrace tailWord_7967051 prefixEnd_7967051 1363642187294604536674235 := by
  unfold tailWord_7967051
  simp only [CollatzResearch.WordTrace]
  refine ⟨290582222259742365827917007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193721481506494910551944671 290582222259742365827917007)
  ·
    refine ⟨435873333389613548741875511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290582222259742365827917007 435873333389613548741875511)
    ·
      refine ⟨653810000084420323112813267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435873333389613548741875511 653810000084420323112813267)
      ·
        refine ⟨980715000126630484669219901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 653810000084420323112813267 980715000126630484669219901)
        ·
          refine ⟨367768125047486431750957463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 980715000126630484669219901 367768125047486431750957463)
          ·
            refine ⟨551652187571229647626436195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 367768125047486431750957463 551652187571229647626436195)
            ·
              refine ⟨827478281356844471439654293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 551652187571229647626436195 827478281356844471439654293)
              ·
                refine ⟨38788044438602084598733795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 827478281356844471439654293 38788044438602084598733795)
                ·
                  refine ⟨58182066657903126898100693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38788044438602084598733795 58182066657903126898100693)
                  ·
                    refine ⟨1363642187294604536674235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58182066657903126898100693 1363642187294604536674235)
                    ·
                      rfl

theorem cell23_7967051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 6, 1, 7].length) (baseStart_7967051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7967051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7967051 prefixEnd_7967051 := by exact prefixLift 7967051
  have htrace : WordTrace (prefixWord ++ tailWord_7967051) baseStart_7967051 baseEnd_7967051 := by
    simpa [prefixWord, tailWord_7967051, baseEnd_7967051] using wordTrace_append hprefix tailTrace_7967051
  have hstable : (prefixWord ++ tailWord_7967051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7967051).length < 2 ^ (prefixWord ++ tailWord_7967051).sum := by decide
  have hdescent : baseEnd_7967051 < baseStart_7967051 := by decide
  rcases family_descends (prefixWord ++ tailWord_7967051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7967115 : List Nat := [1, 1, 1, 1, 4, 5, 1, 2, 3, 4]
def baseStart_7967115 : Nat := 118140960795 + 7967115 * 2 ^ 59
def prefixEnd_7967115 : Nat := 4983230072969 + 3 ^ 40 * 7967115 * 2
def baseEnd_7967115 : Nat := 1363653141548567119874137

theorem tailTrace_7967115 : CollatzResearch.WordTrace tailWord_7967115 prefixEnd_7967115 1363653141548567119874137 := by
  unfold tailWord_7967115
  simp only [CollatzResearch.WordTrace]
  refine ⟨290584556531510504758246799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193723037687673669838831199 290584556531510504758246799)
  ·
    refine ⟨435876834797265757137370199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290584556531510504758246799 435876834797265757137370199)
    ·
      refine ⟨653815252195898635706055299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435876834797265757137370199 653815252195898635706055299)
      ·
        refine ⟨980722878293847953559082949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 653815252195898635706055299 980722878293847953559082949)
        ·
          refine ⟨183885539680096491292328053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 980722878293847953559082949 183885539680096491292328053)
          ·
            refine ⟨17239269345009046058655755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 183885539680096491292328053 17239269345009046058655755)
            ·
              refine ⟨25858904017513569087983633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17239269345009046058655755 25858904017513569087983633)
              ·
                refine ⟨19394178013135176815987725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25858904017513569087983633 19394178013135176815987725)
                ·
                  refine ⟨7272816754925691305995397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19394178013135176815987725 7272816754925691305995397)
                  ·
                    refine ⟨1363653141548567119874137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7272816754925691305995397 1363653141548567119874137)
                    ·
                      rfl

theorem cell23_7967115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 2, 3, 4].length) (baseStart_7967115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7967115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7967115 prefixEnd_7967115 := by exact prefixLift 7967115
  have htrace : WordTrace (prefixWord ++ tailWord_7967115) baseStart_7967115 baseEnd_7967115 := by
    simpa [prefixWord, tailWord_7967115, baseEnd_7967115] using wordTrace_append hprefix tailTrace_7967115
  have hstable : (prefixWord ++ tailWord_7967115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7967115).length < 2 ^ (prefixWord ++ tailWord_7967115).sum := by decide
  have hdescent : baseEnd_7967115 < baseStart_7967115 := by decide
  rcases family_descends (prefixWord ++ tailWord_7967115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7967149 : List Nat := [1, 5, 2, 2, 2, 1, 2, 1, 3, 4]
def baseStart_7967149 : Nat := 118140960795 + 7967149 * 2 ^ 59
def prefixEnd_7967149 : Nat := 4983230072969 + 3 ^ 40 * 7967149 * 2
def baseEnd_7967149 : Nat := 1363658960995984742199085

theorem tailTrace_7967149 : CollatzResearch.WordTrace tailWord_7967149 prefixEnd_7967149 1363658960995984742199085 := by
  unfold tailWord_7967149
  simp only [CollatzResearch.WordTrace]
  refine ⟨290585796613387328564984501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193723864408924885709989667 290585796613387328564984501)
  ·
    refine ⟨27242418432505062052967297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 290585796613387328564984501 27242418432505062052967297)
    ·
      refine ⟨20431813824378796539725473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27242418432505062052967297 20431813824378796539725473)
      ·
        refine ⟨15323860368284097404794105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20431813824378796539725473 15323860368284097404794105)
        ·
          refine ⟨11492895276213073053595579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15323860368284097404794105 11492895276213073053595579)
          ·
            refine ⟨17239342914319609580393369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11492895276213073053595579 17239342914319609580393369)
            ·
              refine ⟨12929507185739707185295027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17239342914319609580393369 12929507185739707185295027)
              ·
                refine ⟨19394260778609560777942541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12929507185739707185295027 19394260778609560777942541)
                ·
                  refine ⟨7272847791978585291728453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19394260778609560777942541 7272847791978585291728453)
                  ·
                    refine ⟨1363658960995984742199085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7272847791978585291728453 1363658960995984742199085)
                    ·
                      rfl

theorem cell23_7967149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_7967149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7967149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7967149 prefixEnd_7967149 := by exact prefixLift 7967149
  have htrace : WordTrace (prefixWord ++ tailWord_7967149) baseStart_7967149 baseEnd_7967149 := by
    simpa [prefixWord, tailWord_7967149, baseEnd_7967149] using wordTrace_append hprefix tailTrace_7967149
  have hstable : (prefixWord ++ tailWord_7967149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7967149).length < 2 ^ (prefixWord ++ tailWord_7967149).sum := by decide
  have hdescent : baseEnd_7967149 < baseStart_7967149 := by decide
  rcases family_descends (prefixWord ++ tailWord_7967149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7967175 : List Nat := [1, 1, 4, 1, 1, 4, 1, 4, 1, 5]
def baseStart_7967175 : Nat := 118140960795 + 7967175 * 2 ^ 59
def prefixEnd_7967175 : Nat := 4983230072969 + 3 ^ 40 * 7967175 * 2
def baseEnd_7967175 : Nat := 1363663411161657041624045

theorem tailTrace_7967175 : CollatzResearch.WordTrace tailWord_7967175 prefixEnd_7967175 1363663411161657041624045 := by
  unfold tailWord_7967175
  simp only [CollatzResearch.WordTrace]
  refine ⟨290586744911293135005430979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193724496607528756670287319 290586744911293135005430979)
  ·
    refine ⟨435880117366939702508146469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290586744911293135005430979 435880117366939702508146469)
    ·
      refine ⟨81727522006301194220277463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 435880117366939702508146469 81727522006301194220277463)
      ·
        refine ⟨122591283009451791330416195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81727522006301194220277463 122591283009451791330416195)
        ·
          refine ⟨183886924514177686995624293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122591283009451791330416195 183886924514177686995624293)
          ·
            refine ⟨34478798346408316311679555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 183886924514177686995624293 34478798346408316311679555)
            ·
              refine ⟨51718197519612474467519333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34478798346408316311679555 51718197519612474467519333)
              ·
                refine ⟨9697162034927338962659875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51718197519612474467519333 9697162034927338962659875)
                ·
                  refine ⟨14545743052391008443989813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9697162034927338962659875 14545743052391008443989813)
                  ·
                    refine ⟨1363663411161657041624045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14545743052391008443989813 1363663411161657041624045)
                    ·
                      rfl

theorem cell23_7967175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 4, 1, 5].length) (baseStart_7967175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7967175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7967175 prefixEnd_7967175 := by exact prefixLift 7967175
  have htrace : WordTrace (prefixWord ++ tailWord_7967175) baseStart_7967175 baseEnd_7967175 := by
    simpa [prefixWord, tailWord_7967175, baseEnd_7967175] using wordTrace_append hprefix tailTrace_7967175
  have hstable : (prefixWord ++ tailWord_7967175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7967175).length < 2 ^ (prefixWord ++ tailWord_7967175).sum := by decide
  have hdescent : baseEnd_7967175 < baseStart_7967175 := by decide
  rcases family_descends (prefixWord ++ tailWord_7967175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7967182 : List Nat := [4, 1, 1, 1, 2, 1, 1, 5, 2, 3, 2]
def baseStart_7967182 : Nat := 118140960795 + 7967182 * 2 ^ 59
def prefixEnd_7967182 : Nat := 4983230072969 + 3 ^ 40 * 7967182 * 2
def baseEnd_7967182 : Nat := 4090993827849552597484603

theorem tailTrace_7967182 : CollatzResearch.WordTrace tailWord_7967182 prefixEnd_7967182 4090993827849552597484603 := by
  unfold tailWord_7967182
  simp only [CollatzResearch.WordTrace]
  refine ⟨36323375027783471900116975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193724666814845183467290533 36323375027783471900116975)
  ·
    refine ⟨54485062541675207850175463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36323375027783471900116975 54485062541675207850175463)
    ·
      refine ⟨81727593812512811775263195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54485062541675207850175463 81727593812512811775263195)
      ·
        refine ⟨122591390718769217662894793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81727593812512811775263195 122591390718769217662894793)
        ·
          refine ⟨91943543039076913247171095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122591390718769217662894793 91943543039076913247171095)
          ·
            refine ⟨137915314558615369870756643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91943543039076913247171095 137915314558615369870756643)
            ·
              refine ⟨206872971837923054806134965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137915314558615369870756643 206872971837923054806134965)
              ·
                refine ⟨19394341109805286388075153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 206872971837923054806134965 19394341109805286388075153)
                ·
                  refine ⟨14545755832353964791056365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19394341109805286388075153 14545755832353964791056365)
                  ·
                    refine ⟨5454658437132736796646137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14545755832353964791056365 5454658437132736796646137)
                    ·
                      refine ⟨4090993827849552597484603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5454658437132736796646137 4090993827849552597484603)
                      ·
                        rfl

theorem cell23_7967182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 5, 2, 3, 2].length) (baseStart_7967182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7967182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7967182 prefixEnd_7967182 := by exact prefixLift 7967182
  have htrace : WordTrace (prefixWord ++ tailWord_7967182) baseStart_7967182 baseEnd_7967182 := by
    simpa [prefixWord, tailWord_7967182, baseEnd_7967182] using wordTrace_append hprefix tailTrace_7967182
  have hstable : (prefixWord ++ tailWord_7967182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7967182).length < 2 ^ (prefixWord ++ tailWord_7967182).sum := by decide
  have hdescent : baseEnd_7967182 < baseStart_7967182 := by decide
  rcases family_descends (prefixWord ++ tailWord_7967182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7967215 : List Nat := [1, 1, 2, 1, 4, 1, 1, 4, 3, 2, 3]
def baseStart_7967215 : Nat := 118140960795 + 7967215 * 2 ^ 59
def prefixEnd_7967215 : Nat := 4983230072969 + 3 ^ 40 * 7967215 * 2
def baseEnd_7967215 : Nat := 4091010772711150968371951

theorem tailTrace_7967215 : CollatzResearch.WordTrace tailWord_7967215 prefixEnd_7967215 4091010772711150968371951 := by
  unfold tailWord_7967215
  simp only [CollatzResearch.WordTrace]
  refine ⟨290588203831148221836887099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193725469220765481224591399 290588203831148221836887099)
  ·
    refine ⟨435882305746722332755330649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290588203831148221836887099 435882305746722332755330649)
    ·
      refine ⟨326911729310041749566497987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 435882305746722332755330649 326911729310041749566497987)
      ·
        refine ⟨490367593965062624349746981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326911729310041749566497987 490367593965062624349746981)
        ·
          refine ⟨91943923868449242065577559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 490367593965062624349746981 91943923868449242065577559)
          ·
            refine ⟨137915885802673863098366339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91943923868449242065577559 137915885802673863098366339)
            ·
              refine ⟨206873828704010794647549509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137915885802673863098366339 206873828704010794647549509)
              ·
                refine ⟨38788842882002023996415533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 206873828704010794647549509 38788842882002023996415533)
                ·
                  refine ⟨14545816080750758998655825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38788842882002023996415533 14545816080750758998655825)
                  ·
                    refine ⟨10909362060563069248991869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14545816080750758998655825 10909362060563069248991869)
                    ·
                      refine ⟨4091010772711150968371951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10909362060563069248991869 4091010772711150968371951)
                      ·
                        rfl

theorem cell23_7967215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 4, 3, 2, 3].length) (baseStart_7967215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7967215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7967215 prefixEnd_7967215 := by exact prefixLift 7967215
  have htrace : WordTrace (prefixWord ++ tailWord_7967215) baseStart_7967215 baseEnd_7967215 := by
    simpa [prefixWord, tailWord_7967215, baseEnd_7967215] using wordTrace_append hprefix tailTrace_7967215
  have hstable : (prefixWord ++ tailWord_7967215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7967215).length < 2 ^ (prefixWord ++ tailWord_7967215).sum := by decide
  have hdescent : baseEnd_7967215 < baseStart_7967215 := by decide
  rcases family_descends (prefixWord ++ tailWord_7967215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7967285 : List Nat := [1, 3, 3, 1, 1, 2, 1, 2, 2, 3, 4]
def baseStart_7967285 : Nat := 118140960795 + 7967285 * 2 ^ 59
def prefixEnd_7967285 : Nat := 4983230072969 + 3 ^ 40 * 7967285 * 2
def baseEnd_7967285 : Nat := 4091046716356965694496629

theorem tailTrace_7967285 : CollatzResearch.WordTrace tailWord_7967285 prefixEnd_7967285 4091046716356965694496629 := by
  unfold tailWord_7967285
  simp only [CollatzResearch.WordTrace]
  refine ⟨290590756940894623791935309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193727171293929749194623539 290590756940894623791935309)
  ·
    refine ⟨108971533852835483921975741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290590756940894623791935309 108971533852835483921975741)
    ·
      refine ⟨40864325194813306470740903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108971533852835483921975741 40864325194813306470740903)
      ·
        refine ⟨61296487792219959706111355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40864325194813306470740903 61296487792219959706111355)
        ·
          refine ⟨91944731688329939559167033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61296487792219959706111355 91944731688329939559167033)
          ·
            refine ⟨68958548766247454669375275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91944731688329939559167033 68958548766247454669375275)
            ·
              refine ⟨103437823149371182004062913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68958548766247454669375275 103437823149371182004062913)
              ·
                refine ⟨77578367362028386503047185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103437823149371182004062913 77578367362028386503047185)
                ·
                  refine ⟨58183775521521289877285389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77578367362028386503047185 58183775521521289877285389)
                  ·
                    refine ⟨21818915820570483703982021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58183775521521289877285389 21818915820570483703982021)
                    ·
                      refine ⟨4091046716356965694496629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21818915820570483703982021 4091046716356965694496629)
                      ·
                        rfl

theorem cell23_7967285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_7967285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7967285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7967285 prefixEnd_7967285 := by exact prefixLift 7967285
  have htrace : WordTrace (prefixWord ++ tailWord_7967285) baseStart_7967285 baseEnd_7967285 := by
    simpa [prefixWord, tailWord_7967285, baseEnd_7967285] using wordTrace_append hprefix tailTrace_7967285
  have hstable : (prefixWord ++ tailWord_7967285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7967285).length < 2 ^ (prefixWord ++ tailWord_7967285).sum := by decide
  have hdescent : baseEnd_7967285 < baseStart_7967285 := by decide
  rcases family_descends (prefixWord ++ tailWord_7967285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7967289 : List Nat := [1, 2, 1, 5, 1, 1, 2, 4, 1, 3, 2]
def baseStart_7967289 : Nat := 118140960795 + 7967289 * 2 ^ 59
def prefixEnd_7967289 : Nat := 4983230072969 + 3 ^ 40 * 7967289 * 2
def baseEnd_7967289 : Nat := 4091048770279583678846611

theorem tailTrace_7967289 : CollatzResearch.WordTrace tailWord_7967289 prefixEnd_7967289 4091048770279583678846611 := by
  unfold tailWord_7967289
  simp only [CollatzResearch.WordTrace]
  refine ⟨290590902832880132475080921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193727268555253421650053947 290590902832880132475080921)
  ·
    refine ⟨217943177124660099356310691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290590902832880132475080921 217943177124660099356310691)
    ·
      refine ⟨326914765686990149034466037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217943177124660099356310691 326914765686990149034466037)
      ·
        refine ⟨30648259283155326471981191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 326914765686990149034466037 30648259283155326471981191)
        ·
          refine ⟨45972388924732989707971787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30648259283155326471981191 45972388924732989707971787)
          ·
            refine ⟨68958583387099484561957681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45972388924732989707971787 68958583387099484561957681)
            ·
              refine ⟨51718937540324613421468261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68958583387099484561957681 51718937540324613421468261)
              ·
                refine ⟨9697300788810865016525299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51718937540324613421468261 9697300788810865016525299)
                ·
                  refine ⟨14545951183216297524787949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9697300788810865016525299 14545951183216297524787949)
                  ·
                    refine ⟨5454731693706111571795481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14545951183216297524787949 5454731693706111571795481)
                    ·
                      refine ⟨4091048770279583678846611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5454731693706111571795481 4091048770279583678846611)
                      ·
                        rfl

theorem cell23_7967289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 4, 1, 3, 2].length) (baseStart_7967289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7967289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7967289 prefixEnd_7967289 := by exact prefixLift 7967289
  have htrace : WordTrace (prefixWord ++ tailWord_7967289) baseStart_7967289 baseEnd_7967289 := by
    simpa [prefixWord, tailWord_7967289, baseEnd_7967289] using wordTrace_append hprefix tailTrace_7967289
  have hstable : (prefixWord ++ tailWord_7967289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7967289).length < 2 ^ (prefixWord ++ tailWord_7967289).sum := by decide
  have hdescent : baseEnd_7967289 < baseStart_7967289 := by decide
  rcases family_descends (prefixWord ++ tailWord_7967289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7967306 : List Nat := [3, 1, 2, 1, 1, 4, 4, 1, 1, 3, 2]
def baseStart_7967306 : Nat := 118140960795 + 7967306 * 2 ^ 59
def prefixEnd_7967306 : Nat := 4983230072969 + 3 ^ 40 * 7967306 * 2
def baseEnd_7967306 : Nat := 4091057499450710112334033

theorem tailTrace_7967306 : CollatzResearch.WordTrace tailWord_7967306 prefixEnd_7967306 4091057499450710112334033 := by
  unfold tailWord_7967306
  simp only [CollatzResearch.WordTrace]
  refine ⟨72647880718454636094612443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193727681915879029585633181 72647880718454636094612443)
  ·
    refine ⟨108971821077681954141918665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72647880718454636094612443 108971821077681954141918665)
    ·
      refine ⟨81728865808261465606438999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108971821077681954141918665 81728865808261465606438999)
      ·
        refine ⟨122593298712392198409658499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81728865808261465606438999 122593298712392198409658499)
        ·
          refine ⟨183889948068588297614487749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122593298712392198409658499 183889948068588297614487749)
          ·
            refine ⟨34479365262860305802716453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 183889948068588297614487749 34479365262860305802716453)
            ·
              refine ⟨6464880986786307338009335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34479365262860305802716453 6464880986786307338009335)
              ·
                refine ⟨9697321480179461007014003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6464880986786307338009335 9697321480179461007014003)
                ·
                  refine ⟨14545982220269191510521005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9697321480179461007014003 14545982220269191510521005)
                  ·
                    refine ⟨5454743332600946816445377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14545982220269191510521005 5454743332600946816445377)
                    ·
                      refine ⟨4091057499450710112334033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5454743332600946816445377 4091057499450710112334033)
                      ·
                        rfl

theorem cell23_7967306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 4, 1, 1, 3, 2].length) (baseStart_7967306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7967306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7967306 prefixEnd_7967306 := by exact prefixLift 7967306
  have htrace : WordTrace (prefixWord ++ tailWord_7967306) baseStart_7967306 baseEnd_7967306 := by
    simpa [prefixWord, tailWord_7967306, baseEnd_7967306] using wordTrace_append hprefix tailTrace_7967306
  have hstable : (prefixWord ++ tailWord_7967306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7967306).length < 2 ^ (prefixWord ++ tailWord_7967306).sum := by decide
  have hdescent : baseEnd_7967306 < baseStart_7967306 := by decide
  rcases family_descends (prefixWord ++ tailWord_7967306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7967319 : List Nat := [1, 1, 3, 2, 2, 2, 3, 1, 4, 2, 2]
def baseStart_7967319 : Nat := 118140960795 + 7967319 * 2 ^ 59
def prefixEnd_7967319 : Nat := 4983230072969 + 3 ^ 40 * 7967319 * 2
def baseEnd_7967319 : Nat := 4091064174699218561471473

theorem tailTrace_7967319 : CollatzResearch.WordTrace tailWord_7967319 prefixEnd_7967319 4091064174699218561471473 := by
  unfold tailWord_7967319
  simp only [CollatzResearch.WordTrace]
  refine ⟨290591997022771447598673011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193727998015180965065782007 290591997022771447598673011)
  ·
    refine ⟨435887995534157171398009517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290591997022771447598673011 435887995534157171398009517)
    ·
      refine ⟨163457998325308939274253569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 435887995534157171398009517 163457998325308939274253569)
      ·
        refine ⟨122593498743981704455690177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163457998325308939274253569 122593498743981704455690177)
        ·
          refine ⟨91945124057986278341767633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122593498743981704455690177 91945124057986278341767633)
          ·
            refine ⟨68958843043489708756325725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91945124057986278341767633 68958843043489708756325725)
            ·
              refine ⟨25859566141308640783622147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68958843043489708756325725 25859566141308640783622147)
              ·
                refine ⟨38789349211962961175433221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25859566141308640783622147 38789349211962961175433221)
                ·
                  refine ⟨7273002977243055220393729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38789349211962961175433221 7273002977243055220393729)
                  ·
                    refine ⟨5454752232932291415295297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7273002977243055220393729 5454752232932291415295297)
                    ·
                      refine ⟨4091064174699218561471473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5454752232932291415295297 4091064174699218561471473)
                      ·
                        rfl

theorem cell23_7967319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 1, 4, 2, 2].length) (baseStart_7967319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7967319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7967319 prefixEnd_7967319 := by exact prefixLift 7967319
  have htrace : WordTrace (prefixWord ++ tailWord_7967319) baseStart_7967319 baseEnd_7967319 := by
    simpa [prefixWord, tailWord_7967319, baseEnd_7967319] using wordTrace_append hprefix tailTrace_7967319
  have hstable : (prefixWord ++ tailWord_7967319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7967319).length < 2 ^ (prefixWord ++ tailWord_7967319).sum := by decide
  have hdescent : baseEnd_7967319 < baseStart_7967319 := by decide
  rcases family_descends (prefixWord ++ tailWord_7967319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7967330 : List Nat := [3, 3, 2, 3, 1, 1, 3, 1, 2, 1, 3]
def baseStart_7967330 : Nat := 118140960795 + 7967330 * 2 ^ 59
def prefixEnd_7967330 : Nat := 4983230072969 + 3 ^ 40 * 7967330 * 2
def baseEnd_7967330 : Nat := 4091069822986418018433923

theorem tailTrace_7967330 : CollatzResearch.WordTrace tailWord_7967330 prefixEnd_7967330 4091069822986418018433923 := by
  unfold tailWord_7967330
  simp only [CollatzResearch.WordTrace]
  refine ⟨72648099556432899119330861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193728265483821064318215629 72648099556432899119330861)
  ·
    refine ⟨27243037333662337169749073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72648099556432899119330861 27243037333662337169749073)
    ·
      refine ⟨20432278000246752877311805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27243037333662337169749073 20432278000246752877311805)
      ·
        refine ⟨7662104250092532328991927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20432278000246752877311805 7662104250092532328991927)
        ·
          refine ⟨11493156375138798493487891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7662104250092532328991927 11493156375138798493487891)
          ·
            refine ⟨17239734562708197740231837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11493156375138798493487891 17239734562708197740231837)
            ·
              refine ⟨6464900461015574152586939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17239734562708197740231837 6464900461015574152586939)
              ·
                refine ⟨9697350691523361228880409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6464900461015574152586939 9697350691523361228880409)
                ·
                  refine ⟨7273013018642520921660307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9697350691523361228880409 7273013018642520921660307)
                  ·
                    refine ⟨10909519527963781382490461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7273013018642520921660307 10909519527963781382490461)
                    ·
                      refine ⟨4091069822986418018433923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10909519527963781382490461 4091069822986418018433923)
                      ·
                        rfl

theorem cell23_7967330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_7967330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7967330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7967330 prefixEnd_7967330 := by exact prefixLift 7967330
  have htrace : WordTrace (prefixWord ++ tailWord_7967330) baseStart_7967330 baseEnd_7967330 := by
    simpa [prefixWord, tailWord_7967330, baseEnd_7967330] using wordTrace_append hprefix tailTrace_7967330
  have hstable : (prefixWord ++ tailWord_7967330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7967330).length < 2 ^ (prefixWord ++ tailWord_7967330).sum := by decide
  have hdescent : baseEnd_7967330 < baseStart_7967330 := by decide
  rcases family_descends (prefixWord ++ tailWord_7967330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7967342 : List Nat := [4, 1, 2, 2, 2, 1, 2, 2, 7]
def baseStart_7967342 : Nat := 118140960795 + 7967342 * 2 ^ 59
def prefixEnd_7967342 : Nat := 4983230072969 + 3 ^ 40 * 7967342 * 2
def baseEnd_7967342 : Nat := 454563998306030219053763

theorem tailTrace_7967342 : CollatzResearch.WordTrace tailWord_7967342 prefixEnd_7967342 454563998306030219053763 := by
  unfold tailWord_7967342
  simp only [CollatzResearch.WordTrace]
  refine ⟨36324104487711015315845035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193728557267792081684506853 36324104487711015315845035)
  ·
    refine ⟨54486156731566522973767553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36324104487711015315845035 54486156731566522973767553)
    ·
      refine ⟨40864617548674892230325665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54486156731566522973767553 40864617548674892230325665)
      ·
        refine ⟨30648463161506169172744249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40864617548674892230325665 30648463161506169172744249)
        ·
          refine ⟨22986347371129626879558187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30648463161506169172744249 22986347371129626879558187)
          ·
            refine ⟨34479521056694440319337281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22986347371129626879558187 34479521056694440319337281)
            ·
              refine ⟨25859640792520830239502961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34479521056694440319337281 25859640792520830239502961)
              ·
                refine ⟨19394730594390622679627221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25859640792520830239502961 19394730594390622679627221)
                ·
                  refine ⟨454563998306030219053763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19394730594390622679627221 454563998306030219053763)
                  ·
                    rfl

theorem cell23_7967342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 2, 7].length) (baseStart_7967342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7967342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7967342 prefixEnd_7967342 := by exact prefixLift 7967342
  have htrace : WordTrace (prefixWord ++ tailWord_7967342) baseStart_7967342 baseEnd_7967342 := by
    simpa [prefixWord, tailWord_7967342, baseEnd_7967342] using wordTrace_append hprefix tailTrace_7967342
  have hstable : (prefixWord ++ tailWord_7967342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7967342).length < 2 ^ (prefixWord ++ tailWord_7967342).sum := by decide
  have hdescent : baseEnd_7967342 < baseStart_7967342 := by decide
  rcases family_descends (prefixWord ++ tailWord_7967342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7967406 : List Nat := [4, 1, 4, 1, 1, 2, 2, 1, 2, 5]
def baseStart_7967406 : Nat := 118140960795 + 7967406 * 2 ^ 59
def prefixEnd_7967406 : Nat := 4983230072969 + 3 ^ 40 * 7967406 * 2
def baseEnd_7967406 : Nat := 1363702949172053240361191

theorem tailTrace_7967406 : CollatzResearch.WordTrace tailWord_7967406 prefixEnd_7967406 1363702949172053240361191 := by
  unfold tailWord_7967406
  simp only [CollatzResearch.WordTrace]
  refine ⟨36324396271682032682136259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193730113448970840971393381 36324396271682032682136259)
  ·
    refine ⟨54486594407523049023204389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36324396271682032682136259 54486594407523049023204389)
    ·
      refine ⟨10216236451410571691850823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54486594407523049023204389 10216236451410571691850823)
      ·
        refine ⟨15324354677115857537776235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10216236451410571691850823 15324354677115857537776235)
        ·
          refine ⟨22986532015673786306664353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15324354677115857537776235 22986532015673786306664353)
          ·
            refine ⟨17239899011755339729998265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22986532015673786306664353 17239899011755339729998265)
            ·
              refine ⟨12929924258816504797498699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17239899011755339729998265 12929924258816504797498699)
              ·
                refine ⟨19394886388224757196248049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12929924258816504797498699 19394886388224757196248049)
                ·
                  refine ⟨14546164791168567897186037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19394886388224757196248049 14546164791168567897186037)
                  ·
                    refine ⟨1363702949172053240361191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14546164791168567897186037 1363702949172053240361191)
                    ·
                      rfl

theorem cell23_7967406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_7967406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7967406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7967406 prefixEnd_7967406 := by exact prefixLift 7967406
  have htrace : WordTrace (prefixWord ++ tailWord_7967406) baseStart_7967406 baseEnd_7967406 := by
    simpa [prefixWord, tailWord_7967406, baseEnd_7967406] using wordTrace_append hprefix tailTrace_7967406
  have hstable : (prefixWord ++ tailWord_7967406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7967406).length < 2 ^ (prefixWord ++ tailWord_7967406).sum := by decide
  have hdescent : baseEnd_7967406 < baseStart_7967406 := by decide
  rcases family_descends (prefixWord ++ tailWord_7967406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7967422 : List Nat := [4, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6]
def baseStart_7967422 : Nat := 118140960795 + 7967422 * 2 ^ 59
def prefixEnd_7967422 : Nat := 4983230072969 + 3 ^ 40 * 7967422 * 2
def baseEnd_7967422 : Nat := 4091117063206631658483499

theorem tailTrace_7967422 : CollatzResearch.WordTrace tailWord_7967422 prefixEnd_7967422 4091117063206631658483499 := by
  unfold tailWord_7967422
  simp only [CollatzResearch.WordTrace]
  refine ⟨36324469217674787023709065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193730502494265530793115013 36324469217674787023709065)
  ·
    refine ⟨27243351913256090267781799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36324469217674787023709065 27243351913256090267781799)
    ·
      refine ⟨40865027869884135401672699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27243351913256090267781799 40865027869884135401672699)
      ·
        refine ⟨61297541804826203102509049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40865027869884135401672699 61297541804826203102509049)
        ·
          refine ⟨45973156353619652326881787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61297541804826203102509049 45973156353619652326881787)
          ·
            refine ⟨68959734530429478490322681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45973156353619652326881787 68959734530429478490322681)
            ·
              refine ⟨51719800897822108867742011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68959734530429478490322681 51719800897822108867742011)
              ·
                refine ⟨77579701346733163301613017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51719800897822108867742011 77579701346733163301613017)
                ·
                  refine ⟨58184776010049872476209763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77579701346733163301613017 58184776010049872476209763)
                  ·
                    refine ⟨87277164015074808714314645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58184776010049872476209763 87277164015074808714314645)
                    ·
                      refine ⟨4091117063206631658483499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87277164015074808714314645 4091117063206631658483499)
                      ·
                        rfl

theorem cell23_7967422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_7967422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7967422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7967422 prefixEnd_7967422 := by exact prefixLift 7967422
  have htrace : WordTrace (prefixWord ++ tailWord_7967422) baseStart_7967422 baseEnd_7967422 := by
    simpa [prefixWord, tailWord_7967422, baseEnd_7967422] using wordTrace_append hprefix tailTrace_7967422
  have hstable : (prefixWord ++ tailWord_7967422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7967422).length < 2 ^ (prefixWord ++ tailWord_7967422).sum := by decide
  have hdescent : baseEnd_7967422 < baseStart_7967422 := by decide
  rcases family_descends (prefixWord ++ tailWord_7967422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7967432 : List Nat := [2, 1, 3, 1, 2, 3, 1, 4, 6]
def baseStart_7967432 : Nat := 118140960795 + 7967432 * 2 ^ 59
def prefixEnd_7967432 : Nat := 4983230072969 + 3 ^ 40 * 7967432 * 2
def baseEnd_7967432 : Nat := 454569133112575179928717

theorem tailTrace_7967432 : CollatzResearch.WordTrace tailWord_7967432 prefixEnd_7967432 454569133112575179928717 := by
  unfold tailWord_7967432
  simp only [CollatzResearch.WordTrace]
  refine ⟨145298059235681033948768275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193730745647574711931691033 145298059235681033948768275)
  ·
    refine ⟨217947088853521550923152413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145298059235681033948768275 217947088853521550923152413)
    ·
      refine ⟨81730158320070581596182155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217947088853521550923152413 81730158320070581596182155)
      ·
        refine ⟨122595237480105872394273233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81730158320070581596182155 122595237480105872394273233)
        ·
          refine ⟨91946428110079404295704925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122595237480105872394273233 91946428110079404295704925)
          ·
            refine ⟨34479910541279776610889347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91946428110079404295704925 34479910541279776610889347)
            ·
              refine ⟨51719865811919664916334021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34479910541279776610889347 51719865811919664916334021)
              ·
                refine ⟨9697474839734937171812629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51719865811919664916334021 9697474839734937171812629)
                ·
                  refine ⟨454569133112575179928717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9697474839734937171812629 454569133112575179928717)
                  ·
                    rfl

theorem cell23_7967432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 4, 6].length) (baseStart_7967432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7967432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7967432 prefixEnd_7967432 := by exact prefixLift 7967432
  have htrace : WordTrace (prefixWord ++ tailWord_7967432) baseStart_7967432 baseEnd_7967432 := by
    simpa [prefixWord, tailWord_7967432, baseEnd_7967432] using wordTrace_append hprefix tailTrace_7967432
  have hstable : (prefixWord ++ tailWord_7967432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7967432).length < 2 ^ (prefixWord ++ tailWord_7967432).sum := by decide
  have hdescent : baseEnd_7967432 < baseStart_7967432 := by decide
  rcases family_descends (prefixWord ++ tailWord_7967432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7967516 : List Nat := [2, 2, 3, 1, 1, 4, 2, 2, 1, 1, 4]
def baseStart_7967516 : Nat := 118140960795 + 7967516 * 2 ^ 59
def prefixEnd_7967516 : Nat := 4983230072969 + 3 ^ 40 * 7967516 * 2
def baseEnd_7967516 : Nat := 4091165330388154290708067

theorem tailTrace_7967516 : CollatzResearch.WordTrace tailWord_7967516 prefixEnd_7967516 4091165330388154290708067 := by
  unfold tailWord_7967516
  simp only [CollatzResearch.WordTrace]
  refine ⟨145299591101528875121797201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193732788135371833495729601 145299591101528875121797201)
  ·
    refine ⟨108974693326146656341347901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145299591101528875121797201 108974693326146656341347901)
    ·
      refine ⟨40865509997304996128005463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108974693326146656341347901 40865509997304996128005463)
      ·
        refine ⟨61298264995957494192008195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40865509997304996128005463 61298264995957494192008195)
        ·
          refine ⟨91947397493936241288012293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61298264995957494192008195 91947397493936241288012293)
          ·
            refine ⟨17240137030113045241502305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91947397493936241288012293 17240137030113045241502305)
            ·
              refine ⟨12930102772584783931126729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17240137030113045241502305 12930102772584783931126729)
              ·
                refine ⟨9697577079438587948345047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12930102772584783931126729 9697577079438587948345047)
                ·
                  refine ⟨14546365619157881922517571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9697577079438587948345047 14546365619157881922517571)
                  ·
                    refine ⟨21819548428736822883776357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14546365619157881922517571 21819548428736822883776357)
                    ·
                      refine ⟨4091165330388154290708067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21819548428736822883776357 4091165330388154290708067)
                      ·
                        rfl

theorem cell23_7967516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 2, 1, 1, 4].length) (baseStart_7967516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7967516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7967516 prefixEnd_7967516 := by exact prefixLift 7967516
  have htrace : WordTrace (prefixWord ++ tailWord_7967516) baseStart_7967516 baseEnd_7967516 := by
    simpa [prefixWord, tailWord_7967516, baseEnd_7967516] using wordTrace_append hprefix tailTrace_7967516
  have hstable : (prefixWord ++ tailWord_7967516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7967516).length < 2 ^ (prefixWord ++ tailWord_7967516).sum := by decide
  have hdescent : baseEnd_7967516 < baseStart_7967516 := by decide
  rcases family_descends (prefixWord ++ tailWord_7967516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7967559 : List Nat := [1, 1, 4, 1, 2, 1, 1, 1, 2, 7, 2]
def baseStart_7967559 : Nat := 118140960795 + 7967559 * 2 ^ 59
def prefixEnd_7967559 : Nat := 4983230072969 + 3 ^ 40 * 7967559 * 2
def baseEnd_7967559 : Nat := 4091187410056297622470369

theorem tailTrace_7967559 : CollatzResearch.WordTrace tailWord_7967559 prefixEnd_7967559 4091187410056297622470369 := by
  unfold tailWord_7967559
  simp only [CollatzResearch.WordTrace]
  refine ⟨290600750541901968587409731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193733833694601312391606487 290600750541901968587409731)
  ·
    refine ⟨435901125812852952881114597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290600750541901968587409731 435901125812852952881114597)
    ·
      refine ⟨81731461089909928665208987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 435901125812852952881114597 81731461089909928665208987)
      ·
        refine ⟨122597191634864892997813481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81731461089909928665208987 122597191634864892997813481)
        ·
          refine ⟨91947893726148669748360111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122597191634864892997813481 91947893726148669748360111)
          ·
            refine ⟨137921840589223004622540167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91947893726148669748360111 137921840589223004622540167)
            ·
              refine ⟨206882760883834506933810251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137921840589223004622540167 206882760883834506933810251)
              ·
                refine ⟨310324141325751760400715377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206882760883834506933810251 310324141325751760400715377)
                ·
                  refine ⟨232743105994313820300536533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 310324141325751760400715377 232743105994313820300536533)
                  ·
                    refine ⟨5454916546741730163293825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 232743105994313820300536533 5454916546741730163293825)
                    ·
                      refine ⟨4091187410056297622470369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5454916546741730163293825 4091187410056297622470369)
                      ·
                        rfl

theorem cell23_7967559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 7, 2].length) (baseStart_7967559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7967559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7967559 prefixEnd_7967559 := by exact prefixLift 7967559
  have htrace : WordTrace (prefixWord ++ tailWord_7967559) baseStart_7967559 baseEnd_7967559 := by
    simpa [prefixWord, tailWord_7967559, baseEnd_7967559] using wordTrace_append hprefix tailTrace_7967559
  have hstable : (prefixWord ++ tailWord_7967559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7967559).length < 2 ^ (prefixWord ++ tailWord_7967559).sum := by decide
  have hdescent : baseEnd_7967559 < baseStart_7967559 := by decide
  rcases family_descends (prefixWord ++ tailWord_7967559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7967562 : List Nat := [3, 1, 2, 1, 1, 1, 2, 2, 1, 4, 5]
def baseStart_7967562 : Nat := 118140960795 + 7967562 * 2 ^ 59
def prefixEnd_7967562 : Nat := 4983230072969 + 3 ^ 40 * 7967562 * 2
def baseEnd_7967562 : Nat := 4091188950498261110732855

theorem tailTrace_7967562 : CollatzResearch.WordTrace tailWord_7967562 prefixEnd_7967562 4091188950498261110732855 := by
  unfold tailWord_7967562
  simp only [CollatzResearch.WordTrace]
  refine ⟨72650214990222775024942235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193733906640594066733179293 72650214990222775024942235)
  ·
    refine ⟨108975322485334162537413353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72650214990222775024942235 108975322485334162537413353)
    ·
      refine ⟨81731491864000621903060015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108975322485334162537413353 81731491864000621903060015)
      ·
        refine ⟨122597237796000932854590023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81731491864000621903060015 122597237796000932854590023)
        ·
          refine ⟨183895856694001399281885035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122597237796000932854590023 183895856694001399281885035)
          ·
            refine ⟨275843785041002098922827553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183895856694001399281885035 275843785041002098922827553)
            ·
              refine ⟨206882838780751574192120665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 275843785041002098922827553 206882838780751574192120665)
              ·
                refine ⟨155162129085563680644090499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 206882838780751574192120665 155162129085563680644090499)
                ·
                  refine ⟨232743193628345520966135749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 155162129085563680644090499 232743193628345520966135749)
                  ·
                    refine ⟨43639348805314785181150453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 232743193628345520966135749 43639348805314785181150453)
                    ·
                      refine ⟨4091188950498261110732855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43639348805314785181150453 4091188950498261110732855)
                      ·
                        rfl

theorem cell23_7967562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 1, 4, 5].length) (baseStart_7967562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7967562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7967562 prefixEnd_7967562 := by exact prefixLift 7967562
  have htrace : WordTrace (prefixWord ++ tailWord_7967562) baseStart_7967562 baseEnd_7967562 := by
    simpa [prefixWord, tailWord_7967562, baseEnd_7967562] using wordTrace_append hprefix tailTrace_7967562
  have hstable : (prefixWord ++ tailWord_7967562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7967562).length < 2 ^ (prefixWord ++ tailWord_7967562).sum := by decide
  have hdescent : baseEnd_7967562 < baseStart_7967562 := by decide
  rcases family_descends (prefixWord ++ tailWord_7967562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7967606 : List Nat := [5, 1, 1, 3, 1, 1, 1, 1, 2, 3, 4]
def baseStart_7967606 : Nat := 118140960795 + 7967606 * 2 ^ 59
def prefixEnd_7967606 : Nat := 4983230072969 + 3 ^ 40 * 7967606 * 2
def baseEnd_7967606 : Nat := 4091211543647058938582653

theorem tailTrace_7967606 : CollatzResearch.WordTrace tailWord_7967606 prefixEnd_7967606 4091211543647058938582653 := by
  unfold tailWord_7967606
  simp only [CollatzResearch.WordTrace]
  refine ⟨18162654048295730975898167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 193734976515154463742913781 18162654048295730975898167)
  ·
    refine ⟨27243981072443596463847251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18162654048295730975898167 27243981072443596463847251)
    ·
      refine ⟨40865971608665394695770877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27243981072443596463847251 40865971608665394695770877)
      ·
        refine ⟨15324739353249523010914079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40865971608665394695770877 15324739353249523010914079)
        ·
          refine ⟨22987109029874284516371119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15324739353249523010914079 22987109029874284516371119)
          ·
            refine ⟨34480663544811426774556679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22987109029874284516371119 34480663544811426774556679)
            ·
              refine ⟨51720995317217140161835019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34480663544811426774556679 51720995317217140161835019)
              ·
                refine ⟨77581492975825710242752529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51720995317217140161835019 77581492975825710242752529)
                ·
                  refine ⟨58186119731869282682064397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77581492975825710242752529 58186119731869282682064397)
                  ·
                    refine ⟨21819794899450981005774149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58186119731869282682064397 21819794899450981005774149)
                    ·
                      refine ⟨4091211543647058938582653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21819794899450981005774149 4091211543647058938582653)
                      ·
                        rfl

theorem cell23_7967606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_7967606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7967606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7967606 prefixEnd_7967606 := by exact prefixLift 7967606
  have htrace : WordTrace (prefixWord ++ tailWord_7967606) baseStart_7967606 baseEnd_7967606 := by
    simpa [prefixWord, tailWord_7967606, baseEnd_7967606] using wordTrace_append hprefix tailTrace_7967606
  have hstable : (prefixWord ++ tailWord_7967606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7967606).length < 2 ^ (prefixWord ++ tailWord_7967606).sum := by decide
  have hdescent : baseEnd_7967606 < baseStart_7967606 := by decide
  rcases family_descends (prefixWord ++ tailWord_7967606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7967609 : List Nat := [1, 2, 1, 3, 2, 3, 1, 1, 2, 4, 3]
def baseStart_7967609 : Nat := 118140960795 + 7967609 * 2 ^ 59
def prefixEnd_7967609 : Nat := 4983230072969 + 3 ^ 40 * 7967609 * 2
def baseEnd_7967609 : Nat := 4091213084089022426845139

theorem tailTrace_7967609 : CollatzResearch.WordTrace tailWord_7967609 prefixEnd_7967609 4091213084089022426845139 := by
  unfold tailWord_7967609
  simp only [CollatzResearch.WordTrace]
  refine ⟨290602574191720827126729881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193735049461147218084486587 290602574191720827126729881)
  ·
    refine ⟨217951930643790620345047411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290602574191720827126729881 217951930643790620345047411)
    ·
      refine ⟨326927895965685930517571117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217951930643790620345047411 326927895965685930517571117)
      ·
        refine ⟨122597960987132223944089169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 326927895965685930517571117 122597960987132223944089169)
        ·
          refine ⟨91948470740349167958066877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122597960987132223944089169 91948470740349167958066877)
          ·
            refine ⟨34480676527630937984275079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91948470740349167958066877 34480676527630937984275079)
            ·
              refine ⟨51721014791446406976412619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34480676527630937984275079 51721014791446406976412619)
              ·
                refine ⟨77581522187169610464618929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51721014791446406976412619 77581522187169610464618929)
                ·
                  refine ⟨58186141640377207848464197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77581522187169610464618929 58186141640377207848464197)
                  ·
                    refine ⟨10909901557570726471587037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58186141640377207848464197 10909901557570726471587037)
                    ·
                      refine ⟨4091213084089022426845139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10909901557570726471587037 4091213084089022426845139)
                      ·
                        rfl

theorem cell23_7967609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 2, 4, 3].length) (baseStart_7967609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7967609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7967609 prefixEnd_7967609 := by exact prefixLift 7967609
  have htrace : WordTrace (prefixWord ++ tailWord_7967609) baseStart_7967609 baseEnd_7967609 := by
    simpa [prefixWord, tailWord_7967609, baseEnd_7967609] using wordTrace_append hprefix tailTrace_7967609
  have hstable : (prefixWord ++ tailWord_7967609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7967609).length < 2 ^ (prefixWord ++ tailWord_7967609).sum := by decide
  have hdescent : baseEnd_7967609 < baseStart_7967609 := by decide
  rcases family_descends (prefixWord ++ tailWord_7967609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7967612 : List Nat := [2, 2, 2, 1, 1, 1, 1, 2, 11]
def baseStart_7967612 : Nat := 118140960795 + 7967612 * 2 ^ 59
def prefixEnd_7967612 : Nat := 4983230072969 + 3 ^ 40 * 7967612 * 2
def baseEnd_7967612 : Nat := 454579402725665101678625

theorem tailTrace_7967612 : CollatzResearch.WordTrace tailWord_7967612 prefixEnd_7967612 454579402725665101678625 := by
  unfold tailWord_7967612
  simp only [CollatzResearch.WordTrace]
  refine ⟨145301341805354979319544545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193735122407139972426059393 145301341805354979319544545)
  ·
    refine ⟨108976006354016234489658409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145301341805354979319544545 108976006354016234489658409)
    ·
      refine ⟨81732004765512175867243807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108976006354016234489658409 81732004765512175867243807)
      ·
        refine ⟨122598007148268263800865711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81732004765512175867243807 122598007148268263800865711)
        ·
          refine ⟨183897010722402395701298567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122598007148268263800865711 183897010722402395701298567)
          ·
            refine ⟨275845516083603593551947851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183897010722402395701298567 275845516083603593551947851)
            ·
              refine ⟨413768274125405390327921777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275845516083603593551947851 413768274125405390327921777)
              ·
                refine ⟨310326205594054042745941333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 413768274125405390327921777 310326205594054042745941333)
                ·
                  refine ⟨454579402725665101678625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 310326205594054042745941333 454579402725665101678625)
                  ·
                    rfl

theorem cell23_7967612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 11].length) (baseStart_7967612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7967612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7967612 prefixEnd_7967612 := by exact prefixLift 7967612
  have htrace : WordTrace (prefixWord ++ tailWord_7967612) baseStart_7967612 baseEnd_7967612 := by
    simpa [prefixWord, tailWord_7967612, baseEnd_7967612] using wordTrace_append hprefix tailTrace_7967612
  have hstable : (prefixWord ++ tailWord_7967612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7967612).length < 2 ^ (prefixWord ++ tailWord_7967612).sum := by decide
  have hdescent : baseEnd_7967612 < baseStart_7967612 := by decide
  rcases family_descends (prefixWord ++ tailWord_7967612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7967619 : List Nat := [1, 1, 1, 3, 4, 1, 3, 1, 2, 2, 4]
def baseStart_7967619 : Nat := 118140960795 + 7967619 * 2 ^ 59
def prefixEnd_7967619 : Nat := 4983230072969 + 3 ^ 40 * 7967619 * 2
def baseEnd_7967619 : Nat := 4091218218895567387720093

theorem tailTrace_7967619 : CollatzResearch.WordTrace tailWord_7967619 prefixEnd_7967619 4091218218895567387720093 := by
  unfold tailWord_7967619
  simp only [CollatzResearch.WordTrace]
  refine ⟨290602938921684598834593911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193735292614456399223062607 290602938921684598834593911)
  ·
    refine ⟨435904408382526898251890867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290602938921684598834593911 435904408382526898251890867)
    ·
      refine ⟨653856612573790347377836301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435904408382526898251890867 653856612573790347377836301)
      ·
        refine ⟨245196229715171380266688613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 653856612573790347377836301 245196229715171380266688613)
        ·
          refine ⟨45974293071594633800004115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 245196229715171380266688613 45974293071594633800004115)
          ·
            refine ⟨68961439607391950700006173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45974293071594633800004115 68961439607391950700006173)
            ·
              refine ⟨25860539852771981512502315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68961439607391950700006173 25860539852771981512502315)
              ·
                refine ⟨38790809779157972268753473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25860539852771981512502315 38790809779157972268753473)
                ·
                  refine ⟨29093107334368479201565105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38790809779157972268753473 29093107334368479201565105)
                  ·
                    refine ⟨21819830500776359401173829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29093107334368479201565105 21819830500776359401173829)
                    ·
                      refine ⟨4091218218895567387720093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21819830500776359401173829 4091218218895567387720093)
                      ·
                        rfl

theorem cell23_7967619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 1, 2, 2, 4].length) (baseStart_7967619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7967619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7967619 prefixEnd_7967619 := by exact prefixLift 7967619
  have htrace : WordTrace (prefixWord ++ tailWord_7967619) baseStart_7967619 baseEnd_7967619 := by
    simpa [prefixWord, tailWord_7967619, baseEnd_7967619] using wordTrace_append hprefix tailTrace_7967619
  have hstable : (prefixWord ++ tailWord_7967619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7967619).length < 2 ^ (prefixWord ++ tailWord_7967619).sum := by decide
  have hdescent : baseEnd_7967619 < baseStart_7967619 := by decide
  rcases family_descends (prefixWord ++ tailWord_7967619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7967623 : List Nat := [1, 1, 4, 2, 3, 2, 2, 1, 1, 4, 2]
def baseStart_7967623 : Nat := 118140960795 + 7967623 * 2 ^ 59
def prefixEnd_7967623 : Nat := 4983230072969 + 3 ^ 40 * 7967623 * 2
def baseEnd_7967623 : Nat := 4091220272818185372070075

theorem tailTrace_7967623 : CollatzResearch.WordTrace tailWord_7967623 prefixEnd_7967623 4091220272818185372070075 := by
  unfold tailWord_7967623
  simp only [CollatzResearch.WordTrace]
  refine ⟨290603084813670107517739523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193735389875780071678493015 290603084813670107517739523)
  ·
    refine ⟨435904627220505161276609285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290603084813670107517739523 435904627220505161276609285)
    ·
      refine ⟨81732117603844717739364241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 435904627220505161276609285 81732117603844717739364241)
      ·
        refine ⟨61299088202883538304523181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81732117603844717739364241 61299088202883538304523181)
        ·
          refine ⟨22987158076081326864196193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61299088202883538304523181 22987158076081326864196193)
          ·
            refine ⟨17240368557060995148147145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22987158076081326864196193 17240368557060995148147145)
            ·
              refine ⟨12930276417795746361110359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17240368557060995148147145 12930276417795746361110359)
              ·
                refine ⟨19395414626693619541665539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12930276417795746361110359 19395414626693619541665539)
                ·
                  refine ⟨29093121940040429312498309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19395414626693619541665539 29093121940040429312498309)
                  ·
                    refine ⟨5454960363757580496093433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29093121940040429312498309 5454960363757580496093433)
                    ·
                      refine ⟨4091220272818185372070075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5454960363757580496093433 4091220272818185372070075)
                      ·
                        rfl

theorem cell23_7967623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 1, 1, 4, 2].length) (baseStart_7967623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7967623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7967623 prefixEnd_7967623 := by exact prefixLift 7967623
  have htrace : WordTrace (prefixWord ++ tailWord_7967623) baseStart_7967623 baseEnd_7967623 := by
    simpa [prefixWord, tailWord_7967623, baseEnd_7967623] using wordTrace_append hprefix tailTrace_7967623
  have hstable : (prefixWord ++ tailWord_7967623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7967623).length < 2 ^ (prefixWord ++ tailWord_7967623).sum := by decide
  have hdescent : baseEnd_7967623 < baseStart_7967623 := by decide
  rcases family_descends (prefixWord ++ tailWord_7967623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7967632 : List Nat := [2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 6]
def baseStart_7967632 : Nat := 118140960795 + 7967632 * 2 ^ 59
def prefixEnd_7967632 : Nat := 4983230072969 + 3 ^ 40 * 7967632 * 2
def baseEnd_7967632 : Nat := 4091224894144075836857533

theorem tailTrace_7967632 : CollatzResearch.WordTrace tailWord_7967632 prefixEnd_7967632 4091224894144075836857533 := by
  unfold tailWord_7967632
  simp only [CollatzResearch.WordTrace]
  refine ⟨145301706535318751027408575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193735608713758334703211433 145301706535318751027408575)
  ·
    refine ⟨217952559802978126541112863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145301706535318751027408575 217952559802978126541112863)
    ·
      refine ⟨326928839704467189811669295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217952559802978126541112863 326928839704467189811669295)
      ·
        refine ⟨490393259556700784717503943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326928839704467189811669295 490393259556700784717503943)
        ·
          refine ⟨735589889335051177076255915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 490393259556700784717503943 735589889335051177076255915)
          ·
            refine ⟨1103384834002576765614383873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 735589889335051177076255915 1103384834002576765614383873)
            ·
              refine ⟨827538625501932574210787905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1103384834002576765614383873 827538625501932574210787905)
              ·
                refine ⟨620653969126449430658090929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 827538625501932574210787905 620653969126449430658090929)
                ·
                  refine ⟨465490476844837072993568197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 620653969126449430658090929 465490476844837072993568197)
                  ·
                    refine ⟨87279464408406951186294037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 465490476844837072993568197 87279464408406951186294037)
                    ·
                      refine ⟨4091224894144075836857533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87279464408406951186294037 4091224894144075836857533)
                      ·
                        rfl

theorem cell23_7967632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 6].length) (baseStart_7967632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7967632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7967632 prefixEnd_7967632 := by exact prefixLift 7967632
  have htrace : WordTrace (prefixWord ++ tailWord_7967632) baseStart_7967632 baseEnd_7967632 := by
    simpa [prefixWord, tailWord_7967632, baseEnd_7967632] using wordTrace_append hprefix tailTrace_7967632
  have hstable : (prefixWord ++ tailWord_7967632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7967632).length < 2 ^ (prefixWord ++ tailWord_7967632).sum := by decide
  have hdescent : baseEnd_7967632 < baseStart_7967632 := by decide
  rcases family_descends (prefixWord ++ tailWord_7967632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7967639 : List Nat := [1, 1, 3, 3, 1, 2, 1, 2, 1, 5, 3]
def baseStart_7967639 : Nat := 118140960795 + 7967639 * 2 ^ 59
def prefixEnd_7967639 : Nat := 4983230072969 + 3 ^ 40 * 7967639 * 2
def baseEnd_7967639 : Nat := 4091228488508657309470001

theorem tailTrace_7967639 : CollatzResearch.WordTrace tailWord_7967639 prefixEnd_7967639 4091228488508657309470001 := by
  unfold tailWord_7967639
  simp only [CollatzResearch.WordTrace]
  refine ⟨290603668381612142250321971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193735778921074761500214647 290603668381612142250321971)
  ·
    refine ⟨435905502572418213375482957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290603668381612142250321971 435905502572418213375482957)
    ·
      refine ⟨163464563464656830015806109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 435905502572418213375482957 163464563464656830015806109)
      ·
        refine ⟨61299211299246311255927291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163464563464656830015806109 61299211299246311255927291)
        ·
          refine ⟨91948816948869466883890937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61299211299246311255927291 91948816948869466883890937)
          ·
            refine ⟨68961612711652100162918203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91948816948869466883890937 68961612711652100162918203)
            ·
              refine ⟨103442419067478150244377305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68961612711652100162918203 103442419067478150244377305)
              ·
                refine ⟨77581814300608612683282979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103442419067478150244377305 77581814300608612683282979)
                ·
                  refine ⟨116372721450912919024924469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77581814300608612683282979 116372721450912919024924469)
                  ·
                    refine ⟨10909942636023086158586669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 116372721450912919024924469 10909942636023086158586669)
                    ·
                      refine ⟨4091228488508657309470001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10909942636023086158586669 4091228488508657309470001)
                      ·
                        rfl

theorem cell23_7967639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 5, 3].length) (baseStart_7967639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7967639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7967639 prefixEnd_7967639 := by exact prefixLift 7967639
  have htrace : WordTrace (prefixWord ++ tailWord_7967639) baseStart_7967639 baseEnd_7967639 := by
    simpa [prefixWord, tailWord_7967639, baseEnd_7967639] using wordTrace_append hprefix tailTrace_7967639
  have hstable : (prefixWord ++ tailWord_7967639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7967639).length < 2 ^ (prefixWord ++ tailWord_7967639).sum := by decide
  have hdescent : baseEnd_7967639 < baseStart_7967639 := by decide
  rcases family_descends (prefixWord ++ tailWord_7967639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7967644 : List Nat := [2, 2, 3, 3, 3, 1, 2, 1, 1, 3, 2]
def baseStart_7967644 : Nat := 118140960795 + 7967644 * 2 ^ 59
def prefixEnd_7967644 : Nat := 4983230072969 + 3 ^ 40 * 7967644 * 2
def baseEnd_7967644 : Nat := 4091231055911929789907479

theorem tailTrace_7967644 : CollatzResearch.WordTrace tailWord_7967644 prefixEnd_7967644 4091231055911929789907479 := by
  unfold tailWord_7967644
  simp only [CollatzResearch.WordTrace]
  refine ⟨145301925373297014052126993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193735900497729352069502657 145301925373297014052126993)
  ·
    refine ⟨108976444029972760539095245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145301925373297014052126993 108976444029972760539095245)
    ·
      refine ⟨40866166511239785202160717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108976444029972760539095245 40866166511239785202160717)
      ·
        refine ⟨15324812441714919450810269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40866166511239785202160717 15324812441714919450810269)
        ·
          refine ⟨5746804665643094794053851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15324812441714919450810269 5746804665643094794053851)
          ·
            refine ⟨8620206998464642191080777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5746804665643094794053851 8620206998464642191080777)
            ·
              refine ⟨6465155248848481643310583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8620206998464642191080777 6465155248848481643310583)
              ·
                refine ⟨9697732873272722464965875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6465155248848481643310583 9697732873272722464965875)
                ·
                  refine ⟨14546599309909083697448813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9697732873272722464965875 14546599309909083697448813)
                  ·
                    refine ⟨5454974741215906386543305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14546599309909083697448813 5454974741215906386543305)
                    ·
                      refine ⟨4091231055911929789907479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5454974741215906386543305 4091231055911929789907479)
                      ·
                        rfl

theorem cell23_7967644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_7967644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7967644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7967644 prefixEnd_7967644 := by exact prefixLift 7967644
  have htrace : WordTrace (prefixWord ++ tailWord_7967644) baseStart_7967644 baseEnd_7967644 := by
    simpa [prefixWord, tailWord_7967644, baseEnd_7967644] using wordTrace_append hprefix tailTrace_7967644
  have hstable : (prefixWord ++ tailWord_7967644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7967644).length < 2 ^ (prefixWord ++ tailWord_7967644).sum := by decide
  have hdescent : baseEnd_7967644 < baseStart_7967644 := by decide
  rcases family_descends (prefixWord ++ tailWord_7967644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7967669 : List Nat := [1, 3, 3, 2, 1, 1, 2, 1, 1, 1, 7]
def baseStart_7967669 : Nat := 118140960795 + 7967669 * 2 ^ 59
def prefixEnd_7967669 : Nat := 4983230072969 + 3 ^ 40 * 7967669 * 2
def baseEnd_7967669 : Nat := 4091243892928292192094863

theorem tailTrace_7967669 : CollatzResearch.WordTrace tailWord_7967669 prefixEnd_7967669 4091243892928292192094863 := by
  unfold tailWord_7967669
  simp only [CollatzResearch.WordTrace]
  refine ⟨290604762571503457373914061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193736508381002304915942707 290604762571503457373914061)
  ·
    refine ⟨108976785964313796515217773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290604762571503457373914061 108976785964313796515217773)
    ·
      refine ⟨40866294736617673693206665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108976785964313796515217773 40866294736617673693206665)
      ·
        refine ⟨30649721052463255269904999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40866294736617673693206665 30649721052463255269904999)
        ·
          refine ⟨45974581578694882904857499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30649721052463255269904999 45974581578694882904857499)
          ·
            refine ⟨68961872368042324357286249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45974581578694882904857499 68961872368042324357286249)
            ·
              refine ⟨51721404276031743267964687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68961872368042324357286249 51721404276031743267964687)
              ·
                refine ⟨77582106414047614901947031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51721404276031743267964687 77582106414047614901947031)
                ·
                  refine ⟨116373159621071422352920547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77582106414047614901947031 116373159621071422352920547)
                  ·
                    refine ⟨174559739431607133529380821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 116373159621071422352920547 174559739431607133529380821)
                    ·
                      refine ⟨4091243892928292192094863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 174559739431607133529380821 4091243892928292192094863)
                      ·
                        rfl

theorem cell23_7967669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_7967669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7967669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7967669 prefixEnd_7967669 := by exact prefixLift 7967669
  have htrace : WordTrace (prefixWord ++ tailWord_7967669) baseStart_7967669 baseEnd_7967669 := by
    simpa [prefixWord, tailWord_7967669, baseEnd_7967669] using wordTrace_append hprefix tailTrace_7967669
  have hstable : (prefixWord ++ tailWord_7967669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7967669).length < 2 ^ (prefixWord ++ tailWord_7967669).sum := by decide
  have hdescent : baseEnd_7967669 < baseStart_7967669 := by decide
  rcases family_descends (prefixWord ++ tailWord_7967669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7967679 : List Nat := [1, 1, 2, 2, 2, 1, 2, 1, 6, 1, 4]
def baseStart_7967679 : Nat := 118140960795 + 7967679 * 2 ^ 59
def prefixEnd_7967679 : Nat := 4983230072969 + 3 ^ 40 * 7967679 * 2
def baseEnd_7967679 : Nat := 4091249027734837152969817

theorem tailTrace_7967679 : CollatzResearch.WordTrace tailWord_7967679 prefixEnd_7967679 4091249027734837152969817 := by
  unfold tailWord_7967679
  simp only [CollatzResearch.WordTrace]
  refine ⟨290605127301467229081778091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193736751534311486054518727 290605127301467229081778091)
  ·
    refine ⟨435907690952200843622667137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290605127301467229081778091 435907690952200843622667137)
    ·
      refine ⟨326930768214150632717000353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 435907690952200843622667137 326930768214150632717000353)
      ·
        refine ⟨245198076160612974537750265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 326930768214150632717000353 245198076160612974537750265)
        ·
          refine ⟨183898557120459730903312699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245198076160612974537750265 183898557120459730903312699)
          ·
            refine ⟨275847835680689596354969049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183898557120459730903312699 275847835680689596354969049)
            ·
              refine ⟨206885876760517197266226787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 275847835680689596354969049 206885876760517197266226787)
              ·
                refine ⟨310328815140775795899340181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206885876760517197266226787 310328815140775795899340181)
                ·
                  refine ⟨14546663209723865432781571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 310328815140775795899340181 14546663209723865432781571)
                  ·
                    refine ⟨21819994814585798149172357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14546663209723865432781571 21819994814585798149172357)
                    ·
                      refine ⟨4091249027734837152969817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21819994814585798149172357 4091249027734837152969817)
                      ·
                        rfl

theorem cell23_7967679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 6, 1, 4].length) (baseStart_7967679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7967679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7967679 prefixEnd_7967679 := by exact prefixLift 7967679
  have htrace : WordTrace (prefixWord ++ tailWord_7967679) baseStart_7967679 baseEnd_7967679 := by
    simpa [prefixWord, tailWord_7967679, baseEnd_7967679] using wordTrace_append hprefix tailTrace_7967679
  have hstable : (prefixWord ++ tailWord_7967679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7967679).length < 2 ^ (prefixWord ++ tailWord_7967679).sum := by decide
  have hdescent : baseEnd_7967679 < baseStart_7967679 := by decide
  rcases family_descends (prefixWord ++ tailWord_7967679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7967783 : List Nat := [1, 1, 7, 1, 1, 1, 1, 2, 3, 5]
def baseStart_7967783 : Nat := 118140960795 + 7967783 * 2 ^ 59
def prefixEnd_7967783 : Nat := 4983230072969 + 3 ^ 40 * 7967783 * 2
def baseEnd_7967783 : Nat := 1363767476574301582023113

theorem tailTrace_7967783 : CollatzResearch.WordTrace tailWord_7967783 prefixEnd_7967783 1363767476574301582023113 := by
  unfold tailWord_7967783
  simp only [CollatzResearch.WordTrace]
  refine ⟨290608920493090454843564003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193739280328726969895709335 290608920493090454843564003)
  ·
    refine ⟨435913380739635682265346005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290608920493090454843564003 435913380739635682265346005)
    ·
      refine ⟨10216719861085211303094047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 435913380739635682265346005 10216719861085211303094047)
      ·
        refine ⟨15325079791627816954641071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10216719861085211303094047 15325079791627816954641071)
        ·
          refine ⟨22987619687441725431961607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15325079791627816954641071 22987619687441725431961607)
          ·
            refine ⟨34481429531162588147942411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22987619687441725431961607 34481429531162588147942411)
            ·
              refine ⟨51722144296743882221913617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34481429531162588147942411 51722144296743882221913617)
              ·
                refine ⟨38791608222557911666435213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51722144296743882221913617 38791608222557911666435213)
                ·
                  refine ⟨14546853083459216874913205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38791608222557911666435213 14546853083459216874913205)
                  ·
                    refine ⟨1363767476574301582023113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14546853083459216874913205 1363767476574301582023113)
                    ·
                      rfl

theorem cell23_7967783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_7967783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7967783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7967783 prefixEnd_7967783 := by exact prefixLift 7967783
  have htrace : WordTrace (prefixWord ++ tailWord_7967783) baseStart_7967783 baseEnd_7967783 := by
    simpa [prefixWord, tailWord_7967783, baseEnd_7967783] using wordTrace_append hprefix tailTrace_7967783
  have hstable : (prefixWord ++ tailWord_7967783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7967783).length < 2 ^ (prefixWord ++ tailWord_7967783).sum := by decide
  have hdescent : baseEnd_7967783 < baseStart_7967783 := by decide
  rcases family_descends (prefixWord ++ tailWord_7967783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7967814 : List Nat := [6, 1, 1, 1, 1, 2, 1, 5, 1, 1, 3]
def baseStart_7967814 : Nat := 118140960795 + 7967814 * 2 ^ 59
def prefixEnd_7967814 : Nat := 4983230072969 + 3 ^ 40 * 7967814 * 2
def baseEnd_7967814 : Nat := 4091318347623194124781697

theorem tailTrace_7967814 : CollatzResearch.WordTrace tailWord_7967814 prefixEnd_7967814 4091318347623194124781697 := by
  unfold tailWord_7967814
  simp only [CollatzResearch.WordTrace]
  refine ⟨9081564098624317098060703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 193740034103985431425294997 9081564098624317098060703)
  ·
    refine ⟨13622346147936475647091055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9081564098624317098060703 13622346147936475647091055)
    ·
      refine ⟨20433519221904713470636583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13622346147936475647091055 20433519221904713470636583)
      ·
        refine ⟨30650278832857070205954875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20433519221904713470636583 30650278832857070205954875)
        ·
          refine ⟨45975418249285605308932313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30650278832857070205954875 45975418249285605308932313)
          ·
            refine ⟨34481563686964203981699235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45975418249285605308932313 34481563686964203981699235)
            ·
              refine ⟨51722345530446305972548853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34481563686964203981699235 51722345530446305972548853)
              ·
                refine ⟨4848969893479341184926455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51722345530446305972548853 4848969893479341184926455)
                ·
                  refine ⟨7273454840219011777389683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4848969893479341184926455 7273454840219011777389683)
                  ·
                    refine ⟨10910182260328517666084525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7273454840219011777389683 10910182260328517666084525)
                    ·
                      refine ⟨4091318347623194124781697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10910182260328517666084525 4091318347623194124781697)
                      ·
                        rfl

theorem cell23_7967814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 5, 1, 1, 3].length) (baseStart_7967814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7967814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7967814 prefixEnd_7967814 := by exact prefixLift 7967814
  have htrace : WordTrace (prefixWord ++ tailWord_7967814) baseStart_7967814 baseEnd_7967814 := by
    simpa [prefixWord, tailWord_7967814, baseEnd_7967814] using wordTrace_append hprefix tailTrace_7967814
  have hstable : (prefixWord ++ tailWord_7967814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7967814).length < 2 ^ (prefixWord ++ tailWord_7967814).sum := by decide
  have hdescent : baseEnd_7967814 < baseStart_7967814 := by decide
  rcases family_descends (prefixWord ++ tailWord_7967814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7967816 : List Nat := [2, 1, 3, 1, 1, 1, 3, 4, 1, 2, 4]
def baseStart_7967816 : Nat := 118140960795 + 7967816 * 2 ^ 59
def prefixEnd_7967816 : Nat := 4983230072969 + 3 ^ 40 * 7967816 * 2
def baseEnd_7967816 : Nat := 4091319374584503116956687

theorem tailTrace_7967816 : CollatzResearch.WordTrace tailWord_7967816 prefixEnd_7967816 4091319374584503116956687 := by
  unfold tailWord_7967816
  simp only [CollatzResearch.WordTrace]
  refine ⟨145305062050985450739757651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193740082734647267653010201 145305062050985450739757651)
  ·
    refine ⟨217957593076478176109636477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145305062050985450739757651 217957593076478176109636477)
    ·
      refine ⟨81734097403679316041113679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217957593076478176109636477 81734097403679316041113679)
      ·
        refine ⟨122601146105518974061670519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81734097403679316041113679 122601146105518974061670519)
        ·
          refine ⟨183901719158278461092505779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122601146105518974061670519 183901719158278461092505779)
          ·
            refine ⟨275852578737417691638758669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183901719158278461092505779 275852578737417691638758669)
            ·
              refine ⟨103444717026531634364534501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 275852578737417691638758669 103444717026531634364534501)
              ·
                refine ⟨19395884442474681443350219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103444717026531634364534501 19395884442474681443350219)
                ·
                  refine ⟨29093826663712022165025329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19395884442474681443350219 29093826663712022165025329)
                  ·
                    refine ⟨21820369997784016623768997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29093826663712022165025329 21820369997784016623768997)
                    ·
                      refine ⟨4091319374584503116956687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21820369997784016623768997 4091319374584503116956687)
                      ·
                        rfl

theorem cell23_7967816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 4, 1, 2, 4].length) (baseStart_7967816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7967816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7967816 prefixEnd_7967816 := by exact prefixLift 7967816
  have htrace : WordTrace (prefixWord ++ tailWord_7967816) baseStart_7967816 baseEnd_7967816 := by
    simpa [prefixWord, tailWord_7967816, baseEnd_7967816] using wordTrace_append hprefix tailTrace_7967816
  have hstable : (prefixWord ++ tailWord_7967816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7967816).length < 2 ^ (prefixWord ++ tailWord_7967816).sum := by decide
  have hdescent : baseEnd_7967816 < baseStart_7967816 := by decide
  rcases family_descends (prefixWord ++ tailWord_7967816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7967826 : List Nat := [3, 2, 2, 1, 3, 2, 10]
def baseStart_7967826 : Nat := 118140960795 + 7967826 * 2 ^ 59
def prefixEnd_7967826 : Nat := 4983230072969 + 3 ^ 40 * 7967826 * 2
def baseEnd_7967826 : Nat := 50510179128284544170761

theorem tailTrace_7967826 : CollatzResearch.WordTrace tailWord_7967826 prefixEnd_7967826 50510179128284544170761 := by
  unfold tailWord_7967826
  simp only [CollatzResearch.WordTrace]
  refine ⟨72652622207983668296844833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193740325887956448791586221 72652622207983668296844833)
  ·
    refine ⟨54489466655987751222633625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72652622207983668296844833 54489466655987751222633625)
    ·
      refine ⟨40867099991990813416975219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54489466655987751222633625 40867099991990813416975219)
      ·
        refine ⟨61300649987986220125462829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40867099991990813416975219 61300649987986220125462829)
        ·
          refine ⟨22987743745494832547048561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61300649987986220125462829 22987743745494832547048561)
          ·
            refine ⟨17240807809121124410286421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22987743745494832547048561 17240807809121124410286421)
            ·
              refine ⟨50510179128284544170761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17240807809121124410286421 50510179128284544170761)
              ·
                rfl

theorem cell23_7967826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 10].length) (baseStart_7967826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7967826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7967826 prefixEnd_7967826 := by exact prefixLift 7967826
  have htrace : WordTrace (prefixWord ++ tailWord_7967826) baseStart_7967826 baseEnd_7967826 := by
    simpa [prefixWord, tailWord_7967826, baseEnd_7967826] using wordTrace_append hprefix tailTrace_7967826
  have hstable : (prefixWord ++ tailWord_7967826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7967826).length < 2 ^ (prefixWord ++ tailWord_7967826).sum := by decide
  have hdescent : baseEnd_7967826 < baseStart_7967826 := by decide
  rcases family_descends (prefixWord ++ tailWord_7967826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7967850 : List Nat := [3, 1, 3, 2, 2, 3, 1, 1, 1, 2, 4]
def baseStart_7967850 : Nat := 118140960795 + 7967850 * 2 ^ 59
def prefixEnd_7967850 : Nat := 4983230072969 + 3 ^ 40 * 7967850 * 2
def baseEnd_7967850 : Nat := 4091336832926755983931531

theorem tailTrace_7967850 : CollatzResearch.WordTrace tailWord_7967850 prefixEnd_7967850 4091336832926755983931531 := by
  unfold tailWord_7967850
  simp only [CollatzResearch.WordTrace]
  refine ⟨72652841045961931321563251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193740909455898483524168669 72652841045961931321563251)
  ·
    refine ⟨108979261568942896982344877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72652841045961931321563251 108979261568942896982344877)
    ·
      refine ⟨40867223088353586368379329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108979261568942896982344877 40867223088353586368379329)
      ·
        refine ⟨30650417316265189776284497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40867223088353586368379329 30650417316265189776284497)
        ·
          refine ⟨22987812987198892332213373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30650417316265189776284497 22987812987198892332213373)
          ·
            refine ⟨8620429870199584624580015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22987812987198892332213373 8620429870199584624580015)
            ·
              refine ⟨12930644805299376936870023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8620429870199584624580015 12930644805299376936870023)
              ·
                refine ⟨19395967207949065405305035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12930644805299376936870023 19395967207949065405305035)
                ·
                  refine ⟨29093950811923598107957553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19395967207949065405305035 29093950811923598107957553)
                  ·
                    refine ⟨21820463108942698580968165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29093950811923598107957553 21820463108942698580968165)
                    ·
                      refine ⟨4091336832926755983931531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21820463108942698580968165 4091336832926755983931531)
                      ·
                        rfl

theorem cell23_7967850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_7967850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7967850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7967850 prefixEnd_7967850 := by exact prefixLift 7967850
  have htrace : WordTrace (prefixWord ++ tailWord_7967850) baseStart_7967850 baseEnd_7967850 := by
    simpa [prefixWord, tailWord_7967850, baseEnd_7967850] using wordTrace_append hprefix tailTrace_7967850
  have hstable : (prefixWord ++ tailWord_7967850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7967850).length < 2 ^ (prefixWord ++ tailWord_7967850).sum := by decide
  have hdescent : baseEnd_7967850 < baseStart_7967850 := by decide
  rcases family_descends (prefixWord ++ tailWord_7967850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7967893 : List Nat := [1, 3, 2, 1, 1, 1, 2, 1, 5, 4, 2]
def baseStart_7967893 : Nat := 118140960795 + 7967893 * 2 ^ 59
def prefixEnd_7967893 : Nat := 4983230072969 + 3 ^ 40 * 7967893 * 2
def baseEnd_7967893 : Nat := 4091358912594899315693833

theorem tailTrace_7967893 : CollatzResearch.WordTrace tailWord_7967893 prefixEnd_7967893 4091358912594899315693833 := by
  unfold tailWord_7967893
  simp only [CollatzResearch.WordTrace]
  refine ⟨290612932522691943630068333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193741955015127962420045555 290612932522691943630068333)
  ·
    refine ⟨108979849696009478861275625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290612932522691943630068333 108979849696009478861275625)
    ·
      refine ⟨81734887272007109145956719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108979849696009478861275625 81734887272007109145956719)
      ·
        refine ⟨122602330908010663718935079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81734887272007109145956719 122602330908010663718935079)
        ·
          refine ⟨183903496362015995578402619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122602330908010663718935079 183903496362015995578402619)
          ·
            refine ⟨275855244543023993367603929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183903496362015995578402619 275855244543023993367603929)
            ·
              refine ⟨206891433407267995025702947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 275855244543023993367603929 206891433407267995025702947)
              ·
                refine ⟨310337150110901992538554421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206891433407267995025702947 310337150110901992538554421)
                ·
                  refine ⟨29094107822897061800489477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 310337150110901992538554421 29094107822897061800489477)
                  ·
                    refine ⟨5455145216793199087591777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29094107822897061800489477 5455145216793199087591777)
                    ·
                      refine ⟨4091358912594899315693833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5455145216793199087591777 4091358912594899315693833)
                      ·
                        rfl

theorem cell23_7967893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 5, 4, 2].length) (baseStart_7967893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7967893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7967893 prefixEnd_7967893 := by exact prefixLift 7967893
  have htrace : WordTrace (prefixWord ++ tailWord_7967893) baseStart_7967893 baseEnd_7967893 := by
    simpa [prefixWord, tailWord_7967893, baseEnd_7967893] using wordTrace_append hprefix tailTrace_7967893
  have hstable : (prefixWord ++ tailWord_7967893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7967893).length < 2 ^ (prefixWord ++ tailWord_7967893).sum := by decide
  have hdescent : baseEnd_7967893 < baseStart_7967893 := by decide
  rcases family_descends (prefixWord ++ tailWord_7967893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7967914 : List Nat := [3, 1, 5, 1, 1, 1, 3, 2, 1, 3, 2]
def baseStart_7967914 : Nat := 118140960795 + 7967914 * 2 ^ 59
def prefixEnd_7967914 : Nat := 4983230072969 + 3 ^ 40 * 7967914 * 2
def baseEnd_7967914 : Nat := 4091369695688643733531237

theorem tailTrace_7967914 : CollatzResearch.WordTrace tailWord_7967914 prefixEnd_7967914 4091369695688643733531237 := by
  unfold tailWord_7967914
  simp only [CollatzResearch.WordTrace]
  refine ⟨72653424613903966054145699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193742465637077242811055197 72653424613903966054145699)
  ·
    refine ⟨108980136920855949081218549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72653424613903966054145699 108980136920855949081218549)
    ·
      refine ⟨10216887836330245226364239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 108980136920855949081218549 10216887836330245226364239)
      ·
        refine ⟨15325331754495367839546359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10216887836330245226364239 15325331754495367839546359)
        ·
          refine ⟨22987997631743051759319539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15325331754495367839546359 22987997631743051759319539)
          ·
            refine ⟨34481996447614577638979309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22987997631743051759319539 34481996447614577638979309)
            ·
              refine ⟨12930748667855466614617241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34481996447614577638979309 12930748667855466614617241)
              ·
                refine ⟨9698061500891599960962931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12930748667855466614617241 9698061500891599960962931)
                ·
                  refine ⟨14547092251337399941444397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9698061500891599960962931 14547092251337399941444397)
                  ·
                    refine ⟨5455159594251524978041649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14547092251337399941444397 5455159594251524978041649)
                    ·
                      refine ⟨4091369695688643733531237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5455159594251524978041649 4091369695688643733531237)
                      ·
                        rfl

theorem cell23_7967914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_7967914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7967914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7967914 prefixEnd_7967914 := by exact prefixLift 7967914
  have htrace : WordTrace (prefixWord ++ tailWord_7967914) baseStart_7967914 baseEnd_7967914 := by
    simpa [prefixWord, tailWord_7967914, baseEnd_7967914] using wordTrace_append hprefix tailTrace_7967914
  have hstable : (prefixWord ++ tailWord_7967914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7967914).length < 2 ^ (prefixWord ++ tailWord_7967914).sum := by decide
  have hdescent : baseEnd_7967914 < baseStart_7967914 := by decide
  rcases family_descends (prefixWord ++ tailWord_7967914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7967960 : List Nat := [2, 1, 2, 2, 5, 1, 1, 1, 2, 3, 3]
def baseStart_7967960 : Nat := 118140960795 + 7967960 * 2 ^ 59
def prefixEnd_7967960 : Nat := 4983230072969 + 3 ^ 40 * 7967960 * 2
def baseEnd_7967960 : Nat := 4091393315798750553556025

theorem tailTrace_7967960 : CollatzResearch.WordTrace tailWord_7967960 prefixEnd_7967960 4091393315798750553556025 := by
  unfold tailWord_7967960
  simp only [CollatzResearch.WordTrace]
  refine ⟨145307688106724607036378667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193743584142299476048504889 145307688106724607036378667)
  ·
    refine ⟨217961532160086910554568001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145307688106724607036378667 217961532160086910554568001)
    ·
      refine ⟨163471149120065182915926001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217961532160086910554568001 163471149120065182915926001)
      ·
        refine ⟨122603361840048887186944501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163471149120065182915926001 122603361840048887186944501)
        ·
          refine ⟨11494065172504583173776047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 122603361840048887186944501 11494065172504583173776047)
          ·
            refine ⟨17241097758756874760664071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11494065172504583173776047 17241097758756874760664071)
            ·
              refine ⟨25861646638135312140996107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17241097758756874760664071 25861646638135312140996107)
              ·
                refine ⟨38792469957202968211494161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25861646638135312140996107 38792469957202968211494161)
                ·
                  refine ⟨29094352467902226158620621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38792469957202968211494161 29094352467902226158620621)
                  ·
                    refine ⟨10910382175463334809482733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29094352467902226158620621 10910382175463334809482733)
                    ·
                      refine ⟨4091393315798750553556025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10910382175463334809482733 4091393315798750553556025)
                      ·
                        rfl

theorem cell23_7967960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 1, 2, 3, 3].length) (baseStart_7967960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7967960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7967960 prefixEnd_7967960 := by exact prefixLift 7967960
  have htrace : WordTrace (prefixWord ++ tailWord_7967960) baseStart_7967960 baseEnd_7967960 := by
    simpa [prefixWord, tailWord_7967960, baseEnd_7967960] using wordTrace_append hprefix tailTrace_7967960
  have hstable : (prefixWord ++ tailWord_7967960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7967960).length < 2 ^ (prefixWord ++ tailWord_7967960).sum := by decide
  have hdescent : baseEnd_7967960 < baseStart_7967960 := by decide
  rcases family_descends (prefixWord ++ tailWord_7967960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7967980 : List Nat := [2, 2, 1, 1, 2, 6, 1, 1, 2, 5]
def baseStart_7967980 : Nat := 118140960795 + 7967980 * 2 ^ 59
def prefixEnd_7967980 : Nat := 4983230072969 + 3 ^ 40 * 7967980 * 2
def baseEnd_7967980 : Nat := 1363801195137280158435311

theorem tailTrace_7967980 : CollatzResearch.WordTrace tailWord_7967980 prefixEnd_7967980 1363801195137280158435311 := by
  unfold tailWord_7967980
  simp only [CollatzResearch.WordTrace]
  refine ⟨145308052836688378744242697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193744070448917838325656929 145308052836688378744242697)
  ·
    refine ⟨108981039627516284058182023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145308052836688378744242697 108981039627516284058182023)
    ·
      refine ⟨163471559441274426087273035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108981039627516284058182023 163471559441274426087273035)
      ·
        refine ⟨245207339161911639130909553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163471559441274426087273035 245207339161911639130909553)
        ·
          refine ⟨183905504371433729348182165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245207339161911639130909553 183905504371433729348182165)
          ·
            refine ⟨8620570517410956063196039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 183905504371433729348182165 8620570517410956063196039)
            ·
              refine ⟨12930855776116434094794059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8620570517410956063196039 12930855776116434094794059)
              ·
                refine ⟨19396283664174651142191089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12930855776116434094794059 19396283664174651142191089)
                ·
                  refine ⟨14547212748130988356643317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19396283664174651142191089 14547212748130988356643317)
                  ·
                    refine ⟨1363801195137280158435311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14547212748130988356643317 1363801195137280158435311)
                    ·
                      rfl

theorem cell23_7967980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 5].length) (baseStart_7967980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7967980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7967980 prefixEnd_7967980 := by exact prefixLift 7967980
  have htrace : WordTrace (prefixWord ++ tailWord_7967980) baseStart_7967980 baseEnd_7967980 := by
    simpa [prefixWord, tailWord_7967980, baseEnd_7967980] using wordTrace_append hprefix tailTrace_7967980
  have hstable : (prefixWord ++ tailWord_7967980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7967980).length < 2 ^ (prefixWord ++ tailWord_7967980).sum := by decide
  have hdescent : baseEnd_7967980 < baseStart_7967980 := by decide
  rcases family_descends (prefixWord ++ tailWord_7967980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7967993 : List Nat := [1, 2, 1, 3, 1, 1, 3, 2, 5, 4]
def baseStart_7967993 : Nat := 118140960795 + 7967993 * 2 ^ 59
def prefixEnd_7967993 : Nat := 4983230072969 + 3 ^ 40 * 7967993 * 2
def baseEnd_7967993 : Nat := 1363803420220116308147791

theorem tailTrace_7967993 : CollatzResearch.WordTrace tailWord_7967993 prefixEnd_7967993 1363803420220116308147791 := by
  unfold tailWord_7967993
  simp only [CollatzResearch.WordTrace]
  refine ⟨290616579822329660708708633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193744386548219773805805755 290616579822329660708708633)
  ·
    refine ⟨217962434866747245531531475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290616579822329660708708633 217962434866747245531531475)
    ·
      refine ⟨326943652300120868297297213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217962434866747245531531475 326943652300120868297297213)
      ·
        refine ⟨122603869612545325611486455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 326943652300120868297297213 122603869612545325611486455)
        ·
          refine ⟨183905804418817988417229683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122603869612545325611486455 183905804418817988417229683)
          ·
            refine ⟨275858706628226982625844525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183905804418817988417229683 275858706628226982625844525)
            ·
              refine ⟨103447014985585118484691697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 275858706628226982625844525 103447014985585118484691697)
              ·
                refine ⟨77585261239188838863518773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103447014985585118484691697 77585261239188838863518773)
                ·
                  refine ⟨7273618241173953643454885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77585261239188838863518773 7273618241173953643454885)
                  ·
                    refine ⟨1363803420220116308147791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7273618241173953643454885 1363803420220116308147791)
                    ·
                      rfl

theorem cell23_7967993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 5, 4].length) (baseStart_7967993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7967993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7967993 prefixEnd_7967993 := by exact prefixLift 7967993
  have htrace : WordTrace (prefixWord ++ tailWord_7967993) baseStart_7967993 baseEnd_7967993 := by
    simpa [prefixWord, tailWord_7967993, baseEnd_7967993] using wordTrace_append hprefix tailTrace_7967993
  have hstable : (prefixWord ++ tailWord_7967993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7967993).length < 2 ^ (prefixWord ++ tailWord_7967993).sum := by decide
  have hdescent : baseEnd_7967993 < baseStart_7967993 := by decide
  rcases family_descends (prefixWord ++ tailWord_7967993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7968016 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 9]
def baseStart_7968016 : Nat := 118140960795 + 7968016 * 2 ^ 59
def prefixEnd_7968016 : Nat := 4983230072969 + 3 ^ 40 * 7968016 * 2
def baseEnd_7968016 : Nat := 4091422070715402334455767

theorem tailTrace_7968016 : CollatzResearch.WordTrace tailWord_7968016 prefixEnd_7968016 4091422070715402334455767 := by
  unfold tailWord_7968016
  simp only [CollatzResearch.WordTrace]
  refine ⟨145308709350623167818397951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193744945800830890424530601 145308709350623167818397951)
  ·
    refine ⟨217963064025934751727596927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145308709350623167818397951 217963064025934751727596927)
    ·
      refine ⟨326944596038902127591395391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217963064025934751727596927 326944596038902127591395391)
      ·
        refine ⟨490416894058353191387093087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326944596038902127591395391 490416894058353191387093087)
        ·
          refine ⟨735625341087529787080639631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 490416894058353191387093087 735625341087529787080639631)
          ·
            refine ⟨1103438011631294680620959447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 735625341087529787080639631 1103438011631294680620959447)
            ·
              refine ⟨1655157017446942020931439171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1103438011631294680620959447 1655157017446942020931439171)
              ·
                refine ⟨2482735526170413031397158757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1655157017446942020931439171 2482735526170413031397158757)
                ·
                  refine ⟨465512911156952443386967267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2482735526170413031397158757 465512911156952443386967267)
                  ·
                    refine ⟨698269366735428665080450901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 465512911156952443386967267 698269366735428665080450901)
                    ·
                      refine ⟨4091422070715402334455767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 698269366735428665080450901 4091422070715402334455767)
                      ·
                        rfl

theorem cell23_7968016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 9].length) (baseStart_7968016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7968016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7968016 prefixEnd_7968016 := by exact prefixLift 7968016
  have htrace : WordTrace (prefixWord ++ tailWord_7968016) baseStart_7968016 baseEnd_7968016 := by
    simpa [prefixWord, tailWord_7968016, baseEnd_7968016] using wordTrace_append hprefix tailTrace_7968016
  have hstable : (prefixWord ++ tailWord_7968016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7968016).length < 2 ^ (prefixWord ++ tailWord_7968016).sum := by decide
  have hdescent : baseEnd_7968016 < baseStart_7968016 := by decide
  rcases family_descends (prefixWord ++ tailWord_7968016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7968033 : List Nat := [1, 2, 3, 2, 1, 1, 1, 1, 1, 7, 3]
def baseStart_7968033 : Nat := 118140960795 + 7968033 * 2 ^ 59
def prefixEnd_7968033 : Nat := 4983230072969 + 3 ^ 40 * 7968033 * 2
def baseEnd_7968033 : Nat := 4091430799886528767943189

theorem tailTrace_7968033 : CollatzResearch.WordTrace tailWord_7968033 prefixEnd_7968033 4091430799886528767943189 := by
  unfold tailWord_7968033
  simp only [CollatzResearch.WordTrace]
  refine ⟨290618038742184747540164753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193745359161456498360109835 290618038742184747540164753)
  ·
    refine ⟨217963529056638560655123565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290618038742184747540164753 217963529056638560655123565)
    ·
      refine ⟨81736323396239460245671337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217963529056638560655123565 81736323396239460245671337)
      ·
        refine ⟨61302242547179595184253503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81736323396239460245671337 61302242547179595184253503)
        ·
          refine ⟨91953363820769392776380255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61302242547179595184253503 91953363820769392776380255)
          ·
            refine ⟨137930045731154089164570383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91953363820769392776380255 137930045731154089164570383)
            ·
              refine ⟨206895068596731133746855575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137930045731154089164570383 206895068596731133746855575)
              ·
                refine ⟨310342602895096700620283363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206895068596731133746855575 310342602895096700620283363)
                ·
                  refine ⟨465513904342645050930425045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 310342602895096700620283363 465513904342645050930425045)
                  ·
                    refine ⟨10910482133030743381181837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 465513904342645050930425045 10910482133030743381181837)
                    ·
                      refine ⟨4091430799886528767943189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10910482133030743381181837 4091430799886528767943189)
                      ·
                        rfl

theorem cell23_7968033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 7, 3].length) (baseStart_7968033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7968033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7968033 prefixEnd_7968033 := by exact prefixLift 7968033
  have htrace : WordTrace (prefixWord ++ tailWord_7968033) baseStart_7968033 baseEnd_7968033 := by
    simpa [prefixWord, tailWord_7968033, baseEnd_7968033] using wordTrace_append hprefix tailTrace_7968033
  have hstable : (prefixWord ++ tailWord_7968033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7968033).length < 2 ^ (prefixWord ++ tailWord_7968033).sum := by decide
  have hdescent : baseEnd_7968033 < baseStart_7968033 := by decide
  rcases family_descends (prefixWord ++ tailWord_7968033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7968061 : List Nat := [1, 4, 1, 5, 2, 1, 1, 1, 3, 4]
def baseStart_7968061 : Nat := 118140960795 + 7968061 * 2 ^ 59
def prefixEnd_7968061 : Nat := 4983230072969 + 3 ^ 40 * 7968061 * 2
def baseEnd_7968061 : Nat := 1363815059114951552797687

theorem tailTrace_7968061 : CollatzResearch.WordTrace tailWord_7968061 prefixEnd_7968061 1363815059114951552797687 := by
  unfold tailWord_7968061
  simp only [CollatzResearch.WordTrace]
  refine ⟨290619059986083308322184037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193746039990722205548122691 290619059986083308322184037)
  ·
    refine ⟨54491073747390620310409507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 290619059986083308322184037 54491073747390620310409507)
    ·
      refine ⟨81736610621085930465614261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54491073747390620310409507 81736610621085930465614261)
      ·
        refine ⟨7662807245726805981151337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81736610621085930465614261 7662807245726805981151337)
        ·
          refine ⟨5747105434295104485863503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7662807245726805981151337 5747105434295104485863503)
          ·
            refine ⟨8620658151442656728795255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5747105434295104485863503 8620658151442656728795255)
            ·
              refine ⟨12930987227163985093192883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8620658151442656728795255 12930987227163985093192883)
              ·
                refine ⟨19396480840745977639789325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12930987227163985093192883 19396480840745977639789325)
                ·
                  refine ⟨7273680315279741614920997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19396480840745977639789325 7273680315279741614920997)
                  ·
                    refine ⟨1363815059114951552797687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7273680315279741614920997 1363815059114951552797687)
                    ·
                      rfl

theorem cell23_7968061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 1, 3, 4].length) (baseStart_7968061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7968061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7968061 prefixEnd_7968061 := by exact prefixLift 7968061
  have htrace : WordTrace (prefixWord ++ tailWord_7968061) baseStart_7968061 baseEnd_7968061 := by
    simpa [prefixWord, tailWord_7968061, baseEnd_7968061] using wordTrace_append hprefix tailTrace_7968061
  have hstable : (prefixWord ++ tailWord_7968061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7968061).length < 2 ^ (prefixWord ++ tailWord_7968061).sum := by decide
  have hdescent : baseEnd_7968061 < baseStart_7968061 := by decide
  rcases family_descends (prefixWord ++ tailWord_7968061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7968083 : List Nat := [1, 1, 1, 2, 1, 1, 6, 3, 1, 6]
def baseStart_7968083 : Nat := 118140960795 + 7968083 * 2 ^ 59
def prefixEnd_7968083 : Nat := 4983230072969 + 3 ^ 40 * 7968083 * 2
def baseEnd_7968083 : Nat := 1363818824639751190772653

theorem tailTrace_7968083 : CollatzResearch.WordTrace tailWord_7968083 prefixEnd_7968083 1363818824639751190772653 := by
  unfold tailWord_7968083
  simp only [CollatzResearch.WordTrace]
  refine ⟨290619862392003606079484903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193746574928002404052989935 290619862392003606079484903)
  ·
    refine ⟨435929793588005409119227355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290619862392003606079484903 435929793588005409119227355)
    ·
      refine ⟨653894690382008113678841033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435929793588005409119227355 653894690382008113678841033)
      ·
        refine ⟨490421017786506085259130775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 653894690382008113678841033 490421017786506085259130775)
        ·
          refine ⟨735631526679759127888696163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 490421017786506085259130775 735631526679759127888696163)
          ·
            refine ⟨1103447290019638691833044245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 735631526679759127888696163 1103447290019638691833044245)
            ·
              refine ⟨51724091719670563679673949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1103447290019638691833044245 51724091719670563679673949)
              ·
                refine ⟨19396534394876461379877731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51724091719670563679673949 19396534394876461379877731)
                ·
                  refine ⟨29094801592314692069816597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19396534394876461379877731 29094801592314692069816597)
                  ·
                    refine ⟨1363818824639751190772653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29094801592314692069816597 1363818824639751190772653)
                    ·
                      rfl

theorem cell23_7968083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 3, 1, 6].length) (baseStart_7968083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7968083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7968083 prefixEnd_7968083 := by exact prefixLift 7968083
  have htrace : WordTrace (prefixWord ++ tailWord_7968083) baseStart_7968083 baseEnd_7968083 := by
    simpa [prefixWord, tailWord_7968083, baseEnd_7968083] using wordTrace_append hprefix tailTrace_7968083
  have hstable : (prefixWord ++ tailWord_7968083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7968083).length < 2 ^ (prefixWord ++ tailWord_7968083).sum := by decide
  have hdescent : baseEnd_7968083 < baseStart_7968083 := by decide
  rcases family_descends (prefixWord ++ tailWord_7968083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7968087 : List Nat := [1, 1, 3, 2, 3, 4, 1, 2, 1, 5]
def baseStart_7968087 : Nat := 118140960795 + 7968087 * 2 ^ 59
def prefixEnd_7968087 : Nat := 4983230072969 + 3 ^ 40 * 7968087 * 2
def baseEnd_7968087 : Nat := 1363819509280623852222647

theorem tailTrace_7968087 : CollatzResearch.WordTrace tailWord_7968087 prefixEnd_7968087 1363819509280623852222647 := by
  unfold tailWord_7968087
  simp only [CollatzResearch.WordTrace]
  refine ⟨290620008283989114762630515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193746672189326076508420343 290620008283989114762630515)
  ·
    refine ⟨435930012425983672143945773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290620008283989114762630515 435930012425983672143945773)
    ·
      refine ⟨163473754659743877053979665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 435930012425983672143945773 163473754659743877053979665)
      ·
        refine ⟨122605315994807907790484749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163473754659743877053979665 122605315994807907790484749)
        ·
          refine ⟨45976993498052965421431781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122605315994807907790484749 45976993498052965421431781)
          ·
            refine ⟨8620686280884931016518459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45976993498052965421431781 8620686280884931016518459)
            ·
              refine ⟨12931029421327396524777689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8620686280884931016518459 12931029421327396524777689)
              ·
                refine ⟨9698272065995547393583267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12931029421327396524777689 9698272065995547393583267)
                ·
                  refine ⟨14547408098993321090374901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9698272065995547393583267 14547408098993321090374901)
                  ·
                    refine ⟨1363819509280623852222647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14547408098993321090374901 1363819509280623852222647)
                    ·
                      rfl

theorem cell23_7968087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 2, 1, 5].length) (baseStart_7968087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7968087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7968087 prefixEnd_7968087 := by exact prefixLift 7968087
  have htrace : WordTrace (prefixWord ++ tailWord_7968087) baseStart_7968087 baseEnd_7968087 := by
    simpa [prefixWord, tailWord_7968087, baseEnd_7968087] using wordTrace_append hprefix tailTrace_7968087
  have hstable : (prefixWord ++ tailWord_7968087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7968087).length < 2 ^ (prefixWord ++ tailWord_7968087).sum := by decide
  have hdescent : baseEnd_7968087 < baseStart_7968087 := by decide
  rcases family_descends (prefixWord ++ tailWord_7968087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7968090 : List Nat := [3, 1, 1, 2, 1, 2, 2, 1, 2, 6, 2]
def baseStart_7968090 : Nat := 118140960795 + 7968090 * 2 ^ 59
def prefixEnd_7968090 : Nat := 4983230072969 + 3 ^ 40 * 7968090 * 2
def baseEnd_7968090 : Nat := 4091460068283835044930427

theorem tailTrace_7968090 : CollatzResearch.WordTrace tailWord_7968090 prefixEnd_7968090 4091460068283835044930427 := by
  unfold tailWord_7968090
  simp only [CollatzResearch.WordTrace]
  refine ⟨72655029425744561568747431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193746745135318830849993149 72655029425744561568747431)
  ·
    refine ⟨108982544138616842353121147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72655029425744561568747431 108982544138616842353121147)
    ·
      refine ⟨163473816207925263529681721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108982544138616842353121147 163473816207925263529681721)
      ·
        refine ⟨122605362155943947647261291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163473816207925263529681721 122605362155943947647261291)
        ·
          refine ⟨183908043233915921470891937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122605362155943947647261291 183908043233915921470891937)
          ·
            refine ⟨137931032425436941103168953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183908043233915921470891937 137931032425436941103168953)
            ·
              refine ⟨103448274319077705827376715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137931032425436941103168953 103448274319077705827376715)
              ·
                refine ⟨155172411478616558741065073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103448274319077705827376715 155172411478616558741065073)
                ·
                  refine ⟨116379308608962419055798805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 155172411478616558741065073 116379308608962419055798805)
                  ·
                    refine ⟨5455280091045113393240569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 116379308608962419055798805 5455280091045113393240569)
                    ·
                      refine ⟨4091460068283835044930427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5455280091045113393240569 4091460068283835044930427)
                      ·
                        rfl

theorem cell23_7968090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 2, 6, 2].length) (baseStart_7968090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7968090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7968090 prefixEnd_7968090 := by exact prefixLift 7968090
  have htrace : WordTrace (prefixWord ++ tailWord_7968090) baseStart_7968090 baseEnd_7968090 := by
    simpa [prefixWord, tailWord_7968090, baseEnd_7968090] using wordTrace_append hprefix tailTrace_7968090
  have hstable : (prefixWord ++ tailWord_7968090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7968090).length < 2 ^ (prefixWord ++ tailWord_7968090).sum := by decide
  have hdescent : baseEnd_7968090 < baseStart_7968090 := by decide
  rcases family_descends (prefixWord ++ tailWord_7968090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7968100 : List Nat := [2, 3, 1, 1, 3, 3, 1, 2, 1, 6]
def baseStart_7968100 : Nat := 118140960795 + 7968100 * 2 ^ 59
def prefixEnd_7968100 : Nat := 4983230072969 + 3 ^ 40 * 7968100 * 2
def baseEnd_7968100 : Nat := 1363821734363460001935127

theorem tailTrace_7968100 : CollatzResearch.WordTrace tailWord_7968100 prefixEnd_7968100 1363821734363460001935127 := by
  unfold tailWord_7968100
  simp only [CollatzResearch.WordTrace]
  refine ⟨145310241216471008991426877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193746988288628011988569169 145310241216471008991426877)
  ·
    refine ⟨54491340456176628371785079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145310241216471008991426877 54491340456176628371785079)
    ·
      refine ⟨81737010684264942557677619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54491340456176628371785079 81737010684264942557677619)
      ·
        refine ⟨122605516026397413836516429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81737010684264942557677619 122605516026397413836516429)
        ·
          refine ⟨45977068509899030188693661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122605516026397413836516429 45977068509899030188693661)
          ·
            refine ⟨17241400691212136320760123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45977068509899030188693661 17241400691212136320760123)
            ·
              refine ⟨25862101036818204481140185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17241400691212136320760123 25862101036818204481140185)
              ·
                refine ⟨19396575777613653360855139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25862101036818204481140185 19396575777613653360855139)
                ·
                  refine ⟨29094863666420480041282709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19396575777613653360855139 29094863666420480041282709)
                  ·
                    refine ⟨1363821734363460001935127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29094863666420480041282709 1363821734363460001935127)
                    ·
                      rfl

theorem cell23_7968100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 2, 1, 6].length) (baseStart_7968100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7968100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7968100 prefixEnd_7968100 := by exact prefixLift 7968100
  have htrace : WordTrace (prefixWord ++ tailWord_7968100) baseStart_7968100 baseEnd_7968100 := by
    simpa [prefixWord, tailWord_7968100, baseEnd_7968100] using wordTrace_append hprefix tailTrace_7968100
  have hstable : (prefixWord ++ tailWord_7968100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7968100).length < 2 ^ (prefixWord ++ tailWord_7968100).sum := by decide
  have hdescent : baseEnd_7968100 < baseStart_7968100 := by decide
  rcases family_descends (prefixWord ++ tailWord_7968100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7968104 : List Nat := [2, 1, 4, 2, 3, 1, 3, 1, 1, 5]
def baseStart_7968104 : Nat := 118140960795 + 7968104 * 2 ^ 59
def prefixEnd_7968104 : Nat := 4983230072969 + 3 ^ 40 * 7968104 * 2
def baseEnd_7968104 : Nat := 1363822419004332663385121

theorem tailTrace_7968104 : CollatzResearch.WordTrace tailWord_7968104 prefixEnd_7968104 1363822419004332663385121 := by
  unfold tailWord_7968104
  simp only [CollatzResearch.WordTrace]
  refine ⟨145310314162463763332999683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193747085549951684443999577 145310314162463763332999683)
  ·
    refine ⟨217965471243695644999499525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145310314162463763332999683 217965471243695644999499525)
    ·
      refine ⟨40868525858192933437406161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 217965471243695644999499525 40868525858192933437406161)
      ·
        refine ⟨30651394393644700078054621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40868525858192933437406161 30651394393644700078054621)
        ·
          refine ⟨11494272897616762529270483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30651394393644700078054621 11494272897616762529270483)
          ·
            refine ⟨17241409346425143793905725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11494272897616762529270483 17241409346425143793905725)
            ·
              refine ⟨6465528504909428922714647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17241409346425143793905725 6465528504909428922714647)
              ·
                refine ⟨9698292757364143384071971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6465528504909428922714647 9698292757364143384071971)
                ·
                  refine ⟨14547439136046215076107957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9698292757364143384071971 14547439136046215076107957)
                  ·
                    refine ⟨1363822419004332663385121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14547439136046215076107957 1363822419004332663385121)
                    ·
                      rfl

theorem cell23_7968104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 3, 1, 1, 5].length) (baseStart_7968104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7968104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7968104 prefixEnd_7968104 := by exact prefixLift 7968104
  have htrace : WordTrace (prefixWord ++ tailWord_7968104) baseStart_7968104 baseEnd_7968104 := by
    simpa [prefixWord, tailWord_7968104, baseEnd_7968104] using wordTrace_append hprefix tailTrace_7968104
  have hstable : (prefixWord ++ tailWord_7968104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7968104).length < 2 ^ (prefixWord ++ tailWord_7968104).sum := by decide
  have hdescent : baseEnd_7968104 < baseStart_7968104 := by decide
  rcases family_descends (prefixWord ++ tailWord_7968104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7968133 : List Nat := [1, 3, 1, 1, 3, 1, 2, 1, 2, 2, 6]
def baseStart_7968133 : Nat := 118140960795 + 7968133 * 2 ^ 59
def prefixEnd_7968133 : Nat := 4983230072969 + 3 ^ 40 * 7968133 * 2
def baseEnd_7968133 : Nat := 4091482147951978376692729

theorem tailTrace_7968133 : CollatzResearch.WordTrace tailWord_7968133 prefixEnd_7968133 4091482147951978376692729 := by
  unfold tailWord_7968133
  simp only [CollatzResearch.WordTrace]
  refine ⟨290621686041822464618805053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193747790694548309745870035 290621686041822464618805053)
  ·
    refine ⟨108983132265683424232051895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290621686041822464618805053 108983132265683424232051895)
    ·
      refine ⟨163474698398525136348077843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108983132265683424232051895 163474698398525136348077843)
      ·
        refine ⟨245212047597787704522116765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163474698398525136348077843 245212047597787704522116765)
        ·
          refine ⟨91954517849170389195793787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 245212047597787704522116765 91954517849170389195793787)
          ·
            refine ⟨137931776773755583793690681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91954517849170389195793787 137931776773755583793690681)
            ·
              refine ⟨103448832580316687845268011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137931776773755583793690681 103448832580316687845268011)
              ·
                refine ⟨155173248870475031767902017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103448832580316687845268011 155173248870475031767902017)
                ·
                  refine ⟨116379936652856273825926513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 155173248870475031767902017 116379936652856273825926513)
                  ·
                    refine ⟨87284952489642205369444885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 116379936652856273825926513 87284952489642205369444885)
                    ·
                      refine ⟨4091482147951978376692729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87284952489642205369444885 4091482147951978376692729)
                      ·
                        rfl

theorem cell23_7968133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 2, 6].length) (baseStart_7968133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7968133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7968133 prefixEnd_7968133 := by exact prefixLift 7968133
  have htrace : WordTrace (prefixWord ++ tailWord_7968133) baseStart_7968133 baseEnd_7968133 := by
    simpa [prefixWord, tailWord_7968133, baseEnd_7968133] using wordTrace_append hprefix tailTrace_7968133
  have hstable : (prefixWord ++ tailWord_7968133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7968133).length < 2 ^ (prefixWord ++ tailWord_7968133).sum := by decide
  have hdescent : baseEnd_7968133 < baseStart_7968133 := by decide
  rcases family_descends (prefixWord ++ tailWord_7968133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7968137 : List Nat := [1, 2, 1, 1, 7, 1, 2, 1, 1, 2, 4]
def baseStart_7968137 : Nat := 118140960795 + 7968137 * 2 ^ 59
def prefixEnd_7968137 : Nat := 4983230072969 + 3 ^ 40 * 7968137 * 2
def baseEnd_7968137 : Nat := 4091484201874596361042711

theorem tailTrace_7968137 : CollatzResearch.WordTrace tailWord_7968137 prefixEnd_7968137 4091484201874596361042711 := by
  unfold tailWord_7968137
  simp only [CollatzResearch.WordTrace]
  refine ⟨290621831933807973301950665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193747887955871982201300443 290621831933807973301950665)
  ·
    refine ⟨217966373950355979976462999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290621831933807973301950665 217966373950355979976462999)
    ·
      refine ⟨326949560925533969964694499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217966373950355979976462999 326949560925533969964694499)
      ·
        refine ⟨490424341388300954947041749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326949560925533969964694499 490424341388300954947041749)
        ·
          refine ⟨11494320501288303631571291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 490424341388300954947041749 11494320501288303631571291)
          ·
            refine ⟨17241480751932455447356937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11494320501288303631571291 17241480751932455447356937)
            ·
              refine ⟨12931110563949341585517703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17241480751932455447356937 12931110563949341585517703)
              ·
                refine ⟨19396665845924012378276555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12931110563949341585517703 19396665845924012378276555)
                ·
                  refine ⟨29094998768886018567414833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19396665845924012378276555 29094998768886018567414833)
                  ·
                    refine ⟨21821249076664513925561125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29094998768886018567414833 21821249076664513925561125)
                    ·
                      refine ⟨4091484201874596361042711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21821249076664513925561125 4091484201874596361042711)
                      ·
                        rfl

theorem cell23_7968137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 1, 1, 2, 4].length) (baseStart_7968137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7968137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7968137 prefixEnd_7968137 := by exact prefixLift 7968137
  have htrace : WordTrace (prefixWord ++ tailWord_7968137) baseStart_7968137 baseEnd_7968137 := by
    simpa [prefixWord, tailWord_7968137, baseEnd_7968137] using wordTrace_append hprefix tailTrace_7968137
  have hstable : (prefixWord ++ tailWord_7968137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7968137).length < 2 ^ (prefixWord ++ tailWord_7968137).sum := by decide
  have hdescent : baseEnd_7968137 < baseStart_7968137 := by decide
  rcases family_descends (prefixWord ++ tailWord_7968137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7968157 : List Nat := [1, 4, 2, 1, 3, 1, 2, 2, 1, 3, 3]
def baseStart_7968157 : Nat := 118140960795 + 7968157 * 2 ^ 59
def prefixEnd_7968157 : Nat := 4983230072969 + 3 ^ 40 * 7968157 * 2
def baseEnd_7968157 : Nat := 4091494471487686282792619

theorem tailTrace_7968157 : CollatzResearch.WordTrace tailWord_7968157 prefixEnd_7968157 4091494471487686282792619 := by
  unfold tailWord_7968157
  simp only [CollatzResearch.WordTrace]
  refine ⟨290622561393735516717678725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193748374262490344478452483 290622561393735516717678725)
  ·
    refine ⟨54491730261325409384564761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 290622561393735516717678725 54491730261325409384564761)
    ·
      refine ⟨40868797695994057038423571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54491730261325409384564761 40868797695994057038423571)
      ·
        refine ⟨61303196543991085557635357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40868797695994057038423571 61303196543991085557635357)
        ·
          refine ⟨22988698703996657084113259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61303196543991085557635357 22988698703996657084113259)
          ·
            refine ⟨34483048055994985626169889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22988698703996657084113259 34483048055994985626169889)
            ·
              refine ⟨25862286041996239219627417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34483048055994985626169889 25862286041996239219627417)
              ·
                refine ⟨19396714531497179414720563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25862286041996239219627417 19396714531497179414720563)
                ·
                  refine ⟨29095071797245769122080845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19396714531497179414720563 29095071797245769122080845)
                  ·
                    refine ⟨10910651923967163420780317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29095071797245769122080845 10910651923967163420780317)
                    ·
                      refine ⟨4091494471487686282792619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10910651923967163420780317 4091494471487686282792619)
                      ·
                        rfl

theorem cell23_7968157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 2, 1, 3, 3].length) (baseStart_7968157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7968157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7968157 prefixEnd_7968157 := by exact prefixLift 7968157
  have htrace : WordTrace (prefixWord ++ tailWord_7968157) baseStart_7968157 baseEnd_7968157 := by
    simpa [prefixWord, tailWord_7968157, baseEnd_7968157] using wordTrace_append hprefix tailTrace_7968157
  have hstable : (prefixWord ++ tailWord_7968157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7968157).length < 2 ^ (prefixWord ++ tailWord_7968157).sum := by decide
  have hdescent : baseEnd_7968157 < baseStart_7968157 := by decide
  rcases family_descends (prefixWord ++ tailWord_7968157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7968158 : List Nat := [4, 3, 1, 2, 2, 2, 2, 1, 1, 1, 4]
def baseStart_7968158 : Nat := 118140960795 + 7968158 * 2 ^ 59
def prefixEnd_7968158 : Nat := 4983230072969 + 3 ^ 40 * 7968158 * 2
def baseEnd_7968158 : Nat := 4091494984968340778880115

theorem tailTrace_7968158 : CollatzResearch.WordTrace tailWord_7968158 prefixEnd_7968158 4091494984968340778880115 := by
  unfold tailWord_7968158
  simp only [CollatzResearch.WordTrace]
  refine ⟨36327824733341486736058141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193748398577821262592310085 36327824733341486736058141)
  ·
    refine ⟨13622934275003057526021803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36327824733341486736058141 13622934275003057526021803)
    ·
      refine ⟨20434401412504586289032705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13622934275003057526021803 20434401412504586289032705)
      ·
        refine ⟨15325801059378439716774529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20434401412504586289032705 15325801059378439716774529)
        ·
          refine ⟨11494350794533829787580897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15325801059378439716774529 11494350794533829787580897)
          ·
            refine ⟨8620763095900372340685673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11494350794533829787580897 8620763095900372340685673)
            ·
              refine ⟨6465572321925279255514255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8620763095900372340685673 6465572321925279255514255)
              ·
                refine ⟨9698358482887918883271383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6465572321925279255514255 9698358482887918883271383)
                ·
                  refine ⟨14547537724331878324907075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9698358482887918883271383 14547537724331878324907075)
                  ·
                    refine ⟨21821306586497817487360613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14547537724331878324907075 21821306586497817487360613)
                    ·
                      refine ⟨4091494984968340778880115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21821306586497817487360613 4091494984968340778880115)
                      ·
                        rfl

theorem cell23_7968158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_7968158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7968158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7968158 prefixEnd_7968158 := by exact prefixLift 7968158
  have htrace : WordTrace (prefixWord ++ tailWord_7968158) baseStart_7968158 baseEnd_7968158 := by
    simpa [prefixWord, tailWord_7968158, baseEnd_7968158] using wordTrace_append hprefix tailTrace_7968158
  have hstable : (prefixWord ++ tailWord_7968158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7968158).length < 2 ^ (prefixWord ++ tailWord_7968158).sum := by decide
  have hdescent : baseEnd_7968158 < baseStart_7968158 := by decide
  rcases family_descends (prefixWord ++ tailWord_7968158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7968168 : List Nat := [2, 1, 6, 1, 3, 1, 1, 2, 2, 4]
def baseStart_7968168 : Nat := 118140960795 + 7968168 * 2 ^ 59
def prefixEnd_7968168 : Nat := 4983230072969 + 3 ^ 40 * 7968168 * 2
def baseEnd_7968168 : Nat := 1363833373258295246585023

theorem tailTrace_7968168 : CollatzResearch.WordTrace tailWord_7968168 prefixEnd_7968168 1363833373258295246585023 := by
  unfold tailWord_7968168
  simp only [CollatzResearch.WordTrace]
  refine ⟨145311481298347832798164579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193748641731130443730886105 145311481298347832798164579)
  ·
    refine ⟨217967221947521749197246869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145311481298347832798164579 217967221947521749197246869)
    ·
      refine ⟨10217213528790081993620947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 217967221947521749197246869 10217213528790081993620947)
      ·
        refine ⟨15325820293185122990431421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10217213528790081993620947 15325820293185122990431421)
        ·
          refine ⟨5747182609944421121411783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15325820293185122990431421 5747182609944421121411783)
          ·
            refine ⟨8620773914916631682117675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5747182609944421121411783 8620773914916631682117675)
            ·
              refine ⟨12931160872374947523176513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8620773914916631682117675 12931160872374947523176513)
              ·
                refine ⟨9698370654281210642382385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12931160872374947523176513 9698370654281210642382385)
                ·
                  refine ⟨7273777990710907981786789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9698370654281210642382385 7273777990710907981786789)
                  ·
                    refine ⟨1363833373258295246585023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7273777990710907981786789 1363833373258295246585023)
                    ·
                      rfl

theorem cell23_7968168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_7968168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7968168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7968168 prefixEnd_7968168 := by exact prefixLift 7968168
  have htrace : WordTrace (prefixWord ++ tailWord_7968168) baseStart_7968168 baseEnd_7968168 := by
    simpa [prefixWord, tailWord_7968168, baseEnd_7968168] using wordTrace_append hprefix tailTrace_7968168
  have hstable : (prefixWord ++ tailWord_7968168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7968168).length < 2 ^ (prefixWord ++ tailWord_7968168).sum := by decide
  have hdescent : baseEnd_7968168 < baseStart_7968168 := by decide
  rcases family_descends (prefixWord ++ tailWord_7968168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7968200 : List Nat := [2, 1, 3, 1, 3, 1, 2, 2, 2, 1, 5]
def baseStart_7968200 : Nat := 118140960795 + 7968200 * 2 ^ 59
def prefixEnd_7968200 : Nat := 4983230072969 + 3 ^ 40 * 7968200 * 2
def baseEnd_7968200 : Nat := 4091516551155829614554921

theorem tailTrace_7968200 : CollatzResearch.WordTrace tailWord_7968200 prefixEnd_7968200 4091516551155829614554921 := by
  unfold tailWord_7968200
  simp only [CollatzResearch.WordTrace]
  refine ⟨145312064866289867530747027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193749419821719823374329369 145312064866289867530747027)
  ·
    refine ⟨217968097299434801296120541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145312064866289867530747027 217968097299434801296120541)
    ·
      refine ⟨81738036487288050486045203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217968097299434801296120541 81738036487288050486045203)
      ·
        refine ⟨122607054730932075729067805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81738036487288050486045203 122607054730932075729067805)
        ·
          refine ⟨45977645524099528398400427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122607054730932075729067805 45977645524099528398400427)
          ·
            refine ⟨68966468286149292597600641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45977645524099528398400427 68966468286149292597600641)
            ·
              refine ⟨51724851214611969448200481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68966468286149292597600641 51724851214611969448200481)
              ·
                refine ⟨38793638410958977086150361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51724851214611969448200481 38793638410958977086150361)
                ·
                  refine ⟨29095228808219232814612771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38793638410958977086150361 29095228808219232814612771)
                  ·
                    refine ⟨43642843212328849221919157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29095228808219232814612771 43642843212328849221919157)
                    ·
                      refine ⟨4091516551155829614554921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43642843212328849221919157 4091516551155829614554921)
                      ·
                        rfl

theorem cell23_7968200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 2, 2, 1, 5].length) (baseStart_7968200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7968200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7968200 prefixEnd_7968200 := by exact prefixLift 7968200
  have htrace : WordTrace (prefixWord ++ tailWord_7968200) baseStart_7968200 baseEnd_7968200 := by
    simpa [prefixWord, tailWord_7968200, baseEnd_7968200] using wordTrace_append hprefix tailTrace_7968200
  have hstable : (prefixWord ++ tailWord_7968200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7968200).length < 2 ^ (prefixWord ++ tailWord_7968200).sum := by decide
  have hdescent : baseEnd_7968200 < baseStart_7968200 := by decide
  rcases family_descends (prefixWord ++ tailWord_7968200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7968248 : List Nat := [2, 1, 2, 1, 1, 7, 2, 1, 2, 2, 2]
def baseStart_7968248 : Nat := 118140960795 + 7968248 * 2 ^ 59
def prefixEnd_7968248 : Nat := 4983230072969 + 3 ^ 40 * 7968248 * 2
def baseEnd_7968248 : Nat := 4091541198227245426754701

theorem tailTrace_7968248 : CollatzResearch.WordTrace tailWord_7968248 prefixEnd_7968248 4091541198227245426754701 := by
  unfold tailWord_7968248
  simp only [CollatzResearch.WordTrace]
  refine ⟨145312940218202919629620699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193750586957603892839494265 145312940218202919629620699)
  ·
    refine ⟨217969410327304379444431049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145312940218202919629620699 217969410327304379444431049)
    ·
      refine ⟨163477057745478284583323287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217969410327304379444431049 163477057745478284583323287)
      ·
        refine ⟨245215586618217426874984931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163477057745478284583323287 245215586618217426874984931)
        ·
          refine ⟨367823379927326140312477397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245215586618217426874984931 367823379927326140312477397)
          ·
            refine ⟨8620860467046706413573689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 367823379927326140312477397 8620860467046706413573689)
            ·
              refine ⟨6465645350285029810180267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8620860467046706413573689 6465645350285029810180267)
              ·
                refine ⟨9698468025427544715270401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6465645350285029810180267 9698468025427544715270401)
                ·
                  refine ⟨7273851019070658536452801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9698468025427544715270401 7273851019070658536452801)
                  ·
                    refine ⟨5455388264302993902339601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7273851019070658536452801 5455388264302993902339601)
                    ·
                      refine ⟨4091541198227245426754701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5455388264302993902339601 4091541198227245426754701)
                      ·
                        rfl

theorem cell23_7968248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 2, 1, 2, 2, 2].length) (baseStart_7968248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7968248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7968248 prefixEnd_7968248 := by exact prefixLift 7968248
  have htrace : WordTrace (prefixWord ++ tailWord_7968248) baseStart_7968248 baseEnd_7968248 := by
    simpa [prefixWord, tailWord_7968248, baseEnd_7968248] using wordTrace_append hprefix tailTrace_7968248
  have hstable : (prefixWord ++ tailWord_7968248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7968248).length < 2 ^ (prefixWord ++ tailWord_7968248).sum := by decide
  have hdescent : baseEnd_7968248 < baseStart_7968248 := by decide
  rcases family_descends (prefixWord ++ tailWord_7968248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7968250 : List Nat := [3, 1, 1, 1, 1, 2, 3, 2, 4, 5]
def baseStart_7968250 : Nat := 118140960795 + 7968250 * 2 ^ 59
def prefixEnd_7968250 : Nat := 4983230072969 + 3 ^ 40 * 7968250 * 2
def baseEnd_7968250 : Nat := 1363847408396184806309897

theorem tailTrace_7968250 : CollatzResearch.WordTrace tailWord_7968250 prefixEnd_7968250 1363847408396184806309897 := by
  unfold tailWord_7968250
  simp only [CollatzResearch.WordTrace]
  refine ⟨72656488345599648400203551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193750635588265729067209469 72656488345599648400203551)
  ·
    refine ⟨108984732518399472600305327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72656488345599648400203551 108984732518399472600305327)
    ·
      refine ⟨163477098777599208900457991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108984732518399472600305327 163477098777599208900457991)
      ·
        refine ⟨245215648166398813350686987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163477098777599208900457991 245215648166398813350686987)
        ·
          refine ⟨367823472249598220026030481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245215648166398813350686987 367823472249598220026030481)
          ·
            refine ⟨275867604187198665019522861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 367823472249598220026030481 275867604187198665019522861)
            ·
              refine ⟨103450351570199499382321073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 275867604187198665019522861 103450351570199499382321073)
              ·
                refine ⟨77587763677649624536740805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103450351570199499382321073 77587763677649624536740805)
                ·
                  refine ⟨14547705689559304600638901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77587763677649624536740805 14547705689559304600638901)
                  ·
                    refine ⟨1363847408396184806309897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14547705689559304600638901 1363847408396184806309897)
                    ·
                      rfl

theorem cell23_7968250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 4, 5].length) (baseStart_7968250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7968250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7968250 prefixEnd_7968250 := by exact prefixLift 7968250
  have htrace : WordTrace (prefixWord ++ tailWord_7968250) baseStart_7968250 baseEnd_7968250 := by
    simpa [prefixWord, tailWord_7968250, baseEnd_7968250] using wordTrace_append hprefix tailTrace_7968250
  have hstable : (prefixWord ++ tailWord_7968250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7968250).length < 2 ^ (prefixWord ++ tailWord_7968250).sum := by decide
  have hdescent : baseEnd_7968250 < baseStart_7968250 := by decide
  rcases family_descends (prefixWord ++ tailWord_7968250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7968287 : List Nat := [1, 1, 2, 4, 1, 1, 4, 2, 2, 1, 4]
def baseStart_7968287 : Nat := 118140960795 + 7968287 * 2 ^ 59
def prefixEnd_7968287 : Nat := 4983230072969 + 3 ^ 40 * 7968287 * 2
def baseEnd_7968287 : Nat := 4091561223972770774167021

theorem tailTrace_7968287 : CollatzResearch.WordTrace tailWord_7968287 prefixEnd_7968287 4091561223972770774167021 := by
  unfold tailWord_7968287
  simp only [CollatzResearch.WordTrace]
  refine ⟨290627302883264548919911115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193751535255509699279940743 290627302883264548919911115)
  ·
    refine ⟨435940954324896823379866673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290627302883264548919911115 435940954324896823379866673)
    ·
      refine ⟨326955715743672617534900005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 435940954324896823379866673 326955715743672617534900005)
      ·
        refine ⟨61304196701938615787793751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 326955715743672617534900005 61304196701938615787793751)
        ·
          refine ⟨91956295052907923681690627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61304196701938615787793751 91956295052907923681690627)
          ·
            refine ⟨137934442579361885522535941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91956295052907923681690627 137934442579361885522535941)
            ·
              refine ⟨25862707983630353535475489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137934442579361885522535941 25862707983630353535475489)
              ·
                refine ⟨19397030987722765151606617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25862707983630353535475489 19397030987722765151606617)
                ·
                  refine ⟨14547773240792073863704963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19397030987722765151606617 14547773240792073863704963)
                  ·
                    refine ⟨21821659861188110795557445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14547773240792073863704963 21821659861188110795557445)
                    ·
                      refine ⟨4091561223972770774167021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21821659861188110795557445 4091561223972770774167021)
                      ·
                        rfl

theorem cell23_7968287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_7968287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7968287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7968287 prefixEnd_7968287 := by exact prefixLift 7968287
  have htrace : WordTrace (prefixWord ++ tailWord_7968287) baseStart_7968287 baseEnd_7968287 := by
    simpa [prefixWord, tailWord_7968287, baseEnd_7968287] using wordTrace_append hprefix tailTrace_7968287
  have hstable : (prefixWord ++ tailWord_7968287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7968287).length < 2 ^ (prefixWord ++ tailWord_7968287).sum := by decide
  have hdescent : baseEnd_7968287 < baseStart_7968287 := by decide
  rcases family_descends (prefixWord ++ tailWord_7968287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7968300 : List Nat := [2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 4]
def baseStart_7968300 : Nat := 118140960795 + 7968300 * 2 ^ 59
def prefixEnd_7968300 : Nat := 4983230072969 + 3 ^ 40 * 7968300 * 2
def baseEnd_7968300 : Nat := 4091567899221279223304461

theorem tailTrace_7968300 : CollatzResearch.WordTrace tailWord_7968300 prefixEnd_7968300 4091567899221279223304461 := by
  unfold tailWord_7968300
  simp only [CollatzResearch.WordTrace]
  refine ⟨145313888516108726070067177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193751851354811634760089569 145313888516108726070067177)
  ·
    refine ⟨108985416387081544552550383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145313888516108726070067177 108985416387081544552550383)
    ·
      refine ⟨163478124580622316828825575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108985416387081544552550383 163478124580622316828825575)
      ·
        refine ⟨245217186870933475243238363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163478124580622316828825575 245217186870933475243238363)
        ·
          refine ⟨367825780306400212864857545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245217186870933475243238363 367825780306400212864857545)
          ·
            refine ⟨275869335229800159648643159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 367825780306400212864857545 275869335229800159648643159)
            ·
              refine ⟨413804002844700239472964739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275869335229800159648643159 413804002844700239472964739)
              ·
                refine ⟨620706004267050359209447109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 413804002844700239472964739 620706004267050359209447109)
                ·
                  refine ⟨116382375800071942351771333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 620706004267050359209447109 116382375800071942351771333)
                  ·
                    refine ⟨21821695462513489190957125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 116382375800071942351771333 21821695462513489190957125)
                    ·
                      refine ⟨4091567899221279223304461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21821695462513489190957125 4091567899221279223304461)
                      ·
                        rfl

theorem cell23_7968300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 4].length) (baseStart_7968300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7968300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7968300 prefixEnd_7968300 := by exact prefixLift 7968300
  have htrace : WordTrace (prefixWord ++ tailWord_7968300) baseStart_7968300 baseEnd_7968300 := by
    simpa [prefixWord, tailWord_7968300, baseEnd_7968300] using wordTrace_append hprefix tailTrace_7968300
  have hstable : (prefixWord ++ tailWord_7968300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7968300).length < 2 ^ (prefixWord ++ tailWord_7968300).sum := by decide
  have hdescent : baseEnd_7968300 < baseStart_7968300 := by decide
  rcases family_descends (prefixWord ++ tailWord_7968300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7968407 : List Nat := [1, 1, 3, 3, 2, 2, 1, 2, 1, 1, 6]
def baseStart_7968407 : Nat := 118140960795 + 7968407 * 2 ^ 59
def prefixEnd_7968407 : Nat := 4983230072969 + 3 ^ 40 * 7968407 * 2
def baseEnd_7968407 : Nat := 4091622841651310304666469

theorem tailTrace_7968407 : CollatzResearch.WordTrace tailWord_7968407 prefixEnd_7968407 4091622841651310304666469 := by
  unfold tailWord_7968407
  simp only [CollatzResearch.WordTrace]
  refine ⟨290631679642829809414279475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193754453095219872942852983 290631679642829809414279475)
  ·
    refine ⟨435947519464244714121419213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290631679642829809414279475 435947519464244714121419213)
    ·
      refine ⟨163480319799091767795532205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 435947519464244714121419213 163480319799091767795532205)
      ·
        refine ⟨61305119924659412923324577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163480319799091767795532205 61305119924659412923324577)
        ·
          refine ⟨45978839943494559692493433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61305119924659412923324577 45978839943494559692493433)
          ·
            refine ⟨34484129957620919769370075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45978839943494559692493433 34484129957620919769370075)
            ·
              refine ⟨51726194936431379654055113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34484129957620919769370075 51726194936431379654055113)
              ·
                refine ⟨38794646202323534740541335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51726194936431379654055113 38794646202323534740541335)
                ·
                  refine ⟨58191969303485302110812003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38794646202323534740541335 58191969303485302110812003)
                  ·
                    refine ⟨87287953955227953166218005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58191969303485302110812003 87287953955227953166218005)
                    ·
                      refine ⟨4091622841651310304666469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87287953955227953166218005 4091622841651310304666469)
                      ·
                        rfl

theorem cell23_7968407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_7968407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7968407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7968407 prefixEnd_7968407 := by exact prefixLift 7968407
  have htrace : WordTrace (prefixWord ++ tailWord_7968407) baseStart_7968407 baseEnd_7968407 := by
    simpa [prefixWord, tailWord_7968407, baseEnd_7968407] using wordTrace_append hprefix tailTrace_7968407
  have hstable : (prefixWord ++ tailWord_7968407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7968407).length < 2 ^ (prefixWord ++ tailWord_7968407).sum := by decide
  have hdescent : baseEnd_7968407 < baseStart_7968407 := by decide
  rcases family_descends (prefixWord ++ tailWord_7968407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7968417 : List Nat := [1, 2, 3, 3, 2, 1, 1, 10]
def baseStart_7968417 : Nat := 118140960795 + 7968417 * 2 ^ 59
def prefixEnd_7968417 : Nat := 4983230072969 + 3 ^ 40 * 7968417 * 2
def baseEnd_7968417 : Nat := 151541776905846491316349

theorem tailTrace_7968417 : CollatzResearch.WordTrace tailWord_7968417 prefixEnd_7968417 151541776905846491316349 := by
  unfold tailWord_7968417
  simp only [CollatzResearch.WordTrace]
  refine ⟨290632044372793581122143505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193754696248529054081429003 290632044372793581122143505)
  ·
    refine ⟨217974033279595185841607629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290632044372793581122143505 217974033279595185841607629)
    ·
      refine ⟨81740262479848194690602861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217974033279595185841607629 81740262479848194690602861)
      ·
        refine ⟨30652598429943073008976073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81740262479848194690602861 30652598429943073008976073)
        ·
          refine ⟨22989448822457304756732055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30652598429943073008976073 22989448822457304756732055)
          ·
            refine ⟨34484173233685957135098083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22989448822457304756732055 34484173233685957135098083)
            ·
              refine ⟨51726259850528935702647125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34484173233685957135098083 51726259850528935702647125)
              ·
                refine ⟨151541776905846491316349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 51726259850528935702647125 151541776905846491316349)
                ·
                  rfl

theorem cell23_7968417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 10].length) (baseStart_7968417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7968417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7968417 prefixEnd_7968417 := by exact prefixLift 7968417
  have htrace : WordTrace (prefixWord ++ tailWord_7968417) baseStart_7968417 baseEnd_7968417 := by
    simpa [prefixWord, tailWord_7968417, baseEnd_7968417] using wordTrace_append hprefix tailTrace_7968417
  have hstable : (prefixWord ++ tailWord_7968417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7968417).length < 2 ^ (prefixWord ++ tailWord_7968417).sum := by decide
  have hdescent : baseEnd_7968417 < baseStart_7968417 := by decide
  rcases family_descends (prefixWord ++ tailWord_7968417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7968421 : List Nat := [1, 3, 1, 2, 1, 2, 6, 1, 2, 4]
def baseStart_7968421 : Nat := 118140960795 + 7968421 * 2 ^ 59
def prefixEnd_7968421 : Nat := 4983230072969 + 3 ^ 40 * 7968421 * 2
def baseEnd_7968421 : Nat := 1363876676793491083297135

theorem tailTrace_7968421 : CollatzResearch.WordTrace tailWord_7968421 prefixEnd_7968421 1363876676793491083297135 := by
  unfold tailWord_7968421
  simp only [CollatzResearch.WordTrace]
  refine ⟨290632190264779089805289117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193754793509852726536859411 290632190264779089805289117)
  ·
    refine ⟨108987071349292158676983419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290632190264779089805289117 108987071349292158676983419)
    ·
      refine ⟨163480607023938238015475129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108987071349292158676983419 163480607023938238015475129)
      ·
        refine ⟨122610455267953678511606347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163480607023938238015475129 122610455267953678511606347)
        ·
          refine ⟨183915682901930517767409521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122610455267953678511606347 183915682901930517767409521)
          ·
            refine ⟨137936762176447888325557141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183915682901930517767409521 137936762176447888325557141)
            ·
              refine ⟨6465785727020994765260491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 137936762176447888325557141 6465785727020994765260491)
              ·
                refine ⟨9698678590531492147890737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6465785727020994765260491 9698678590531492147890737)
                ·
                  refine ⟨7274008942898619110918053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9698678590531492147890737 7274008942898619110918053)
                  ·
                    refine ⟨1363876676793491083297135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7274008942898619110918053 1363876676793491083297135)
                    ·
                      rfl

theorem cell23_7968421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 6, 1, 2, 4].length) (baseStart_7968421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7968421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7968421 prefixEnd_7968421 := by exact prefixLift 7968421
  have htrace : WordTrace (prefixWord ++ tailWord_7968421) baseStart_7968421 baseEnd_7968421 := by
    simpa [prefixWord, tailWord_7968421, baseEnd_7968421] using wordTrace_append hprefix tailTrace_7968421
  have hstable : (prefixWord ++ tailWord_7968421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7968421).length < 2 ^ (prefixWord ++ tailWord_7968421).sum := by decide
  have hdescent : baseEnd_7968421 < baseStart_7968421 := by decide
  rcases family_descends (prefixWord ++ tailWord_7968421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7968444 : List Nat := [2, 2, 2, 3, 1, 2, 1, 1, 3, 3, 3]
def baseStart_7968444 : Nat := 118140960795 + 7968444 * 2 ^ 59
def prefixEnd_7968444 : Nat := 4983230072969 + 3 ^ 40 * 7968444 * 2
def baseEnd_7968444 : Nat := 4091641840435526659903799

theorem tailTrace_7968444 : CollatzResearch.WordTrace tailWord_7968444 prefixEnd_7968444 4091641840435526659903799 := by
  unfold tailWord_7968444
  simp only [CollatzResearch.WordTrace]
  refine ⟨145316514571847882366688193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193755352762463843155584257 145316514571847882366688193)
  ·
    refine ⟨108987385928885911775016145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145316514571847882366688193 108987385928885911775016145)
    ·
      refine ⟨81740539446664433831262109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108987385928885911775016145 81740539446664433831262109)
      ·
        refine ⟨30652702292499162686723291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81740539446664433831262109 30652702292499162686723291)
        ·
          refine ⟨45979053438748744030084937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30652702292499162686723291 45979053438748744030084937)
          ·
            refine ⟨34484290079061558022563703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45979053438748744030084937 34484290079061558022563703)
            ·
              refine ⟨51726435118592337033845555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34484290079061558022563703 51726435118592337033845555)
              ·
                refine ⟨77589652677888505550768333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51726435118592337033845555 77589652677888505550768333)
                ·
                  refine ⟨29096119754208189581538125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77589652677888505550768333 29096119754208189581538125)
                  ·
                    refine ⟨10911044907828071093076797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29096119754208189581538125 10911044907828071093076797)
                    ·
                      refine ⟨4091641840435526659903799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10911044907828071093076797 4091641840435526659903799)
                      ·
                        rfl

theorem cell23_7968444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_7968444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7968444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7968444 prefixEnd_7968444 := by exact prefixLift 7968444
  have htrace : WordTrace (prefixWord ++ tailWord_7968444) baseStart_7968444 baseEnd_7968444 := by
    simpa [prefixWord, tailWord_7968444, baseEnd_7968444] using wordTrace_append hprefix tailTrace_7968444
  have hstable : (prefixWord ++ tailWord_7968444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7968444).length < 2 ^ (prefixWord ++ tailWord_7968444).sum := by decide
  have hdescent : baseEnd_7968444 < baseStart_7968444 := by decide
  rcases family_descends (prefixWord ++ tailWord_7968444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7968651 : List Nat := [1, 1, 1, 1, 4, 2, 1, 4, 1, 5, 2]
def baseStart_7968651 : Nat := 118140960795 + 7968651 * 2 ^ 59
def prefixEnd_7968651 : Nat := 4983230072969 + 3 ^ 40 * 7968651 * 2
def baseEnd_7968651 : Nat := 4091748130931007350015347

theorem tailTrace_7968651 : CollatzResearch.WordTrace tailWord_7968651 prefixEnd_7968651 4091748130931007350015347 := by
  unfold tailWord_7968651
  simp only [CollatzResearch.WordTrace]
  refine ⟨290640579053945839086161807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193760386035963892724107871 290640579053945839086161807)
  ·
    refine ⟨435960868580918758629242711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290640579053945839086161807 435960868580918758629242711)
    ·
      refine ⟨653941302871378137943864067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435960868580918758629242711 653941302871378137943864067)
      ·
        refine ⟨980911954307067206915796101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 653941302871378137943864067 980911954307067206915796101)
        ·
          refine ⟨183920991432575101296711769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 980911954307067206915796101 183920991432575101296711769)
          ·
            refine ⟨137940743574431325972533827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183920991432575101296711769 137940743574431325972533827)
            ·
              refine ⟨206911115361646988958800741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137940743574431325972533827 206911115361646988958800741)
              ·
                refine ⟨38795834130308810429775139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 206911115361646988958800741 38795834130308810429775139)
                ·
                  refine ⟨58193751195463215644662709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38795834130308810429775139 58193751195463215644662709)
                  ·
                    refine ⟨5455664174574676466687129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58193751195463215644662709 5455664174574676466687129)
                    ·
                      refine ⟨4091748130931007350015347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5455664174574676466687129 4091748130931007350015347)
                      ·
                        rfl

theorem cell23_7968651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 4, 1, 5, 2].length) (baseStart_7968651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7968651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7968651 prefixEnd_7968651 := by exact prefixLift 7968651
  have htrace : WordTrace (prefixWord ++ tailWord_7968651) baseStart_7968651 baseEnd_7968651 := by
    simpa [prefixWord, tailWord_7968651, baseEnd_7968651] using wordTrace_append hprefix tailTrace_7968651
  have hstable : (prefixWord ++ tailWord_7968651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7968651).length < 2 ^ (prefixWord ++ tailWord_7968651).sum := by decide
  have hdescent : baseEnd_7968651 < baseStart_7968651 := by decide
  rcases family_descends (prefixWord ++ tailWord_7968651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7968661 : List Nat := [1, 3, 2, 1, 1, 3, 2, 4, 1, 5]
def baseStart_7968661 : Nat := 118140960795 + 7968661 * 2 ^ 59
def prefixEnd_7968661 : Nat := 4983230072969 + 3 ^ 40 * 7968661 * 2
def baseEnd_7968661 : Nat := 1363917755245850770296767

theorem tailTrace_7968661 : CollatzResearch.WordTrace tailWord_7968661 prefixEnd_7968661 1363917755245850770296767 := by
  unfold tailWord_7968661
  simp only [CollatzResearch.WordTrace]
  refine ⟨290640943783909610794025837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193760629189273073862683891 290640943783909610794025837)
  ·
    refine ⟨108990353918966104047759689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290640943783909610794025837 108990353918966104047759689)
    ·
      refine ⟨81742765439224578035819767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108990353918966104047759689 81742765439224578035819767)
      ·
        refine ⟨122614148158836867053729651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81742765439224578035819767 122614148158836867053729651)
        ·
          refine ⟨183921222238255300580594477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122614148158836867053729651 183921222238255300580594477)
          ·
            refine ⟨68970458339345737717722929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183921222238255300580594477 68970458339345737717722929)
            ·
              refine ⟨51727843754509303288292197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68970458339345737717722929 51727843754509303288292197)
              ·
                refine ⟨9698970703970494366554787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51727843754509303288292197 9698970703970494366554787)
                ·
                  refine ⟨14548456055955741549832181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9698970703970494366554787 14548456055955741549832181)
                  ·
                    refine ⟨1363917755245850770296767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14548456055955741549832181 1363917755245850770296767)
                    ·
                      rfl

theorem cell23_7968661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 4, 1, 5].length) (baseStart_7968661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7968661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7968661 prefixEnd_7968661 := by exact prefixLift 7968661
  have htrace : WordTrace (prefixWord ++ tailWord_7968661) baseStart_7968661 baseEnd_7968661 := by
    simpa [prefixWord, tailWord_7968661, baseEnd_7968661] using wordTrace_append hprefix tailTrace_7968661
  have hstable : (prefixWord ++ tailWord_7968661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7968661).length < 2 ^ (prefixWord ++ tailWord_7968661).sum := by decide
  have hdescent : baseEnd_7968661 < baseStart_7968661 := by decide
  rcases family_descends (prefixWord ++ tailWord_7968661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7968662 : List Nat := [5, 3, 1, 1, 2, 1, 1, 1, 1, 4, 3]
def baseStart_7968662 : Nat := 118140960795 + 7968662 * 2 ^ 59
def prefixEnd_7968662 : Nat := 4983230072969 + 3 ^ 40 * 7968662 * 2
def baseEnd_7968662 : Nat := 4091753779218206806977797

theorem tailTrace_7968662 : CollatzResearch.WordTrace tailWord_7968662 prefixEnd_7968662 4091753779218206806977797 := by
  unfold tailWord_7968662
  simp only [CollatzResearch.WordTrace]
  refine ⟨18165061266056624247800765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 193760653504603991976541493 18165061266056624247800765)
  ·
    refine ⟨6811897974771234092925287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18165061266056624247800765 6811897974771234092925287)
    ·
      refine ⟨10217846962156851139387931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6811897974771234092925287 10217846962156851139387931)
      ·
        refine ⟨15326770443235276709081897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10217846962156851139387931 15326770443235276709081897)
        ·
          refine ⟨11495077832426457531811423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15326770443235276709081897 11495077832426457531811423)
          ·
            refine ⟨17242616748639686297717135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11495077832426457531811423 17242616748639686297717135)
            ·
              refine ⟨25863925122959529446575703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17242616748639686297717135 25863925122959529446575703)
              ·
                refine ⟨38795887684439294169863555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25863925122959529446575703 38795887684439294169863555)
                ·
                  refine ⟨58193831526658941254795333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38795887684439294169863555 58193831526658941254795333)
                  ·
                    refine ⟨10911343411248551485274125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58193831526658941254795333 10911343411248551485274125)
                    ·
                      refine ⟨4091753779218206806977797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10911343411248551485274125 4091753779218206806977797)
                      ·
                        rfl

theorem cell23_7968662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_7968662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7968662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7968662 prefixEnd_7968662 := by exact prefixLift 7968662
  have htrace : WordTrace (prefixWord ++ tailWord_7968662) baseStart_7968662 baseEnd_7968662 := by
    simpa [prefixWord, tailWord_7968662, baseEnd_7968662] using wordTrace_append hprefix tailTrace_7968662
  have hstable : (prefixWord ++ tailWord_7968662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7968662).length < 2 ^ (prefixWord ++ tailWord_7968662).sum := by decide
  have hdescent : baseEnd_7968662 < baseStart_7968662 := by decide
  rcases family_descends (prefixWord ++ tailWord_7968662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7968691 : List Nat := [1, 1, 1, 2, 3, 1, 5, 1, 4, 4]
def baseStart_7968691 : Nat := 118140960795 + 7968691 * 2 ^ 59
def prefixEnd_7968691 : Nat := 4983230072969 + 3 ^ 40 * 7968691 * 2
def baseEnd_7968691 : Nat := 1363922890052395731171721

theorem tailTrace_7968691 : CollatzResearch.WordTrace tailWord_7968691 prefixEnd_7968691 1363922890052395731171721 := by
  unfold tailWord_7968691
  simp only [CollatzResearch.WordTrace]
  refine ⟨290642037973800925917617927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193761358649200617278411951 290642037973800925917617927)
  ·
    refine ⟨435963056960701388876426891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290642037973800925917617927 435963056960701388876426891)
    ·
      refine ⟨653944585441052083314640337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435963056960701388876426891 653944585441052083314640337)
      ·
        refine ⟨490458439080789062485980253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 653944585441052083314640337 490458439080789062485980253)
        ·
          refine ⟨183921914655295898432242595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 490458439080789062485980253 183921914655295898432242595)
          ·
            refine ⟨275882871982943847648363893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183921914655295898432242595 275882871982943847648363893)
            ·
              refine ⟨25864019248400985717034115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 275882871982943847648363893 25864019248400985717034115)
              ·
                refine ⟨38796028872601478575551173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25864019248400985717034115 38796028872601478575551173)
                ·
                  refine ⟨7274255413612777232915845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38796028872601478575551173 7274255413612777232915845)
                  ·
                    refine ⟨1363922890052395731171721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7274255413612777232915845 1363922890052395731171721)
                    ·
                      rfl

theorem cell23_7968691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 1, 4, 4].length) (baseStart_7968691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7968691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7968691 prefixEnd_7968691 := by exact prefixLift 7968691
  have htrace : WordTrace (prefixWord ++ tailWord_7968691) baseStart_7968691 baseEnd_7968691 := by
    simpa [prefixWord, tailWord_7968691, baseEnd_7968691] using wordTrace_append hprefix tailTrace_7968691
  have hstable : (prefixWord ++ tailWord_7968691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7968691).length < 2 ^ (prefixWord ++ tailWord_7968691).sum := by decide
  have hdescent : baseEnd_7968691 < baseStart_7968691 := by decide
  rcases family_descends (prefixWord ++ tailWord_7968691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7968701 : List Nat := [1, 4, 1, 2, 3, 1, 1, 1, 3, 1, 5]
def baseStart_7968701 : Nat := 118140960795 + 7968701 * 2 ^ 59
def prefixEnd_7968701 : Nat := 4983230072969 + 3 ^ 40 * 7968701 * 2
def baseEnd_7968701 : Nat := 4091773804963732154390117

theorem tailTrace_7968701 : CollatzResearch.WordTrace tailWord_7968701 prefixEnd_7968701 4091773804963732154390117 := by
  unfold tailWord_7968701
  simp only [CollatzResearch.WordTrace]
  refine ⟨290642402703764697625481957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193761601802509798416987971 290642402703764697625481957)
  ·
    refine ⟨54495450506955880804777867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 290642402703764697625481957 54495450506955880804777867)
    ·
      refine ⟨81743175760433821207166801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54495450506955880804777867 81743175760433821207166801)
      ·
        refine ⟨61307381820325365905375101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81743175760433821207166801 61307381820325365905375101)
        ·
          refine ⟨22990268182622012214515663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61307381820325365905375101 22990268182622012214515663)
          ·
            refine ⟨34485402273933018321773495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22990268182622012214515663 34485402273933018321773495)
            ·
              refine ⟨51728103410899527482660243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34485402273933018321773495 51728103410899527482660243)
              ·
                refine ⟨77592155116349291223990365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51728103410899527482660243 77592155116349291223990365)
                ·
                  refine ⟨29097058168630984208996387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77592155116349291223990365 29097058168630984208996387)
                  ·
                    refine ⟨43645587252946476313494581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29097058168630984208996387 43645587252946476313494581)
                    ·
                      refine ⟨4091773804963732154390117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43645587252946476313494581 4091773804963732154390117)
                      ·
                        rfl

theorem cell23_7968701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_7968701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7968701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7968701 prefixEnd_7968701 := by exact prefixLift 7968701
  have htrace : WordTrace (prefixWord ++ tailWord_7968701) baseStart_7968701 baseEnd_7968701 := by
    simpa [prefixWord, tailWord_7968701, baseEnd_7968701] using wordTrace_append hprefix tailTrace_7968701
  have hstable : (prefixWord ++ tailWord_7968701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7968701).length < 2 ^ (prefixWord ++ tailWord_7968701).sum := by decide
  have hdescent : baseEnd_7968701 < baseStart_7968701 := by decide
  rcases family_descends (prefixWord ++ tailWord_7968701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7968704 : List Nat := [2, 1, 1, 2, 3, 2, 2, 10]
def baseStart_7968704 : Nat := 118140960795 + 7968704 * 2 ^ 59
def prefixEnd_7968704 : Nat := 4983230072969 + 3 ^ 40 * 7968704 * 2
def baseEnd_7968704 : Nat := 151547235015025764542689

theorem tailTrace_7968704 : CollatzResearch.WordTrace tailWord_7968704 prefixEnd_7968704 151547235015025764542689 := by
  unfold tailWord_7968704
  simp only [CollatzResearch.WordTrace]
  refine ⟨145321256061376914568920583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193761674748502552758560777 145321256061376914568920583)
  ·
    refine ⟨217981884092065371853380875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145321256061376914568920583 217981884092065371853380875)
    ·
      refine ⟨326972826138098057780071313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217981884092065371853380875 326972826138098057780071313)
      ·
        refine ⟨245229619603573543335053485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 326972826138098057780071313 245229619603573543335053485)
        ·
          refine ⟨91961107351340078750645057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 245229619603573543335053485 91961107351340078750645057)
          ·
            refine ⟨68970830513505059062983793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91961107351340078750645057 68970830513505059062983793)
            ·
              refine ⟨51728122885128794297237845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68970830513505059062983793 51728122885128794297237845)
              ·
                refine ⟨151547235015025764542689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 51728122885128794297237845 151547235015025764542689)
                ·
                  rfl

theorem cell23_7968704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 10].length) (baseStart_7968704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7968704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7968704 prefixEnd_7968704 := by exact prefixLift 7968704
  have htrace : WordTrace (prefixWord ++ tailWord_7968704) baseStart_7968704 baseEnd_7968704 := by
    simpa [prefixWord, tailWord_7968704, baseEnd_7968704] using wordTrace_append hprefix tailTrace_7968704
  have hstable : (prefixWord ++ tailWord_7968704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7968704).length < 2 ^ (prefixWord ++ tailWord_7968704).sum := by decide
  have hdescent : baseEnd_7968704 < baseStart_7968704 := by decide
  rcases family_descends (prefixWord ++ tailWord_7968704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7968726 : List Nat := [5, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3]
def baseStart_7968726 : Nat := 118140960795 + 7968726 * 2 ^ 59
def prefixEnd_7968726 : Nat := 4983230072969 + 3 ^ 40 * 7968726 * 2
def baseEnd_7968726 : Nat := 4091786641980094556577503

theorem tailTrace_7968726 : CollatzResearch.WordTrace tailWord_7968726 prefixEnd_7968726 4091786641980094556577503 := by
  unfold tailWord_7968726
  simp only [CollatzResearch.WordTrace]
  refine ⟨18165207158042132930946377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 193762209685782751263428021 18165207158042132930946377)
  ·
    refine ⟨13623905368531599698209783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18165207158042132930946377 13623905368531599698209783)
    ·
      refine ⟨20435858052797399547314675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13623905368531599698209783 20435858052797399547314675)
      ·
        refine ⟨30653787079196099320972013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20435858052797399547314675 30653787079196099320972013)
        ·
          refine ⟨11495170154698537245364505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30653787079196099320972013 11495170154698537245364505)
          ·
            refine ⟨8621377616023902934023379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11495170154698537245364505 8621377616023902934023379)
            ·
              refine ⟨12932066424035854401035069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8621377616023902934023379 12932066424035854401035069)
              ·
                refine ⟨4849524909013445400388151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12932066424035854401035069 4849524909013445400388151)
                ·
                  refine ⟨7274287363520168100582227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4849524909013445400388151 7274287363520168100582227)
                  ·
                    refine ⟨10911431045280252150873341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7274287363520168100582227 10911431045280252150873341)
                    ·
                      refine ⟨4091786641980094556577503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10911431045280252150873341 4091786641980094556577503)
                      ·
                        rfl

theorem cell23_7968726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3].length) (baseStart_7968726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7968726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7968726 prefixEnd_7968726 := by exact prefixLift 7968726
  have htrace : WordTrace (prefixWord ++ tailWord_7968726) baseStart_7968726 baseEnd_7968726 := by
    simpa [prefixWord, tailWord_7968726, baseEnd_7968726] using wordTrace_append hprefix tailTrace_7968726
  have hstable : (prefixWord ++ tailWord_7968726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7968726).length < 2 ^ (prefixWord ++ tailWord_7968726).sum := by decide
  have hdescent : baseEnd_7968726 < baseStart_7968726 := by decide
  rcases family_descends (prefixWord ++ tailWord_7968726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7968775 : List Nat := [1, 1, 4, 3, 1, 3, 1, 1, 3, 3, 2]
def baseStart_7968775 : Nat := 118140960795 + 7968775 * 2 ^ 59
def prefixEnd_7968775 : Nat := 4983230072969 + 3 ^ 40 * 7968775 * 2
def baseEnd_7968775 : Nat := 4091811802532164864864777

theorem tailTrace_7968775 : CollatzResearch.WordTrace tailWord_7968775 prefixEnd_7968775 4091811802532164864864777 := by
  unfold tailWord_7968775
  simp only [CollatzResearch.WordTrace]
  refine ⟨290645101705496608263675779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193763401136997738842450519 290645101705496608263675779)
  ·
    refine ⟨435967652558244912395513669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290645101705496608263675779 435967652558244912395513669)
    ·
      refine ⟨81743934854670921074158813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 435967652558244912395513669 81743934854670921074158813)
      ·
        refine ⟨30653975570501595402809555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81743934854670921074158813 30653975570501595402809555)
        ·
          refine ⟨45980963355752393104214333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30653975570501595402809555 45980963355752393104214333)
          ·
            refine ⟨17242861258407147414080375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45980963355752393104214333 17242861258407147414080375)
            ·
              refine ⟨25864291887610721121120563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17242861258407147414080375 25864291887610721121120563)
              ·
                refine ⟨38796437831416081681680845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25864291887610721121120563 38796437831416081681680845)
                ·
                  refine ⟨14548664186781030630630317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38796437831416081681680845 14548664186781030630630317)
                  ·
                    refine ⟨5455749070042886486486369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14548664186781030630630317 5455749070042886486486369)
                    ·
                      refine ⟨4091811802532164864864777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5455749070042886486486369 4091811802532164864864777)
                      ·
                        rfl

theorem cell23_7968775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 1, 3, 3, 2].length) (baseStart_7968775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7968775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7968775 prefixEnd_7968775 := by exact prefixLift 7968775
  have htrace : WordTrace (prefixWord ++ tailWord_7968775) baseStart_7968775 baseEnd_7968775 := by
    simpa [prefixWord, tailWord_7968775, baseEnd_7968775] using wordTrace_append hprefix tailTrace_7968775
  have hstable : (prefixWord ++ tailWord_7968775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7968775).length < 2 ^ (prefixWord ++ tailWord_7968775).sum := by decide
  have hdescent : baseEnd_7968775 < baseStart_7968775 := by decide
  rcases family_descends (prefixWord ++ tailWord_7968775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7968792 : List Nat := [2, 1, 2, 3, 2, 1, 5, 1, 1, 3, 2]
def baseStart_7968792 : Nat := 118140960795 + 7968792 * 2 ^ 59
def prefixEnd_7968792 : Nat := 4983230072969 + 3 ^ 40 * 7968792 * 2
def baseEnd_7968792 : Nat := 4091820531703291298352199

theorem tailTrace_7968792 : CollatzResearch.WordTrace tailWord_7968792 prefixEnd_7968792 4091820531703291298352199 := by
  unfold tailWord_7968792
  simp only [CollatzResearch.WordTrace]
  refine ⟨145322860873217510083522315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193763814497623346778029753 145322860873217510083522315)
  ·
    refine ⟨217984291309826265125283473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145322860873217510083522315 217984291309826265125283473)
    ·
      refine ⟨163488218482369698843962605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217984291309826265125283473 163488218482369698843962605)
      ·
        refine ⟨61308081930888637066485977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163488218482369698843962605 61308081930888637066485977)
        ·
          refine ⟨45981061448166477799864483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61308081930888637066485977 45981061448166477799864483)
          ·
            refine ⟨68971592172249716699796725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45981061448166477799864483 68971592172249716699796725)
            ·
              refine ⟨6466086766148410940605943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68971592172249716699796725 6466086766148410940605943)
              ·
                refine ⟨9699130149222616410908915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6466086766148410940605943 9699130149222616410908915)
                ·
                  refine ⟨14548695223833924616363373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9699130149222616410908915 14548695223833924616363373)
                  ·
                    refine ⟨5455760708937721731136265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14548695223833924616363373 5455760708937721731136265)
                    ·
                      refine ⟨4091820531703291298352199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5455760708937721731136265 4091820531703291298352199)
                      ·
                        rfl

theorem cell23_7968792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 5, 1, 1, 3, 2].length) (baseStart_7968792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7968792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7968792 prefixEnd_7968792 := by exact prefixLift 7968792
  have htrace : WordTrace (prefixWord ++ tailWord_7968792) baseStart_7968792 baseEnd_7968792 := by
    simpa [prefixWord, tailWord_7968792, baseEnd_7968792] using wordTrace_append hprefix tailTrace_7968792
  have hstable : (prefixWord ++ tailWord_7968792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7968792).length < 2 ^ (prefixWord ++ tailWord_7968792).sum := by decide
  have hdescent : baseEnd_7968792 < baseStart_7968792 := by decide
  rcases family_descends (prefixWord ++ tailWord_7968792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7968818 : List Nat := [3, 2, 1, 1, 2, 4, 1, 1, 2, 2, 4]
def baseStart_7968818 : Nat := 118140960795 + 7968818 * 2 ^ 59
def prefixEnd_7968818 : Nat := 4983230072969 + 3 ^ 40 * 7968818 * 2
def baseEnd_7968818 : Nat := 4091833882200308196627079

theorem tailTrace_7968818 : CollatzResearch.WordTrace tailWord_7968818 prefixEnd_7968818 4091833882200308196627079 := by
  unfold tailWord_7968818
  simp only [CollatzResearch.WordTrace]
  refine ⟨72661667511085206651872777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193764446696227217738327405 72661667511085206651872777)
  ·
    refine ⟨54496250633313904988904583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72661667511085206651872777 54496250633313904988904583)
    ·
      refine ⟨81744375949970857483356875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54496250633313904988904583 81744375949970857483356875)
      ·
        refine ⟨122616563924956286225035313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81744375949970857483356875 122616563924956286225035313)
        ·
          refine ⟨91962422943717214668776485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122616563924956286225035313 91962422943717214668776485)
          ·
            refine ⟨17242954301946977750395591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91962422943717214668776485 17242954301946977750395591)
            ·
              refine ⟨25864431452920466625593387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17242954301946977750395591 25864431452920466625593387)
              ·
                refine ⟨38796647179380699938390081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25864431452920466625593387 38796647179380699938390081)
                ·
                  refine ⟨29097485384535524953792561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38796647179380699938390081 29097485384535524953792561)
                  ·
                    refine ⟨21823114038401643715344421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29097485384535524953792561 21823114038401643715344421)
                    ·
                      refine ⟨4091833882200308196627079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21823114038401643715344421 4091833882200308196627079)
                      ·
                        rfl

theorem cell23_7968818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 1, 2, 2, 4].length) (baseStart_7968818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7968818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7968818 prefixEnd_7968818 := by exact prefixLift 7968818
  have htrace : WordTrace (prefixWord ++ tailWord_7968818) baseStart_7968818 baseEnd_7968818 := by
    simpa [prefixWord, tailWord_7968818, baseEnd_7968818] using wordTrace_append hprefix tailTrace_7968818
  have hstable : (prefixWord ++ tailWord_7968818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7968818).length < 2 ^ (prefixWord ++ tailWord_7968818).sum := by decide
  have hdescent : baseEnd_7968818 < baseStart_7968818 := by decide
  rcases family_descends (prefixWord ++ tailWord_7968818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7968822 : List Nat := [5, 1, 2, 1, 1, 1, 4, 1, 1, 4, 2]
def baseStart_7968822 : Nat := 118140960795 + 7968822 * 2 ^ 59
def prefixEnd_7968822 : Nat := 4983230072969 + 3 ^ 40 * 7968822 * 2
def baseEnd_7968822 : Nat := 4091835936122926180977061

theorem tailTrace_7968822 : CollatzResearch.WordTrace tailWord_7968822 prefixEnd_7968822 4091835936122926180977061 := by
  unfold tailWord_7968822
  simp only [CollatzResearch.WordTrace]
  refine ⟨18165425996020395955664795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 193764543957550890193757813 18165425996020395955664795)
  ·
    refine ⟨27248138994030593933497193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18165425996020395955664795 27248138994030593933497193)
    ·
      refine ⟨20436104245522945450122895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27248138994030593933497193 20436104245522945450122895)
      ·
        refine ⟨30654156368284418175184343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20436104245522945450122895 30654156368284418175184343)
        ·
          refine ⟨45981234552426627262776515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30654156368284418175184343 45981234552426627262776515)
          ·
            refine ⟨68971851828639940894164773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45981234552426627262776515 68971851828639940894164773)
            ·
              refine ⟨12932222217869988917655895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68971851828639940894164773 12932222217869988917655895)
              ·
                refine ⟨19398333326804983376483843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12932222217869988917655895 19398333326804983376483843)
                ·
                  refine ⟨29097499990207475064725765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19398333326804983376483843 29097499990207475064725765)
                  ·
                    refine ⟨5455781248163901574636081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29097499990207475064725765 5455781248163901574636081)
                    ·
                      refine ⟨4091835936122926180977061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5455781248163901574636081 4091835936122926180977061)
                      ·
                        rfl

theorem cell23_7968822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 1, 1, 4, 2].length) (baseStart_7968822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7968822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7968822 prefixEnd_7968822 := by exact prefixLift 7968822
  have htrace : WordTrace (prefixWord ++ tailWord_7968822) baseStart_7968822 baseEnd_7968822 := by
    simpa [prefixWord, tailWord_7968822, baseEnd_7968822] using wordTrace_append hprefix tailTrace_7968822
  have hstable : (prefixWord ++ tailWord_7968822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7968822).length < 2 ^ (prefixWord ++ tailWord_7968822).sum := by decide
  have hdescent : baseEnd_7968822 < baseStart_7968822 := by decide
  rcases family_descends (prefixWord ++ tailWord_7968822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7968841 : List Nat := [1, 2, 1, 1, 2, 2, 5, 1, 1, 7]
def baseStart_7968841 : Nat := 118140960795 + 7968841 * 2 ^ 59
def prefixEnd_7968841 : Nat := 4983230072969 + 3 ^ 40 * 7968841 * 2
def baseEnd_7968841 : Nat := 1363948564085120535546491

theorem tailTrace_7968841 : CollatzResearch.WordTrace tailWord_7968841 prefixEnd_7968841 1363948564085120535546491 := by
  unfold tailWord_7968841
  simp only [CollatzResearch.WordTrace]
  refine ⟨290647508923257501535578377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193765005948838334357052251 290647508923257501535578377)
  ·
    refine ⟨217985631692443126151683783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290647508923257501535578377 217985631692443126151683783)
    ·
      refine ⟨326978447538664689227525675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217985631692443126151683783 326978447538664689227525675)
      ·
        refine ⟨490467671307997033841288513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326978447538664689227525675 490467671307997033841288513)
        ·
          refine ⟨367850753480997775380966385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 490467671307997033841288513 367850753480997775380966385)
          ·
            refine ⟨275888065110748331535724789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 367850753480997775380966385 275888065110748331535724789)
            ·
              refine ⟨25864506104132656081474199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 275888065110748331535724789 25864506104132656081474199)
              ·
                refine ⟨38796759156198984122211299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25864506104132656081474199 38796759156198984122211299)
                ·
                  refine ⟨58195138734298476183316949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38796759156198984122211299 58195138734298476183316949)
                  ·
                    refine ⟨1363948564085120535546491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58195138734298476183316949 1363948564085120535546491)
                    ·
                      rfl

theorem cell23_7968841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 1, 1, 7].length) (baseStart_7968841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7968841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7968841 prefixEnd_7968841 := by exact prefixLift 7968841
  have htrace : WordTrace (prefixWord ++ tailWord_7968841) baseStart_7968841 baseEnd_7968841 := by
    simpa [prefixWord, tailWord_7968841, baseEnd_7968841] using wordTrace_append hprefix tailTrace_7968841
  have hstable : (prefixWord ++ tailWord_7968841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7968841).length < 2 ^ (prefixWord ++ tailWord_7968841).sum := by decide
  have hdescent : baseEnd_7968841 < baseStart_7968841 := by decide
  rcases family_descends (prefixWord ++ tailWord_7968841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7968878 : List Nat := [4, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4]
def baseStart_7968878 : Nat := 118140960795 + 7968878 * 2 ^ 59
def prefixEnd_7968878 : Nat := 4983230072969 + 3 ^ 40 * 7968878 * 2
def baseEnd_7968878 : Nat := 4091864691039577961876803

theorem tailTrace_7968878 : CollatzResearch.WordTrace tailWord_7968878 prefixEnd_7968878 4091864691039577961876803 := by
  unfold tailWord_7968878
  simp only [CollatzResearch.WordTrace]
  refine ⟨36331107303015432106834411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193765905616082304569783525 36331107303015432106834411)
  ·
    refine ⟨54496660954523148160251617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36331107303015432106834411 54496660954523148160251617)
    ·
      refine ⟨40872495715892361120188713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54496660954523148160251617 40872495715892361120188713)
      ·
        refine ⟨30654371786919270840141535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40872495715892361120188713 30654371786919270840141535)
        ·
          refine ⟨45981557680378906260212303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30654371786919270840141535 45981557680378906260212303)
          ·
            refine ⟨68972336520568359390318455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45981557680378906260212303 68972336520568359390318455)
            ·
              refine ⟨103458504780852539085477683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68972336520568359390318455 103458504780852539085477683)
              ·
                refine ⟨155187757171278808628216525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103458504780852539085477683 155187757171278808628216525)
                ·
                  refine ⟨58195408939229553235581197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 155187757171278808628216525 58195408939229553235581197)
                  ·
                    refine ⟨21823278352211082463342949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58195408939229553235581197 21823278352211082463342949)
                    ·
                      refine ⟨4091864691039577961876803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21823278352211082463342949 4091864691039577961876803)
                      ·
                        rfl

theorem cell23_7968878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_7968878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7968878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7968878 prefixEnd_7968878 := by exact prefixLift 7968878
  have htrace : WordTrace (prefixWord ++ tailWord_7968878) baseStart_7968878 baseEnd_7968878 := by
    simpa [prefixWord, tailWord_7968878, baseEnd_7968878] using wordTrace_append hprefix tailTrace_7968878
  have hstable : (prefixWord ++ tailWord_7968878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7968878).length < 2 ^ (prefixWord ++ tailWord_7968878).sum := by decide
  have hdescent : baseEnd_7968878 < baseStart_7968878 := by decide
  rcases family_descends (prefixWord ++ tailWord_7968878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7968921 : List Nat := [1, 2, 1, 2, 1, 2, 1, 3, 1, 1, 8]
def baseStart_7968921 : Nat := 118140960795 + 7968921 * 2 ^ 59
def prefixEnd_7968921 : Nat := 4983230072969 + 3 ^ 40 * 7968921 * 2
def baseEnd_7968921 : Nat := 4091886770707721293639105

theorem tailTrace_7968921 : CollatzResearch.WordTrace tailWord_7968921 prefixEnd_7968921 4091886770707721293639105 := by
  unfold tailWord_7968921
  simp only [CollatzResearch.WordTrace]
  refine ⟨290650426762967675198490617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193766951175311783465660411 290650426762967675198490617)
  ·
    refine ⟨217987820072225756398867963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290650426762967675198490617 217987820072225756398867963)
    ·
      refine ⟨326981730108338634598301945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217987820072225756398867963 326981730108338634598301945)
      ·
        refine ⟨245236297581253975948726459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 326981730108338634598301945 245236297581253975948726459)
        ·
          refine ⟨367854446371880963923089689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245236297581253975948726459 367854446371880963923089689)
          ·
            refine ⟨275890834778910722942317267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 367854446371880963923089689 275890834778910722942317267)
            ·
              refine ⟨413836252168366084413475901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275890834778910722942317267 413836252168366084413475901)
              ·
                refine ⟨155188594563137281655053463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 413836252168366084413475901 155188594563137281655053463)
                ·
                  refine ⟨232782891844705922482580195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 155188594563137281655053463 232782891844705922482580195)
                  ·
                    refine ⟨349174337767058883723870293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 232782891844705922482580195 349174337767058883723870293)
                    ·
                      refine ⟨4091886770707721293639105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 349174337767058883723870293 4091886770707721293639105)
                      ·
                        rfl

theorem cell23_7968921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 1, 8].length) (baseStart_7968921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7968921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7968921 prefixEnd_7968921 := by exact prefixLift 7968921
  have htrace : WordTrace (prefixWord ++ tailWord_7968921) baseStart_7968921 baseEnd_7968921 := by
    simpa [prefixWord, tailWord_7968921, baseEnd_7968921] using wordTrace_append hprefix tailTrace_7968921
  have hstable : (prefixWord ++ tailWord_7968921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7968921).length < 2 ^ (prefixWord ++ tailWord_7968921).sum := by decide
  have hdescent : baseEnd_7968921 < baseStart_7968921 := by decide
  rcases family_descends (prefixWord ++ tailWord_7968921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7968931 : List Nat := [1, 1, 1, 4, 1, 1, 1, 1, 1, 11]
def baseStart_7968931 : Nat := 118140960795 + 7968931 * 2 ^ 59
def prefixEnd_7968931 : Nat := 4983230072969 + 3 ^ 40 * 7968931 * 2
def baseEnd_7968931 : Nat := 1363963968504755418171353

theorem tailTrace_7968931 : CollatzResearch.WordTrace tailWord_7968931 prefixEnd_7968931 1363963968504755418171353 := by
  unfold tailWord_7968931
  simp only [CollatzResearch.WordTrace]
  refine ⟨290650791492931446906354647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193767194328620964604236431 290650791492931446906354647)
  ·
    refine ⟨435976187239397170359531971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290650791492931446906354647 435976187239397170359531971)
    ·
      refine ⟨653964280859095755539297957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435976187239397170359531971 653964280859095755539297957)
      ·
        refine ⟨122618302661080454163618367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 653964280859095755539297957 122618302661080454163618367)
        ·
          refine ⟨183927453991620681245427551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122618302661080454163618367 183927453991620681245427551)
          ·
            refine ⟨275891180987431021868141327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183927453991620681245427551 275891180987431021868141327)
            ·
              refine ⟨413836771481146532802211991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275891180987431021868141327 413836771481146532802211991)
              ·
                refine ⟨620755157221719799203317987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 413836771481146532802211991 620755157221719799203317987)
                ·
                  refine ⟨931132735832579698804976981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 620755157221719799203317987 931132735832579698804976981)
                  ·
                    refine ⟨1363963968504755418171353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 931132735832579698804976981 1363963968504755418171353)
                    ·
                      rfl

theorem cell23_7968931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 11].length) (baseStart_7968931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7968931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7968931 prefixEnd_7968931 := by exact prefixLift 7968931
  have htrace : WordTrace (prefixWord ++ tailWord_7968931) baseStart_7968931 baseEnd_7968931 := by
    simpa [prefixWord, tailWord_7968931, baseEnd_7968931] using wordTrace_append hprefix tailTrace_7968931
  have hstable : (prefixWord ++ tailWord_7968931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7968931).length < 2 ^ (prefixWord ++ tailWord_7968931).sum := by decide
  have hdescent : baseEnd_7968931 < baseStart_7968931 := by decide
  rcases family_descends (prefixWord ++ tailWord_7968931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7968949 : List Nat := [1, 3, 3, 4, 1, 1, 2, 1, 2, 2, 3]
def baseStart_7968949 : Nat := 118140960795 + 7968949 * 2 ^ 59
def prefixEnd_7968949 : Nat := 4983230072969 + 3 ^ 40 * 7968949 * 2
def baseEnd_7968949 : Nat := 4091901148166047184088977

theorem tailTrace_7968949 : CollatzResearch.WordTrace tailWord_7968949 prefixEnd_7968949 4091901148166047184088977 := by
  unfold tailWord_7968949
  simp only [CollatzResearch.WordTrace]
  refine ⟨290651448006866235980509901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193767632004577490653673267 290651448006866235980509901)
  ·
    refine ⟨108994293002574838492691213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290651448006866235980509901 108994293002574838492691213)
    ·
      refine ⟨40872859875965564434759205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108994293002574838492691213 40872859875965564434759205)
      ·
        refine ⟨7663661226743543331517351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40872859875965564434759205 7663661226743543331517351)
        ·
          refine ⟨11495491840115314997276027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7663661226743543331517351 11495491840115314997276027)
          ·
            refine ⟨17243237760172972495914041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11495491840115314997276027 17243237760172972495914041)
            ·
              refine ⟨12932428320129729371935531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17243237760172972495914041 12932428320129729371935531)
              ·
                refine ⟨19398642480194594057903297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12932428320129729371935531 19398642480194594057903297)
                ·
                  refine ⟨14548981860145945543427473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19398642480194594057903297 14548981860145945543427473)
                  ·
                    refine ⟨10911736395109459157570605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14548981860145945543427473 10911736395109459157570605)
                    ·
                      refine ⟨4091901148166047184088977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10911736395109459157570605 4091901148166047184088977)
                      ·
                        rfl

theorem cell23_7968949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_7968949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7968949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7968949 prefixEnd_7968949 := by exact prefixLift 7968949
  have htrace : WordTrace (prefixWord ++ tailWord_7968949) baseStart_7968949 baseEnd_7968949 := by
    simpa [prefixWord, tailWord_7968949, baseEnd_7968949] using wordTrace_append hprefix tailTrace_7968949
  have hstable : (prefixWord ++ tailWord_7968949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7968949).length < 2 ^ (prefixWord ++ tailWord_7968949).sum := by decide
  have hdescent : baseEnd_7968949 < baseStart_7968949 := by decide
  rcases family_descends (prefixWord ++ tailWord_7968949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7968982 : List Nat := [5, 2, 1, 2, 1, 1, 1, 2, 3, 5]
def baseStart_7968982 : Nat := 118140960795 + 7968982 * 2 ^ 59
def prefixEnd_7968982 : Nat := 4983230072969 + 3 ^ 40 * 7968982 * 2
def baseEnd_7968982 : Nat := 1363972697675881851658775

theorem tailTrace_7968982 : CollatzResearch.WordTrace tailWord_7968982 prefixEnd_7968982 1363972697675881851658775 := by
  unfold tailWord_7968982
  simp only [CollatzResearch.WordTrace]
  refine ⟨18165790725984167663528825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 193768434410497788410974133 18165790725984167663528825)
  ·
    refine ⟨13624343044488125747646619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18165790725984167663528825 13624343044488125747646619)
    ·
      refine ⟨20436514566732188621469929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13624343044488125747646619 20436514566732188621469929)
      ·
        refine ⟨15327385925049141466102447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20436514566732188621469929 15327385925049141466102447)
        ·
          refine ⟨22991078887573712199153671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15327385925049141466102447 22991078887573712199153671)
          ·
            refine ⟨34486618331360568298730507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22991078887573712199153671 34486618331360568298730507)
            ·
              refine ⟨51729927497040852448095761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34486618331360568298730507 51729927497040852448095761)
              ·
                refine ⟨38797445622780639336071821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51729927497040852448095761 38797445622780639336071821)
                ·
                  refine ⟨14549042108542739751026933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38797445622780639336071821 14549042108542739751026933)
                  ·
                    refine ⟨1363972697675881851658775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14549042108542739751026933 1363972697675881851658775)
                    ·
                      rfl

theorem cell23_7968982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_7968982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7968982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7968982 prefixEnd_7968982 := by exact prefixLift 7968982
  have htrace : WordTrace (prefixWord ++ tailWord_7968982) baseStart_7968982 baseEnd_7968982 := by
    simpa [prefixWord, tailWord_7968982, baseEnd_7968982] using wordTrace_append hprefix tailTrace_7968982
  have hstable : (prefixWord ++ tailWord_7968982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7968982).length < 2 ^ (prefixWord ++ tailWord_7968982).sum := by decide
  have hdescent : baseEnd_7968982 < baseStart_7968982 := by decide
  rcases family_descends (prefixWord ++ tailWord_7968982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7969068 : List Nat := [2, 2, 1, 1, 1, 3, 2, 2, 1, 8]
def baseStart_7969068 : Nat := 118140960795 + 7969068 * 2 ^ 59
def prefixEnd_7969068 : Nat := 4983230072969 + 3 ^ 40 * 7969068 * 2
def baseEnd_7969068 : Nat := 1363987417454644072833643

theorem tailTrace_7969068 : CollatzResearch.WordTrace tailWord_7969068 prefixEnd_7969068 1363987417454644072833643 := by
  unfold tailWord_7969068
  simp only [CollatzResearch.WordTrace]
  refine ⟨145327894146717559652045929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193770525528956746202727905 145327894146717559652045929)
  ·
    refine ⟨108995920610038169739034447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145327894146717559652045929 108995920610038169739034447)
    ·
      refine ⟨163493880915057254608551671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108995920610038169739034447 163493880915057254608551671)
      ·
        refine ⟨245240821372585881912827507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163493880915057254608551671 245240821372585881912827507)
        ·
          refine ⟨367861232058878822869241261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245240821372585881912827507 367861232058878822869241261)
          ·
            refine ⟨137947962022079558575965473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 367861232058878822869241261 137947962022079558575965473)
            ·
              refine ⟨103460971516559668931974105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137947962022079558575965473 103460971516559668931974105)
              ·
                refine ⟨77595728637419751698980579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103460971516559668931974105 77595728637419751698980579)
                ·
                  refine ⟨116393592956129627548470869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77595728637419751698980579 116393592956129627548470869)
                  ·
                    refine ⟨1363987417454644072833643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 116393592956129627548470869 1363987417454644072833643)
                    ·
                      rfl

theorem cell23_7969068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 8].length) (baseStart_7969068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7969068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7969068 prefixEnd_7969068 := by exact prefixLift 7969068
  have htrace : WordTrace (prefixWord ++ tailWord_7969068) baseStart_7969068 baseEnd_7969068 := by
    simpa [prefixWord, tailWord_7969068, baseEnd_7969068] using wordTrace_append hprefix tailTrace_7969068
  have hstable : (prefixWord ++ tailWord_7969068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7969068).length < 2 ^ (prefixWord ++ tailWord_7969068).sum := by decide
  have hdescent : baseEnd_7969068 < baseStart_7969068 := by decide
  rcases family_descends (prefixWord ++ tailWord_7969068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7969088 : List Nat := [2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 6]
def baseStart_7969088 : Nat := 118140960795 + 7969088 * 2 ^ 59
def prefixEnd_7969088 : Nat := 4983230072969 + 3 ^ 40 * 7969088 * 2
def baseEnd_7969088 : Nat := 4091972521977022140250837

theorem tailTrace_7969088 : CollatzResearch.WordTrace tailWord_7969088 prefixEnd_7969088 4091972521977022140250837 := by
  unfold tailWord_7969088
  simp only [CollatzResearch.WordTrace]
  refine ⟨145328258876681331359909959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193771011835575108479879945 145328258876681331359909959)
  ·
    refine ⟨217992388315021997039864939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145328258876681331359909959 217992388315021997039864939)
    ·
      refine ⟨326988582472532995559797409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217992388315021997039864939 326988582472532995559797409)
      ·
        refine ⟨245241436854399746669848057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 326988582472532995559797409 245241436854399746669848057)
        ·
          refine ⟨183931077640799810002386043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245241436854399746669848057 183931077640799810002386043)
          ·
            refine ⟨275896616461199715003579065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183931077640799810002386043 275896616461199715003579065)
            ·
              refine ⟨206922462345899786252684299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 275896616461199715003579065 206922462345899786252684299)
              ·
                refine ⟨310383693518849679379026449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206922462345899786252684299 310383693518849679379026449)
                ·
                  refine ⟨232787770139137259534269837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 310383693518849679379026449 232787770139137259534269837)
                  ·
                    refine ⟨87295413802176472325351189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 232787770139137259534269837 87295413802176472325351189)
                    ·
                      refine ⟨4091972521977022140250837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87295413802176472325351189 4091972521977022140250837)
                      ·
                        rfl

theorem cell23_7969088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 6].length) (baseStart_7969088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7969088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7969088 prefixEnd_7969088 := by exact prefixLift 7969088
  have htrace : WordTrace (prefixWord ++ tailWord_7969088) baseStart_7969088 baseEnd_7969088 := by
    simpa [prefixWord, tailWord_7969088, baseEnd_7969088] using wordTrace_append hprefix tailTrace_7969088
  have hstable : (prefixWord ++ tailWord_7969088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7969088).length < 2 ^ (prefixWord ++ tailWord_7969088).sum := by decide
  have hdescent : baseEnd_7969088 < baseStart_7969088 := by decide
  rcases family_descends (prefixWord ++ tailWord_7969088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7969095 : List Nat := [1, 1, 4, 1, 2, 2, 2, 1, 2, 4, 3]
def baseStart_7969095 : Nat := 118140960795 + 7969095 * 2 ^ 59
def prefixEnd_7969095 : Nat := 4983230072969 + 3 ^ 40 * 7969095 * 2
def baseEnd_7969095 : Nat := 4091976116341603612863305

theorem tailTrace_7969095 : CollatzResearch.WordTrace tailWord_7969095 prefixEnd_7969095 4091976116341603612863305 := by
  unfold tailWord_7969095
  simp only [CollatzResearch.WordTrace]
  refine ⟨290656773064337302915324739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193771182042891535276883159 290656773064337302915324739)
  ·
    refine ⟨435985159596505954372987109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290656773064337302915324739 435985159596505954372987109)
    ·
      refine ⟨81747217424344866444935083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 435985159596505954372987109 81747217424344866444935083)
      ·
        refine ⟨122620826136517299667402625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81747217424344866444935083 122620826136517299667402625)
        ·
          refine ⟨91965619602387974750551969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122620826136517299667402625 91965619602387974750551969)
          ·
            refine ⟨68974214701790981062913977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91965619602387974750551969 68974214701790981062913977)
            ·
              refine ⟨51730661026343235797185483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68974214701790981062913977 51730661026343235797185483)
              ·
                refine ⟨77595991539514853695778225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51730661026343235797185483 77595991539514853695778225)
                ·
                  refine ⟨58196993654636140271833669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77595991539514853695778225 58196993654636140271833669)
                  ·
                    refine ⟨10911936310244276300968813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58196993654636140271833669 10911936310244276300968813)
                    ·
                      refine ⟨4091976116341603612863305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10911936310244276300968813 4091976116341603612863305)
                      ·
                        rfl

theorem cell23_7969095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 2, 4, 3].length) (baseStart_7969095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7969095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7969095 prefixEnd_7969095 := by exact prefixLift 7969095
  have htrace : WordTrace (prefixWord ++ tailWord_7969095) baseStart_7969095 baseEnd_7969095 := by
    simpa [prefixWord, tailWord_7969095, baseEnd_7969095] using wordTrace_append hprefix tailTrace_7969095
  have hstable : (prefixWord ++ tailWord_7969095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7969095).length < 2 ^ (prefixWord ++ tailWord_7969095).sum := by decide
  have hdescent : baseEnd_7969095 < baseStart_7969095 := by decide
  rcases family_descends (prefixWord ++ tailWord_7969095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7969149 : List Nat := [1, 4, 1, 1, 2, 3, 4, 2, 5]
def baseStart_7969149 : Nat := 118140960795 + 7969149 * 2 ^ 59
def prefixEnd_7969149 : Nat := 4983230072969 + 3 ^ 40 * 7969149 * 2
def baseEnd_7969149 : Nat := 454667093810771822398673

theorem tailTrace_7969149 : CollatzResearch.WordTrace tailWord_7969149 prefixEnd_7969149 454667093810771822398673 := by
  unfold tailWord_7969149
  simp only [CollatzResearch.WordTrace]
  refine ⟨290658742606141670137790501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193772495070761113425193667 290658742606141670137790501)
  ·
    refine ⟨54498514238651563150835719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 290658742606141670137790501 54498514238651563150835719)
    ·
      refine ⟨81747771357977344726253579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54498514238651563150835719 81747771357977344726253579)
      ·
        refine ⟨122621657036966017089380369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81747771357977344726253579 122621657036966017089380369)
        ·
          refine ⟨91966242777724512817035277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122621657036966017089380369 91966242777724512817035277)
          ·
            refine ⟨34487341041646692306388229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91966242777724512817035277 34487341041646692306388229)
            ·
              refine ⟨6466376445308754807447793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34487341041646692306388229 6466376445308754807447793)
              ·
                refine ⟨4849782333981566105585845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6466376445308754807447793 4849782333981566105585845)
                ·
                  refine ⟨454667093810771822398673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4849782333981566105585845 454667093810771822398673)
                  ·
                    rfl

theorem cell23_7969149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 4, 2, 5].length) (baseStart_7969149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7969149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7969149 prefixEnd_7969149 := by exact prefixLift 7969149
  have htrace : WordTrace (prefixWord ++ tailWord_7969149) baseStart_7969149 baseEnd_7969149 := by
    simpa [prefixWord, tailWord_7969149, baseEnd_7969149] using wordTrace_append hprefix tailTrace_7969149
  have hstable : (prefixWord ++ tailWord_7969149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7969149).length < 2 ^ (prefixWord ++ tailWord_7969149).sum := by decide
  have hdescent : baseEnd_7969149 < baseStart_7969149 := by decide
  rcases family_descends (prefixWord ++ tailWord_7969149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7969194 : List Nat := [3, 1, 6, 1, 2, 1, 1, 2, 2, 2, 2]
def baseStart_7969194 : Nat := 118140960795 + 7969194 * 2 ^ 59
def prefixEnd_7969194 : Nat := 4983230072969 + 3 ^ 40 * 7969194 * 2
def baseEnd_7969194 : Nat := 4092026950926398725525351

theorem tailTrace_7969194 : CollatzResearch.WordTrace tailWord_7969194 prefixEnd_7969194 4092026950926398725525351 := by
  unfold tailWord_7969194
  simp only [CollatzResearch.WordTrace]
  refine ⟨72665095972744660705794659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193773589260652428548785757 72665095972744660705794659)
  ·
    refine ⟨108997643959116991058691989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72665095972744660705794659 108997643959116991058691989)
    ·
      refine ⟨5109264560583608955876187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 108997643959116991058691989 5109264560583608955876187)
      ·
        refine ⟨7663896840875413433814281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5109264560583608955876187 7663896840875413433814281)
        ·
          refine ⟨5747922630656560075360711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7663896840875413433814281 5747922630656560075360711)
          ·
            refine ⟨8621883945984840113041067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5747922630656560075360711 8621883945984840113041067)
            ·
              refine ⟨12932825918977260169561601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8621883945984840113041067 12932825918977260169561601)
              ·
                refine ⟨9699619439232945127171201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12932825918977260169561601 9699619439232945127171201)
                ·
                  refine ⟨7274714579424708845378401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9699619439232945127171201 7274714579424708845378401)
                  ·
                    refine ⟨5456035934568531634033801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7274714579424708845378401 5456035934568531634033801)
                    ·
                      refine ⟨4092026950926398725525351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5456035934568531634033801 4092026950926398725525351)
                      ·
                        rfl

theorem cell23_7969194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_7969194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7969194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7969194 prefixEnd_7969194 := by exact prefixLift 7969194
  have htrace : WordTrace (prefixWord ++ tailWord_7969194) baseStart_7969194 baseEnd_7969194 := by
    simpa [prefixWord, tailWord_7969194, baseEnd_7969194] using wordTrace_append hprefix tailTrace_7969194
  have hstable : (prefixWord ++ tailWord_7969194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7969194).length < 2 ^ (prefixWord ++ tailWord_7969194).sum := by decide
  have hdescent : baseEnd_7969194 < baseStart_7969194 := by decide
  rcases family_descends (prefixWord ++ tailWord_7969194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7969202 : List Nat := [3, 2, 1, 1, 1, 1, 4, 1, 4, 2, 3]
def baseStart_7969202 : Nat := 118140960795 + 7969202 * 2 ^ 59
def prefixEnd_7969202 : Nat := 4983230072969 + 3 ^ 40 * 7969202 * 2
def baseEnd_7969202 : Nat := 4092031058771634694225313

theorem tailTrace_7969202 : CollatzResearch.WordTrace tailWord_7969202 prefixEnd_7969202 4092031058771634694225313 := by
  unfold tailWord_7969202
  simp only [CollatzResearch.WordTrace]
  refine ⟨72665168918737415047367465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193773783783299773459646573 72665168918737415047367465)
  ·
    refine ⟨54498876689053061285525599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72665168918737415047367465 54498876689053061285525599)
    ·
      refine ⟨81748315033579591928288399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54498876689053061285525599 81748315033579591928288399)
      ·
        refine ⟨122622472550369387892432599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81748315033579591928288399 122622472550369387892432599)
        ·
          refine ⟨183933708825554081838648899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122622472550369387892432599 183933708825554081838648899)
          ·
            refine ⟨275900563238331122757973349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183933708825554081838648899 275900563238331122757973349)
            ·
              refine ⟨51731355607187085517120003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 275900563238331122757973349 51731355607187085517120003)
              ·
                refine ⟨77597033410780628275680005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51731355607187085517120003 77597033410780628275680005)
                ·
                  refine ⟨14549443764521367801690001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77597033410780628275680005 14549443764521367801690001)
                  ·
                    refine ⟨10912082823391025851267501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14549443764521367801690001 10912082823391025851267501)
                    ·
                      refine ⟨4092031058771634694225313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10912082823391025851267501 4092031058771634694225313)
                      ·
                        rfl

theorem cell23_7969202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 4, 2, 3].length) (baseStart_7969202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7969202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7969202 prefixEnd_7969202 := by exact prefixLift 7969202
  have htrace : WordTrace (prefixWord ++ tailWord_7969202) baseStart_7969202 baseEnd_7969202 := by
    simpa [prefixWord, tailWord_7969202, baseEnd_7969202] using wordTrace_append hprefix tailTrace_7969202
  have hstable : (prefixWord ++ tailWord_7969202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7969202).length < 2 ^ (prefixWord ++ tailWord_7969202).sum := by decide
  have hdescent : baseEnd_7969202 < baseStart_7969202 := by decide
  rcases family_descends (prefixWord ++ tailWord_7969202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7969209 : List Nat := [1, 2, 1, 4, 3, 2, 2, 1, 3, 4]
def baseStart_7969209 : Nat := 118140960795 + 7969209 * 2 ^ 59
def prefixEnd_7969209 : Nat := 4983230072969 + 3 ^ 40 * 7969209 * 2
def baseEnd_7969209 : Nat := 1364011551045405388945927

theorem tailTrace_7969209 : CollatzResearch.WordTrace tailWord_7969209 prefixEnd_7969209 1364011551045405388945927 := by
  unfold tailWord_7969209
  simp only [CollatzResearch.WordTrace]
  refine ⟨290660930985924300384974681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193773953990616200256649787 290660930985924300384974681)
  ·
    refine ⟨217995698239443225288731011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290660930985924300384974681 217995698239443225288731011)
    ·
      refine ⟨326993547359164837933096517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217995698239443225288731011 326993547359164837933096517)
      ·
        refine ⟨61311290129843407112455597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 326993547359164837933096517 61311290129843407112455597)
        ·
          refine ⟨22991733798691277667170849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61311290129843407112455597 22991733798691277667170849)
          ·
            refine ⟨17243800349018458250378137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22991733798691277667170849 17243800349018458250378137)
            ·
              refine ⟨12932850261763843687783603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17243800349018458250378137 12932850261763843687783603)
              ·
                refine ⟨19399275392645765531675405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12932850261763843687783603 19399275392645765531675405)
                ·
                  refine ⟨7274728272242162074378277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19399275392645765531675405 7274728272242162074378277)
                  ·
                    refine ⟨1364011551045405388945927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7274728272242162074378277 1364011551045405388945927)
                    ·
                      rfl

theorem cell23_7969209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 1, 3, 4].length) (baseStart_7969209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7969209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7969209 prefixEnd_7969209 := by exact prefixLift 7969209
  have htrace : WordTrace (prefixWord ++ tailWord_7969209) baseStart_7969209 baseEnd_7969209 := by
    simpa [prefixWord, tailWord_7969209, baseEnd_7969209] using wordTrace_append hprefix tailTrace_7969209
  have hstable : (prefixWord ++ tailWord_7969209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7969209).length < 2 ^ (prefixWord ++ tailWord_7969209).sum := by decide
  have hdescent : baseEnd_7969209 < baseStart_7969209 := by decide
  rcases family_descends (prefixWord ++ tailWord_7969209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7969235 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 9, 5]
def baseStart_7969235 : Nat := 118140960795 + 7969235 * 2 ^ 59
def prefixEnd_7969235 : Nat := 4983230072969 + 3 ^ 40 * 7969235 * 2
def baseEnd_7969235 : Nat := 1364016001211077688370887

theorem tailTrace_7969235 : CollatzResearch.WordTrace tailWord_7969235 prefixEnd_7969235 1364016001211077688370887 := by
  unfold tailWord_7969235
  simp only [CollatzResearch.WordTrace]
  refine ⟨290661879283830106825421159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193774586189220071216947439 290661879283830106825421159)
  ·
    refine ⟨435992818925745160238131739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290661879283830106825421159 435992818925745160238131739)
    ·
      refine ⟨653989228388617740357197609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435992818925745160238131739 653989228388617740357197609)
      ·
        refine ⟨490491921291463305267898207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 653989228388617740357197609 490491921291463305267898207)
        ·
          refine ⟨735737881937194957901847311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 490491921291463305267898207 735737881937194957901847311)
          ·
            refine ⟨1103606822905792436852770967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 735737881937194957901847311 1103606822905792436852770967)
            ·
              refine ⟨1655410234358688655279156451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1103606822905792436852770967 1655410234358688655279156451)
              ·
                refine ⟨2483115351538032982918734677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1655410234358688655279156451 2483115351538032982918734677)
                ·
                  refine ⟨14549504012918162009289461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 2483115351538032982918734677 14549504012918162009289461)
                  ·
                    refine ⟨1364016001211077688370887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14549504012918162009289461 1364016001211077688370887)
                    ·
                      rfl

theorem cell23_7969235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 9, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 9, 5].length) (baseStart_7969235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7969235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7969235 prefixEnd_7969235 := by exact prefixLift 7969235
  have htrace : WordTrace (prefixWord ++ tailWord_7969235) baseStart_7969235 baseEnd_7969235 := by
    simpa [prefixWord, tailWord_7969235, baseEnd_7969235] using wordTrace_append hprefix tailTrace_7969235
  have hstable : (prefixWord ++ tailWord_7969235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7969235).length < 2 ^ (prefixWord ++ tailWord_7969235).sum := by decide
  have hdescent : baseEnd_7969235 < baseStart_7969235 := by decide
  rcases family_descends (prefixWord ++ tailWord_7969235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7969259 : List Nat := [1, 1, 1, 1, 2, 3, 5, 2, 2, 3, 2]
def baseStart_7969259 : Nat := 118140960795 + 7969259 * 2 ^ 59
def prefixEnd_7969259 : Nat := 4983230072969 + 3 ^ 40 * 7969259 * 2
def baseEnd_7969259 : Nat := 4092060327168940971212551

theorem tailTrace_7969259 : CollatzResearch.WordTrace tailWord_7969259 prefixEnd_7969259 4092060327168940971212551 := by
  unfold tailWord_7969259
  simp only [CollatzResearch.WordTrace]
  refine ⟨290662754635743158924294831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193775169757162105949529887 290662754635743158924294831)
  ·
    refine ⟨435994131953614738386442247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290662754635743158924294831 435994131953614738386442247)
    ·
      refine ⟨653991197930422107579663371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435994131953614738386442247 653991197930422107579663371)
      ·
        refine ⟨980986796895633161369495057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 653991197930422107579663371 980986796895633161369495057)
        ·
          refine ⟨735740097671724871027121293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 980986796895633161369495057 735740097671724871027121293)
          ·
            refine ⟨275902536626896826635170485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 735740097671724871027121293 275902536626896826635170485)
            ·
              refine ⟨25865862808771577497047233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 275902536626896826635170485 25865862808771577497047233)
              ·
                refine ⟨19399397106578683122785425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25865862808771577497047233 19399397106578683122785425)
                ·
                  refine ⟨14549547829934012342089069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19399397106578683122785425 14549547829934012342089069)
                  ·
                    refine ⟨5456080436225254628283401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14549547829934012342089069 5456080436225254628283401)
                    ·
                      refine ⟨4092060327168940971212551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5456080436225254628283401 4092060327168940971212551)
                      ·
                        rfl

theorem cell23_7969259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 2, 2, 3, 2].length) (baseStart_7969259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7969259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7969259 prefixEnd_7969259 := by exact prefixLift 7969259
  have htrace : WordTrace (prefixWord ++ tailWord_7969259) baseStart_7969259 baseEnd_7969259 := by
    simpa [prefixWord, tailWord_7969259, baseEnd_7969259] using wordTrace_append hprefix tailTrace_7969259
  have hstable : (prefixWord ++ tailWord_7969259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7969259).length < 2 ^ (prefixWord ++ tailWord_7969259).sum := by decide
  have hdescent : baseEnd_7969259 < baseStart_7969259 := by decide
  rcases family_descends (prefixWord ++ tailWord_7969259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7969272 : List Nat := [2, 1, 2, 1, 1, 4, 2, 2, 3, 1, 4]
def baseStart_7969272 : Nat := 118140960795 + 7969272 * 2 ^ 59
def prefixEnd_7969272 : Nat := 4983230072969 + 3 ^ 40 * 7969272 * 2
def baseEnd_7969272 : Nat := 4092067002417449420349991

theorem tailTrace_7969272 : CollatzResearch.WordTrace tailWord_7969272 prefixEnd_7969272 4092067002417449420349991 := by
  unfold tailWord_7969272
  simp only [CollatzResearch.WordTrace]
  refine ⟨145331614392348031072259035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193775485856464041429678713 145331614392348031072259035)
  ·
    refine ⟨217997421588522046608388553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145331614392348031072259035 217997421588522046608388553)
    ·
      refine ⟨163498066191391534956291415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217997421588522046608388553 163498066191391534956291415)
      ·
        refine ⟨245247099287087302434437123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163498066191391534956291415 245247099287087302434437123)
        ·
          refine ⟨367870648930630953651655685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245247099287087302434437123 367870648930630953651655685)
          ·
            refine ⟨68975746674493303809685441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 367870648930630953651655685 68975746674493303809685441)
            ·
              refine ⟨51731810005869977857264081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68975746674493303809685441 51731810005869977857264081)
              ·
                refine ⟨38798857504402483392948061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51731810005869977857264081 38798857504402483392948061)
                ·
                  refine ⟨14549571564150931272355523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38798857504402483392948061 14549571564150931272355523)
                  ·
                    refine ⟨21824357346226396908533285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14549571564150931272355523 21824357346226396908533285)
                    ·
                      refine ⟨4092067002417449420349991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21824357346226396908533285 4092067002417449420349991)
                      ·
                        rfl

theorem cell23_7969272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 2, 3, 1, 4].length) (baseStart_7969272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7969272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7969272 prefixEnd_7969272 := by exact prefixLift 7969272
  have htrace : WordTrace (prefixWord ++ tailWord_7969272) baseStart_7969272 baseEnd_7969272 := by
    simpa [prefixWord, tailWord_7969272, baseEnd_7969272] using wordTrace_append hprefix tailTrace_7969272
  have hstable : (prefixWord ++ tailWord_7969272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7969272).length < 2 ^ (prefixWord ++ tailWord_7969272).sum := by decide
  have hdescent : baseEnd_7969272 < baseStart_7969272 := by decide
  rcases family_descends (prefixWord ++ tailWord_7969272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7969303 : List Nat := [1, 1, 3, 6, 1, 1, 3, 1, 1, 5]
def baseStart_7969303 : Nat := 118140960795 + 7969303 * 2 ^ 59
def prefixEnd_7969303 : Nat := 4983230072969 + 3 ^ 40 * 7969303 * 2
def baseEnd_7969303 : Nat := 1364027640105912933020783

theorem tailTrace_7969303 : CollatzResearch.WordTrace tailWord_7969303 prefixEnd_7969303 1364027640105912933020783 := by
  unfold tailWord_7969303
  simp only [CollatzResearch.WordTrace]
  refine ⟨290664359447583754438896563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193776239631722502959264375 290664359447583754438896563)
  ·
    refine ⟨435996539171375631658344845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290664359447583754438896563 435996539171375631658344845)
    ·
      refine ⟨163498702189265861871879317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 435996539171375631658344845 163498702189265861871879317)
      ·
        refine ⟨7664001665121837275244343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 163498702189265861871879317 7664001665121837275244343)
        ·
          refine ⟨11496002497682755912866515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7664001665121837275244343 11496002497682755912866515)
          ·
            refine ⟨17244003746524133869299773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11496002497682755912866515 17244003746524133869299773)
            ·
              refine ⟨6466501404946550200987415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17244003746524133869299773 6466501404946550200987415)
              ·
                refine ⟨9699752107419825301481123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6466501404946550200987415 9699752107419825301481123)
                ·
                  refine ⟨14549628161129737952221685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9699752107419825301481123 14549628161129737952221685)
                  ·
                    refine ⟨1364027640105912933020783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14549628161129737952221685 1364027640105912933020783)
                    ·
                      rfl

theorem cell23_7969303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 3, 1, 1, 5].length) (baseStart_7969303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7969303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7969303 prefixEnd_7969303 := by exact prefixLift 7969303
  have htrace : WordTrace (prefixWord ++ tailWord_7969303) baseStart_7969303 baseEnd_7969303 := by
    simpa [prefixWord, tailWord_7969303, baseEnd_7969303] using wordTrace_append hprefix tailTrace_7969303
  have hstable : (prefixWord ++ tailWord_7969303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7969303).length < 2 ^ (prefixWord ++ tailWord_7969303).sum := by decide
  have hdescent : baseEnd_7969303 < baseStart_7969303 := by decide
  rcases family_descends (prefixWord ++ tailWord_7969303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7969309 : List Nat := [1, 4, 2, 2, 1, 2, 3, 1, 1, 1, 5]
def baseStart_7969309 : Nat := 118140960795 + 7969309 * 2 ^ 59
def prefixEnd_7969309 : Nat := 4983230072969 + 3 ^ 40 * 7969309 * 2
def baseEnd_7969309 : Nat := 4092086001201665775587321

theorem tailTrace_7969309 : CollatzResearch.WordTrace tailWord_7969309 prefixEnd_7969309 4092086001201665775587321 := by
  unfold tailWord_7969309
  simp only [CollatzResearch.WordTrace]
  refine ⟨290664578285562017463614981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193776385523708011642409987 290664578285562017463614981)
  ·
    refine ⟨54499608428542878274427809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 290664578285562017463614981 54499608428542878274427809)
    ·
      refine ⟨40874706321407158705820857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54499608428542878274427809 40874706321407158705820857)
      ·
        refine ⟨30656029741055369029365643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40874706321407158705820857 30656029741055369029365643)
        ·
          refine ⟨45984044611583053544048465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30656029741055369029365643 45984044611583053544048465)
          ·
            refine ⟨34488033458687290158036349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45984044611583053544048465 34488033458687290158036349)
            ·
              refine ⟨12933012547007733809263631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34488033458687290158036349 12933012547007733809263631)
              ·
                refine ⟨19399518820511600713895447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12933012547007733809263631 19399518820511600713895447)
                ·
                  refine ⟨29099278230767401070843171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19399518820511600713895447 29099278230767401070843171)
                  ·
                    refine ⟨43648917346151101606264757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29099278230767401070843171 43648917346151101606264757)
                    ·
                      refine ⟨4092086001201665775587321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43648917346151101606264757 4092086001201665775587321)
                      ·
                        rfl

theorem cell23_7969309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_7969309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7969309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7969309 prefixEnd_7969309 := by exact prefixLift 7969309
  have htrace : WordTrace (prefixWord ++ tailWord_7969309) baseStart_7969309 baseEnd_7969309 := by
    simpa [prefixWord, tailWord_7969309, baseEnd_7969309] using wordTrace_append hprefix tailTrace_7969309
  have hstable : (prefixWord ++ tailWord_7969309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7969309).length < 2 ^ (prefixWord ++ tailWord_7969309).sum := by decide
  have hdescent : baseEnd_7969309 < baseStart_7969309 := by decide
  rcases family_descends (prefixWord ++ tailWord_7969309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7969312 : List Nat := [2, 1, 1, 6, 2, 11]
def baseStart_7969312 : Nat := 118140960795 + 7969312 * 2 ^ 59
def prefixEnd_7969312 : Nat := 4983230072969 + 3 ^ 40 * 7969312 * 2
def baseEnd_7969312 : Nat := 16839866426516992855349

theorem tailTrace_7969312 : CollatzResearch.WordTrace tailWord_7969312 prefixEnd_7969312 16839866426516992855349 := by
  unfold tailWord_7969312
  simp only [CollatzResearch.WordTrace]
  refine ⟨145332343852275574487987095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193776458469700765983982793 145332343852275574487987095)
  ·
    refine ⟨217998515778413361731980643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145332343852275574487987095 217998515778413361731980643)
    ·
      refine ⟨326997773667620042597970965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217998515778413361731980643 326997773667620042597970965)
      ·
        refine ⟨15328020640669689496779889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 326997773667620042597970965 15328020640669689496779889)
        ·
          refine ⟨11496015480502267122584917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15328020640669689496779889 11496015480502267122584917)
          ·
            refine ⟨16839866426516992855349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 11496015480502267122584917 16839866426516992855349)
            ·
              rfl

theorem cell23_7969312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 11].length) (baseStart_7969312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7969312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7969312 prefixEnd_7969312 := by exact prefixLift 7969312
  have htrace : WordTrace (prefixWord ++ tailWord_7969312) baseStart_7969312 baseEnd_7969312 := by
    simpa [prefixWord, tailWord_7969312, baseEnd_7969312] using wordTrace_append hprefix tailTrace_7969312
  have hstable : (prefixWord ++ tailWord_7969312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7969312).length < 2 ^ (prefixWord ++ tailWord_7969312).sum := by decide
  have hdescent : baseEnd_7969312 < baseStart_7969312 := by decide
  rcases family_descends (prefixWord ++ tailWord_7969312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7969357 : List Nat := [1, 6, 1, 1, 2, 2, 2, 3, 1, 2, 2]
def baseStart_7969357 : Nat := 118140960795 + 7969357 * 2 ^ 59
def prefixEnd_7969357 : Nat := 4983230072969 + 3 ^ 40 * 7969357 * 2
def baseEnd_7969357 : Nat := 4092110648273081587787101

theorem tailTrace_7969357 : CollatzResearch.WordTrace tailWord_7969357 prefixEnd_7969357 4092110648273081587787101 := by
  unfold tailWord_7969357
  simp only [CollatzResearch.WordTrace]
  refine ⟨290666328989388121661362325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193777552659592081107574883 290666328989388121661362325)
  ·
    refine ⟨13624984171377568202876359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 290666328989388121661362325 13624984171377568202876359)
    ·
      refine ⟨20437476257066352304314539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13624984171377568202876359 20437476257066352304314539)
      ·
        refine ⟨30656214385599528456471809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20437476257066352304314539 30656214385599528456471809)
        ·
          refine ⟨22992160789199646342353857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30656214385599528456471809 22992160789199646342353857)
          ·
            refine ⟨17244120591899734756765393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22992160789199646342353857 17244120591899734756765393)
            ·
              refine ⟨12933090443924801067574045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17244120591899734756765393 12933090443924801067574045)
              ·
                refine ⟨4849908916471800400340267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12933090443924801067574045 4849908916471800400340267)
                ·
                  refine ⟨7274863374707700600510401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4849908916471800400340267 7274863374707700600510401)
                  ·
                    refine ⟨5456147531030775450382801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7274863374707700600510401 5456147531030775450382801)
                    ·
                      refine ⟨4092110648273081587787101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5456147531030775450382801 4092110648273081587787101)
                      ·
                        rfl

theorem cell23_7969357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 3, 1, 2, 2].length) (baseStart_7969357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7969357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7969357 prefixEnd_7969357 := by exact prefixLift 7969357
  have htrace : WordTrace (prefixWord ++ tailWord_7969357) baseStart_7969357 baseEnd_7969357 := by
    simpa [prefixWord, tailWord_7969357, baseEnd_7969357] using wordTrace_append hprefix tailTrace_7969357
  have hstable : (prefixWord ++ tailWord_7969357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7969357).length < 2 ^ (prefixWord ++ tailWord_7969357).sum := by decide
  have hdescent : baseEnd_7969357 < baseStart_7969357 := by decide
  rcases family_descends (prefixWord ++ tailWord_7969357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7969374 : List Nat := [4, 4, 1, 2, 1, 1, 2, 1, 3, 2, 2]
def baseStart_7969374 : Nat := 118140960795 + 7969374 * 2 ^ 59
def prefixEnd_7969374 : Nat := 4983230072969 + 3 ^ 40 * 7969374 * 2
def baseEnd_7969374 : Nat := 4092119377444208021274523

theorem tailTrace_7969374 : CollatzResearch.WordTrace tailWord_7969374 prefixEnd_7969374 4092119377444208021274523 := by
  unfold tailWord_7969374
  simp only [CollatzResearch.WordTrace]
  refine ⟨36333368628790816695591397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193777966020217689043154117 36333368628790816695591397)
  ·
    refine ⟨6812506617898278130423387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36333368628790816695591397 6812506617898278130423387)
    ·
      refine ⟨10218759926847417195635081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6812506617898278130423387 10218759926847417195635081)
      ·
        refine ⟨7664069945135562896726311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10218759926847417195635081 7664069945135562896726311)
        ·
          refine ⟨11496104917703344345089467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7664069945135562896726311 11496104917703344345089467)
          ·
            refine ⟨17244157376555016517634201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11496104917703344345089467 17244157376555016517634201)
            ·
              refine ⟨12933118032416262388225651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17244157376555016517634201 12933118032416262388225651)
              ·
                refine ⟨19399677048624393582338477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12933118032416262388225651 19399677048624393582338477)
                ·
                  refine ⟨7274878893234147593376929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19399677048624393582338477 7274878893234147593376929)
                  ·
                    refine ⟨5456159169925610695032697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7274878893234147593376929 5456159169925610695032697)
                    ·
                      refine ⟨4092119377444208021274523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5456159169925610695032697 4092119377444208021274523)
                      ·
                        rfl

theorem cell23_7969374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_7969374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7969374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7969374 prefixEnd_7969374 := by exact prefixLift 7969374
  have htrace : WordTrace (prefixWord ++ tailWord_7969374) baseStart_7969374 baseEnd_7969374 := by
    simpa [prefixWord, tailWord_7969374, baseEnd_7969374] using wordTrace_append hprefix tailTrace_7969374
  have hstable : (prefixWord ++ tailWord_7969374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7969374).length < 2 ^ (prefixWord ++ tailWord_7969374).sum := by decide
  have hdescent : baseEnd_7969374 < baseStart_7969374 := by decide
  rcases family_descends (prefixWord ++ tailWord_7969374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7969389 : List Nat := [1, 5, 1, 1, 3, 1, 2, 1, 2, 6]
def baseStart_7969389 : Nat := 118140960795 + 7969389 * 2 ^ 59
def prefixEnd_7969389 : Nat := 4983230072969 + 3 ^ 40 * 7969389 * 2
def baseEnd_7969389 : Nat := 1364042359884675154195651

theorem tailTrace_7969389 : CollatzResearch.WordTrace tailWord_7969389 prefixEnd_7969389 1364042359884675154195651 := by
  unfold tailWord_7969389
  simp only [CollatzResearch.WordTrace]
  refine ⟨290667496125272191126527221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193778330750181460751018147 290667496125272191126527221)
  ·
    refine ⟨27250077761744267918111927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 290667496125272191126527221 27250077761744267918111927)
    ·
      refine ⟨40875116642616401877167891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27250077761744267918111927 40875116642616401877167891)
      ·
        refine ⟨61312674963924602815751837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40875116642616401877167891 61312674963924602815751837)
        ·
          refine ⟨22992253111471726055906939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61312674963924602815751837 22992253111471726055906939)
          ·
            refine ⟨34488379667207589083860409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22992253111471726055906939 34488379667207589083860409)
            ·
              refine ⟨25866284750405691812895307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34488379667207589083860409 25866284750405691812895307)
              ·
                refine ⟨38799427125608537719342961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25866284750405691812895307 38799427125608537719342961)
                ·
                  refine ⟨29099570344206403289507221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38799427125608537719342961 29099570344206403289507221)
                  ·
                    refine ⟨1364042359884675154195651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29099570344206403289507221 1364042359884675154195651)
                    ·
                      rfl

theorem cell23_7969389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 1, 2, 6].length) (baseStart_7969389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7969389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7969389 prefixEnd_7969389 := by exact prefixLift 7969389
  have htrace : WordTrace (prefixWord ++ tailWord_7969389) baseStart_7969389 baseEnd_7969389 := by
    simpa [prefixWord, tailWord_7969389, baseEnd_7969389] using wordTrace_append hprefix tailTrace_7969389
  have hstable : (prefixWord ++ tailWord_7969389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7969389).length < 2 ^ (prefixWord ++ tailWord_7969389).sum := by decide
  have hdescent : baseEnd_7969389 < baseStart_7969389 := by decide
  rcases family_descends (prefixWord ++ tailWord_7969389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7969390 : List Nat := [4, 1, 2, 2, 2, 2, 3, 1, 2, 1, 3]
def baseStart_7969390 : Nat := 118140960795 + 7969390 * 2 ^ 59
def prefixEnd_7969390 : Nat := 4983230072969 + 3 ^ 40 * 7969390 * 2
def baseEnd_7969390 : Nat := 4092127593134679958674449

theorem tailTrace_7969390 : CollatzResearch.WordTrace tailWord_7969390 prefixEnd_7969390 4092127593134679958674449 := by
  unfold tailWord_7969390
  simp only [CollatzResearch.WordTrace]
  refine ⟨36333441574783571037164203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193778355065512378864875749 36333441574783571037164203)
  ·
    refine ⟨54500162362175356555746305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36333441574783571037164203 54500162362175356555746305)
    ·
      refine ⟨40875121771631517416809729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54500162362175356555746305 40875121771631517416809729)
      ·
        refine ⟨30656341328723638062607297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40875121771631517416809729 30656341328723638062607297)
        ·
          refine ⟨22992255996542728546955473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30656341328723638062607297 22992255996542728546955473)
          ·
            refine ⟨17244191997407046410216605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22992255996542728546955473 17244191997407046410216605)
            ·
              refine ⟨6466571999027642403831227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17244191997407046410216605 6466571999027642403831227)
              ·
                refine ⟨9699857998541463605746841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6466571999027642403831227 9699857998541463605746841)
                ·
                  refine ⟨7274893498906097704310131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9699857998541463605746841 7274893498906097704310131)
                  ·
                    refine ⟨10912340248359146556465197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7274893498906097704310131 10912340248359146556465197)
                    ·
                      refine ⟨4092127593134679958674449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10912340248359146556465197 4092127593134679958674449)
                      ·
                        rfl

theorem cell23_7969390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 3, 1, 2, 1, 3].length) (baseStart_7969390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7969390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7969390 prefixEnd_7969390 := by exact prefixLift 7969390
  have htrace : WordTrace (prefixWord ++ tailWord_7969390) baseStart_7969390 baseEnd_7969390 := by
    simpa [prefixWord, tailWord_7969390, baseEnd_7969390] using wordTrace_append hprefix tailTrace_7969390
  have hstable : (prefixWord ++ tailWord_7969390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7969390).length < 2 ^ (prefixWord ++ tailWord_7969390).sum := by decide
  have hdescent : baseEnd_7969390 < baseStart_7969390 := by decide
  rcases family_descends (prefixWord ++ tailWord_7969390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7969419 : List Nat := [1, 1, 1, 1, 4, 1, 2, 7, 5]
def baseStart_7969419 : Nat := 118140960795 + 7969419 * 2 ^ 59
def prefixEnd_7969419 : Nat := 4983230072969 + 3 ^ 40 * 7969419 * 2
def baseEnd_7969419 : Nat := 454682498230406705023535

theorem tailTrace_7969419 : CollatzResearch.WordTrace tailWord_7969419 prefixEnd_7969419 454682498230406705023535 := by
  unfold tailWord_7969419
  simp only [CollatzResearch.WordTrace]
  refine ⟨290668590315163506250119311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193779060210109004166746207 290668590315163506250119311)
  ·
    refine ⟨436002885472745259375178967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290668590315163506250119311 436002885472745259375178967)
    ·
      refine ⟨654004328209117889062768451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436002885472745259375178967 654004328209117889062768451)
      ·
        refine ⟨981006492313676833594152677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 654004328209117889062768451 981006492313676833594152677)
        ·
          refine ⟨183938717308814406298903627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 981006492313676833594152677 183938717308814406298903627)
          ·
            refine ⟨275908075963221609448355441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183938717308814406298903627 275908075963221609448355441)
            ·
              refine ⟨206931056972416207086266581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 275908075963221609448355441 206931056972416207086266581)
              ·
                refine ⟨4849946647791004853584373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 206931056972416207086266581 4849946647791004853584373)
                ·
                  refine ⟨454682498230406705023535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4849946647791004853584373 454682498230406705023535)
                  ·
                    rfl

theorem cell23_7969419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 7, 5].length) (baseStart_7969419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7969419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7969419 prefixEnd_7969419 := by exact prefixLift 7969419
  have htrace : WordTrace (prefixWord ++ tailWord_7969419) baseStart_7969419 baseEnd_7969419 := by
    simpa [prefixWord, tailWord_7969419, baseEnd_7969419] using wordTrace_append hprefix tailTrace_7969419
  have hstable : (prefixWord ++ tailWord_7969419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7969419).length < 2 ^ (prefixWord ++ tailWord_7969419).sum := by decide
  have hdescent : baseEnd_7969419 < baseStart_7969419 := by decide
  rcases family_descends (prefixWord ++ tailWord_7969419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7969436 : List Nat := [2, 2, 3, 2, 2, 3, 1, 1, 7]
def baseStart_7969436 : Nat := 118140960795 + 7969436 * 2 ^ 59
def prefixEnd_7969436 : Nat := 4983230072969 + 3 ^ 40 * 7969436 * 2
def baseEnd_7969436 : Nat := 454683468138309642077693

theorem tailTrace_7969436 : CollatzResearch.WordTrace tailWord_7969436 prefixEnd_7969436 454683468138309642077693 := by
  unfold tailWord_7969436
  simp only [CollatzResearch.WordTrace]
  refine ⟨145334605178050959076744081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193779473570734612102325441 145334605178050959076744081)
  ·
    refine ⟨109000953883538219307558061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145334605178050959076744081 109000953883538219307558061)
    ·
      refine ⟨40875357706326832240334273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109000953883538219307558061 40875357706326832240334273)
      ·
        refine ⟨30656518279745124180250705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40875357706326832240334273 30656518279745124180250705)
        ·
          refine ⟨22992388709808843135188029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30656518279745124180250705 22992388709808843135188029)
          ·
            refine ⟨8622145766178316175695511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22992388709808843135188029 8622145766178316175695511)
            ·
              refine ⟨12933218649267474263543267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8622145766178316175695511 12933218649267474263543267)
              ·
                refine ⟨19399827973901211395314901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12933218649267474263543267 19399827973901211395314901)
                ·
                  refine ⟨454683468138309642077693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19399827973901211395314901 454683468138309642077693)
                  ·
                    rfl

theorem cell23_7969436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 1, 7].length) (baseStart_7969436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7969436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7969436 prefixEnd_7969436 := by exact prefixLift 7969436
  have htrace : WordTrace (prefixWord ++ tailWord_7969436) baseStart_7969436 baseEnd_7969436 := by
    simpa [prefixWord, tailWord_7969436, baseEnd_7969436] using wordTrace_append hprefix tailTrace_7969436
  have hstable : (prefixWord ++ tailWord_7969436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7969436).length < 2 ^ (prefixWord ++ tailWord_7969436).sum := by decide
  have hdescent : baseEnd_7969436 < baseStart_7969436 := by decide
  rcases family_descends (prefixWord ++ tailWord_7969436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7969447 : List Nat := [1, 1, 6, 3, 1, 1, 1, 3, 2, 2, 2]
def baseStart_7969447 : Nat := 118140960795 + 7969447 * 2 ^ 59
def prefixEnd_7969447 : Nat := 4983230072969 + 3 ^ 40 * 7969447 * 2
def baseEnd_7969447 : Nat := 4092156861531986235661687

theorem tailTrace_7969447 : CollatzResearch.WordTrace tailWord_7969447 prefixEnd_7969447 4092156861531986235661687 := by
  unfold tailWord_7969447
  simp only [CollatzResearch.WordTrace]
  refine ⟨290669611559062067032138595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193779741039374711354759063 290669611559062067032138595)
  ·
    refine ⟨436004417338593100548207893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290669611559062067032138595 436004417338593100548207893)
    ·
      refine ⟨20437707062746551588197245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 436004417338593100548207893 20437707062746551588197245)
      ·
        refine ⟨7664140148529956845573967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20437707062746551588197245 7664140148529956845573967)
        ·
          refine ⟨11496210222794935268360951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7664140148529956845573967 11496210222794935268360951)
          ·
            refine ⟨17244315334192402902541427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11496210222794935268360951 17244315334192402902541427)
            ·
              refine ⟨25866473001288604353812141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17244315334192402902541427 25866473001288604353812141)
              ·
                refine ⟨9699927375483226632679553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25866473001288604353812141 9699927375483226632679553)
                ·
                  refine ⟨7274945531612419974509665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9699927375483226632679553 7274945531612419974509665)
                  ·
                    refine ⟨5456209148709314980882249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7274945531612419974509665 5456209148709314980882249)
                    ·
                      refine ⟨4092156861531986235661687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5456209148709314980882249 4092156861531986235661687)
                      ·
                        rfl

theorem cell23_7969447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_7969447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7969447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7969447 prefixEnd_7969447 := by exact prefixLift 7969447
  have htrace : WordTrace (prefixWord ++ tailWord_7969447) baseStart_7969447 baseEnd_7969447 := by
    simpa [prefixWord, tailWord_7969447, baseEnd_7969447] using wordTrace_append hprefix tailTrace_7969447
  have hstable : (prefixWord ++ tailWord_7969447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7969447).length < 2 ^ (prefixWord ++ tailWord_7969447).sum := by decide
  have hdescent : baseEnd_7969447 < baseStart_7969447 := by decide
  rcases family_descends (prefixWord ++ tailWord_7969447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7969479 : List Nat := [1, 1, 4, 1, 1, 1, 2, 1, 7, 4]
def baseStart_7969479 : Nat := 118140960795 + 7969479 * 2 ^ 59
def prefixEnd_7969479 : Nat := 4983230072969 + 3 ^ 40 * 7969479 * 2
def baseEnd_7969479 : Nat := 1364057764304310036820513

theorem tailTrace_7969479 : CollatzResearch.WordTrace tailWord_7969479 prefixEnd_7969479 1364057764304310036820513 := by
  unfold tailWord_7969479
  simp only [CollatzResearch.WordTrace]
  refine ⟨290670778694946136497303491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193780519129964090998202327 290670778694946136497303491)
  ·
    refine ⟨436006168042419204745955237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290670778694946136497303491 436006168042419204745955237)
    ·
      refine ⟨81751156507953600889866607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 436006168042419204745955237 81751156507953600889866607)
      ·
        refine ⟨122626734761930401334799911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81751156507953600889866607 122626734761930401334799911)
        ·
          refine ⟨183940102142895602002199867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122626734761930401334799911 183940102142895602002199867)
          ·
            refine ⟨275910153214343403003299801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183940102142895602002199867 275910153214343403003299801)
            ·
              refine ⟨206932614910757552252474851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 275910153214343403003299801 206932614910757552252474851)
              ·
                refine ⟨310398922366136328378712277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206932614910757552252474851 310398922366136328378712277)
                ·
                  refine ⟨7274974742956320196376069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 310398922366136328378712277 7274974742956320196376069)
                  ·
                    refine ⟨1364057764304310036820513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7274974742956320196376069 1364057764304310036820513)
                    ·
                      rfl

theorem cell23_7969479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 7, 4].length) (baseStart_7969479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7969479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7969479 prefixEnd_7969479 := by exact prefixLift 7969479
  have htrace : WordTrace (prefixWord ++ tailWord_7969479) baseStart_7969479 baseEnd_7969479 := by
    simpa [prefixWord, tailWord_7969479, baseEnd_7969479] using wordTrace_append hprefix tailTrace_7969479
  have hstable : (prefixWord ++ tailWord_7969479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7969479).length < 2 ^ (prefixWord ++ tailWord_7969479).sum := by decide
  have hdescent : baseEnd_7969479 < baseStart_7969479 := by decide
  rcases family_descends (prefixWord ++ tailWord_7969479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7969486 : List Nat := [4, 1, 1, 1, 3, 2, 2, 2, 2, 1, 4]
def baseStart_7969486 : Nat := 118140960795 + 7969486 * 2 ^ 59
def prefixEnd_7969486 : Nat := 4983230072969 + 3 ^ 40 * 7969486 * 2
def baseEnd_7969486 : Nat := 4092176887277511583074007

theorem tailTrace_7969486 : CollatzResearch.WordTrace tailWord_7969486 prefixEnd_7969486 4092176887277511583074007 := by
  unfold tailWord_7969486
  simp only [CollatzResearch.WordTrace]
  refine ⟨36333879250740097086601039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193780689337280517795205541 36333879250740097086601039)
  ·
    refine ⟨54500818876110145629901559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36333879250740097086601039 54500818876110145629901559)
    ·
      refine ⟨81751228314165218444852339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54500818876110145629901559 81751228314165218444852339)
      ·
        refine ⟨122626842471247827667278509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81751228314165218444852339 122626842471247827667278509)
        ·
          refine ⟨45985065926717935375229441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122626842471247827667278509 45985065926717935375229441)
          ·
            refine ⟨34488799445038451531422081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45985065926717935375229441 34488799445038451531422081)
            ·
              refine ⟨25866599583778838648566561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34488799445038451531422081 25866599583778838648566561)
              ·
                refine ⟨19399949687834128986424921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25866599583778838648566561 19399949687834128986424921)
                ·
                  refine ⟨14549962265875596739818691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19399949687834128986424921 14549962265875596739818691)
                  ·
                    refine ⟨21824943398813395109728037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14549962265875596739818691 21824943398813395109728037)
                    ·
                      refine ⟨4092176887277511583074007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21824943398813395109728037 4092176887277511583074007)
                      ·
                        rfl

theorem cell23_7969486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 2, 2, 1, 4].length) (baseStart_7969486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7969486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7969486 prefixEnd_7969486 := by exact prefixLift 7969486
  have htrace : WordTrace (prefixWord ++ tailWord_7969486) baseStart_7969486 baseEnd_7969486 := by
    simpa [prefixWord, tailWord_7969486, baseEnd_7969486] using wordTrace_append hprefix tailTrace_7969486
  have hstable : (prefixWord ++ tailWord_7969486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7969486).length < 2 ^ (prefixWord ++ tailWord_7969486).sum := by decide
  have hdescent : baseEnd_7969486 < baseStart_7969486 := by decide
  rcases family_descends (prefixWord ++ tailWord_7969486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7969543 : List Nat := [1, 1, 4, 4, 1, 3, 1, 2, 6]
def baseStart_7969543 : Nat := 118140960795 + 7969543 * 2 ^ 59
def prefixEnd_7969543 : Nat := 4983230072969 + 3 ^ 40 * 7969543 * 2
def baseEnd_7969543 : Nat := 454689572852757540006805

theorem tailTrace_7969543 : CollatzResearch.WordTrace tailWord_7969543 prefixEnd_7969543 454689572852757540006805 := by
  unfold tailWord_7969543
  simp only [CollatzResearch.WordTrace]
  refine ⟨290673112966714275427633283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193782075311142850285088855 290673112966714275427633283)
  ·
    refine ⟨436009669450071413141449925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290673112966714275427633283 436009669450071413141449925)
    ·
      refine ⟨81751813021888389964021861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 436009669450071413141449925 81751813021888389964021861)
      ·
        refine ⟨15328464941604073118254099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81751813021888389964021861 15328464941604073118254099)
        ·
          refine ⟨22992697412406109677381149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15328464941604073118254099 22992697412406109677381149)
          ·
            refine ⟨8622261529652291129017931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22992697412406109677381149 8622261529652291129017931)
            ·
              refine ⟨12933392294478436693526897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8622261529652291129017931 12933392294478436693526897)
              ·
                refine ⟨9700044220858827520145173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12933392294478436693526897 9700044220858827520145173)
                ·
                  refine ⟨454689572852757540006805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9700044220858827520145173 454689572852757540006805)
                  ·
                    rfl

theorem cell23_7969543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 2, 6].length) (baseStart_7969543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7969543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7969543 prefixEnd_7969543 := by exact prefixLift 7969543
  have htrace : WordTrace (prefixWord ++ tailWord_7969543) baseStart_7969543 baseEnd_7969543 := by
    simpa [prefixWord, tailWord_7969543, baseEnd_7969543] using wordTrace_append hprefix tailTrace_7969543
  have hstable : (prefixWord ++ tailWord_7969543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7969543).length < 2 ^ (prefixWord ++ tailWord_7969543).sum := by decide
  have hdescent : baseEnd_7969543 < baseStart_7969543 := by decide
  rcases family_descends (prefixWord ++ tailWord_7969543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7969581 : List Nat := [1, 5, 3, 2, 2, 1, 1, 3, 1, 4]
def baseStart_7969581 : Nat := 118140960795 + 7969581 * 2 ^ 59
def prefixEnd_7969581 : Nat := 4983230072969 + 3 ^ 40 * 7969581 * 2
def baseEnd_7969581 : Nat := 1364075222646562903795357

theorem tailTrace_7969581 : CollatzResearch.WordTrace tailWord_7969581 prefixEnd_7969581 1364075222646562903795357 := by
  unfold tailWord_7969581
  simp only [CollatzResearch.WordTrace]
  refine ⟨290674498940576607917516597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193782999293717738611677731 290674498940576607917516597)
  ·
    refine ⟨27250734275679056992267181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 290674498940576607917516597 27250734275679056992267181)
    ·
      refine ⟨10219025353379646372100193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27250734275679056992267181 10219025353379646372100193)
      ·
        refine ⟨7664269015034734779075145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10219025353379646372100193 7664269015034734779075145)
        ·
          refine ⟨5748201761276051084306359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7664269015034734779075145 5748201761276051084306359)
          ·
            refine ⟨8622302641914076626459539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5748201761276051084306359 8622302641914076626459539)
            ·
              refine ⟨12933453962871114939689309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8622302641914076626459539 12933453962871114939689309)
              ·
                refine ⟨4850045236076668102383491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12933453962871114939689309 4850045236076668102383491)
                ·
                  refine ⟨7275067854115002153575237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4850045236076668102383491 7275067854115002153575237)
                  ·
                    refine ⟨1364075222646562903795357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7275067854115002153575237 1364075222646562903795357)
                    ·
                      rfl

theorem cell23_7969581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_7969581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7969581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7969581 prefixEnd_7969581 := by exact prefixLift 7969581
  have htrace : WordTrace (prefixWord ++ tailWord_7969581) baseStart_7969581 baseEnd_7969581 := by
    simpa [prefixWord, tailWord_7969581, baseEnd_7969581] using wordTrace_append hprefix tailTrace_7969581
  have hstable : (prefixWord ++ tailWord_7969581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7969581).length < 2 ^ (prefixWord ++ tailWord_7969581).sum := by decide
  have hdescent : baseEnd_7969581 < baseStart_7969581 := by decide
  rcases family_descends (prefixWord ++ tailWord_7969581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7969586 : List Nat := [3, 2, 1, 1, 3, 1, 1, 1, 6, 4]
def baseStart_7969586 : Nat := 118140960795 + 7969586 * 2 ^ 59
def prefixEnd_7969586 : Nat := 4983230072969 + 3 ^ 40 * 7969586 * 2
def baseEnd_7969586 : Nat := 1364076078447653730607849

theorem tailTrace_7969586 : CollatzResearch.WordTrace tailWord_7969586 prefixEnd_7969586 1364076078447653730607849 := by
  unfold tailWord_7969586
  simp only [CollatzResearch.WordTrace]
  refine ⟨72668670326389623442862153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193783120870372329180965741 72668670326389623442862153)
  ·
    refine ⟨54501502744792217582146615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72668670326389623442862153 54501502744792217582146615)
    ·
      refine ⟨81752254117188326373219923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54501502744792217582146615 81752254117188326373219923)
      ·
        refine ⟨122628381175782489559829885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81752254117188326373219923 122628381175782489559829885)
        ·
          refine ⟨45985642940918433584936207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122628381175782489559829885 45985642940918433584936207)
          ·
            refine ⟨68978464411377650377404311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45985642940918433584936207 68978464411377650377404311)
            ·
              refine ⟨103467696617066475566106467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68978464411377650377404311 103467696617066475566106467)
              ·
                refine ⟨155201544925599713349159701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103467696617066475566106467 155201544925599713349159701)
                ·
                  refine ⟨7275072418387486563241861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 155201544925599713349159701 7275072418387486563241861)
                  ·
                    refine ⟨1364076078447653730607849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7275072418387486563241861 1364076078447653730607849)
                    ·
                      rfl

theorem cell23_7969586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 6, 4].length) (baseStart_7969586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7969586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7969586 prefixEnd_7969586 := by exact prefixLift 7969586
  have htrace : WordTrace (prefixWord ++ tailWord_7969586) baseStart_7969586 baseEnd_7969586 := by
    simpa [prefixWord, tailWord_7969586, baseEnd_7969586] using wordTrace_append hprefix tailTrace_7969586
  have hstable : (prefixWord ++ tailWord_7969586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7969586).length < 2 ^ (prefixWord ++ tailWord_7969586).sum := by decide
  have hdescent : baseEnd_7969586 < baseStart_7969586 := by decide
  rcases family_descends (prefixWord ++ tailWord_7969586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7969587 : List Nat := [1, 1, 1, 2, 6, 3, 1, 3, 1, 1, 3]
def baseStart_7969587 : Nat := 118140960795 + 7969587 * 2 ^ 59
def prefixEnd_7969587 : Nat := 4983230072969 + 3 ^ 40 * 7969587 * 2
def baseEnd_7969587 : Nat := 4092228748823615687911043

theorem tailTrace_7969587 : CollatzResearch.WordTrace tailWord_7969587 prefixEnd_7969587 4092228748823615687911043 := by
  unfold tailWord_7969587
  simp only [CollatzResearch.WordTrace]
  refine ⟨290674717778554870942235015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193783145185703247294823343 290674717778554870942235015)
  ·
    refine ⟨436012076667832306413352523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290674717778554870942235015 436012076667832306413352523)
    ·
      refine ⟨654018115001748459620028785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436012076667832306413352523 654018115001748459620028785)
      ·
        refine ⟨490513586251311344715021589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 654018115001748459620028785 490513586251311344715021589)
        ·
          refine ⟨22992824355530219283516637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 490513586251311344715021589 22992824355530219283516637)
          ·
            refine ⟨8622309133323832231318739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22992824355530219283516637 8622309133323832231318739)
            ·
              refine ⟨12933463699985748346978109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8622309133323832231318739 12933463699985748346978109)
              ·
                refine ⟨4850048887494655630116791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12933463699985748346978109 4850048887494655630116791)
                ·
                  refine ⟨7275073331241983445175187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4850048887494655630116791 7275073331241983445175187)
                  ·
                    refine ⟨10912609996862975167762781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7275073331241983445175187 10912609996862975167762781)
                    ·
                      refine ⟨4092228748823615687911043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10912609996862975167762781 4092228748823615687911043)
                      ·
                        rfl

theorem cell23_7969587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 3, 1, 1, 3].length) (baseStart_7969587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7969587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7969587 prefixEnd_7969587 := by exact prefixLift 7969587
  have htrace : WordTrace (prefixWord ++ tailWord_7969587) baseStart_7969587 baseEnd_7969587 := by
    simpa [prefixWord, tailWord_7969587, baseEnd_7969587] using wordTrace_append hprefix tailTrace_7969587
  have hstable : (prefixWord ++ tailWord_7969587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7969587).length < 2 ^ (prefixWord ++ tailWord_7969587).sum := by decide
  have hdescent : baseEnd_7969587 < baseStart_7969587 := by decide
  rcases family_descends (prefixWord ++ tailWord_7969587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7969596 : List Nat := [2, 2, 2, 2, 1, 1, 1, 2, 5, 2, 3]
def baseStart_7969596 : Nat := 118140960795 + 7969596 * 2 ^ 59
def prefixEnd_7969596 : Nat := 4983230072969 + 3 ^ 40 * 7969596 * 2
def baseEnd_7969596 : Nat := 4092233370149506152698501

theorem tailTrace_7969596 : CollatzResearch.WordTrace tailWord_7969596 prefixEnd_7969596 4092233370149506152698501 := by
  unfold tailWord_7969596
  simp only [CollatzResearch.WordTrace]
  refine ⟨145337523017761132739656321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193783364023681510319541761 145337523017761132739656321)
  ·
    refine ⟨109003142263320849554742241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145337523017761132739656321 109003142263320849554742241)
    ·
      refine ⟨81752356697490637166056681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109003142263320849554742241 81752356697490637166056681)
      ·
        refine ⟨61314267523117977874542511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81752356697490637166056681 61314267523117977874542511)
        ·
          refine ⟨91971401284676966811813767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61314267523117977874542511 91971401284676966811813767)
          ·
            refine ⟨137957101927015450217720651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91971401284676966811813767 137957101927015450217720651)
            ·
              refine ⟨206935652890523175326580977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137957101927015450217720651 206935652890523175326580977)
              ·
                refine ⟨155201739667892381494935733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 206935652890523175326580977 155201739667892381494935733)
                ·
                  refine ⟨14550163093864910765150225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 155201739667892381494935733 14550163093864910765150225)
                  ·
                    refine ⟨10912622320398683073862669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14550163093864910765150225 10912622320398683073862669)
                    ·
                      refine ⟨4092233370149506152698501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10912622320398683073862669 4092233370149506152698501)
                      ·
                        rfl

theorem cell23_7969596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 5, 2, 3].length) (baseStart_7969596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7969596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7969596 prefixEnd_7969596 := by exact prefixLift 7969596
  have htrace : WordTrace (prefixWord ++ tailWord_7969596) baseStart_7969596 baseEnd_7969596 := by
    simpa [prefixWord, tailWord_7969596, baseEnd_7969596] using wordTrace_append hprefix tailTrace_7969596
  have hstable : (prefixWord ++ tailWord_7969596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7969596).length < 2 ^ (prefixWord ++ tailWord_7969596).sum := by decide
  have hdescent : baseEnd_7969596 < baseStart_7969596 := by decide
  rcases family_descends (prefixWord ++ tailWord_7969596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7969599 : List Nat := [1, 1, 2, 2, 5, 1, 11]
def baseStart_7969599 : Nat := 118140960795 + 7969599 * 2 ^ 59
def prefixEnd_7969599 : Nat := 4983230072969 + 3 ^ 40 * 7969599 * 2
def baseEnd_7969599 : Nat := 50521418649277402974827

theorem tailTrace_7969599 : CollatzResearch.WordTrace tailWord_7969599 prefixEnd_7969599 50521418649277402974827 := by
  unfold tailWord_7969599
  simp only [CollatzResearch.WordTrace]
  refine ⟨290675155454511396991671851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193783436969674264661114567 290675155454511396991671851)
  ·
    refine ⟨436012733181767095487507777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290675155454511396991671851 436012733181767095487507777)
    ·
      refine ⟨327009549886325321615630833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 436012733181767095487507777 327009549886325321615630833)
      ·
        refine ⟨245257162414743991211723125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327009549886325321615630833 245257162414743991211723125)
        ·
          refine ⟨22992858976382249176099043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 245257162414743991211723125 22992858976382249176099043)
          ·
            refine ⟨34489288464573373764148565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22992858976382249176099043 34489288464573373764148565)
            ·
              refine ⟨50521418649277402974827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 34489288464573373764148565 50521418649277402974827)
              ·
                rfl

theorem cell23_7969599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 11].length) (baseStart_7969599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7969599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7969599 prefixEnd_7969599 := by exact prefixLift 7969599
  have htrace : WordTrace (prefixWord ++ tailWord_7969599) baseStart_7969599 baseEnd_7969599 := by
    simpa [prefixWord, tailWord_7969599, baseEnd_7969599] using wordTrace_append hprefix tailTrace_7969599
  have hstable : (prefixWord ++ tailWord_7969599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7969599).length < 2 ^ (prefixWord ++ tailWord_7969599).sum := by decide
  have hdescent : baseEnd_7969599 < baseStart_7969599 := by decide
  rcases family_descends (prefixWord ++ tailWord_7969599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7969604 : List Nat := [2, 3, 4, 2, 1, 2, 1, 1, 3, 1, 3]
def baseStart_7969604 : Nat := 118140960795 + 7969604 * 2 ^ 59
def prefixEnd_7969604 : Nat := 4983230072969 + 3 ^ 40 * 7969604 * 2
def baseEnd_7969604 : Nat := 4092237477994742121398465

theorem tailTrace_7969604 : CollatzResearch.WordTrace tailWord_7969604 prefixEnd_7969604 4092237477994742121398465 := by
  unfold tailWord_7969604
  simp only [CollatzResearch.WordTrace]
  refine ⟨145337668909746641422801933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193783558546328855230402577 145337668909746641422801933)
  ·
    refine ⟨54501625841154990533550725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145337668909746641422801933 54501625841154990533550725)
    ·
      refine ⟨10219054845216560725040761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54501625841154990533550725 10219054845216560725040761)
      ·
        refine ⟨7664291133912420543780571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10219054845216560725040761 7664291133912420543780571)
        ·
          refine ⟨11496436700868630815670857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7664291133912420543780571 11496436700868630815670857)
          ·
            refine ⟨8622327525651473111753143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11496436700868630815670857 8622327525651473111753143)
            ·
              refine ⟨12933491288477209667629715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8622327525651473111753143 12933491288477209667629715)
              ·
                refine ⟨19400236932715814501444573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12933491288477209667629715 19400236932715814501444573)
                ·
                  refine ⟨7275088849768430438041715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19400236932715814501444573 7275088849768430438041715)
                  ·
                    refine ⟨10912633274652645657062573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7275088849768430438041715 10912633274652645657062573)
                    ·
                      refine ⟨4092237477994742121398465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10912633274652645657062573 4092237477994742121398465)
                      ·
                        rfl

theorem cell23_7969604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_7969604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7969604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7969604 prefixEnd_7969604 := by exact prefixLift 7969604
  have htrace : WordTrace (prefixWord ++ tailWord_7969604) baseStart_7969604 baseEnd_7969604 := by
    simpa [prefixWord, tailWord_7969604, baseEnd_7969604] using wordTrace_append hprefix tailTrace_7969604
  have hstable : (prefixWord ++ tailWord_7969604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7969604).length < 2 ^ (prefixWord ++ tailWord_7969604).sum := by decide
  have hdescent : baseEnd_7969604 < baseStart_7969604 := by decide
  rcases family_descends (prefixWord ++ tailWord_7969604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7969620 : List Nat := [2, 4, 1, 1, 4, 1, 1, 3, 2, 4]
def baseStart_7969620 : Nat := 118140960795 + 7969620 * 2 ^ 59
def prefixEnd_7969620 : Nat := 4983230072969 + 3 ^ 40 * 7969620 * 2
def baseEnd_7969620 : Nat := 1364081897895071352932797

theorem tailTrace_7969620 : CollatzResearch.WordTrace tailWord_7969620 prefixEnd_7969620 1364081897895071352932797 := by
  unfold tailWord_7969620
  simp only [CollatzResearch.WordTrace]
  refine ⟨145337960693717658789093157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193783947591623545052124209 145337960693717658789093157)
  ·
    refine ⟨27250867630072061022954967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145337960693717658789093157 27250867630072061022954967)
    ·
      refine ⟨40876301445108091534432451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27250867630072061022954967 40876301445108091534432451)
      ·
        refine ⟨61314452167662137301648677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40876301445108091534432451 61314452167662137301648677)
        ·
          refine ⟨11496459781436650744059127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61314452167662137301648677 11496459781436650744059127)
          ·
            refine ⟨17244689672154976116088691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11496459781436650744059127 17244689672154976116088691)
            ·
              refine ⟨25867034508232464174133037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17244689672154976116088691 25867034508232464174133037)
              ·
                refine ⟨9700137940587174065299889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25867034508232464174133037 9700137940587174065299889)
                ·
                  refine ⟨7275103455440380548974917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9700137940587174065299889 7275103455440380548974917)
                  ·
                    refine ⟨1364081897895071352932797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7275103455440380548974917 1364081897895071352932797)
                    ·
                      rfl

theorem cell23_7969620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 3, 2, 4].length) (baseStart_7969620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7969620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7969620 prefixEnd_7969620 := by exact prefixLift 7969620
  have htrace : WordTrace (prefixWord ++ tailWord_7969620) baseStart_7969620 baseEnd_7969620 := by
    simpa [prefixWord, tailWord_7969620, baseEnd_7969620] using wordTrace_append hprefix tailTrace_7969620
  have hstable : (prefixWord ++ tailWord_7969620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7969620).length < 2 ^ (prefixWord ++ tailWord_7969620).sum := by decide
  have hdescent : baseEnd_7969620 < baseStart_7969620 := by decide
  rcases family_descends (prefixWord ++ tailWord_7969620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7969700 : List Nat := [2, 3, 1, 2, 1, 2, 2, 2, 4, 2, 2]
def baseStart_7969700 : Nat := 118140960795 + 7969700 * 2 ^ 59
def prefixEnd_7969700 : Nat := 4983230072969 + 3 ^ 40 * 7969700 * 2
def baseEnd_7969700 : Nat := 4092286772137573745798023

theorem tailTrace_7969700 : CollatzResearch.WordTrace tailWord_7969700 prefixEnd_7969700 4092286772137573745798023 := by
  unfold tailWord_7969700
  simp only [CollatzResearch.WordTrace]
  refine ⟨145339419613572745620549277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193785892818096994160732369 145339419613572745620549277)
  ·
    refine ⟨54502282355089779607705979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145339419613572745620549277 54502282355089779607705979)
    ·
      refine ⟨81753423532634669411558969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54502282355089779607705979 81753423532634669411558969)
      ·
        refine ⟨61315067649476002058669227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81753423532634669411558969 61315067649476002058669227)
        ·
          refine ⟨91972601474214003088003841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61315067649476002058669227 91972601474214003088003841)
          ·
            refine ⟨68979451105660502316002881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91972601474214003088003841 68979451105660502316002881)
            ·
              refine ⟨51734588329245376737002161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68979451105660502316002881 51734588329245376737002161)
              ·
                refine ⟨38800941246934032552751621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51734588329245376737002161 38800941246934032552751621)
                ·
                  refine ⟨7275176483800131103640929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38800941246934032552751621 7275176483800131103640929)
                  ·
                    refine ⟨5456382362850098327730697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7275176483800131103640929 5456382362850098327730697)
                    ·
                      refine ⟨4092286772137573745798023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5456382362850098327730697 4092286772137573745798023)
                      ·
                        rfl

theorem cell23_7969700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 2, 4, 2, 2].length) (baseStart_7969700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7969700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7969700 prefixEnd_7969700 := by exact prefixLift 7969700
  have htrace : WordTrace (prefixWord ++ tailWord_7969700) baseStart_7969700 baseEnd_7969700 := by
    simpa [prefixWord, tailWord_7969700, baseEnd_7969700] using wordTrace_append hprefix tailTrace_7969700
  have hstable : (prefixWord ++ tailWord_7969700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7969700).length < 2 ^ (prefixWord ++ tailWord_7969700).sum := by decide
  have hdescent : baseEnd_7969700 < baseStart_7969700 := by decide
  rcases family_descends (prefixWord ++ tailWord_7969700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7969757 : List Nat := [1, 4, 3, 1, 2, 3, 1, 3, 5]
def baseStart_7969757 : Nat := 118140960795 + 7969757 * 2 ^ 59
def prefixEnd_7969757 : Nat := 4983230072969 + 3 ^ 40 * 7969757 * 2
def baseEnd_7969757 : Nat := 454701782281653335865029

theorem tailTrace_7969757 : CollatzResearch.WordTrace tailWord_7969757 prefixEnd_7969757 454701782281653335865029 := by
  unfold tailWord_7969757
  simp only [CollatzResearch.WordTrace]
  refine ⟨290680918187938989975923525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193787278791959326650615683 290680918187938989975923525)
  ·
    refine ⟨54502672160238560620485661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 290680918187938989975923525 54502672160238560620485661)
    ·
      refine ⟨20438502060089460232682123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54502672160238560620485661 20438502060089460232682123)
      ·
        refine ⟨30657753090134190349023185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20438502060089460232682123 30657753090134190349023185)
        ·
          refine ⟨22993314817600642761767389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30657753090134190349023185 22993314817600642761767389)
          ·
            refine ⟨8622493056600241035662771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22993314817600642761767389 8622493056600241035662771)
            ·
              refine ⟨12933739584900361553494157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8622493056600241035662771 12933739584900361553494157)
              ·
                refine ⟨4850152344337635582560309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12933739584900361553494157 4850152344337635582560309)
                ·
                  refine ⟨454701782281653335865029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4850152344337635582560309 454701782281653335865029)
                  ·
                    rfl

theorem cell23_7969757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 3, 5].length) (baseStart_7969757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7969757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7969757 prefixEnd_7969757 := by exact prefixLift 7969757
  have htrace : WordTrace (prefixWord ++ tailWord_7969757) baseStart_7969757 baseEnd_7969757 := by
    simpa [prefixWord, tailWord_7969757, baseEnd_7969757] using wordTrace_append hprefix tailTrace_7969757
  have hstable : (prefixWord ++ tailWord_7969757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7969757).length < 2 ^ (prefixWord ++ tailWord_7969757).sum := by decide
  have hdescent : baseEnd_7969757 < baseStart_7969757 := by decide
  rcases family_descends (prefixWord ++ tailWord_7969757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7969786 : List Nat := [3, 1, 1, 1, 1, 2, 1, 4, 2, 1, 6]
def baseStart_7969786 : Nat := 118140960795 + 7969786 * 2 ^ 59
def prefixEnd_7969786 : Nat := 4983230072969 + 3 ^ 40 * 7969786 * 2
def baseEnd_7969786 : Nat := 4092330931473860409322627

theorem tailTrace_7969786 : CollatzResearch.WordTrace tailWord_7969786 prefixEnd_7969786 4092330931473860409322627 := by
  unfold tailWord_7969786
  simp only [CollatzResearch.WordTrace]
  refine ⟨72670493976208481982182303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193787983936555951952486141 72670493976208481982182303)
  ·
    refine ⟨109005740964312722973273455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72670493976208481982182303 109005740964312722973273455)
    ·
      refine ⟨163508611446469084459910183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109005740964312722973273455 163508611446469084459910183)
      ·
        refine ⟨245262917169703626689865275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163508611446469084459910183 245262917169703626689865275)
        ·
          refine ⟨367894375754555440034797913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245262917169703626689865275 367894375754555440034797913)
          ·
            refine ⟨275920781815916580026098435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 367894375754555440034797913 275920781815916580026098435)
            ·
              refine ⟨413881172723874870039147653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275920781815916580026098435 413881172723874870039147653)
              ·
                refine ⟨77602719885726538132340185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 413881172723874870039147653 77602719885726538132340185)
                ·
                  refine ⟨58202039914294903599255139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77602719885726538132340185 58202039914294903599255139)
                  ·
                    refine ⟨87303059871442355398882709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58202039914294903599255139 87303059871442355398882709)
                    ·
                      refine ⟨4092330931473860409322627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87303059871442355398882709 4092330931473860409322627)
                      ·
                        rfl

theorem cell23_7969786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 2, 1, 6].length) (baseStart_7969786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7969786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7969786 prefixEnd_7969786 := by exact prefixLift 7969786
  have htrace : WordTrace (prefixWord ++ tailWord_7969786) baseStart_7969786 baseEnd_7969786 := by
    simpa [prefixWord, tailWord_7969786, baseEnd_7969786] using wordTrace_append hprefix tailTrace_7969786
  have hstable : (prefixWord ++ tailWord_7969786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7969786).length < 2 ^ (prefixWord ++ tailWord_7969786).sum := by decide
  have hdescent : baseEnd_7969786 < baseStart_7969786 := by decide
  rcases family_descends (prefixWord ++ tailWord_7969786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7969834 : List Nat := [3, 1, 4, 1, 3, 1, 1, 4, 1, 4]
def baseStart_7969834 : Nat := 118140960795 + 7969834 * 2 ^ 59
def prefixEnd_7969834 : Nat := 4983230072969 + 3 ^ 40 * 7969834 * 2
def baseEnd_7969834 : Nat := 1364118526181758740507469

theorem tailTrace_7969834 : CollatzResearch.WordTrace tailWord_7969834 prefixEnd_7969834 1364118526181758740507469 := by
  unfold tailWord_7969834
  simp only [CollatzResearch.WordTrace]
  refine ⟨72670931652165008031619139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193789151072440021417651037 72670931652165008031619139)
  ·
    refine ⟨109006397478247512047428709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72670931652165008031619139 109006397478247512047428709)
    ·
      refine ⟨20438699527171408508892883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109006397478247512047428709 20438699527171408508892883)
      ·
        refine ⟨30658049290757112763339325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20438699527171408508892883 30658049290757112763339325)
        ·
          refine ⟨11496768484033917286252247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30658049290757112763339325 11496768484033917286252247)
          ·
            refine ⟨17245152726050875929378371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11496768484033917286252247 17245152726050875929378371)
            ·
              refine ⟨25867729089076313894067557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17245152726050875929378371 25867729089076313894067557)
              ·
                refine ⟨4850199204201808855137667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25867729089076313894067557 4850199204201808855137667)
                ·
                  refine ⟨7275298806302713282706501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4850199204201808855137667 7275298806302713282706501)
                  ·
                    refine ⟨1364118526181758740507469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7275298806302713282706501 1364118526181758740507469)
                    ·
                      rfl

theorem cell23_7969834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_7969834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7969834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7969834 prefixEnd_7969834 := by exact prefixLift 7969834
  have htrace : WordTrace (prefixWord ++ tailWord_7969834) baseStart_7969834 baseEnd_7969834 := by
    simpa [prefixWord, tailWord_7969834, baseEnd_7969834] using wordTrace_append hprefix tailTrace_7969834
  have hstable : (prefixWord ++ tailWord_7969834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7969834).length < 2 ^ (prefixWord ++ tailWord_7969834).sum := by decide
  have hdescent : baseEnd_7969834 < baseStart_7969834 := by decide
  rcases family_descends (prefixWord ++ tailWord_7969834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7969840 : List Nat := [2, 1, 1, 1, 2, 4, 2, 3, 3, 1, 3]
def baseStart_7969840 : Nat := 118140960795 + 7969840 * 2 ^ 59
def prefixEnd_7969840 : Nat := 4983230072969 + 3 ^ 40 * 7969840 * 2
def baseEnd_7969840 : Nat := 4092358659429203198047379

theorem tailTrace_7969840 : CollatzResearch.WordTrace tailWord_7969840 prefixEnd_7969840 4092358659429203198047379 := by
  unfold tailWord_7969840
  simp only [CollatzResearch.WordTrace]
  refine ⟨145341972723319147575597487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193789296964425530100796649 145341972723319147575597487)
  ·
    refine ⟨218012959084978721363396231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145341972723319147575597487 218012959084978721363396231)
    ·
      refine ⟨327019438627468082045094347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218012959084978721363396231 327019438627468082045094347)
      ·
        refine ⟨490529157941202123067641521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327019438627468082045094347 490529157941202123067641521)
        ·
          refine ⟨367896868455901592300731141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 490529157941202123067641521 367896868455901592300731141)
          ·
            refine ⟨68980662835481548556387089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 367896868455901592300731141 68980662835481548556387089)
            ·
              refine ⟨51735497126611161417290317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68980662835481548556387089 51735497126611161417290317)
              ·
                refine ⟨19400811422479185531483869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51735497126611161417290317 19400811422479185531483869)
                ·
                  refine ⟨7275304283429694574306451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19400811422479185531483869 7275304283429694574306451)
                  ·
                    refine ⟨10912956425144541861459677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7275304283429694574306451 10912956425144541861459677)
                    ·
                      refine ⟨4092358659429203198047379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10912956425144541861459677 4092358659429203198047379)
                      ·
                        rfl

theorem cell23_7969840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 3, 3, 1, 3].length) (baseStart_7969840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7969840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7969840 prefixEnd_7969840 := by exact prefixLift 7969840
  have htrace : WordTrace (prefixWord ++ tailWord_7969840) baseStart_7969840 baseEnd_7969840 := by
    simpa [prefixWord, tailWord_7969840, baseEnd_7969840] using wordTrace_append hprefix tailTrace_7969840
  have hstable : (prefixWord ++ tailWord_7969840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7969840).length < 2 ^ (prefixWord ++ tailWord_7969840).sum := by decide
  have hdescent : baseEnd_7969840 < baseStart_7969840 := by decide
  rcases family_descends (prefixWord ++ tailWord_7969840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7969850 : List Nat := [3, 1, 1, 1, 3, 1, 2, 2, 4, 3, 2]
def baseStart_7969850 : Nat := 118140960795 + 7969850 * 2 ^ 59
def prefixEnd_7969850 : Nat := 4983230072969 + 3 ^ 40 * 7969850 * 2
def baseEnd_7969850 : Nat := 4092363794235748158922333

theorem tailTrace_7969850 : CollatzResearch.WordTrace tailWord_7969850 prefixEnd_7969850 4092363794235748158922333 := by
  unfold tailWord_7969850
  simp only [CollatzResearch.WordTrace]
  refine ⟨72671077544150516714764751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193789540117734711239372669 72671077544150516714764751)
  ·
    refine ⟨109006616316225775072147127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72671077544150516714764751 109006616316225775072147127)
    ·
      refine ⟨163509924474338662608220691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109006616316225775072147127 163509924474338662608220691)
      ·
        refine ⟨245264886711507993912331037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163509924474338662608220691 245264886711507993912331037)
        ·
          refine ⟨91974332516815497717124139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 245264886711507993912331037 91974332516815497717124139)
          ·
            refine ⟨137961498775223246575686209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91974332516815497717124139 137961498775223246575686209)
            ·
              refine ⟨103471124081417434931764657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137961498775223246575686209 103471124081417434931764657)
              ·
                refine ⟨77603343061063076198823493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103471124081417434931764657 77603343061063076198823493)
                ·
                  refine ⟨14550626823949326787279405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77603343061063076198823493 14550626823949326787279405)
                  ·
                    refine ⟨5456485058980997545229777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14550626823949326787279405 5456485058980997545229777)
                    ·
                      refine ⟨4092363794235748158922333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5456485058980997545229777 4092363794235748158922333)
                      ·
                        rfl

theorem cell23_7969850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 4, 3, 2].length) (baseStart_7969850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7969850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7969850 prefixEnd_7969850 := by exact prefixLift 7969850
  have htrace : WordTrace (prefixWord ++ tailWord_7969850) baseStart_7969850 baseEnd_7969850 := by
    simpa [prefixWord, tailWord_7969850, baseEnd_7969850] using wordTrace_append hprefix tailTrace_7969850
  have hstable : (prefixWord ++ tailWord_7969850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7969850).length < 2 ^ (prefixWord ++ tailWord_7969850).sum := by decide
  have hdescent : baseEnd_7969850 < baseStart_7969850 := by decide
  rcases family_descends (prefixWord ++ tailWord_7969850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7969873 : List Nat := [1, 2, 2, 1, 3, 1, 4, 2, 1, 6]
def baseStart_7969873 : Nat := 118140960795 + 7969873 * 2 ^ 59
def prefixEnd_7969873 : Nat := 4983230072969 + 3 ^ 40 * 7969873 * 2
def baseEnd_7969873 : Nat := 1364125201430267189644909

theorem tailTrace_7969873 : CollatzResearch.WordTrace tailWord_7969873 prefixEnd_7969873 1364125201430267189644909 := by
  unfold tailWord_7969873
  simp only [CollatzResearch.WordTrace]
  refine ⟨290685149055518741787146273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193790099370345827858097515 290685149055518741787146273)
  ·
    refine ⟨218013861791639056340359705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290685149055518741787146273 218013861791639056340359705)
    ·
      refine ⟨163510396343729292255269779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218013861791639056340359705 163510396343729292255269779)
      ·
        refine ⟨245265594515593938382904669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163510396343729292255269779 245265594515593938382904669)
        ·
          refine ⟨91974597943347726893589251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 245265594515593938382904669 91974597943347726893589251)
          ·
            refine ⟨137961896915021590340383877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91974597943347726893589251 137961896915021590340383877)
            ·
              refine ⟨25867855671566548188821977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137961896915021590340383877 25867855671566548188821977)
              ·
                refine ⟨19400891753674911141616483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25867855671566548188821977 19400891753674911141616483)
                ·
                  refine ⟨29101337630512366712424725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19400891753674911141616483 29101337630512366712424725)
                  ·
                    refine ⟨1364125201430267189644909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29101337630512366712424725 1364125201430267189644909)
                    ·
                      rfl

theorem cell23_7969873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 2, 1, 6].length) (baseStart_7969873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7969873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7969873 prefixEnd_7969873 := by exact prefixLift 7969873
  have htrace : WordTrace (prefixWord ++ tailWord_7969873) baseStart_7969873 baseEnd_7969873 := by
    simpa [prefixWord, tailWord_7969873, baseEnd_7969873] using wordTrace_append hprefix tailTrace_7969873
  have hstable : (prefixWord ++ tailWord_7969873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7969873).length < 2 ^ (prefixWord ++ tailWord_7969873).sum := by decide
  have hdescent : baseEnd_7969873 < baseStart_7969873 := by decide
  rcases family_descends (prefixWord ++ tailWord_7969873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7969874 : List Nat := [3, 2, 2, 1, 3, 1, 1, 5, 1, 1, 3]
def baseStart_7969874 : Nat := 118140960795 + 7969874 * 2 ^ 59
def prefixEnd_7969874 : Nat := 4983230072969 + 3 ^ 40 * 7969874 * 2
def baseEnd_7969874 : Nat := 4092376117771456065022223

theorem tailTrace_7969874 : CollatzResearch.WordTrace tailWord_7969874 prefixEnd_7969874 4092376117771456065022223 := by
  unfold tailWord_7969874
  simp only [CollatzResearch.WordTrace]
  refine ⟨72671296382128779739483169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193790123685676745971955117 72671296382128779739483169)
  ·
    refine ⟨54503472286596584804612377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72671296382128779739483169 54503472286596584804612377)
    ·
      refine ⟨40877604214947438603459283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54503472286596584804612377 40877604214947438603459283)
      ·
        refine ⟨61316406322421157905188925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40877604214947438603459283 61316406322421157905188925)
        ·
          refine ⟨22993652370907934214445847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61316406322421157905188925 22993652370907934214445847)
          ·
            refine ⟨34490478556361901321668771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22993652370907934214445847 34490478556361901321668771)
            ·
              refine ⟨51735717834542851982503157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34490478556361901321668771 51735717834542851982503157)
              ·
                refine ⟨4850223546988392373359671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51735717834542851982503157 4850223546988392373359671)
                ·
                  refine ⟨7275335320482588560039507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4850223546988392373359671 7275335320482588560039507)
                  ·
                    refine ⟨10913002980723882840059261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7275335320482588560039507 10913002980723882840059261)
                    ·
                      refine ⟨4092376117771456065022223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10913002980723882840059261 4092376117771456065022223)
                      ·
                        rfl

theorem cell23_7969874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 5, 1, 1, 3].length) (baseStart_7969874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7969874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7969874 prefixEnd_7969874 := by exact prefixLift 7969874
  have htrace : WordTrace (prefixWord ++ tailWord_7969874) baseStart_7969874 baseEnd_7969874 := by
    simpa [prefixWord, tailWord_7969874, baseEnd_7969874] using wordTrace_append hprefix tailTrace_7969874
  have hstable : (prefixWord ++ tailWord_7969874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7969874).length < 2 ^ (prefixWord ++ tailWord_7969874).sum := by decide
  have hdescent : baseEnd_7969874 < baseStart_7969874 := by decide
  rcases family_descends (prefixWord ++ tailWord_7969874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7969880 : List Nat := [2, 1, 2, 2, 1, 3, 3, 3, 1, 1, 4]
def baseStart_7969880 : Nat := 118140960795 + 7969880 * 2 ^ 59
def prefixEnd_7969880 : Nat := 4983230072969 + 3 ^ 40 * 7969880 * 2
def baseEnd_7969880 : Nat := 4092379198655383041547195

theorem tailTrace_7969880 : CollatzResearch.WordTrace tailWord_7969880 prefixEnd_7969880 4092379198655383041547195 := by
  unfold tailWord_7969880
  simp only [CollatzResearch.WordTrace]
  refine ⟨145342702183246690991325547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193790269577662254655100729 145342702183246690991325547)
  ·
    refine ⟨218014053274870036486988321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145342702183246690991325547 218014053274870036486988321)
    ·
      refine ⟨163510539956152527365241241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218014053274870036486988321 163510539956152527365241241)
      ·
        refine ⟨122632904967114395523930931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163510539956152527365241241 122632904967114395523930931)
        ·
          refine ⟨183949357450671593285896397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122632904967114395523930931 183949357450671593285896397)
          ·
            refine ⟨68981009044001847482211149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183949357450671593285896397 68981009044001847482211149)
            ·
              refine ⟨25867878391500692805829181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68981009044001847482211149 25867878391500692805829181)
              ·
                refine ⟨9700454396812759802185943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25867878391500692805829181 9700454396812759802185943)
                ·
                  refine ⟨14550681595219139703278915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9700454396812759802185943 14550681595219139703278915)
                  ·
                    refine ⟨21826022392828709554918373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14550681595219139703278915 21826022392828709554918373)
                    ·
                      refine ⟨4092379198655383041547195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21826022392828709554918373 4092379198655383041547195)
                      ·
                        rfl

theorem cell23_7969880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 3, 1, 1, 4].length) (baseStart_7969880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7969880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7969880 prefixEnd_7969880 := by exact prefixLift 7969880
  have htrace : WordTrace (prefixWord ++ tailWord_7969880) baseStart_7969880 baseEnd_7969880 := by
    simpa [prefixWord, tailWord_7969880, baseEnd_7969880] using wordTrace_append hprefix tailTrace_7969880
  have hstable : (prefixWord ++ tailWord_7969880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7969880).length < 2 ^ (prefixWord ++ tailWord_7969880).sum := by decide
  have hdescent : baseEnd_7969880 < baseStart_7969880 := by decide
  rcases family_descends (prefixWord ++ tailWord_7969880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7969893 : List Nat := [1, 3, 1, 3, 2, 1, 2, 2, 1, 1, 6]
def baseStart_7969893 : Nat := 118140960795 + 7969893 * 2 ^ 59
def prefixEnd_7969893 : Nat := 4983230072969 + 3 ^ 40 * 7969893 * 2
def baseEnd_7969893 : Nat := 4092385873903891490684635

theorem tailTrace_7969893 : CollatzResearch.WordTrace tailWord_7969893 prefixEnd_7969893 4092385873903891490684635 := by
  unfold tailWord_7969893
  simp only [CollatzResearch.WordTrace]
  refine ⟨290685878515446285202874333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193790585676964190135249555 290685878515446285202874333)
  ·
    refine ⟨109007204443292356951077875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290685878515446285202874333 109007204443292356951077875)
    ·
      refine ⟨163510806664938535426616813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109007204443292356951077875 163510806664938535426616813)
      ·
        refine ⟨61316552499351950784981305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163510806664938535426616813 61316552499351950784981305)
        ·
          refine ⟨45987414374513963088735979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61316552499351950784981305 45987414374513963088735979)
          ·
            refine ⟨68981121561770944633103969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45987414374513963088735979 68981121561770944633103969)
            ·
              refine ⟨51735841171328208474827977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68981121561770944633103969 51735841171328208474827977)
              ·
                refine ⟨38801880878496156356120983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51735841171328208474827977 38801880878496156356120983)
                ·
                  refine ⟨58202821317744234534181475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38801880878496156356120983 58202821317744234534181475)
                  ·
                    refine ⟨87304231976616351801272213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58202821317744234534181475 87304231976616351801272213)
                    ·
                      refine ⟨4092385873903891490684635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87304231976616351801272213 4092385873903891490684635)
                      ·
                        rfl

theorem cell23_7969893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_7969893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7969893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7969893 prefixEnd_7969893 := by exact prefixLift 7969893
  have htrace : WordTrace (prefixWord ++ tailWord_7969893) baseStart_7969893 baseEnd_7969893 := by
    simpa [prefixWord, tailWord_7969893, baseEnd_7969893] using wordTrace_append hprefix tailTrace_7969893
  have hstable : (prefixWord ++ tailWord_7969893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7969893).length < 2 ^ (prefixWord ++ tailWord_7969893).sum := by decide
  have hdescent : baseEnd_7969893 < baseStart_7969893 := by decide
  rcases family_descends (prefixWord ++ tailWord_7969893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7969897 : List Nat := [1, 2, 1, 1, 1, 6, 1, 3, 3, 2, 2]
def baseStart_7969897 : Nat := 118140960795 + 7969897 * 2 ^ 59
def prefixEnd_7969897 : Nat := 4983230072969 + 3 ^ 40 * 7969897 * 2
def baseEnd_7969897 : Nat := 4092387927826509475034617

theorem tailTrace_7969897 : CollatzResearch.WordTrace tailWord_7969897 prefixEnd_7969897 4092387927826509475034617 := by
  unfold tailWord_7969897
  simp only [CollatzResearch.WordTrace]
  refine ⟨290686024407431793886019945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193790682938287862590679963 290686024407431793886019945)
  ·
    refine ⟨218014518305573845414514959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290686024407431793886019945 218014518305573845414514959)
    ·
      refine ⟨327021777458360768121772439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218014518305573845414514959 327021777458360768121772439)
      ·
        refine ⟨490532666187541152182658659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327021777458360768121772439 490532666187541152182658659)
        ·
          refine ⟨735798999281311728273987989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 490532666187541152182658659 735798999281311728273987989)
          ·
            refine ⟨34490578091311487262843187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 735798999281311728273987989 34490578091311487262843187)
            ·
              refine ⟨51735867136967230894264781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34490578091311487262843187 51735867136967230894264781)
              ·
                refine ⟨19400950176362711585349293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51735867136967230894264781 19400950176362711585349293)
                ·
                  refine ⟨7275356316136016844505985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19400950176362711585349293 7275356316136016844505985)
                  ·
                    refine ⟨5456517237102012633379489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7275356316136016844505985 5456517237102012633379489)
                    ·
                      refine ⟨4092387927826509475034617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5456517237102012633379489 4092387927826509475034617)
                      ·
                        rfl

theorem cell23_7969897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 3, 3, 2, 2].length) (baseStart_7969897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7969897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7969897 prefixEnd_7969897 := by exact prefixLift 7969897
  have htrace : WordTrace (prefixWord ++ tailWord_7969897) baseStart_7969897 baseEnd_7969897 := by
    simpa [prefixWord, tailWord_7969897, baseEnd_7969897] using wordTrace_append hprefix tailTrace_7969897
  have hstable : (prefixWord ++ tailWord_7969897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7969897).length < 2 ^ (prefixWord ++ tailWord_7969897).sum := by decide
  have hdescent : baseEnd_7969897 < baseStart_7969897 := by decide
  rcases family_descends (prefixWord ++ tailWord_7969897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7969910 : List Nat := [5, 1, 1, 2, 1, 1, 3, 1, 1, 1, 6]
def baseStart_7969910 : Nat := 118140960795 + 7969910 * 2 ^ 59
def prefixEnd_7969910 : Nat := 4983230072969 + 3 ^ 40 * 7969910 * 2
def baseEnd_7969910 : Nat := 4092394603075017924172057

theorem tailTrace_7969910 : CollatzResearch.WordTrace tailWord_7969910 prefixEnd_7969910 4092394603075017924172057 := by
  unfold tailWord_7969910
  simp only [CollatzResearch.WordTrace]
  refine ⟨18167906159774043569140199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 193790999037589798070828789 18167906159774043569140199)
  ·
    refine ⟨27251859239661065353710299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18167906159774043569140199 27251859239661065353710299)
    ·
      refine ⟨40877788859491598030565449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27251859239661065353710299 40877788859491598030565449)
      ·
        refine ⟨30658341644618698522924087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40877788859491598030565449 30658341644618698522924087)
        ·
          refine ⟨45987512466928047784386131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30658341644618698522924087 45987512466928047784386131)
          ·
            refine ⟨68981268700392071676579197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45987512466928047784386131 68981268700392071676579197)
            ·
              refine ⟨25867975762647026878717199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68981268700392071676579197 25867975762647026878717199)
              ·
                refine ⟨38801963643970540318075799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25867975762647026878717199 38801963643970540318075799)
                ·
                  refine ⟨58202945465955810477113699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38801963643970540318075799 58202945465955810477113699)
                  ·
                    refine ⟨87304418198933715715670549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58202945465955810477113699 87304418198933715715670549)
                    ·
                      refine ⟨4092394603075017924172057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87304418198933715715670549 4092394603075017924172057)
                      ·
                        rfl

theorem cell23_7969910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_7969910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7969910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7969910 prefixEnd_7969910 := by exact prefixLift 7969910
  have htrace : WordTrace (prefixWord ++ tailWord_7969910) baseStart_7969910 baseEnd_7969910 := by
    simpa [prefixWord, tailWord_7969910, baseEnd_7969910] using wordTrace_append hprefix tailTrace_7969910
  have hstable : (prefixWord ++ tailWord_7969910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7969910).length < 2 ^ (prefixWord ++ tailWord_7969910).sum := by decide
  have hdescent : baseEnd_7969910 < baseStart_7969910 := by decide
  rcases family_descends (prefixWord ++ tailWord_7969910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7969917 : List Nat := [1, 4, 1, 1, 3, 1, 4, 2, 1, 2, 3]
def baseStart_7969917 : Nat := 118140960795 + 7969917 * 2 ^ 59
def prefixEnd_7969917 : Nat := 4983230072969 + 3 ^ 40 * 7969917 * 2
def baseEnd_7969917 : Nat := 4092398197439599396784525

theorem tailTrace_7969917 : CollatzResearch.WordTrace tailWord_7969917 prefixEnd_7969917 4092398197439599396784525 := by
  unfold tailWord_7969917
  simp only [CollatzResearch.WordTrace]
  refine ⟨290686753867359337301748005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193791169244906224867832003 290686753867359337301748005)
  ·
    refine ⟨54503766350129875744077751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 290686753867359337301748005 54503766350129875744077751)
    ·
      refine ⟨81755649525194813616116627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54503766350129875744077751 81755649525194813616116627)
      ·
        refine ⟨122633474287792220424174941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81755649525194813616116627 122633474287792220424174941)
        ·
          refine ⟨45987552857922082659065603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122633474287792220424174941 45987552857922082659065603)
          ·
            refine ⟨68981329286883123988598405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45987552857922082659065603 68981329286883123988598405)
            ·
              refine ⟨12933999241290585747862201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68981329286883123988598405 12933999241290585747862201)
              ·
                refine ⟨9700499430967939310896651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12933999241290585747862201 9700499430967939310896651)
                ·
                  refine ⟨14550749146451908966344977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9700499430967939310896651 14550749146451908966344977)
                  ·
                    refine ⟨10913061859838931724758733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14550749146451908966344977 10913061859838931724758733)
                    ·
                      refine ⟨4092398197439599396784525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10913061859838931724758733 4092398197439599396784525)
                      ·
                        rfl

theorem cell23_7969917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 2, 1, 2, 3].length) (baseStart_7969917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7969917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7969917 prefixEnd_7969917 := by exact prefixLift 7969917
  have htrace : WordTrace (prefixWord ++ tailWord_7969917) baseStart_7969917 baseEnd_7969917 := by
    simpa [prefixWord, tailWord_7969917, baseEnd_7969917] using wordTrace_append hprefix tailTrace_7969917
  have hstable : (prefixWord ++ tailWord_7969917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7969917).length < 2 ^ (prefixWord ++ tailWord_7969917).sum := by decide
  have hdescent : baseEnd_7969917 < baseStart_7969917 := by decide
  rcases family_descends (prefixWord ++ tailWord_7969917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7969930 : List Nat := [3, 1, 2, 3, 1, 1, 2, 1, 3, 3, 3]
def baseStart_7969930 : Nat := 118140960795 + 7969930 * 2 ^ 59
def prefixEnd_7969930 : Nat := 4983230072969 + 3 ^ 40 * 7969930 * 2
def baseEnd_7969930 : Nat := 4092404872688107845921965

theorem tailTrace_7969930 : CollatzResearch.WordTrace tailWord_7969930 prefixEnd_7969930 4092404872688107845921965 := by
  unfold tailWord_7969930
  simp only [CollatzResearch.WordTrace]
  refine ⟨72671807004078060130492811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193791485344208160347980829 72671807004078060130492811)
  ·
    refine ⟨109007710506117090195739217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72671807004078060130492811 109007710506117090195739217)
    ·
      refine ⟨81755782879587817646804413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109007710506117090195739217 81755782879587817646804413)
      ·
        refine ⟨30658418579845431617551655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81755782879587817646804413 30658418579845431617551655)
        ·
          refine ⟨45987627869768147426327483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30658418579845431617551655 45987627869768147426327483)
          ·
            refine ⟨68981441804652221139491225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45987627869768147426327483 68981441804652221139491225)
            ·
              refine ⟨51736081353489165854618419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68981441804652221139491225 51736081353489165854618419)
              ·
                refine ⟨77604122030233748781927629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51736081353489165854618419 77604122030233748781927629)
                ·
                  refine ⟨29101545761337655793222861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77604122030233748781927629 29101545761337655793222861)
                  ·
                    refine ⟨10913079660501620922458573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29101545761337655793222861 10913079660501620922458573)
                    ·
                      refine ⟨4092404872688107845921965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10913079660501620922458573 4092404872688107845921965)
                      ·
                        rfl

theorem cell23_7969930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_7969930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7969930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7969930 prefixEnd_7969930 := by exact prefixLift 7969930
  have htrace : WordTrace (prefixWord ++ tailWord_7969930) baseStart_7969930 baseEnd_7969930 := by
    simpa [prefixWord, tailWord_7969930, baseEnd_7969930] using wordTrace_append hprefix tailTrace_7969930
  have hstable : (prefixWord ++ tailWord_7969930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7969930).length < 2 ^ (prefixWord ++ tailWord_7969930).sum := by decide
  have hdescent : baseEnd_7969930 < baseStart_7969930 := by decide
  rcases family_descends (prefixWord ++ tailWord_7969930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7969948 : List Nat := [2, 2, 3, 2, 1, 3, 3, 2, 1, 2, 2]
def baseStart_7969948 : Nat := 118140960795 + 7969948 * 2 ^ 59
def prefixEnd_7969948 : Nat := 4983230072969 + 3 ^ 40 * 7969948 * 2
def baseEnd_7969948 : Nat := 4092414115339888775496883

theorem tailTrace_7969948 : CollatzResearch.WordTrace tailWord_7969948 prefixEnd_7969948 4092414115339888775496883 := by
  unfold tailWord_7969948
  simp only [CollatzResearch.WordTrace]
  refine ⟨145343942265123514798063249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193791923020164686397417665 145343942265123514798063249)
  ·
    refine ⟨109007956698842636098547437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145343942265123514798063249 109007956698842636098547437)
    ·
      refine ⟨40877983762065988536955289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109007956698842636098547437 40877983762065988536955289)
      ·
        refine ⟨30658487821549491402716467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40877983762065988536955289 30658487821549491402716467)
        ·
          refine ⟨45987731732324237104074701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30658487821549491402716467 45987731732324237104074701)
          ·
            refine ⟨17245399399621588914028013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45987731732324237104074701 17245399399621588914028013)
            ·
              refine ⟨6467024774858095842760505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17245399399621588914028013 6467024774858095842760505)
              ·
                refine ⟨4850268581143571882070379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6467024774858095842760505 4850268581143571882070379)
                ·
                  refine ⟨7275402871715357823105569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4850268581143571882070379 7275402871715357823105569)
                  ·
                    refine ⟨5456552153786518367329177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7275402871715357823105569 5456552153786518367329177)
                    ·
                      refine ⟨4092414115339888775496883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5456552153786518367329177 4092414115339888775496883)
                      ·
                        rfl

theorem cell23_7969948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 3, 2, 1, 2, 2].length) (baseStart_7969948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7969948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7969948 prefixEnd_7969948 := by exact prefixLift 7969948
  have htrace : WordTrace (prefixWord ++ tailWord_7969948) baseStart_7969948 baseEnd_7969948 := by
    simpa [prefixWord, tailWord_7969948, baseEnd_7969948] using wordTrace_append hprefix tailTrace_7969948
  have hstable : (prefixWord ++ tailWord_7969948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7969948).length < 2 ^ (prefixWord ++ tailWord_7969948).sum := by decide
  have hdescent : baseEnd_7969948 < baseStart_7969948 := by decide
  rcases family_descends (prefixWord ++ tailWord_7969948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7969987 : List Nat := [1, 1, 1, 3, 1, 1, 1, 6, 4, 2, 2]
def baseStart_7969987 : Nat := 118140960795 + 7969987 * 2 ^ 59
def prefixEnd_7969987 : Nat := 4983230072969 + 3 ^ 40 * 7969987 * 2
def baseEnd_7969987 : Nat := 4092434141085414122909203

theorem tailTrace_7969987 : CollatzResearch.WordTrace tailWord_7969987 prefixEnd_7969987 4092434141085414122909203 := by
  unfold tailWord_7969987
  simp only [CollatzResearch.WordTrace]
  refine ⟨290689306977105739256796215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193792871318070492837864143 290689306977105739256796215)
  ·
    refine ⟨436033960465658608885194323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290689306977105739256796215 436033960465658608885194323)
    ·
      refine ⟨654050940698487913327791485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436033960465658608885194323 654050940698487913327791485)
      ·
        refine ⟨245269102761932967497921807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 654050940698487913327791485 245269102761932967497921807)
        ·
          refine ⟨367903654142899451246882711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245269102761932967497921807 367903654142899451246882711)
          ·
            refine ⟨551855481214349176870324067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 367903654142899451246882711 551855481214349176870324067)
            ·
              refine ⟨827783221821523765305486101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 551855481214349176870324067 827783221821523765305486101)
              ·
                refine ⟨38802338522883926498694661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 827783221821523765305486101 38802338522883926498694661)
                ·
                  refine ⟨7275438473040736218505249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38802338522883926498694661 7275438473040736218505249)
                  ·
                    refine ⟨5456578854780552163878937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7275438473040736218505249 5456578854780552163878937)
                    ·
                      refine ⟨4092434141085414122909203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5456578854780552163878937 4092434141085414122909203)
                      ·
                        rfl

theorem cell23_7969987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 6, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 6, 4, 2, 2].length) (baseStart_7969987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7969987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7969987 prefixEnd_7969987 := by exact prefixLift 7969987
  have htrace : WordTrace (prefixWord ++ tailWord_7969987) baseStart_7969987 baseEnd_7969987 := by
    simpa [prefixWord, tailWord_7969987, baseEnd_7969987] using wordTrace_append hprefix tailTrace_7969987
  have hstable : (prefixWord ++ tailWord_7969987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7969987).length < 2 ^ (prefixWord ++ tailWord_7969987).sum := by decide
  have hdescent : baseEnd_7969987 < baseStart_7969987 := by decide
  rcases family_descends (prefixWord ++ tailWord_7969987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7970020 : List Nat := [2, 3, 1, 1, 1, 2, 3, 1, 1, 5, 3]
def baseStart_7970020 : Nat := 118140960795 + 7970020 * 2 ^ 59
def prefixEnd_7970020 : Nat := 4983230072969 + 3 ^ 40 * 7970020 * 2
def baseEnd_7970020 : Nat := 4092451085947012493796551

theorem tailTrace_7970020 : CollatzResearch.WordTrace tailWord_7970020 prefixEnd_7970020 4092451085947012493796551 := by
  unfold tailWord_7970020
  simp only [CollatzResearch.WordTrace]
  refine ⟨145345255292993092946373757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193793673723990790595165009 145345255292993092946373757)
  ·
    refine ⟨54504470734872409854890159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145345255292993092946373757 54504470734872409854890159)
    ·
      refine ⟨81756706102308614782335239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54504470734872409854890159 81756706102308614782335239)
      ·
        refine ⟨122635059153462922173502859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81756706102308614782335239 122635059153462922173502859)
        ·
          refine ⟨183952588730194383260254289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122635059153462922173502859 183952588730194383260254289)
          ·
            refine ⟨137964441547645787445190717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183952588730194383260254289 137964441547645787445190717)
            ·
              refine ⟨51736665580367170291946519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137964441547645787445190717 51736665580367170291946519)
              ·
                refine ⟨77604998370550755437919779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51736665580367170291946519 77604998370550755437919779)
                ·
                  refine ⟨116407497555826133156879669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77604998370550755437919779 116407497555826133156879669)
                  ·
                    refine ⟨10913202895858699983457469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 116407497555826133156879669 10913202895858699983457469)
                    ·
                      refine ⟨4092451085947012493796551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10913202895858699983457469 4092451085947012493796551)
                      ·
                        rfl

theorem cell23_7970020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 1, 5, 3].length) (baseStart_7970020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7970020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7970020 prefixEnd_7970020 := by exact prefixLift 7970020
  have htrace : WordTrace (prefixWord ++ tailWord_7970020) baseStart_7970020 baseEnd_7970020 := by
    simpa [prefixWord, tailWord_7970020, baseEnd_7970020] using wordTrace_append hprefix tailTrace_7970020
  have hstable : (prefixWord ++ tailWord_7970020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7970020).length < 2 ^ (prefixWord ++ tailWord_7970020).sum := by decide
  have hdescent : baseEnd_7970020 < baseStart_7970020 := by decide
  rcases family_descends (prefixWord ++ tailWord_7970020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7970044 : List Nat := [2, 2, 2, 1, 5, 1, 2, 3, 5]
def baseStart_7970044 : Nat := 118140960795 + 7970044 * 2 ^ 59
def prefixEnd_7970044 : Nat := 4983230072969 + 3 ^ 40 * 7970044 * 2
def baseEnd_7970044 : Nat := 454718156609191155544049

theorem tailTrace_7970044 : CollatzResearch.WordTrace tailWord_7970044 prefixEnd_7970044 454718156609191155544049 := by
  unfold tailWord_7970044
  simp only [CollatzResearch.WordTrace]
  refine ⟨145345692968949618995810593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193794257291932825327747457 145345692968949618995810593)
  ·
    refine ⟨109009269726712214246857945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145345692968949618995810593 109009269726712214246857945)
    ·
      refine ⟨81756952295034160685143459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109009269726712214246857945 81756952295034160685143459)
      ·
        refine ⟨122635428442551241027715189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81756952295034160685143459 122635428442551241027715189)
        ·
          refine ⟨11497071416489178846348299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 122635428442551241027715189 11497071416489178846348299)
          ·
            refine ⟨17245607124733768269522449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11497071416489178846348299 17245607124733768269522449)
            ·
              refine ⟨12934205343550326202141837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17245607124733768269522449 12934205343550326202141837)
              ·
                refine ⟨4850327003831372325803189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12934205343550326202141837 4850327003831372325803189)
                ·
                  refine ⟨454718156609191155544049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4850327003831372325803189 454718156609191155544049)
                  ·
                    rfl

theorem cell23_7970044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 3, 5].length) (baseStart_7970044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7970044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7970044 prefixEnd_7970044 := by exact prefixLift 7970044
  have htrace : WordTrace (prefixWord ++ tailWord_7970044) baseStart_7970044 baseEnd_7970044 := by
    simpa [prefixWord, tailWord_7970044, baseEnd_7970044] using wordTrace_append hprefix tailTrace_7970044
  have hstable : (prefixWord ++ tailWord_7970044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7970044).length < 2 ^ (prefixWord ++ tailWord_7970044).sum := by decide
  have hdescent : baseEnd_7970044 < baseStart_7970044 := by decide
  rcases family_descends (prefixWord ++ tailWord_7970044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7970077 : List Nat := [1, 4, 2, 3, 1, 1, 1, 2, 1, 3, 4]
def baseStart_7970077 : Nat := 118140960795 + 7970077 * 2 ^ 59
def prefixEnd_7970077 : Nat := 4983230072969 + 3 ^ 40 * 7970077 * 2
def baseEnd_7970077 : Nat := 4092480354344318770783789

theorem tailTrace_7970077 : CollatzResearch.WordTrace tailWord_7970077 prefixEnd_7970077 4092480354344318770783789 := by
  unfold tailWord_7970077
  simp only [CollatzResearch.WordTrace]
  refine ⟨290692589546779684627572485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193795059697853123085048323 290692589546779684627572485)
  ·
    refine ⟨54504860540021190867669841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 290692589546779684627572485 54504860540021190867669841)
    ·
      refine ⟨40878645405015893150752381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54504860540021190867669841 40878645405015893150752381)
      ·
        refine ⟨15329492026880959931532143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40878645405015893150752381 15329492026880959931532143)
        ·
          refine ⟨22994238040321439897298215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15329492026880959931532143 22994238040321439897298215)
          ·
            refine ⟨34491357060482159845947323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22994238040321439897298215 34491357060482159845947323)
            ·
              refine ⟨51737035590723239768920985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34491357060482159845947323 51737035590723239768920985)
              ·
                refine ⟨38802776693042429826690739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51737035590723239768920985 38802776693042429826690739)
                ·
                  refine ⟨58204165039563644740036109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38802776693042429826690739 58204165039563644740036109)
                  ·
                    refine ⟨21826561889836366777513541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58204165039563644740036109 21826561889836366777513541)
                    ·
                      refine ⟨4092480354344318770783789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21826561889836366777513541 4092480354344318770783789)
                      ·
                        rfl

theorem cell23_7970077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_7970077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7970077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7970077 prefixEnd_7970077 := by exact prefixLift 7970077
  have htrace : WordTrace (prefixWord ++ tailWord_7970077) baseStart_7970077 baseEnd_7970077 := by
    simpa [prefixWord, tailWord_7970077, baseEnd_7970077] using wordTrace_append hprefix tailTrace_7970077
  have hstable : (prefixWord ++ tailWord_7970077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7970077).length < 2 ^ (prefixWord ++ tailWord_7970077).sum := by decide
  have hdescent : baseEnd_7970077 < baseStart_7970077 := by decide
  rcases family_descends (prefixWord ++ tailWord_7970077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7970097 : List Nat := [1, 2, 2, 3, 3, 1, 2, 1, 1, 4, 3]
def baseStart_7970097 : Nat := 118140960795 + 7970097 * 2 ^ 59
def prefixEnd_7970097 : Nat := 4983230072969 + 3 ^ 40 * 7970097 * 2
def baseEnd_7970097 : Nat := 4092490623957408692533697

theorem tailTrace_7970097 : CollatzResearch.WordTrace tailWord_7970097 prefixEnd_7970097 4092490623957408692533697 := by
  unfold tailWord_7970097
  simp only [CollatzResearch.WordTrace]
  refine ⟨290693319006707228043300545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193795546004471485362200363 290693319006707228043300545)
  ·
    refine ⟨218019989255030421032475409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290693319006707228043300545 218019989255030421032475409)
    ·
      refine ⟨163514991941272815774356557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218019989255030421032475409 163514991941272815774356557)
      ·
        refine ⟨61318121977977305915383709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163514991941272815774356557 61318121977977305915383709)
        ·
          refine ⟨22994295741741489718268891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61318121977977305915383709 22994295741741489718268891)
          ·
            refine ⟨34491443612612234577403337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22994295741741489718268891 34491443612612234577403337)
            ·
              refine ⟨25868582709459175933052503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34491443612612234577403337 25868582709459175933052503)
              ·
                refine ⟨38802874064188763899578755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25868582709459175933052503 38802874064188763899578755)
                ·
                  refine ⟨58204311096283145849368133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38802874064188763899578755 58204311096283145849368133)
                  ·
                    refine ⟨10913308330553089846756525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58204311096283145849368133 10913308330553089846756525)
                    ·
                      refine ⟨4092490623957408692533697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10913308330553089846756525 4092490623957408692533697)
                      ·
                        rfl

theorem cell23_7970097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 1, 1, 4, 3].length) (baseStart_7970097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7970097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7970097 prefixEnd_7970097 := by exact prefixLift 7970097
  have htrace : WordTrace (prefixWord ++ tailWord_7970097) baseStart_7970097 baseEnd_7970097 := by
    simpa [prefixWord, tailWord_7970097, baseEnd_7970097] using wordTrace_append hprefix tailTrace_7970097
  have hstable : (prefixWord ++ tailWord_7970097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7970097).length < 2 ^ (prefixWord ++ tailWord_7970097).sum := by decide
  have hdescent : baseEnd_7970097 < baseStart_7970097 := by decide
  rcases family_descends (prefixWord ++ tailWord_7970097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7970130 : List Nat := [3, 2, 2, 1, 1, 1, 1, 1, 2, 9]
def baseStart_7970130 : Nat := 118140960795 + 7970130 * 2 ^ 59
def prefixEnd_7970130 : Nat := 4983230072969 + 3 ^ 40 * 7970130 * 2
def baseEnd_7970130 : Nat := 1364169189606335687807015

theorem tailTrace_7970130 : CollatzResearch.WordTrace tailWord_7970130 prefixEnd_7970130 1364169189606335687807015 := by
  unfold tailWord_7970130
  simp only [CollatzResearch.WordTrace]
  refine ⟨72673630653896918669812961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193796348410391783119501229 72673630653896918669812961)
  ·
    refine ⟨54505222990422689002359721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72673630653896918669812961 54505222990422689002359721)
    ·
      refine ⟨40878917242817016751769791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54505222990422689002359721 40878917242817016751769791)
      ·
        refine ⟨61318375864225525127654687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40878917242817016751769791 61318375864225525127654687)
        ·
          refine ⟨91977563796338287691482031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61318375864225525127654687 91977563796338287691482031)
          ·
            refine ⟨137966345694507431537223047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91977563796338287691482031 137966345694507431537223047)
            ·
              refine ⟨206949518541761147305834571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137966345694507431537223047 206949518541761147305834571)
              ·
                refine ⟨310424277812641720958751857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206949518541761147305834571 310424277812641720958751857)
                ·
                  refine ⟨232818208359481290719063893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 310424277812641720958751857 232818208359481290719063893)
                  ·
                    refine ⟨1364169189606335687807015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 232818208359481290719063893 1364169189606335687807015)
                    ·
                      rfl

theorem cell23_7970130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 2, 9].length) (baseStart_7970130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7970130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7970130 prefixEnd_7970130 := by exact prefixLift 7970130
  have htrace : WordTrace (prefixWord ++ tailWord_7970130) baseStart_7970130 baseEnd_7970130 := by
    simpa [prefixWord, tailWord_7970130, baseEnd_7970130] using wordTrace_append hprefix tailTrace_7970130
  have hstable : (prefixWord ++ tailWord_7970130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7970130).length < 2 ^ (prefixWord ++ tailWord_7970130).sum := by decide
  have hdescent : baseEnd_7970130 < baseStart_7970130 := by decide
  rcases family_descends (prefixWord ++ tailWord_7970130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7970137 : List Nat := [1, 2, 1, 2, 2, 2, 2, 1, 3, 5, 2]
def baseStart_7970137 : Nat := 118140960795 + 7970137 * 2 ^ 59
def prefixEnd_7970137 : Nat := 4983230072969 + 3 ^ 40 * 7970137 * 2
def baseEnd_7970137 : Nat := 4092511163183588536033513

theorem tailTrace_7970137 : CollatzResearch.WordTrace tailWord_7970137 prefixEnd_7970137 4092511163183588536033513 := by
  unfold tailWord_7970137
  simp only [CollatzResearch.WordTrace]
  refine ⟨290694777926562314874756665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193796518617708209916504443 290694777926562314874756665)
  ·
    refine ⟨218021083444921736156067499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290694777926562314874756665 218021083444921736156067499)
    ·
      refine ⟨327031625167382604234101249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218021083444921736156067499 327031625167382604234101249)
      ·
        refine ⟨245273718875536953175575937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327031625167382604234101249 245273718875536953175575937)
        ·
          refine ⟨183955289156652714881681953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245273718875536953175575937 183955289156652714881681953)
          ·
            refine ⟨137966466867489536161261465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183955289156652714881681953 137966466867489536161261465)
            ·
              refine ⟨103474850150617152120946099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137966466867489536161261465 103474850150617152120946099)
              ·
                refine ⟨155212275225925728181419149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103474850150617152120946099 155212275225925728181419149)
                ·
                  refine ⟨58204603209722148068032181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 155212275225925728181419149 58204603209722148068032181)
                  ·
                    refine ⟨5456681550911451381378017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58204603209722148068032181 5456681550911451381378017)
                    ·
                      refine ⟨4092511163183588536033513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5456681550911451381378017 4092511163183588536033513)
                      ·
                        rfl

theorem cell23_7970137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 3, 5, 2].length) (baseStart_7970137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7970137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7970137 prefixEnd_7970137 := by exact prefixLift 7970137
  have htrace : WordTrace (prefixWord ++ tailWord_7970137) baseStart_7970137 baseEnd_7970137 := by
    simpa [prefixWord, tailWord_7970137, baseEnd_7970137] using wordTrace_append hprefix tailTrace_7970137
  have hstable : (prefixWord ++ tailWord_7970137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7970137).length < 2 ^ (prefixWord ++ tailWord_7970137).sum := by decide
  have hdescent : baseEnd_7970137 < baseStart_7970137 := by decide
  rcases family_descends (prefixWord ++ tailWord_7970137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7970147 : List Nat := [1, 1, 1, 5, 2, 3, 1, 1, 3, 5]
def baseStart_7970147 : Nat := 118140960795 + 7970147 * 2 ^ 59
def prefixEnd_7970147 : Nat := 4983230072969 + 3 ^ 40 * 7970147 * 2
def baseEnd_7970147 : Nat := 1364172099330044498969489

theorem tailTrace_7970147 : CollatzResearch.WordTrace tailWord_7970147 prefixEnd_7970147 1364172099330044498969489 := by
  unfold tailWord_7970147
  simp only [CollatzResearch.WordTrace]
  refine ⟨290695142656526086582620695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193796761771017391055080463 290695142656526086582620695)
  ·
    refine ⟨436042713984789129873931043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290695142656526086582620695 436042713984789129873931043)
    ·
      refine ⟨654064070977183694810896565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436042713984789129873931043 654064070977183694810896565)
      ·
        refine ⟨61318506654110971388521553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 654064070977183694810896565 61318506654110971388521553)
        ·
          refine ⟨45988879990583228541391165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61318506654110971388521553 45988879990583228541391165)
          ·
            refine ⟨17245829996468710703021687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45988879990583228541391165 17245829996468710703021687)
            ·
              refine ⟨25868744994703066054532531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17245829996468710703021687 25868744994703066054532531)
              ·
                refine ⟨38803117492054599081798797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25868744994703066054532531 38803117492054599081798797)
                ·
                  refine ⟨14551169059520474655674549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38803117492054599081798797 14551169059520474655674549)
                  ·
                    refine ⟨1364172099330044498969489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14551169059520474655674549 1364172099330044498969489)
                    ·
                      rfl

theorem cell23_7970147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 1, 3, 5].length) (baseStart_7970147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7970147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7970147 prefixEnd_7970147 := by exact prefixLift 7970147
  have htrace : WordTrace (prefixWord ++ tailWord_7970147) baseStart_7970147 baseEnd_7970147 := by
    simpa [prefixWord, tailWord_7970147, baseEnd_7970147] using wordTrace_append hprefix tailTrace_7970147
  have hstable : (prefixWord ++ tailWord_7970147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7970147).length < 2 ^ (prefixWord ++ tailWord_7970147).sum := by decide
  have hdescent : baseEnd_7970147 < baseStart_7970147 := by decide
  rcases family_descends (prefixWord ++ tailWord_7970147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7970187 : List Nat := [1, 1, 1, 1, 4, 3, 1, 1, 5, 2, 3]
def baseStart_7970187 : Nat := 118140960795 + 7970187 * 2 ^ 59
def prefixEnd_7970187 : Nat := 4983230072969 + 3 ^ 40 * 7970187 * 2
def baseEnd_7970187 : Nat := 4092536837216313340408283

theorem tailTrace_7970187 : CollatzResearch.WordTrace tailWord_7970187 prefixEnd_7970187 4092536837216313340408283 := by
  unfold tailWord_7970187
  simp only [CollatzResearch.WordTrace]
  refine ⟨290696601576381173414076815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193797734384254115609384543 290696601576381173414076815)
  ·
    refine ⟨436044902364571760121115223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290696601576381173414076815 436044902364571760121115223)
    ·
      refine ⟨654067353546857640181672835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436044902364571760121115223 654067353546857640181672835)
      ·
        refine ⟨981101030320286460272509253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 654067353546857640181672835 981101030320286460272509253)
        ·
          refine ⟨183956443185053711301095485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 981101030320286460272509253 183956443185053711301095485)
          ·
            refine ⟨68983666194395141737910807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183956443185053711301095485 68983666194395141737910807)
            ·
              refine ⟨103475499291592712606866211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68983666194395141737910807 103475499291592712606866211)
              ·
                refine ⟨155213248937389068910299317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103475499291592712606866211 155213248937389068910299317)
                ·
                  refine ⟨14551242087880225210340561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 155213248937389068910299317 14551242087880225210340561)
                  ·
                    refine ⟨10913431565910168907755421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14551242087880225210340561 10913431565910168907755421)
                    ·
                      refine ⟨4092536837216313340408283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10913431565910168907755421 4092536837216313340408283)
                      ·
                        rfl

theorem cell23_7970187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 5, 2, 3].length) (baseStart_7970187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7970187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7970187 prefixEnd_7970187 := by exact prefixLift 7970187
  have htrace : WordTrace (prefixWord ++ tailWord_7970187) baseStart_7970187 baseEnd_7970187 := by
    simpa [prefixWord, tailWord_7970187, baseEnd_7970187] using wordTrace_append hprefix tailTrace_7970187
  have hstable : (prefixWord ++ tailWord_7970187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7970187).length < 2 ^ (prefixWord ++ tailWord_7970187).sum := by decide
  have hdescent : baseEnd_7970187 < baseStart_7970187 := by decide
  rcases family_descends (prefixWord ++ tailWord_7970187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7970197 : List Nat := [1, 3, 2, 1, 1, 2, 3, 3, 1, 2, 4]
def baseStart_7970197 : Nat := 118140960795 + 7970197 * 2 ^ 59
def prefixEnd_7970197 : Nat := 4983230072969 + 3 ^ 40 * 7970197 * 2
def baseEnd_7970197 : Nat := 4092541972022858301283237

theorem tailTrace_7970197 : CollatzResearch.WordTrace tailWord_7970197 prefixEnd_7970197 4092541972022858301283237 := by
  unfold tailWord_7970197
  simp only [CollatzResearch.WordTrace]
  refine ⟨290696966306344945121940845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193797977537563296747960563 290696966306344945121940845)
  ·
    refine ⟨109011362364879354420727817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290696966306344945121940845 109011362364879354420727817)
    ·
      refine ⟨81758521773659515815545863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109011362364879354420727817 81758521773659515815545863)
      ·
        refine ⟨122637782660489273723318795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81758521773659515815545863 122637782660489273723318795)
        ·
          refine ⟨183956673990733910584978193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122637782660489273723318795 183956673990733910584978193)
          ·
            refine ⟨137967505493050432938733645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183956673990733910584978193 137967505493050432938733645)
            ·
              refine ⟨51737814559893912352025117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137967505493050432938733645 51737814559893912352025117)
              ·
                refine ⟨19401680459960217132009419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51737814559893912352025117 19401680459960217132009419)
                ·
                  refine ⟨29102520689940325698014129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19401680459960217132009419 29102520689940325698014129)
                  ·
                    refine ⟨21826890517455244273510597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29102520689940325698014129 21826890517455244273510597)
                    ·
                      refine ⟨4092541972022858301283237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21826890517455244273510597 4092541972022858301283237)
                      ·
                        rfl

theorem cell23_7970197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 3, 1, 2, 4].length) (baseStart_7970197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7970197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7970197 prefixEnd_7970197 := by exact prefixLift 7970197
  have htrace : WordTrace (prefixWord ++ tailWord_7970197) baseStart_7970197 baseEnd_7970197 := by
    simpa [prefixWord, tailWord_7970197, baseEnd_7970197] using wordTrace_append hprefix tailTrace_7970197
  have hstable : (prefixWord ++ tailWord_7970197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7970197).length < 2 ^ (prefixWord ++ tailWord_7970197).sum := by decide
  have hdescent : baseEnd_7970197 < baseStart_7970197 := by decide
  rcases family_descends (prefixWord ++ tailWord_7970197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7970201 : List Nat := [1, 2, 1, 2, 1, 6, 1, 2, 3, 2, 2]
def baseStart_7970201 : Nat := 118140960795 + 7970201 * 2 ^ 59
def prefixEnd_7970201 : Nat := 4983230072969 + 3 ^ 40 * 7970201 * 2
def baseEnd_7970201 : Nat := 4092544025945476285633219

theorem tailTrace_7970201 : CollatzResearch.WordTrace tailWord_7970201 prefixEnd_7970201 4092544025945476285633219 := by
  unfold tailWord_7970201
  simp only [CollatzResearch.WordTrace]
  refine ⟨290697112198330453805086457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193798074798886969203390971 290697112198330453805086457)
  ·
    refine ⟨218022834148747840353814843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290697112198330453805086457 218022834148747840353814843)
    ·
      refine ⟨327034251223121760530722265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218022834148747840353814843 327034251223121760530722265)
      ·
        refine ⟨245275688417341320398041699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327034251223121760530722265 245275688417341320398041699)
        ·
          refine ⟨367913532626011980597062549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245275688417341320398041699 367913532626011980597062549)
          ·
            refine ⟨17245946841844311590487307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 367913532626011980597062549 17245946841844311590487307)
            ·
              refine ⟨25868920262766467385730961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17245946841844311590487307 25868920262766467385730961)
              ·
                refine ⟨19401690197074850539298221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25868920262766467385730961 19401690197074850539298221)
                ·
                  refine ⟨7275633823903068952236833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19401690197074850539298221 7275633823903068952236833)
                  ·
                    refine ⟨5456725367927301714177625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7275633823903068952236833 5456725367927301714177625)
                    ·
                      refine ⟨4092544025945476285633219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5456725367927301714177625 4092544025945476285633219)
                      ·
                        rfl

theorem cell23_7970201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 2, 3, 2, 2].length) (baseStart_7970201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7970201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7970201 prefixEnd_7970201 := by exact prefixLift 7970201
  have htrace : WordTrace (prefixWord ++ tailWord_7970201) baseStart_7970201 baseEnd_7970201 := by
    simpa [prefixWord, tailWord_7970201, baseEnd_7970201] using wordTrace_append hprefix tailTrace_7970201
  have hstable : (prefixWord ++ tailWord_7970201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7970201).length < 2 ^ (prefixWord ++ tailWord_7970201).sum := by decide
  have hdescent : baseEnd_7970201 < baseStart_7970201 := by decide
  rcases family_descends (prefixWord ++ tailWord_7970201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7970287 : List Nat := [1, 1, 2, 1, 4, 1, 2, 1, 4, 2, 4]
def baseStart_7970287 : Nat := 118140960795 + 7970287 * 2 ^ 59
def prefixEnd_7970287 : Nat := 4983230072969 + 3 ^ 40 * 7970287 * 2
def baseEnd_7970287 : Nat := 4092588185281762949157823

theorem tailTrace_7970287 : CollatzResearch.WordTrace tailWord_7970287 prefixEnd_7970287 4092588185281762949157823 := by
  unfold tailWord_7970287
  simp only [CollatzResearch.WordTrace]
  refine ⟨290700248876018890492717115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193800165917345926995144743 290700248876018890492717115)
  ·
    refine ⟨436050373314028335739075673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290700248876018890492717115 436050373314028335739075673)
    ·
      refine ⟨327037779985521251804306755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 436050373314028335739075673 327037779985521251804306755)
      ·
        refine ⟨490556669978281877706460133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327037779985521251804306755 490556669978281877706460133)
        ·
          refine ⟨91979375620927852069961275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 490556669978281877706460133 91979375620927852069961275)
          ·
            refine ⟨137969063431391778104941913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91979375620927852069961275 137969063431391778104941913)
            ·
              refine ⟨103476797573543833578706435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137969063431391778104941913 103476797573543833578706435)
              ·
                refine ⟨155215196360315750368059653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103476797573543833578706435 155215196360315750368059653)
                ·
                  refine ⟨29102849317559203194011185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 155215196360315750368059653 29102849317559203194011185)
                  ·
                    refine ⟨21827136988169402395508389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29102849317559203194011185 21827136988169402395508389)
                    ·
                      refine ⟨4092588185281762949157823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21827136988169402395508389 4092588185281762949157823)
                      ·
                        rfl

theorem cell23_7970287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 4, 2, 4].length) (baseStart_7970287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7970287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7970287 prefixEnd_7970287 := by exact prefixLift 7970287
  have htrace : WordTrace (prefixWord ++ tailWord_7970287) baseStart_7970287 baseEnd_7970287 := by
    simpa [prefixWord, tailWord_7970287, baseEnd_7970287] using wordTrace_append hprefix tailTrace_7970287
  have hstable : (prefixWord ++ tailWord_7970287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7970287).length < 2 ^ (prefixWord ++ tailWord_7970287).sum := by decide
  have hdescent : baseEnd_7970287 < baseStart_7970287 := by decide
  rcases family_descends (prefixWord ++ tailWord_7970287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7970347 : List Nat := [1, 1, 1, 1, 2, 1, 3, 1, 5, 3, 4]
def baseStart_7970347 : Nat := 118140960795 + 7970347 * 2 ^ 59
def prefixEnd_7970347 : Nat := 4983230072969 + 3 ^ 40 * 7970347 * 2
def baseEnd_7970347 : Nat := 4092618994121032714407547

theorem tailTrace_7970347 : CollatzResearch.WordTrace tailWord_7970347 prefixEnd_7970347 4092618994121032714407547 := by
  unfold tailWord_7970347
  simp only [CollatzResearch.WordTrace]
  refine ⟨290702437255801520739901295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193801624837201013826600863 290702437255801520739901295)
  ·
    refine ⟨436053655883702281109851943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290702437255801520739901295 436053655883702281109851943)
    ·
      refine ⟨654080483825553421664777915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436053655883702281109851943 654080483825553421664777915)
      ·
        refine ⟨981120725738330132497166873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 654080483825553421664777915 981120725738330132497166873)
        ·
          refine ⟨735840544303747599372875155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 981120725738330132497166873 735840544303747599372875155)
          ·
            refine ⟨1103760816455621399059312733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 735840544303747599372875155 1103760816455621399059312733)
            ·
              refine ⟨413910306170858024647242275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1103760816455621399059312733 413910306170858024647242275)
              ·
                refine ⟨620865459256287036970863413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 413910306170858024647242275 620865459256287036970863413)
                ·
                  refine ⟨58206136805276909716018445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 620865459256287036970863413 58206136805276909716018445)
                  ·
                    refine ⟨21827301301978841143506917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58206136805276909716018445 21827301301978841143506917)
                    ·
                      refine ⟨4092618994121032714407547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21827301301978841143506917 4092618994121032714407547)
                      ·
                        rfl

theorem cell23_7970347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 5, 3, 4].length) (baseStart_7970347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7970347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7970347 prefixEnd_7970347 := by exact prefixLift 7970347
  have htrace : WordTrace (prefixWord ++ tailWord_7970347) baseStart_7970347 baseEnd_7970347 := by
    simpa [prefixWord, tailWord_7970347, baseEnd_7970347] using wordTrace_append hprefix tailTrace_7970347
  have hstable : (prefixWord ++ tailWord_7970347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7970347).length < 2 ^ (prefixWord ++ tailWord_7970347).sum := by decide
  have hdescent : baseEnd_7970347 < baseStart_7970347 := by decide
  rcases family_descends (prefixWord ++ tailWord_7970347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7970358 : List Nat := [5, 1, 2, 1, 3, 1, 1, 1, 2, 3, 3]
def baseStart_7970358 : Nat := 118140960795 + 7970358 * 2 ^ 59
def prefixEnd_7970358 : Nat := 4983230072969 + 3 ^ 40 * 7970358 * 2
def baseEnd_7970358 : Nat := 4092624642408232171369997

theorem tailTrace_7970358 : CollatzResearch.WordTrace tailWord_7970358 prefixEnd_7970358 4092624642408232171369997 := by
  unfold tailWord_7970358
  simp only [CollatzResearch.WordTrace]
  refine ⟨18168927403672604351159483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 193801892305841113079034485 18168927403672604351159483)
  ·
    refine ⟨27253391105508906526739225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18168927403672604351159483 27253391105508906526739225)
    ·
      refine ⟨20440043329131679895054419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27253391105508906526739225 20440043329131679895054419)
      ·
        refine ⟨30660064993697519842581629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20440043329131679895054419 30660064993697519842581629)
        ·
          refine ⟨11497524372636569940968111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30660064993697519842581629 11497524372636569940968111)
          ·
            refine ⟨17246286558954854911452167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11497524372636569940968111 17246286558954854911452167)
            ·
              refine ⟨25869429838432282367178251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17246286558954854911452167 25869429838432282367178251)
              ·
                refine ⟨38804144757648423550767377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25869429838432282367178251 38804144757648423550767377)
                ·
                  refine ⟨29103108568236317663075533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38804144757648423550767377 29103108568236317663075533)
                  ·
                    refine ⟨10913665713088619123653325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29103108568236317663075533 10913665713088619123653325)
                    ·
                      refine ⟨4092624642408232171369997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10913665713088619123653325 4092624642408232171369997)
                      ·
                        rfl

theorem cell23_7970358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_7970358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7970358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7970358 prefixEnd_7970358 := by exact prefixLift 7970358
  have htrace : WordTrace (prefixWord ++ tailWord_7970358) baseStart_7970358 baseEnd_7970358 := by
    simpa [prefixWord, tailWord_7970358, baseEnd_7970358] using wordTrace_append hprefix tailTrace_7970358
  have hstable : (prefixWord ++ tailWord_7970358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7970358).length < 2 ^ (prefixWord ++ tailWord_7970358).sum := by decide
  have hdescent : baseEnd_7970358 < baseStart_7970358 := by decide
  rcases family_descends (prefixWord ++ tailWord_7970358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7970377 : List Nat := [1, 2, 1, 1, 2, 2, 1, 2, 4, 1, 6]
def baseStart_7970377 : Nat := 118140960795 + 7970377 * 2 ^ 59
def prefixEnd_7970377 : Nat := 4983230072969 + 3 ^ 40 * 7970377 * 2
def baseEnd_7970377 : Nat := 4092634398540667597032409

theorem tailTrace_7970377 : CollatzResearch.WordTrace tailWord_7970377 prefixEnd_7970377 4092634398540667597032409 := by
  unfold tailWord_7970377
  simp only [CollatzResearch.WordTrace]
  refine ⟨290703531445692835863493385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193802354297128557242328923 290703531445692835863493385)
  ·
    refine ⟨218027648584269626897620039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290703531445692835863493385 218027648584269626897620039)
    ·
      refine ⟨327041472876404440346430059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218027648584269626897620039 327041472876404440346430059)
      ·
        refine ⟨490562209314606660519645089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327041472876404440346430059 490562209314606660519645089)
        ·
          refine ⟨367921656985954995389733817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 490562209314606660519645089 367921656985954995389733817)
          ·
            refine ⟨275941242739466246542300363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 367921656985954995389733817 275941242739466246542300363)
            ·
              refine ⟨413911864109199369813450545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275941242739466246542300363 413911864109199369813450545)
              ·
                refine ⟨310433898081899527360087909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 413911864109199369813450545 310433898081899527360087909)
                ·
                  refine ⟨58206355890356161380016483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 310433898081899527360087909 58206355890356161380016483)
                  ·
                    refine ⟨87309533835534242070024725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58206355890356161380016483 87309533835534242070024725)
                    ·
                      refine ⟨4092634398540667597032409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87309533835534242070024725 4092634398540667597032409)
                      ·
                        rfl

theorem cell23_7970377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 4, 1, 6].length) (baseStart_7970377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7970377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7970377 prefixEnd_7970377 := by exact prefixLift 7970377
  have htrace : WordTrace (prefixWord ++ tailWord_7970377) baseStart_7970377 baseEnd_7970377 := by
    simpa [prefixWord, tailWord_7970377, baseEnd_7970377] using wordTrace_append hprefix tailTrace_7970377
  have hstable : (prefixWord ++ tailWord_7970377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7970377).length < 2 ^ (prefixWord ++ tailWord_7970377).sum := by decide
  have hdescent : baseEnd_7970377 < baseStart_7970377 := by decide
  rcases family_descends (prefixWord ++ tailWord_7970377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7970384 : List Nat := [2, 1, 1, 1, 1, 3, 5, 1, 1, 4, 3]
def baseStart_7970384 : Nat := 118140960795 + 7970384 * 2 ^ 59
def prefixEnd_7970384 : Nat := 4983230072969 + 3 ^ 40 * 7970384 * 2
def baseEnd_7970384 : Nat := 4092637992905249069644877

theorem tailTrace_7970384 : CollatzResearch.WordTrace tailWord_7970384 prefixEnd_7970384 4092637992905249069644877 := by
  unfold tailWord_7970384
  simp only [CollatzResearch.WordTrace]
  refine ⟨145351893378333738029499103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193802524504444984039332137 145351893378333738029499103)
  ·
    refine ⟨218027840067500607044248655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145351893378333738029499103 218027840067500607044248655)
    ·
      refine ⟨327041760101250910566372983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218027840067500607044248655 327041760101250910566372983)
      ·
        refine ⟨490562640151876365849559475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327041760101250910566372983 490562640151876365849559475)
        ·
          refine ⟨735843960227814548774339213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 490562640151876365849559475 735843960227814548774339213)
          ·
            refine ⟨275941485085430455790377205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 735843960227814548774339213 275941485085430455790377205)
            ·
              refine ⟨25869514226759105230347863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 275941485085430455790377205 25869514226759105230347863)
              ·
                refine ⟨38804271340138657845521795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25869514226759105230347863 38804271340138657845521795)
                ·
                  refine ⟨58206407010207986768282693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38804271340138657845521795 58206407010207986768282693)
                  ·
                    refine ⟨10913701314413997519053005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58206407010207986768282693 10913701314413997519053005)
                    ·
                      refine ⟨4092637992905249069644877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10913701314413997519053005 4092637992905249069644877)
                      ·
                        rfl

theorem cell23_7970384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 1, 1, 4, 3].length) (baseStart_7970384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7970384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7970384 prefixEnd_7970384 := by exact prefixLift 7970384
  have htrace : WordTrace (prefixWord ++ tailWord_7970384) baseStart_7970384 baseEnd_7970384 := by
    simpa [prefixWord, tailWord_7970384, baseEnd_7970384] using wordTrace_append hprefix tailTrace_7970384
  have hstable : (prefixWord ++ tailWord_7970384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7970384).length < 2 ^ (prefixWord ++ tailWord_7970384).sum := by decide
  have hdescent : baseEnd_7970384 < baseStart_7970384 := by decide
  rcases family_descends (prefixWord ++ tailWord_7970384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7970404 : List Nat := [2, 3, 1, 1, 2, 4, 1, 1, 8]
def baseStart_7970404 : Nat := 118140960795 + 7970404 * 2 ^ 59
def prefixEnd_7970404 : Nat := 4983230072969 + 3 ^ 40 * 7970404 * 2
def baseEnd_7970404 : Nat := 454738695835370999043865

theorem tailTrace_7970404 : CollatzResearch.WordTrace tailWord_7970404 prefixEnd_7970404 454738695835370999043865 := by
  unfold tailWord_7970404
  simp only [CollatzResearch.WordTrace]
  refine ⟨145352258108297509737363133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193803010811063346316484177 145352258108297509737363133)
  ·
    refine ⟨54507096790611566151511175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145352258108297509737363133 54507096790611566151511175)
    ·
      refine ⟨81760645185917349227266763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54507096790611566151511175 81760645185917349227266763)
      ·
        refine ⟨122640967778876023840900145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81760645185917349227266763 122640967778876023840900145)
        ·
          refine ⟨91980725834157017880675109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122640967778876023840900145 91980725834157017880675109)
          ·
            refine ⟨17246386093904440852626583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91980725834157017880675109 17246386093904440852626583)
            ·
              refine ⟨25869579140856661278939875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17246386093904440852626583 25869579140856661278939875)
              ·
                refine ⟨38804368711284991918409813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25869579140856661278939875 38804368711284991918409813)
                ·
                  refine ⟨454738695835370999043865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38804368711284991918409813 454738695835370999043865)
                  ·
                    rfl

theorem cell23_7970404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 1, 8].length) (baseStart_7970404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7970404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7970404 prefixEnd_7970404 := by exact prefixLift 7970404
  have htrace : WordTrace (prefixWord ++ tailWord_7970404) baseStart_7970404 baseEnd_7970404 := by
    simpa [prefixWord, tailWord_7970404, baseEnd_7970404] using wordTrace_append hprefix tailTrace_7970404
  have hstable : (prefixWord ++ tailWord_7970404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7970404).length < 2 ^ (prefixWord ++ tailWord_7970404).sum := by decide
  have hdescent : baseEnd_7970404 < baseStart_7970404 := by decide
  rcases family_descends (prefixWord ++ tailWord_7970404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7970408 : List Nat := [2, 1, 4, 3, 1, 2, 2, 1, 3, 4]
def baseStart_7970408 : Nat := 118140960795 + 7970408 * 2 ^ 59
def prefixEnd_7970408 : Nat := 4983230072969 + 3 ^ 40 * 7970408 * 2
def baseEnd_7970408 : Nat := 1364216772146985658581589

theorem tailTrace_7970408 : CollatzResearch.WordTrace tailWord_7970408 prefixEnd_7970408 1364216772146985658581589 := by
  unfold tailWord_7970408
  simp only [CollatzResearch.WordTrace]
  refine ⟨145352331054290264078935939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193803108072387018771914585 145352331054290264078935939)
  ·
    refine ⟨218028496581435396118403909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145352331054290264078935939 218028496581435396118403909)
    ·
      refine ⟨40880343109019136772200733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 218028496581435396118403909 40880343109019136772200733)
      ·
        refine ⟨15330128665882176289575275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40880343109019136772200733 15330128665882176289575275)
        ·
          refine ⟨22995192998823264434362913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15330128665882176289575275 22995192998823264434362913)
          ·
            refine ⟨17246394749117448325772185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22995192998823264434362913 17246394749117448325772185)
            ·
              refine ⟨12934796061838086244329139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17246394749117448325772185 12934796061838086244329139)
              ·
                refine ⟨19402194092757129366493709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12934796061838086244329139 19402194092757129366493709)
                ·
                  refine ⟨7275822784783923512435141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19402194092757129366493709 7275822784783923512435141)
                  ·
                    refine ⟨1364216772146985658581589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7275822784783923512435141 1364216772146985658581589)
                    ·
                      rfl

theorem cell23_7970408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 1, 3, 4].length) (baseStart_7970408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7970408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7970408 prefixEnd_7970408 := by exact prefixLift 7970408
  have htrace : WordTrace (prefixWord ++ tailWord_7970408) baseStart_7970408 baseEnd_7970408 := by
    simpa [prefixWord, tailWord_7970408, baseEnd_7970408] using wordTrace_append hprefix tailTrace_7970408
  have hstable : (prefixWord ++ tailWord_7970408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7970408).length < 2 ^ (prefixWord ++ tailWord_7970408).sum := by decide
  have hdescent : baseEnd_7970408 < baseStart_7970408 := by decide
  rcases family_descends (prefixWord ++ tailWord_7970408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7970441 : List Nat := [1, 2, 1, 1, 4, 1, 4, 1, 1, 5, 2]
def baseStart_7970441 : Nat := 118140960795 + 7970441 * 2 ^ 59
def prefixEnd_7970441 : Nat := 4983230072969 + 3 ^ 40 * 7970441 * 2
def baseEnd_7970441 : Nat := 4092667261302555346632115

theorem tailTrace_7970441 : CollatzResearch.WordTrace tailWord_7970441 prefixEnd_7970441 4092667261302555346632115 := by
  unfold tailWord_7970441
  simp only [CollatzResearch.WordTrace]
  refine ⟨290705865717460974793823177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193803910478307316529215451 290705865717460974793823177)
  ·
    refine ⟨218029399288095731095367383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290705865717460974793823177 218029399288095731095367383)
    ·
      refine ⟨327044098932143596643051075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218029399288095731095367383 327044098932143596643051075)
      ·
        refine ⟨490566148398215394964576613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327044098932143596643051075 490566148398215394964576613)
        ·
          refine ⟨91981152824665386555858115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 490566148398215394964576613 91981152824665386555858115)
          ·
            refine ⟨137971729236998079833787173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91981152824665386555858115 137971729236998079833787173)
            ·
              refine ⟨25869699231937139968835095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137971729236998079833787173 25869699231937139968835095)
              ·
                refine ⟨38804548847905709953252643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25869699231937139968835095 38804548847905709953252643)
                ·
                  refine ⟨58206823271858564929878965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38804548847905709953252643 58206823271858564929878965)
                  ·
                    refine ⟨5456889681736740462176153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58206823271858564929878965 5456889681736740462176153)
                    ·
                      refine ⟨4092667261302555346632115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5456889681736740462176153 4092667261302555346632115)
                      ·
                        rfl

theorem cell23_7970441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 1, 1, 5, 2].length) (baseStart_7970441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7970441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7970441 prefixEnd_7970441 := by exact prefixLift 7970441
  have htrace : WordTrace (prefixWord ++ tailWord_7970441) baseStart_7970441 baseEnd_7970441 := by
    simpa [prefixWord, tailWord_7970441, baseEnd_7970441] using wordTrace_append hprefix tailTrace_7970441
  have hstable : (prefixWord ++ tailWord_7970441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7970441).length < 2 ^ (prefixWord ++ tailWord_7970441).sum := by decide
  have hdescent : baseEnd_7970441 < baseStart_7970441 := by decide
  rcases family_descends (prefixWord ++ tailWord_7970441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7970465 : List Nat := [1, 2, 3, 3, 2, 3, 1, 1, 3, 1, 3]
def baseStart_7970465 : Nat := 118140960795 + 7970465 * 2 ^ 59
def prefixEnd_7970465 : Nat := 4983230072969 + 3 ^ 40 * 7970465 * 2
def baseEnd_7970465 : Nat := 4092679584838263252732005

theorem tailTrace_7970465 : CollatzResearch.WordTrace tailWord_7970465 prefixEnd_7970465 4092679584838263252732005 := by
  unfold tailWord_7970465
  simp only [CollatzResearch.WordTrace]
  refine ⟨290706741069374026892696849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193804494046249351261797899 290706741069374026892696849)
  ·
    refine ⟨218030055802030520169522637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290706741069374026892696849 218030055802030520169522637)
    ·
      refine ⟨81761270925761445063570989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218030055802030520169522637 81761270925761445063570989)
      ·
        refine ⟨30660476597160541898839121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81761270925761445063570989 30660476597160541898839121)
        ·
          refine ⟨22995357447870406424129341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30660476597160541898839121 22995357447870406424129341)
          ·
            refine ⟨8623259042951402409048503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22995357447870406424129341 8623259042951402409048503)
            ·
              refine ⟨12934888564427103613572755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8623259042951402409048503 12934888564427103613572755)
              ·
                refine ⟨19402332846640655420359133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12934888564427103613572755 19402332846640655420359133)
                ·
                  refine ⟨7275874817490245782634675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19402332846640655420359133 7275874817490245782634675)
                  ·
                    refine ⟨10913812226235368673952013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7275874817490245782634675 10913812226235368673952013)
                    ·
                      refine ⟨4092679584838263252732005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10913812226235368673952013 4092679584838263252732005)
                      ·
                        rfl

theorem cell23_7970465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_7970465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7970465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7970465 prefixEnd_7970465 := by exact prefixLift 7970465
  have htrace : WordTrace (prefixWord ++ tailWord_7970465) baseStart_7970465 baseEnd_7970465 := by
    simpa [prefixWord, tailWord_7970465, baseEnd_7970465] using wordTrace_append hprefix tailTrace_7970465
  have hstable : (prefixWord ++ tailWord_7970465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7970465).length < 2 ^ (prefixWord ++ tailWord_7970465).sum := by decide
  have hdescent : baseEnd_7970465 < baseStart_7970465 := by decide
  rcases family_descends (prefixWord ++ tailWord_7970465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7970485 : List Nat := [1, 3, 3, 3, 2, 2, 1, 2, 1, 5]
def baseStart_7970485 : Nat := 118140960795 + 7970485 * 2 ^ 59
def prefixEnd_7970485 : Nat := 4983230072969 + 3 ^ 40 * 7970485 * 2
def baseEnd_7970485 : Nat := 1364229951483784391493971

theorem tailTrace_7970485 : CollatzResearch.WordTrace tailWord_7970485 prefixEnd_7970485 1364229951483784391493971 := by
  unfold tailWord_7970485
  simp only [CollatzResearch.WordTrace]
  refine ⟨290707470529301570308424909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193804980352867713538949939 290707470529301570308424909)
  ·
    refine ⟨109015301448488088865659341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290707470529301570308424909 109015301448488088865659341)
    ·
      refine ⟨40880738043183033324622253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109015301448488088865659341 40880738043183033324622253)
      ·
        refine ⟨15330276766193637496733345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40880738043183033324622253 15330276766193637496733345)
        ·
          refine ⟨11497707574645228122550009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15330276766193637496733345 11497707574645228122550009)
          ·
            refine ⟨8623280680983921091912507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11497707574645228122550009 8623280680983921091912507)
            ·
              refine ⟨12934921021475881637868761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8623280680983921091912507 12934921021475881637868761)
              ·
                refine ⟨9701190766106911228401571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12934921021475881637868761 9701190766106911228401571)
                ·
                  refine ⟨14551786149160366842602357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9701190766106911228401571 14551786149160366842602357)
                  ·
                    refine ⟨1364229951483784391493971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14551786149160366842602357 1364229951483784391493971)
                    ·
                      rfl

theorem cell23_7970485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 2, 1, 5].length) (baseStart_7970485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7970485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7970485 prefixEnd_7970485 := by exact prefixLift 7970485
  have htrace : WordTrace (prefixWord ++ tailWord_7970485) baseStart_7970485 baseEnd_7970485 := by
    simpa [prefixWord, tailWord_7970485, baseEnd_7970485] using wordTrace_append hprefix tailTrace_7970485
  have hstable : (prefixWord ++ tailWord_7970485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7970485).length < 2 ^ (prefixWord ++ tailWord_7970485).sum := by decide
  have hdescent : baseEnd_7970485 < baseStart_7970485 := by decide
  rcases family_descends (prefixWord ++ tailWord_7970485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7970488 : List Nat := [2, 1, 2, 1, 2, 1, 1, 6, 3, 2, 2]
def baseStart_7970488 : Nat := 118140960795 + 7970488 * 2 ^ 59
def prefixEnd_7970488 : Nat := 4983230072969 + 3 ^ 40 * 7970488 * 2
def baseEnd_7970488 : Nat := 4092691394893316662744399

theorem tailTrace_7970488 : CollatzResearch.WordTrace tailWord_7970488 prefixEnd_7970488 4092691394893316662744399 := by
  unfold tailWord_7970488
  simp only [CollatzResearch.WordTrace]
  refine ⟨145353789974145350910392059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193805053298860467880522745 145353789974145350910392059)
  ·
    refine ⟨218030684961218026365588089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145353789974145350910392059 218030684961218026365588089)
    ·
      refine ⟨163523013720913519774191067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218030684961218026365588089 163523013720913519774191067)
      ·
        refine ⟨245284520581370279661286601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163523013720913519774191067 245284520581370279661286601)
        ·
          refine ⟨183963390436027709745964951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245284520581370279661286601 183963390436027709745964951)
          ·
            refine ⟨275945085654041564618947427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183963390436027709745964951 275945085654041564618947427)
            ·
              refine ⟨413917628481062346928421141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275945085654041564618947427 413917628481062346928421141)
              ·
                refine ⟨19402388835049797512269741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 413917628481062346928421141 19402388835049797512269741)
                ·
                  refine ⟨7275895813143674067101153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19402388835049797512269741 7275895813143674067101153)
                  ·
                    refine ⟨5456921859857755550325865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7275895813143674067101153 5456921859857755550325865)
                    ·
                      refine ⟨4092691394893316662744399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5456921859857755550325865 4092691394893316662744399)
                      ·
                        rfl

theorem cell23_7970488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 6, 3, 2, 2].length) (baseStart_7970488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7970488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7970488 prefixEnd_7970488 := by exact prefixLift 7970488
  have htrace : WordTrace (prefixWord ++ tailWord_7970488) baseStart_7970488 baseEnd_7970488 := by
    simpa [prefixWord, tailWord_7970488, baseEnd_7970488] using wordTrace_append hprefix tailTrace_7970488
  have hstable : (prefixWord ++ tailWord_7970488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7970488).length < 2 ^ (prefixWord ++ tailWord_7970488).sum := by decide
  have hdescent : baseEnd_7970488 < baseStart_7970488 := by decide
  rcases family_descends (prefixWord ++ tailWord_7970488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7970522 : List Nat := [3, 1, 1, 2, 2, 4, 1, 4, 1, 2, 2]
def baseStart_7970522 : Nat := 118140960795 + 7970522 * 2 ^ 59
def prefixEnd_7970522 : Nat := 4983230072969 + 3 ^ 40 * 7970522 * 2
def baseEnd_7970522 : Nat := 4092708853235569529719243

theorem tailTrace_7970522 : CollatzResearch.WordTrace tailWord_7970522 prefixEnd_7970522 4092708853235569529719243 := by
  unfold tailWord_7970522
  simp only [CollatzResearch.WordTrace]
  refine ⟨72677205007541881406880455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193805880020111683751681213 72677205007541881406880455)
  ·
    refine ⟨109015807511312822110320683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72677205007541881406880455 109015807511312822110320683)
    ·
      refine ⟨163523711266969233165481025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109015807511312822110320683 163523711266969233165481025)
      ·
        refine ⟨122642783450226924874110769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163523711266969233165481025 122642783450226924874110769)
        ·
          refine ⟨91982087587670193655583077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122642783450226924874110769 91982087587670193655583077)
          ·
            refine ⟨17246641422688161310421827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91982087587670193655583077 17246641422688161310421827)
            ·
              refine ⟨25869962134032241965632741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17246641422688161310421827 25869962134032241965632741)
              ·
                refine ⟨4850617900131045368556139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25869962134032241965632741 4850617900131045368556139)
                ·
                  refine ⟨7275926850196568052834209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4850617900131045368556139 7275926850196568052834209)
                  ·
                    refine ⟨5456945137647426039625657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7275926850196568052834209 5456945137647426039625657)
                    ·
                      refine ⟨4092708853235569529719243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5456945137647426039625657 4092708853235569529719243)
                      ·
                        rfl

theorem cell23_7970522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 4, 1, 2, 2].length) (baseStart_7970522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7970522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7970522 prefixEnd_7970522 := by exact prefixLift 7970522
  have htrace : WordTrace (prefixWord ++ tailWord_7970522) baseStart_7970522 baseEnd_7970522 := by
    simpa [prefixWord, tailWord_7970522, baseEnd_7970522] using wordTrace_append hprefix tailTrace_7970522
  have hstable : (prefixWord ++ tailWord_7970522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7970522).length < 2 ^ (prefixWord ++ tailWord_7970522).sum := by decide
  have hdescent : baseEnd_7970522 < baseStart_7970522 := by decide
  rcases family_descends (prefixWord ++ tailWord_7970522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7970535 : List Nat := [1, 1, 5, 4, 1, 1, 2, 1, 1, 2, 4]
def baseStart_7970535 : Nat := 118140960795 + 7970535 * 2 ^ 59
def prefixEnd_7970535 : Nat := 4983230072969 + 3 ^ 40 * 7970535 * 2
def baseEnd_7970535 : Nat := 4092715528484077978856683

theorem tailTrace_7970535 : CollatzResearch.WordTrace tailWord_7970535 prefixEnd_7970535 4092715528484077978856683 := by
  unfold tailWord_7970535
  simp only [CollatzResearch.WordTrace]
  refine ⟨290709294179120428847745059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193806196119413619231830039 290709294179120428847745059)
  ·
    refine ⟨436063941268680643271617589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290709294179120428847745059 436063941268680643271617589)
    ·
      refine ⟨40880994493938810306714149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 436063941268680643271617589 40880994493938810306714149)
      ·
        refine ⟨7665186467613526932508903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40880994493938810306714149 7665186467613526932508903)
        ·
          refine ⟨11497779701420290398763355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7665186467613526932508903 11497779701420290398763355)
          ·
            refine ⟨17246669552130435598145033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11497779701420290398763355 17246669552130435598145033)
            ·
              refine ⟨12935002164097826698608775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17246669552130435598145033 12935002164097826698608775)
              ·
                refine ⟨19402503246146740047913163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12935002164097826698608775 19402503246146740047913163)
                ·
                  refine ⟨29103754869220110071869745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19402503246146740047913163 29103754869220110071869745)
                  ·
                    refine ⟨21827816151915082553902309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29103754869220110071869745 21827816151915082553902309)
                    ·
                      refine ⟨4092715528484077978856683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21827816151915082553902309 4092715528484077978856683)
                      ·
                        rfl

theorem cell23_7970535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_7970535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7970535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7970535 prefixEnd_7970535 := by exact prefixLift 7970535
  have htrace : WordTrace (prefixWord ++ tailWord_7970535) baseStart_7970535 baseEnd_7970535 := by
    simpa [prefixWord, tailWord_7970535, baseEnd_7970535] using wordTrace_append hprefix tailTrace_7970535
  have hstable : (prefixWord ++ tailWord_7970535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7970535).length < 2 ^ (prefixWord ++ tailWord_7970535).sum := by decide
  have hdescent : baseEnd_7970535 < baseStart_7970535 := by decide
  rcases family_descends (prefixWord ++ tailWord_7970535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7970554 : List Nat := [3, 1, 1, 1, 1, 3, 1, 1, 3, 8]
def baseStart_7970554 : Nat := 118140960795 + 7970554 * 2 ^ 59
def prefixEnd_7970554 : Nat := 4983230072969 + 3 ^ 40 * 7970554 * 2
def baseEnd_7970554 : Nat := 1364241761538837801506365

theorem tailTrace_7970554 : CollatzResearch.WordTrace tailWord_7970554 prefixEnd_7970554 1364241761538837801506365 := by
  unfold tailWord_7970554
  simp only [CollatzResearch.WordTrace]
  refine ⟨72677496791512898773171679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193806658110701063395124477 72677496791512898773171679)
  ·
    refine ⟨109016245187269348159757519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72677496791512898773171679 109016245187269348159757519)
    ·
      refine ⟨163524367780904022239636279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109016245187269348159757519 163524367780904022239636279)
      ·
        refine ⟨245286551671356033359454419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163524367780904022239636279 245286551671356033359454419)
        ·
          refine ⟨367929827507034050039181629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245286551671356033359454419 367929827507034050039181629)
          ·
            refine ⟨137973685315137768764693111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 367929827507034050039181629 137973685315137768764693111)
            ·
              refine ⟨206960527972706653147039667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137973685315137768764693111 206960527972706653147039667)
              ·
                refine ⟨310440791959059979720559501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206960527972706653147039667 310440791959059979720559501)
                ·
                  refine ⟨116415296984647492395209813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 310440791959059979720559501 116415296984647492395209813)
                  ·
                    refine ⟨1364241761538837801506365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 116415296984647492395209813 1364241761538837801506365)
                    ·
                      rfl

theorem cell23_7970554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 3, 8].length) (baseStart_7970554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7970554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7970554 prefixEnd_7970554 := by exact prefixLift 7970554
  have htrace : WordTrace (prefixWord ++ tailWord_7970554) baseStart_7970554 baseEnd_7970554 := by
    simpa [prefixWord, tailWord_7970554, baseEnd_7970554] using wordTrace_append hprefix tailTrace_7970554
  have hstable : (prefixWord ++ tailWord_7970554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7970554).length < 2 ^ (prefixWord ++ tailWord_7970554).sum := by decide
  have hdescent : baseEnd_7970554 < baseStart_7970554 := by decide
  rcases family_descends (prefixWord ++ tailWord_7970554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7970566 : List Nat := [6, 2, 2, 1, 1, 1, 1, 1, 4, 4]
def baseStart_7970566 : Nat := 118140960795 + 7970566 * 2 ^ 59
def prefixEnd_7970566 : Nat := 4983230072969 + 3 ^ 40 * 7970566 * 2
def baseEnd_7970566 : Nat := 1364243815461455785856347

theorem tailTrace_7970566 : CollatzResearch.WordTrace tailWord_7970566 prefixEnd_7970566 1364243815461455785856347 := by
  unfold tailWord_7970566
  simp only [CollatzResearch.WordTrace]
  refine ⟨9084700776312753785691361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 193806949894672080761415701 9084700776312753785691361)
  ·
    refine ⟨6813525582234565339268521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9084700776312753785691361 6813525582234565339268521)
    ·
      refine ⟨5110144186675924004451391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6813525582234565339268521 5110144186675924004451391)
      ·
        refine ⟨7665216280013886006677087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5110144186675924004451391 7665216280013886006677087)
        ·
          refine ⟨11497824420020829010015631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7665216280013886006677087 11497824420020829010015631)
          ·
            refine ⟨17246736630031243515023447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11497824420020829010015631 17246736630031243515023447)
            ·
              refine ⟨25870104945046865272535171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17246736630031243515023447 25870104945046865272535171)
              ·
                refine ⟨38805157417570297908802757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25870104945046865272535171 38805157417570297908802757)
                ·
                  refine ⟨7275967015794430857900517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38805157417570297908802757 7275967015794430857900517)
                  ·
                    refine ⟨1364243815461455785856347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7275967015794430857900517 1364243815461455785856347)
                    ·
                      rfl

theorem cell23_7970566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_7970566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7970566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7970566 prefixEnd_7970566 := by exact prefixLift 7970566
  have htrace : WordTrace (prefixWord ++ tailWord_7970566) baseStart_7970566 baseEnd_7970566 := by
    simpa [prefixWord, tailWord_7970566, baseEnd_7970566] using wordTrace_append hprefix tailTrace_7970566
  have hstable : (prefixWord ++ tailWord_7970566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7970566).length < 2 ^ (prefixWord ++ tailWord_7970566).sum := by decide
  have hdescent : baseEnd_7970566 < baseStart_7970566 := by decide
  rcases family_descends (prefixWord ++ tailWord_7970566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7970573 : List Nat := [1, 7, 2, 1, 1, 1, 2, 1, 3, 2, 2]
def baseStart_7970573 : Nat := 118140960795 + 7970573 * 2 ^ 59
def prefixEnd_7970573 : Nat := 4983230072969 + 3 ^ 40 * 7970573 * 2
def baseEnd_7970573 : Nat := 4092735040748948830181509

theorem tailTrace_7970573 : CollatzResearch.WordTrace tailWord_7970573 prefixEnd_7970573 4092735040748948830181509 := by
  unfold tailWord_7970573
  simp only [CollatzResearch.WordTrace]
  refine ⟨290710680152982761337628373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193807120101988507558418915 290710680152982761337628373)
  ·
    refine ⟨6813531566085533468850665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 290710680152982761337628373 6813531566085533468850665)
    ·
      refine ⟨5110148674564150101637999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6813531566085533468850665 5110148674564150101637999)
      ·
        refine ⟨7665223011846225152456999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5110148674564150101637999 7665223011846225152456999)
        ·
          refine ⟨11497834517769337728685499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7665223011846225152456999 11497834517769337728685499)
          ·
            refine ⟨17246751776654006593028249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11497834517769337728685499 17246751776654006593028249)
            ·
              refine ⟨12935063832490504944771187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17246751776654006593028249 12935063832490504944771187)
              ·
                refine ⟨19402595748735757417156781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12935063832490504944771187 19402595748735757417156781)
                ·
                  refine ⟨7275973405775909031433793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19402595748735757417156781 7275973405775909031433793)
                  ·
                    refine ⟨5456980054331931773575345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7275973405775909031433793 5456980054331931773575345)
                    ·
                      refine ⟨4092735040748948830181509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5456980054331931773575345 4092735040748948830181509)
                      ·
                        rfl

theorem cell23_7970573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_7970573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7970573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7970573 prefixEnd_7970573 := by exact prefixLift 7970573
  have htrace : WordTrace (prefixWord ++ tailWord_7970573) baseStart_7970573 baseEnd_7970573 := by
    simpa [prefixWord, tailWord_7970573, baseEnd_7970573] using wordTrace_append hprefix tailTrace_7970573
  have hstable : (prefixWord ++ tailWord_7970573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7970573).length < 2 ^ (prefixWord ++ tailWord_7970573).sum := by decide
  have hdescent : baseEnd_7970573 < baseStart_7970573 := by decide
  rcases family_descends (prefixWord ++ tailWord_7970573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7970591 : List Nat := [1, 1, 2, 4, 2, 1, 1, 3, 2, 2, 4]
def baseStart_7970591 : Nat := 118140960795 + 7970591 * 2 ^ 59
def prefixEnd_7970591 : Nat := 4983230072969 + 3 ^ 40 * 7970591 * 2
def baseEnd_7970591 : Nat := 4092744283400729759756425

theorem tailTrace_7970591 : CollatzResearch.WordTrace tailWord_7970591 prefixEnd_7970591 4092744283400729759756425 := by
  unfold tailWord_7970591
  simp only [CollatzResearch.WordTrace]
  refine ⟨290711336666917550411783627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193807557777945033607855751 290711336666917550411783627)
  ·
    refine ⟨436067005000376325617675441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290711336666917550411783627 436067005000376325617675441)
    ·
      refine ⟨327050253750282244213256581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 436067005000376325617675441 327050253750282244213256581)
      ·
        refine ⟨61321922578177920789985609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 327050253750282244213256581 61321922578177920789985609)
        ·
          refine ⟨45991441933633440592489207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61321922578177920789985609 45991441933633440592489207)
          ·
            refine ⟨68987162900450160888733811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45991441933633440592489207 68987162900450160888733811)
            ·
              refine ⟨103480744350675241333100717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68987162900450160888733811 103480744350675241333100717)
              ·
                refine ⟨38805279131503215499912769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103480744350675241333100717 38805279131503215499912769)
                ·
                  refine ⟨29103959348627411624934577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38805279131503215499912769 29103959348627411624934577)
                  ·
                    refine ⟨21827969511470558718700933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29103959348627411624934577 21827969511470558718700933)
                    ·
                      refine ⟨4092744283400729759756425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21827969511470558718700933 4092744283400729759756425)
                      ·
                        rfl

theorem cell23_7970591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_7970591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7970591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7970591 prefixEnd_7970591 := by exact prefixLift 7970591
  have htrace : WordTrace (prefixWord ++ tailWord_7970591) baseStart_7970591 baseEnd_7970591 := by
    simpa [prefixWord, tailWord_7970591, baseEnd_7970591] using wordTrace_append hprefix tailTrace_7970591
  have hstable : (prefixWord ++ tailWord_7970591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7970591).length < 2 ^ (prefixWord ++ tailWord_7970591).sum := by decide
  have hdescent : baseEnd_7970591 < baseStart_7970591 := by decide
  rcases family_descends (prefixWord ++ tailWord_7970591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7970595 : List Nat := [1, 1, 1, 4, 2, 1, 2, 5, 2, 2, 2]
def baseStart_7970595 : Nat := 118140960795 + 7970595 * 2 ^ 59
def prefixEnd_7970595 : Nat := 4983230072969 + 3 ^ 40 * 7970595 * 2
def baseEnd_7970595 : Nat := 4092746337323347744106407

theorem tailTrace_7970595 : CollatzResearch.WordTrace tailWord_7970595 prefixEnd_7970595 4092746337323347744106407 := by
  unfold tailWord_7970595
  simp only [CollatzResearch.WordTrace]
  refine ⟨290711482558903059094929239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193807655039268706063286159 290711482558903059094929239)
  ·
    refine ⟨436067223838354588642393859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290711482558903059094929239 436067223838354588642393859)
    ·
      refine ⟨654100835757531882963590789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436067223838354588642393859 654100835757531882963590789)
      ·
        refine ⟨122643906704537228055673273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 654100835757531882963590789 122643906704537228055673273)
        ·
          refine ⟨91982930028402921041754955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122643906704537228055673273 91982930028402921041754955)
          ·
            refine ⟨137974395042604381562632433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91982930028402921041754955 137974395042604381562632433)
            ·
              refine ⟨103480796281953286171974325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137974395042604381562632433 103480796281953286171974325)
              ·
                refine ⟨9701324651433120578622593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 103480796281953286171974325 9701324651433120578622593)
                ·
                  refine ⟨7275993488574840433966945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9701324651433120578622593 7275993488574840433966945)
                  ·
                    refine ⟨5456995116431130325475209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7275993488574840433966945 5456995116431130325475209)
                    ·
                      refine ⟨4092746337323347744106407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5456995116431130325475209 4092746337323347744106407)
                      ·
                        rfl

theorem cell23_7970595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 5, 2, 2, 2].length) (baseStart_7970595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7970595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7970595 prefixEnd_7970595 := by exact prefixLift 7970595
  have htrace : WordTrace (prefixWord ++ tailWord_7970595) baseStart_7970595 baseEnd_7970595 := by
    simpa [prefixWord, tailWord_7970595, baseEnd_7970595] using wordTrace_append hprefix tailTrace_7970595
  have hstable : (prefixWord ++ tailWord_7970595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7970595).length < 2 ^ (prefixWord ++ tailWord_7970595).sum := by decide
  have hdescent : baseEnd_7970595 < baseStart_7970595 := by decide
  rcases family_descends (prefixWord ++ tailWord_7970595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7970612 : List Nat := [2, 5, 1, 1, 2, 1, 1, 2, 4, 2, 2]
def baseStart_7970612 : Nat := 118140960795 + 7970612 * 2 ^ 59
def prefixEnd_7970612 : Nat := 4983230072969 + 3 ^ 40 * 7970612 * 2
def baseEnd_7970612 : Nat := 4092755066494474177593829

theorem tailTrace_7970612 : CollatzResearch.WordTrace tailWord_7970612 prefixEnd_7970612 4092755066494474177593829 := by
  unfold tailWord_7970612
  simp only [CollatzResearch.WordTrace]
  refine ⟨145356051299920735499149045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193808068399894313998865393 145356051299920735499149045)
  ·
    refine ⟨13627129809367568953045223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 145356051299920735499149045 13627129809367568953045223)
    ·
      refine ⟨20440694714051353429567835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13627129809367568953045223 20440694714051353429567835)
      ·
        refine ⟨30661042071077030144351753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20440694714051353429567835 30661042071077030144351753)
        ·
          refine ⟨22995781553307772608263815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30661042071077030144351753 22995781553307772608263815)
          ·
            refine ⟨34493672329961658912395723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22995781553307772608263815 34493672329961658912395723)
            ·
              refine ⟨51740508494942488368593585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34493672329961658912395723 51740508494942488368593585)
              ·
                refine ⟨38805381371206866276445189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51740508494942488368593585 38805381371206866276445189)
                ·
                  refine ⟨7276009007101287426833473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38805381371206866276445189 7276009007101287426833473)
                  ·
                    refine ⟨5457006755325965570125105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7276009007101287426833473 5457006755325965570125105)
                    ·
                      refine ⟨4092755066494474177593829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5457006755325965570125105 4092755066494474177593829)
                      ·
                        rfl

theorem cell23_7970612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 2, 4, 2, 2].length) (baseStart_7970612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7970612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7970612 prefixEnd_7970612 := by exact prefixLift 7970612
  have htrace : WordTrace (prefixWord ++ tailWord_7970612) baseStart_7970612 baseEnd_7970612 := by
    simpa [prefixWord, tailWord_7970612, baseEnd_7970612] using wordTrace_append hprefix tailTrace_7970612
  have hstable : (prefixWord ++ tailWord_7970612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7970612).length < 2 ^ (prefixWord ++ tailWord_7970612).sum := by decide
  have hdescent : baseEnd_7970612 < baseStart_7970612 := by decide
  rcases family_descends (prefixWord ++ tailWord_7970612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7970631 : List Nat := [1, 1, 4, 1, 2, 1, 3, 1, 4, 5]
def baseStart_7970631 : Nat := 118140960795 + 7970631 * 2 ^ 59
def prefixEnd_7970631 : Nat := 4983230072969 + 3 ^ 40 * 7970631 * 2
def baseEnd_7970631 : Nat := 1364254940875636534418747

theorem tailTrace_7970631 : CollatzResearch.WordTrace tailWord_7970631 prefixEnd_7970631 1364254940875636534418747 := by
  unfold tailWord_7970631
  simp only [CollatzResearch.WordTrace]
  refine ⟨290712795586772637243239747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193808530391181758162159831 290712795586772637243239747)
  ·
    refine ⟨436069193380158955864859621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290712795586772637243239747 436069193380158955864859621)
    ·
      refine ⟨81762973758779804224661179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 436069193380158955864859621 81762973758779804224661179)
      ·
        refine ⟨122644460638169706336991769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81762973758779804224661179 122644460638169706336991769)
        ·
          refine ⟨91983345478627279752743827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122644460638169706336991769 91983345478627279752743827)
          ·
            refine ⟨137975018217940919629115741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91983345478627279752743827 137975018217940919629115741)
            ·
              refine ⟨51740631831727844860918403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137975018217940919629115741 51740631831727844860918403)
              ·
                refine ⟨77610947747591767291377605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51740631831727844860918403 77610947747591767291377605)
                ·
                  refine ⟨14552052702673456367133301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77610947747591767291377605 14552052702673456367133301)
                  ·
                    refine ⟨1364254940875636534418747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14552052702673456367133301 1364254940875636534418747)
                    ·
                      rfl

theorem cell23_7970631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 4, 5].length) (baseStart_7970631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7970631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7970631 prefixEnd_7970631 := by exact prefixLift 7970631
  have htrace : WordTrace (prefixWord ++ tailWord_7970631) baseStart_7970631 baseEnd_7970631 := by
    simpa [prefixWord, tailWord_7970631, baseEnd_7970631] using wordTrace_append hprefix tailTrace_7970631
  have hstable : (prefixWord ++ tailWord_7970631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7970631).length < 2 ^ (prefixWord ++ tailWord_7970631).sum := by decide
  have hdescent : baseEnd_7970631 < baseStart_7970631 := by decide
  rcases family_descends (prefixWord ++ tailWord_7970631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7970641 : List Nat := [1, 2, 2, 1, 5, 1, 1, 1, 1, 1, 7]
def baseStart_7970641 : Nat := 118140960795 + 7970641 * 2 ^ 59
def prefixEnd_7970641 : Nat := 4983230072969 + 3 ^ 40 * 7970641 * 2
def baseEnd_7970641 : Nat := 4092769957433454564131195

theorem tailTrace_7970641 : CollatzResearch.WordTrace tailWord_7970641 prefixEnd_7970641 4092769957433454564131195 := by
  unfold tailWord_7970641
  simp only [CollatzResearch.WordTrace]
  refine ⟨290713160316736408951103777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193808773544490939300735851 290713160316736408951103777)
  ·
    refine ⟨218034870237552306713327833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290713160316736408951103777 218034870237552306713327833)
    ·
      refine ⟨163526152678164230034995875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218034870237552306713327833 163526152678164230034995875)
      ·
        refine ⟨245289229017246345052493813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163526152678164230034995875 245289229017246345052493813)
        ·
          refine ⟨22995865220366844848671295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 245289229017246345052493813 22995865220366844848671295)
          ·
            refine ⟨34493797830550267273006943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22995865220366844848671295 34493797830550267273006943)
            ·
              refine ⟨51740696745825400909510415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34493797830550267273006943 51740696745825400909510415)
              ·
                refine ⟨77611045118738101364265623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51740696745825400909510415 77611045118738101364265623)
                ·
                  refine ⟨116416567678107152046398435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77611045118738101364265623 116416567678107152046398435)
                  ·
                    refine ⟨174624851517160728069597653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 116416567678107152046398435 174624851517160728069597653)
                    ·
                      refine ⟨4092769957433454564131195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 174624851517160728069597653 4092769957433454564131195)
                      ·
                        rfl

theorem cell23_7970641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 1, 7].length) (baseStart_7970641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7970641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7970641 prefixEnd_7970641 := by exact prefixLift 7970641
  have htrace : WordTrace (prefixWord ++ tailWord_7970641) baseStart_7970641 baseEnd_7970641 := by
    simpa [prefixWord, tailWord_7970641, baseEnd_7970641] using wordTrace_append hprefix tailTrace_7970641
  have hstable : (prefixWord ++ tailWord_7970641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7970641).length < 2 ^ (prefixWord ++ tailWord_7970641).sum := by decide
  have hdescent : baseEnd_7970641 < baseStart_7970641 := by decide
  rcases family_descends (prefixWord ++ tailWord_7970641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7970668 : List Nat := [2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 4]
def baseStart_7970668 : Nat := 118140960795 + 7970668 * 2 ^ 59
def prefixEnd_7970668 : Nat := 4983230072969 + 3 ^ 40 * 7970668 * 2
def baseEnd_7970668 : Nat := 4092783821411125958493571

theorem tailTrace_7970668 : CollatzResearch.WordTrace tailWord_7970668 prefixEnd_7970668 4092783821411125958493571 := by
  unfold tailWord_7970668
  simp only [CollatzResearch.WordTrace]
  refine ⟨145357072543819296281168329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193809430058425728374891105 145357072543819296281168329)
  ·
    refine ⟨109017804407864472210876247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145357072543819296281168329 109017804407864472210876247)
    ·
      refine ⟨163526706611796708316314371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109017804407864472210876247 163526706611796708316314371)
      ·
        refine ⟨245290059917695062474471557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163526706611796708316314371 245290059917695062474471557)
        ·
          refine ⟨45991886234567824213963417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 245290059917695062474471557 45991886234567824213963417)
          ·
            refine ⟨34493914675925868160472563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45991886234567824213963417 34493914675925868160472563)
            ·
              refine ⟨51740872013888802240708845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34493914675925868160472563 51740872013888802240708845)
              ·
                refine ⟨19402827005208300840265817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51740872013888802240708845 19402827005208300840265817)
                ·
                  refine ⟨14552120253906225630199363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19402827005208300840265817 14552120253906225630199363)
                  ·
                    refine ⟨21828180380859338445299045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14552120253906225630199363 21828180380859338445299045)
                    ·
                      refine ⟨4092783821411125958493571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21828180380859338445299045 4092783821411125958493571)
                      ·
                        rfl

theorem cell23_7970668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 4].length) (baseStart_7970668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7970668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7970668 prefixEnd_7970668 := by exact prefixLift 7970668
  have htrace : WordTrace (prefixWord ++ tailWord_7970668) baseStart_7970668 baseEnd_7970668 := by
    simpa [prefixWord, tailWord_7970668, baseEnd_7970668] using wordTrace_append hprefix tailTrace_7970668
  have hstable : (prefixWord ++ tailWord_7970668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7970668).length < 2 ^ (prefixWord ++ tailWord_7970668).sum := by decide
  have hdescent : baseEnd_7970668 < baseStart_7970668 := by decide
  rcases family_descends (prefixWord ++ tailWord_7970668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7970681 : List Nat := [1, 2, 1, 3, 2, 2, 2, 1, 2, 1, 6]
def baseStart_7970681 : Nat := 118140960795 + 7970681 * 2 ^ 59
def prefixEnd_7970681 : Nat := 4983230072969 + 3 ^ 40 * 7970681 * 2
def baseEnd_7970681 : Nat := 4092790496659634407631011

theorem tailTrace_7970681 : CollatzResearch.WordTrace tailWord_7970681 prefixEnd_7970681 4092790496659634407631011 := by
  unfold tailWord_7970681
  simp only [CollatzResearch.WordTrace]
  refine ⟨290714619236591495782559897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193809746157727663855039931 290714619236591495782559897)
  ·
    refine ⟨218035964427443621836919923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290714619236591495782559897 218035964427443621836919923)
    ·
      refine ⟨327053946641165432755379885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218035964427443621836919923 327053946641165432755379885)
      ·
        refine ⟨122645229990437037283267457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 327053946641165432755379885 122645229990437037283267457)
        ·
          refine ⟨91983922492827777962450593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122645229990437037283267457 91983922492827777962450593)
          ·
            refine ⟨68987941869620833471837945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91983922492827777962450593 68987941869620833471837945)
            ·
              refine ⟨51740956402215625103878459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68987941869620833471837945 51740956402215625103878459)
              ·
                refine ⟨77611434603323437655817689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51740956402215625103878459 77611434603323437655817689)
                ·
                  refine ⟨58208575952492578241863267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77611434603323437655817689 58208575952492578241863267)
                  ·
                    refine ⟨87312863928738867362794901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58208575952492578241863267 87312863928738867362794901)
                    ·
                      refine ⟨4092790496659634407631011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87312863928738867362794901 4092790496659634407631011)
                      ·
                        rfl

theorem cell23_7970681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 2, 1, 6].length) (baseStart_7970681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7970681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7970681 prefixEnd_7970681 := by exact prefixLift 7970681
  have htrace : WordTrace (prefixWord ++ tailWord_7970681) baseStart_7970681 baseEnd_7970681 := by
    simpa [prefixWord, tailWord_7970681, baseEnd_7970681] using wordTrace_append hprefix tailTrace_7970681
  have hstable : (prefixWord ++ tailWord_7970681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7970681).length < 2 ^ (prefixWord ++ tailWord_7970681).sum := by decide
  have hdescent : baseEnd_7970681 < baseStart_7970681 := by decide
  rcases family_descends (prefixWord ++ tailWord_7970681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7970688 : List Nat := [2, 1, 1, 2, 1, 2, 3, 4, 2, 2, 3]
def baseStart_7970688 : Nat := 118140960795 + 7970688 * 2 ^ 59
def prefixEnd_7970688 : Nat := 4983230072969 + 3 ^ 40 * 7970688 * 2
def baseEnd_7970688 : Nat := 4092794091024215880243479

theorem tailTrace_7970688 : CollatzResearch.WordTrace tailWord_7970688 prefixEnd_7970688 4092794091024215880243479 := by
  unfold tailWord_7970688
  simp only [CollatzResearch.WordTrace]
  refine ⟨145357437273783067989032359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193809916365044090652043145 145357437273783067989032359)
  ·
    refine ⟨218036155910674601983548539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145357437273783067989032359 218036155910674601983548539)
    ·
      refine ⟨327054233866011902975322809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218036155910674601983548539 327054233866011902975322809)
      ·
        refine ⟨245290675399508927231492107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327054233866011902975322809 245290675399508927231492107)
        ·
          refine ⟨367936013099263390847238161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245290675399508927231492107 367936013099263390847238161)
          ·
            refine ⟨275952009824447543135428621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 367936013099263390847238161 275952009824447543135428621)
            ·
              refine ⟨103482003684167828675785733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 275952009824447543135428621 103482003684167828675785733)
              ·
                refine ⟨19402875690781467876709825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103482003684167828675785733 19402875690781467876709825)
                ·
                  refine ⟨14552156768086100907532369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19402875690781467876709825 14552156768086100907532369)
                  ·
                    refine ⟨10914117576064575680649277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14552156768086100907532369 10914117576064575680649277)
                    ·
                      refine ⟨4092794091024215880243479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10914117576064575680649277 4092794091024215880243479)
                      ·
                        rfl

theorem cell23_7970688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 4, 2, 2, 3].length) (baseStart_7970688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7970688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7970688 prefixEnd_7970688 := by exact prefixLift 7970688
  have htrace : WordTrace (prefixWord ++ tailWord_7970688) baseStart_7970688 baseEnd_7970688 := by
    simpa [prefixWord, tailWord_7970688, baseEnd_7970688] using wordTrace_append hprefix tailTrace_7970688
  have hstable : (prefixWord ++ tailWord_7970688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7970688).length < 2 ^ (prefixWord ++ tailWord_7970688).sum := by decide
  have hdescent : baseEnd_7970688 < baseStart_7970688 := by decide
  rcases family_descends (prefixWord ++ tailWord_7970688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7970712 : List Nat := [2, 1, 2, 6, 1, 1, 1, 2, 3, 4]
def baseStart_7970712 : Nat := 118140960795 + 7970712 * 2 ^ 59
def prefixEnd_7970712 : Nat := 4983230072969 + 3 ^ 40 * 7970712 * 2
def baseEnd_7970712 : Nat := 1364268804853307928781123

theorem tailTrace_7970712 : CollatzResearch.WordTrace tailWord_7970712 prefixEnd_7970712 1364268804853307928781123 := by
  unfold tailWord_7970712
  simp only [CollatzResearch.WordTrace]
  refine ⟨145357874949739594038469195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193810499932986125384625593 145357874949739594038469195)
  ·
    refine ⟨218036812424609391057703793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145357874949739594038469195 218036812424609391057703793)
    ·
      refine ⟨163527609318457043293277845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218036812424609391057703793 163527609318457043293277845)
      ·
        refine ⟨7665356686802673904372399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 163527609318457043293277845 7665356686802673904372399)
        ·
          refine ⟨11498035030204010856558599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7665356686802673904372399 11498035030204010856558599)
          ·
            refine ⟨17247052545306016284837899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11498035030204010856558599 17247052545306016284837899)
            ·
              refine ⟨25870578817959024427256849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17247052545306016284837899 25870578817959024427256849)
              ·
                refine ⟨19402934113469268320442637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25870578817959024427256849 19402934113469268320442637)
                ·
                  refine ⟨7276100292550975620165989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19402934113469268320442637 7276100292550975620165989)
                  ·
                    refine ⟨1364268804853307928781123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7276100292550975620165989 1364268804853307928781123)
                    ·
                      rfl

theorem cell23_7970712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 2, 3, 4].length) (baseStart_7970712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7970712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7970712 prefixEnd_7970712 := by exact prefixLift 7970712
  have htrace : WordTrace (prefixWord ++ tailWord_7970712) baseStart_7970712 baseEnd_7970712 := by
    simpa [prefixWord, tailWord_7970712, baseEnd_7970712] using wordTrace_append hprefix tailTrace_7970712
  have hstable : (prefixWord ++ tailWord_7970712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7970712).length < 2 ^ (prefixWord ++ tailWord_7970712).sum := by decide
  have hdescent : baseEnd_7970712 < baseStart_7970712 := by decide
  rcases family_descends (prefixWord ++ tailWord_7970712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7970745 : List Nat := [1, 2, 1, 4, 2, 1, 2, 1, 4, 3, 2]
def baseStart_7970745 : Nat := 118140960795 + 7970745 * 2 ^ 59
def prefixEnd_7970745 : Nat := 4983230072969 + 3 ^ 40 * 7970745 * 2
def baseEnd_7970745 : Nat := 4092823359421522157230717

theorem tailTrace_7970745 : CollatzResearch.WordTrace tailWord_7970745 prefixEnd_7970745 4092823359421522157230717 := by
  unfold tailWord_7970745
  simp only [CollatzResearch.WordTrace]
  refine ⟨290716953508359634712889689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193811302338906423141926459 290716953508359634712889689)
  ·
    refine ⟨218037715131269726034667267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290716953508359634712889689 218037715131269726034667267)
    ·
      refine ⟨327056572696904589052000901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218037715131269726034667267 327056572696904589052000901)
      ·
        refine ⟨61323107380669610447250169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 327056572696904589052000901 61323107380669610447250169)
        ·
          refine ⟨45992330535502207835437627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61323107380669610447250169 45992330535502207835437627)
          ·
            refine ⟨68988495803253311753156441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45992330535502207835437627 68988495803253311753156441)
            ·
              refine ⟨51741371852439983814867331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68988495803253311753156441 51741371852439983814867331)
              ·
                refine ⟨77612057778659975722300997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51741371852439983814867331 77612057778659975722300997)
                ·
                  refine ⟨14552260833498745447931437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77612057778659975722300997 14552260833498745447931437)
                  ·
                    refine ⟨5457097812562029542974289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14552260833498745447931437 5457097812562029542974289)
                    ·
                      refine ⟨4092823359421522157230717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5457097812562029542974289 4092823359421522157230717)
                      ·
                        rfl

theorem cell23_7970745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 4, 3, 2].length) (baseStart_7970745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7970745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7970745 prefixEnd_7970745 := by exact prefixLift 7970745
  have htrace : WordTrace (prefixWord ++ tailWord_7970745) baseStart_7970745 baseEnd_7970745 := by
    simpa [prefixWord, tailWord_7970745, baseEnd_7970745] using wordTrace_append hprefix tailTrace_7970745
  have hstable : (prefixWord ++ tailWord_7970745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7970745).length < 2 ^ (prefixWord ++ tailWord_7970745).sum := by decide
  have hdescent : baseEnd_7970745 < baseStart_7970745 := by decide
  rcases family_descends (prefixWord ++ tailWord_7970745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7970752 : List Nat := [2, 1, 1, 2, 3, 2, 1, 6, 1, 1, 3]
def baseStart_7970752 : Nat := 118140960795 + 7970752 * 2 ^ 59
def prefixEnd_7970752 : Nat := 4983230072969 + 3 ^ 40 * 7970752 * 2
def baseEnd_7970752 : Nat := 4092826953786103629843185

theorem tailTrace_7970752 : CollatzResearch.WordTrace tailWord_7970752 prefixEnd_7970752 4092826953786103629843185 := by
  unfold tailWord_7970752
  simp only [CollatzResearch.WordTrace]
  refine ⟨145358604409667137454197255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193811472546222849938929673 145358604409667137454197255)
  ·
    refine ⟨218037906614500706181295883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145358604409667137454197255 218037906614500706181295883)
    ·
      refine ⟨327056859921751059271943825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218037906614500706181295883 327056859921751059271943825)
      ·
        refine ⟨245292644941313294453957869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327056859921751059271943825 245292644941313294453957869)
        ·
          refine ⟨91984741852992485420234201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 245292644941313294453957869 91984741852992485420234201)
          ·
            refine ⟨68988556389744364065175651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91984741852992485420234201 68988556389744364065175651)
            ·
              refine ⟨103482834584616546097763477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68988556389744364065175651 103482834584616546097763477)
              ·
                refine ⟨4850757871153900598332663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 103482834584616546097763477 4850757871153900598332663)
                ·
                  refine ⟨7276136806730850897498995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4850757871153900598332663 7276136806730850897498995)
                  ·
                    refine ⟨10914205210096276346248493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7276136806730850897498995 10914205210096276346248493)
                    ·
                      refine ⟨4092826953786103629843185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10914205210096276346248493 4092826953786103629843185)
                      ·
                        rfl

theorem cell23_7970752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 6, 1, 1, 3].length) (baseStart_7970752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7970752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7970752 prefixEnd_7970752 := by exact prefixLift 7970752
  have htrace : WordTrace (prefixWord ++ tailWord_7970752) baseStart_7970752 baseEnd_7970752 := by
    simpa [prefixWord, tailWord_7970752, baseEnd_7970752] using wordTrace_append hprefix tailTrace_7970752
  have hstable : (prefixWord ++ tailWord_7970752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7970752).length < 2 ^ (prefixWord ++ tailWord_7970752).sum := by decide
  have hdescent : baseEnd_7970752 < baseStart_7970752 := by decide
  rcases family_descends (prefixWord ++ tailWord_7970752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7970768 : List Nat := [2, 1, 1, 1, 1, 2, 7, 1, 1, 6]
def baseStart_7970768 : Nat := 118140960795 + 7970768 * 2 ^ 59
def prefixEnd_7970768 : Nat := 4983230072969 + 3 ^ 40 * 7970768 * 2
def baseEnd_7970768 : Nat := 1364278389825525189081037

theorem tailTrace_7970768 : CollatzResearch.WordTrace tailWord_7970768 prefixEnd_7970768 1364278389825525189081037 := by
  unfold tailWord_7970768
  simp only [CollatzResearch.WordTrace]
  refine ⟨145358896193638154820488479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193811861591517539760651305 145358896193638154820488479)
  ·
    refine ⟨218038344290457232230732719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145358896193638154820488479 218038344290457232230732719)
    ·
      refine ⟨327057516435685848346099079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218038344290457232230732719 327057516435685848346099079)
      ·
        refine ⟨490586274653528772519148619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327057516435685848346099079 490586274653528772519148619)
        ·
          refine ⟨735879411980293158778722929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 490586274653528772519148619 735879411980293158778722929)
          ·
            refine ⟨551909558985219869084042197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 735879411980293158778722929 551909558985219869084042197)
            ·
              refine ⟨12935380288716090681657239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 551909558985219869084042197 12935380288716090681657239)
              ·
                refine ⟨19403070433074136022485859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12935380288716090681657239 19403070433074136022485859)
                ·
                  refine ⟨29104605649611204033728789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19403070433074136022485859 29104605649611204033728789)
                  ·
                    refine ⟨1364278389825525189081037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29104605649611204033728789 1364278389825525189081037)
                    ·
                      rfl

theorem cell23_7970768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 1, 1, 6].length) (baseStart_7970768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7970768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7970768 prefixEnd_7970768 := by exact prefixLift 7970768
  have htrace : WordTrace (prefixWord ++ tailWord_7970768) baseStart_7970768 baseEnd_7970768 := by
    simpa [prefixWord, tailWord_7970768, baseEnd_7970768] using wordTrace_append hprefix tailTrace_7970768
  have hstable : (prefixWord ++ tailWord_7970768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7970768).length < 2 ^ (prefixWord ++ tailWord_7970768).sum := by decide
  have hdescent : baseEnd_7970768 < baseStart_7970768 := by decide
  rcases family_descends (prefixWord ++ tailWord_7970768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7970775 : List Nat := [1, 1, 3, 2, 1, 1, 6, 2, 1, 1, 4]
def baseStart_7970775 : Nat := 118140960795 + 7970775 * 2 ^ 59
def prefixEnd_7970775 : Nat := 4983230072969 + 3 ^ 40 * 7970775 * 2
def baseEnd_7970775 : Nat := 4092838763841157039855579

theorem tailTrace_7970775 : CollatzResearch.WordTrace tailWord_7970775 prefixEnd_7970775 4092838763841157039855579 := by
  unfold tailWord_7970775
  simp only [CollatzResearch.WordTrace]
  refine ⟨290718047698250949836481779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193812031798833966557654519 290718047698250949836481779)
  ·
    refine ⟨436077071547376424754722669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290718047698250949836481779 436077071547376424754722669)
    ·
      refine ⟨163528901830266159283021001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 436077071547376424754722669 163528901830266159283021001)
      ·
        refine ⟨122646676372699619462265751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163528901830266159283021001 122646676372699619462265751)
        ·
          refine ⟨183970014559049429193398627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122646676372699619462265751 183970014559049429193398627)
          ·
            refine ⟨275955021838574143790097941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183970014559049429193398627 275955021838574143790097941)
            ·
              refine ⟨12935391648683162990160841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 275955021838574143790097941 12935391648683162990160841)
              ·
                refine ⟨9701543736512372242620631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12935391648683162990160841 9701543736512372242620631)
                ·
                  refine ⟨14552315604768558363930947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9701543736512372242620631 14552315604768558363930947)
                  ·
                    refine ⟨21828473407152837545896421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14552315604768558363930947 21828473407152837545896421)
                    ·
                      refine ⟨4092838763841157039855579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21828473407152837545896421 4092838763841157039855579)
                      ·
                        rfl

theorem cell23_7970775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 2, 1, 1, 4].length) (baseStart_7970775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7970775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7970775 prefixEnd_7970775 := by exact prefixLift 7970775
  have htrace : WordTrace (prefixWord ++ tailWord_7970775) baseStart_7970775 baseEnd_7970775 := by
    simpa [prefixWord, tailWord_7970775, baseEnd_7970775] using wordTrace_append hprefix tailTrace_7970775
  have hstable : (prefixWord ++ tailWord_7970775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7970775).length < 2 ^ (prefixWord ++ tailWord_7970775).sum := by decide
  have hdescent : baseEnd_7970775 < baseStart_7970775 := by decide
  rcases family_descends (prefixWord ++ tailWord_7970775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7970780 : List Nat := [2, 2, 6, 1, 2, 1, 1, 3, 1, 4]
def baseStart_7970780 : Nat := 118140960795 + 7970780 * 2 ^ 59
def prefixEnd_7970780 : Nat := 4983230072969 + 3 ^ 40 * 7970780 * 2
def baseEnd_7970780 : Nat := 1364280443748143173431019

theorem tailTrace_7970780 : CollatzResearch.WordTrace tailWord_7970780 prefixEnd_7970780 1364280443748143173431019 := by
  unfold tailWord_7970780
  simp only [CollatzResearch.WordTrace]
  refine ⟨145359115031616417845206897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193812153375488557126942529 145359115031616417845206897)
  ·
    refine ⟨109019336273712313383905173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145359115031616417845206897 109019336273712313383905173)
    ·
      refine ⟨5110281387830264689870555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 109019336273712313383905173 5110281387830264689870555)
      ·
        refine ⟨7665422081745397034805833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5110281387830264689870555 7665422081745397034805833)
        ·
          refine ⟨5749066561309047776104375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7665422081745397034805833 5749066561309047776104375)
          ·
            refine ⟨8623599841963571664156563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5749066561309047776104375 8623599841963571664156563)
            ·
              refine ⟨12935399762945357496234845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8623599841963571664156563 12935399762945357496234845)
              ·
                refine ⟨4850774911104509061088067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12935399762945357496234845 4850774911104509061088067)
                ·
                  refine ⟨7276162366656763591632101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4850774911104509061088067 7276162366656763591632101)
                  ·
                    refine ⟨1364280443748143173431019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7276162366656763591632101 1364280443748143173431019)
                    ·
                      rfl

theorem cell23_7970780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_7970780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7970780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7970780 prefixEnd_7970780 := by exact prefixLift 7970780
  have htrace : WordTrace (prefixWord ++ tailWord_7970780) baseStart_7970780 baseEnd_7970780 := by
    simpa [prefixWord, tailWord_7970780, baseEnd_7970780] using wordTrace_append hprefix tailTrace_7970780
  have hstable : (prefixWord ++ tailWord_7970780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7970780).length < 2 ^ (prefixWord ++ tailWord_7970780).sum := by decide
  have hdescent : baseEnd_7970780 < baseStart_7970780 := by decide
  rcases family_descends (prefixWord ++ tailWord_7970780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7970788 : List Nat := [2, 3, 1, 1, 1, 1, 4, 1, 3, 2, 4]
def baseStart_7970788 : Nat := 118140960795 + 7970788 * 2 ^ 59
def prefixEnd_7970788 : Nat := 4983230072969 + 3 ^ 40 * 7970788 * 2
def baseEnd_7970788 : Nat := 4092845439089665488993019

theorem tailTrace_7970788 : CollatzResearch.WordTrace tailWord_7970788 prefixEnd_7970788 4092845439089665488993019 := by
  unfold tailWord_7970788
  simp only [CollatzResearch.WordTrace]
  refine ⟨145359260923601926528352509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193812347898135902037803345 145359260923601926528352509)
  ·
    refine ⟨54509722846350722448132191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145359260923601926528352509 54509722846350722448132191)
    ·
      refine ⟨81764584269526083672198287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54509722846350722448132191 81764584269526083672198287)
      ·
        refine ⟨122646876404289125508297431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81764584269526083672198287 122646876404289125508297431)
        ·
          refine ⟨183970314606433688262446147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122646876404289125508297431 183970314606433688262446147)
          ·
            refine ⟨275955471909650532393669221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183970314606433688262446147 275955471909650532393669221)
            ·
              refine ⟨51741650983059474823812979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 275955471909650532393669221 51741650983059474823812979)
              ·
                refine ⟨77612476474589212235719469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51741650983059474823812979 77612476474589212235719469)
                ·
                  refine ⟨29104678677970954588394801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77612476474589212235719469 29104678677970954588394801)
                  ·
                    refine ⟨21828509008478215941296101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29104678677970954588394801 21828509008478215941296101)
                    ·
                      refine ⟨4092845439089665488993019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21828509008478215941296101 4092845439089665488993019)
                      ·
                        rfl

theorem cell23_7970788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 3, 2, 4].length) (baseStart_7970788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7970788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7970788 prefixEnd_7970788 := by exact prefixLift 7970788
  have htrace : WordTrace (prefixWord ++ tailWord_7970788) baseStart_7970788 baseEnd_7970788 := by
    simpa [prefixWord, tailWord_7970788, baseEnd_7970788] using wordTrace_append hprefix tailTrace_7970788
  have hstable : (prefixWord ++ tailWord_7970788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7970788).length < 2 ^ (prefixWord ++ tailWord_7970788).sum := by decide
  have hdescent : baseEnd_7970788 < baseStart_7970788 := by decide
  rcases family_descends (prefixWord ++ tailWord_7970788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7970798 : List Nat := [4, 1, 2, 1, 3, 1, 11]
def baseStart_7970798 : Nat := 118140960795 + 7970798 * 2 ^ 59
def prefixEnd_7970798 : Nat := 4983230072969 + 3 ^ 40 * 7970798 * 2
def baseEnd_7970798 : Nat := 50529019430817412961333

theorem tailTrace_7970798 : CollatzResearch.WordTrace tailWord_7970798 prefixEnd_7970798 50529019430817412961333 := by
  unfold tailWord_7970798
  simp only [CollatzResearch.WordTrace]
  refine ⟨36339860822145953095571131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193812591051445083176379365 36339860822145953095571131)
  ·
    refine ⟨54509791233218929643356697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36339860822145953095571131 54509791233218929643356697)
    ·
      refine ⟨40882343424914197232517523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54509791233218929643356697 40882343424914197232517523)
      ·
        refine ⟨61323515137371295848776285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40882343424914197232517523 61323515137371295848776285)
        ·
          refine ⟨22996318176514235943291107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61323515137371295848776285 22996318176514235943291107)
          ·
            refine ⟨34494477264771353914936661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22996318176514235943291107 34494477264771353914936661)
            ·
              refine ⟨50529019430817412961333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 34494477264771353914936661 50529019430817412961333)
              ·
                rfl

theorem cell23_7970798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 11].length) (baseStart_7970798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7970798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7970798 prefixEnd_7970798 := by exact prefixLift 7970798
  have htrace : WordTrace (prefixWord ++ tailWord_7970798) baseStart_7970798 baseEnd_7970798 := by
    simpa [prefixWord, tailWord_7970798, baseEnd_7970798] using wordTrace_append hprefix tailTrace_7970798
  have hstable : (prefixWord ++ tailWord_7970798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7970798).length < 2 ^ (prefixWord ++ tailWord_7970798).sum := by decide
  have hdescent : baseEnd_7970798 < baseStart_7970798 := by decide
  rcases family_descends (prefixWord ++ tailWord_7970798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7970809 : List Nat := [1, 2, 1, 3, 1, 6, 1, 1, 3, 2, 2]
def baseStart_7970809 : Nat := 118140960795 + 7970809 * 2 ^ 59
def prefixEnd_7970809 : Nat := 4983230072969 + 3 ^ 40 * 7970809 * 2
def baseEnd_7970809 : Nat := 4092856222183409906830423

theorem tailTrace_7970809 : CollatzResearch.WordTrace tailWord_7970809 prefixEnd_7970809 4092856222183409906830423 := by
  unfold tailWord_7970809
  simp only [CollatzResearch.WordTrace]
  refine ⟨290719287780127773643219481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193812858520085182428812987 290719287780127773643219481)
  ·
    refine ⟨218039465835095830232414611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290719287780127773643219481 218039465835095830232414611)
    ·
      refine ⟨327059198752643745348621917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218039465835095830232414611 327059198752643745348621917)
      ·
        refine ⟨122647199532241404505733219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 327059198752643745348621917 122647199532241404505733219)
        ·
          refine ⟨183970799298362106758599829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122647199532241404505733219 183970799298362106758599829)
          ·
            refine ⟨8623631217110723754309367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 183970799298362106758599829 8623631217110723754309367)
            ·
              refine ⟨12935446825666085631464051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8623631217110723754309367 12935446825666085631464051)
              ·
                refine ⟨19403170238499128447196077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12935446825666085631464051 19403170238499128447196077)
                ·
                  refine ⟨7276188839437173167698529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19403170238499128447196077 7276188839437173167698529)
                  ·
                    refine ⟨5457141629577879875773897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7276188839437173167698529 5457141629577879875773897)
                    ·
                      refine ⟨4092856222183409906830423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5457141629577879875773897 4092856222183409906830423)
                      ·
                        rfl

theorem cell23_7970809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 1, 3, 2, 2].length) (baseStart_7970809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7970809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7970809 prefixEnd_7970809 := by exact prefixLift 7970809
  have htrace : WordTrace (prefixWord ++ tailWord_7970809) baseStart_7970809 baseEnd_7970809 := by
    simpa [prefixWord, tailWord_7970809, baseEnd_7970809] using wordTrace_append hprefix tailTrace_7970809
  have hstable : (prefixWord ++ tailWord_7970809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7970809).length < 2 ^ (prefixWord ++ tailWord_7970809).sum := by decide
  have hdescent : baseEnd_7970809 < baseStart_7970809 := by decide
  rcases family_descends (prefixWord ++ tailWord_7970809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7970886 : List Nat := [6, 1, 1, 1, 1, 1, 2, 4, 1, 3, 2]
def baseStart_7970886 : Nat := 118140960795 + 7970886 * 2 ^ 59
def prefixEnd_7970886 : Nat := 4983230072969 + 3 ^ 40 * 7970886 * 2
def baseEnd_7970886 : Nat := 4092895760193806105567569

theorem tailTrace_7970886 : CollatzResearch.WordTrace tailWord_7970886 prefixEnd_7970886 4092895760193806105567569 := by
  unfold tailWord_7970886
  simp only [CollatzResearch.WordTrace]
  refine ⟨9085065506276525493555391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 193814730800565877195848341 9085065506276525493555391)
  ·
    refine ⟨13627598259414788240333087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9085065506276525493555391 13627598259414788240333087)
    ·
      refine ⟨20441397389122182360499631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13627598259414788240333087 20441397389122182360499631)
      ·
        refine ⟨30662096083683273540749447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20441397389122182360499631 30662096083683273540749447)
        ·
          refine ⟨45993144125524910311124171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30662096083683273540749447 45993144125524910311124171)
          ·
            refine ⟨68989716188287365466686257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45993144125524910311124171 68989716188287365466686257)
            ·
              refine ⟨51742287141215524100014693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68989716188287365466686257 51742287141215524100014693)
              ·
                refine ⟨9701678838977910768752755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51742287141215524100014693 9701678838977910768752755)
                ·
                  refine ⟨14552518258466866153129133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9701678838977910768752755 14552518258466866153129133)
                  ·
                    refine ⟨5457194346925074807423425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14552518258466866153129133 5457194346925074807423425)
                    ·
                      refine ⟨4092895760193806105567569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5457194346925074807423425 4092895760193806105567569)
                      ·
                        rfl

theorem cell23_7970886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 4, 1, 3, 2].length) (baseStart_7970886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7970886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7970886 prefixEnd_7970886 := by exact prefixLift 7970886
  have htrace : WordTrace (prefixWord ++ tailWord_7970886) baseStart_7970886 baseEnd_7970886 := by
    simpa [prefixWord, tailWord_7970886, baseEnd_7970886] using wordTrace_append hprefix tailTrace_7970886
  have hstable : (prefixWord ++ tailWord_7970886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7970886).length < 2 ^ (prefixWord ++ tailWord_7970886).sum := by decide
  have hdescent : baseEnd_7970886 < baseStart_7970886 := by decide
  rcases family_descends (prefixWord ++ tailWord_7970886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7970910 : List Nat := [4, 4, 1, 1, 2, 2, 1, 2, 2, 1, 3]
def baseStart_7970910 : Nat := 118140960795 + 7970910 * 2 ^ 59
def prefixEnd_7970910 : Nat := 4983230072969 + 3 ^ 40 * 7970910 * 2
def baseEnd_7970910 : Nat := 4092908083729514011667459

theorem tailTrace_7970910 : CollatzResearch.WordTrace tailWord_7970910 prefixEnd_7970910 4092908083729514011667459 := by
  unfold tailWord_7970910
  simp only [CollatzResearch.WordTrace]
  refine ⟨36340371444095233486580773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193815314368507911928430789 36340371444095233486580773)
  ·
    refine ⟨6813819645767856278733895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36340371444095233486580773 6813819645767856278733895)
    ·
      refine ⟨10220729468651784418100843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6813819645767856278733895 10220729468651784418100843)
      ·
        refine ⟨15331094202977676627151265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10220729468651784418100843 15331094202977676627151265)
        ·
          refine ⟨11498320652233257470363449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15331094202977676627151265 11498320652233257470363449)
          ·
            refine ⟨8623740489174943102772587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11498320652233257470363449 8623740489174943102772587)
            ·
              refine ⟨12935610733762414654158881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8623740489174943102772587 12935610733762414654158881)
              ·
                refine ⟨9701708050321810990619161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12935610733762414654158881 9701708050321810990619161)
                ·
                  refine ⟨7276281037741358242964371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9701708050321810990619161 7276281037741358242964371)
                  ·
                    refine ⟨10914421556612037364446557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7276281037741358242964371 10914421556612037364446557)
                    ·
                      refine ⟨4092908083729514011667459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10914421556612037364446557 4092908083729514011667459)
                      ·
                        rfl

theorem cell23_7970910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_7970910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7970910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7970910 prefixEnd_7970910 := by exact prefixLift 7970910
  have htrace : WordTrace (prefixWord ++ tailWord_7970910) baseStart_7970910 baseEnd_7970910 := by
    simpa [prefixWord, tailWord_7970910, baseEnd_7970910] using wordTrace_append hprefix tailTrace_7970910
  have hstable : (prefixWord ++ tailWord_7970910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7970910).length < 2 ^ (prefixWord ++ tailWord_7970910).sum := by decide
  have hdescent : baseEnd_7970910 < baseStart_7970910 := by decide
  rcases family_descends (prefixWord ++ tailWord_7970910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7970915 : List Nat := [1, 1, 1, 5, 1, 1, 3, 2, 2, 3, 3]
def baseStart_7970915 : Nat := 118140960795 + 7970915 * 2 ^ 59
def prefixEnd_7970915 : Nat := 4983230072969 + 3 ^ 40 * 7970915 * 2
def baseEnd_7970915 : Nat := 4092910651132786492104935

theorem tailTrace_7970915 : CollatzResearch.WordTrace tailWord_7970915 prefixEnd_7970915 4092910651132786492104935 := by
  unfold tailWord_7970915
  simp only [CollatzResearch.WordTrace]
  refine ⟨290723153917743753746578199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193815435945162502497718799 290723153917743753746578199)
  ·
    refine ⟨436084730876615630619867299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290723153917743753746578199 436084730876615630619867299)
    ·
      refine ⟨654127096314923445929800949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436084730876615630619867299 654127096314923445929800949)
      ·
        refine ⟨61324415279524073055918839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 654127096314923445929800949 61324415279524073055918839)
        ·
          refine ⟨91986622919286109583878259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61324415279524073055918839 91986622919286109583878259)
          ·
            refine ⟨137979934378929164375817389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91986622919286109583878259 137979934378929164375817389)
            ·
              refine ⟨51742475392098436640931521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137979934378929164375817389 51742475392098436640931521)
              ·
                refine ⟨38806856544073827480698641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51742475392098436640931521 38806856544073827480698641)
                ·
                  refine ⟨29105142408055370610523981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38806856544073827480698641 29105142408055370610523981)
                  ·
                    refine ⟨10914428403020763978946493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29105142408055370610523981 10914428403020763978946493)
                    ·
                      refine ⟨4092910651132786492104935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10914428403020763978946493 4092910651132786492104935)
                      ·
                        rfl

theorem cell23_7970915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 2, 2, 3, 3].length) (baseStart_7970915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7970915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7970915 prefixEnd_7970915 := by exact prefixLift 7970915
  have htrace : WordTrace (prefixWord ++ tailWord_7970915) baseStart_7970915 baseEnd_7970915 := by
    simpa [prefixWord, tailWord_7970915, baseEnd_7970915] using wordTrace_append hprefix tailTrace_7970915
  have hstable : (prefixWord ++ tailWord_7970915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7970915).length < 2 ^ (prefixWord ++ tailWord_7970915).sum := by decide
  have hdescent : baseEnd_7970915 < baseStart_7970915 := by decide
  rcases family_descends (prefixWord ++ tailWord_7970915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7970922 : List Nat := [3, 1, 3, 2, 3, 1, 2, 1, 7]
def baseStart_7970922 : Nat := 118140960795 + 7970922 * 2 ^ 59
def prefixEnd_7970922 : Nat := 4983230072969 + 3 ^ 40 * 7970922 * 2
def baseEnd_7970922 : Nat := 454768249499707551635267

theorem tailTrace_7970922 : CollatzResearch.WordTrace tailWord_7970922 prefixEnd_7970922 454768249499707551635267 := by
  unfold tailWord_7970922
  simp only [CollatzResearch.WordTrace]
  refine ⟨72680852307179598485520755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193815606152478929294722013 72680852307179598485520755)
  ·
    refine ⟨109021278460769397728281133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72680852307179598485520755 109021278460769397728281133)
    ·
      refine ⟨40882979422788524148105425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109021278460769397728281133 40882979422788524148105425)
      ·
        refine ⟨30662234567091393111079069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40882979422788524148105425 30662234567091393111079069)
        ·
          refine ⟨11498337962659272416654651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30662234567091393111079069 11498337962659272416654651)
          ·
            refine ⟨17247506943988908624981977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11498337962659272416654651 17247506943988908624981977)
            ·
              refine ⟨12935630207991681468736483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17247506943988908624981977 12935630207991681468736483)
              ·
                refine ⟨19403445311987522203104725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12935630207991681468736483 19403445311987522203104725)
                ·
                  refine ⟨454768249499707551635267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19403445311987522203104725 454768249499707551635267)
                  ·
                    rfl

theorem cell23_7970922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 1, 7].length) (baseStart_7970922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7970922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7970922 prefixEnd_7970922 := by exact prefixLift 7970922
  have htrace : WordTrace (prefixWord ++ tailWord_7970922) baseStart_7970922 baseEnd_7970922 := by
    simpa [prefixWord, tailWord_7970922, baseEnd_7970922] using wordTrace_append hprefix tailTrace_7970922
  have hstable : (prefixWord ++ tailWord_7970922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7970922).length < 2 ^ (prefixWord ++ tailWord_7970922).sum := by decide
  have hdescent : baseEnd_7970922 < baseStart_7970922 := by decide
  rcases family_descends (prefixWord ++ tailWord_7970922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7970972 : List Nat := [2, 2, 3, 2, 1, 1, 3, 2, 2, 1, 4]
def baseStart_7970972 : Nat := 118140960795 + 7970972 * 2 ^ 59
def prefixEnd_7970972 : Nat := 4983230072969 + 3 ^ 40 * 7970972 * 2
def baseEnd_7970972 : Nat := 4092939919530092769092173

theorem tailTrace_7970972 : CollatzResearch.WordTrace tailWord_7970972 prefixEnd_7970972 4092939919530092769092173 := by
  unfold tailWord_7970972
  simp only [CollatzResearch.WordTrace]
  refine ⟨145362616439268626240701585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193816821919024834987602113 145362616439268626240701585)
  ·
    refine ⟨109021962329451469680526189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145362616439268626240701585 109021962329451469680526189)
    ·
      refine ⟨40883235873544301130197321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109021962329451469680526189 40883235873544301130197321)
      ·
        refine ⟨30662426905158225847647991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40883235873544301130197321 30662426905158225847647991)
        ·
          refine ⟨45993640357737338771471987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30662426905158225847647991 45993640357737338771471987)
          ·
            refine ⟨68990460536606008157207981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45993640357737338771471987 68990460536606008157207981)
            ·
              refine ⟨25871422701227253058952993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68990460536606008157207981 25871422701227253058952993)
              ·
                refine ⟨19403567025920439794214745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25871422701227253058952993 19403567025920439794214745)
                ·
                  refine ⟨14552675269440329845661059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19403567025920439794214745 14552675269440329845661059)
                  ·
                    refine ⟨21829012904160494768491589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14552675269440329845661059 21829012904160494768491589)
                    ·
                      refine ⟨4092939919530092769092173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21829012904160494768491589 4092939919530092769092173)
                      ·
                        rfl

theorem cell23_7970972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_7970972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7970972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7970972 prefixEnd_7970972 := by exact prefixLift 7970972
  have htrace : WordTrace (prefixWord ++ tailWord_7970972) baseStart_7970972 baseEnd_7970972 := by
    simpa [prefixWord, tailWord_7970972, baseEnd_7970972] using wordTrace_append hprefix tailTrace_7970972
  have hstable : (prefixWord ++ tailWord_7970972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7970972).length < 2 ^ (prefixWord ++ tailWord_7970972).sum := by decide
  have hdescent : baseEnd_7970972 < baseStart_7970972 := by decide
  rcases family_descends (prefixWord ++ tailWord_7970972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7971029 : List Nat := [1, 3, 2, 4, 2, 1, 2, 2, 6]
def baseStart_7971029 : Nat := 118140960795 + 7971029 * 2 ^ 59
def prefixEnd_7971029 : Nat := 4983230072969 + 3 ^ 40 * 7971029 * 2
def baseEnd_7971029 : Nat := 454774354214155449564379

theorem tailTrace_7971029 : CollatzResearch.WordTrace tailWord_7971029 prefixEnd_7971029 454774354214155449564379 := by
  unfold tailWord_7971029
  simp only [CollatzResearch.WordTrace]
  refine ⟨290727311839330751216228141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193818207892887167477485427 290727311839330751216228141)
  ·
    refine ⟨109022741939749031706085553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290727311839330751216228141 109022741939749031706085553)
    ·
      refine ⟨81767056454811773779564165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109022741939749031706085553 81767056454811773779564165)
      ·
        refine ⟨15331323085277207583668281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81767056454811773779564165 15331323085277207583668281)
        ·
          refine ⟨11498492313957905687751211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15331323085277207583668281 11498492313957905687751211)
          ·
            refine ⟨17247738470936858531626817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11498492313957905687751211 17247738470936858531626817)
            ·
              refine ⟨12935803853202643898720113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17247738470936858531626817 12935803853202643898720113)
              ·
                refine ⟨9701852889901982924040085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12935803853202643898720113 9701852889901982924040085)
                ·
                  refine ⟨454774354214155449564379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9701852889901982924040085 454774354214155449564379)
                  ·
                    rfl

theorem cell23_7971029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 2, 6].length) (baseStart_7971029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7971029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7971029 prefixEnd_7971029 := by exact prefixLift 7971029
  have htrace : WordTrace (prefixWord ++ tailWord_7971029) baseStart_7971029 baseEnd_7971029 := by
    simpa [prefixWord, tailWord_7971029, baseEnd_7971029] using wordTrace_append hprefix tailTrace_7971029
  have hstable : (prefixWord ++ tailWord_7971029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7971029).length < 2 ^ (prefixWord ++ tailWord_7971029).sum := by decide
  have hdescent : baseEnd_7971029 < baseStart_7971029 := by decide
  rcases family_descends (prefixWord ++ tailWord_7971029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7971065 : List Nat := [1, 2, 1, 3, 1, 1, 2, 1, 5, 1, 5]
def baseStart_7971065 : Nat := 118140960795 + 7971065 * 2 ^ 59
def prefixEnd_7971065 : Nat := 4983230072969 + 3 ^ 40 * 7971065 * 2
def baseEnd_7971065 : Nat := 4092987673230960905229245

theorem tailTrace_7971065 : CollatzResearch.WordTrace tailWord_7971065 prefixEnd_7971065 4092987673230960905229245 := by
  unfold tailWord_7971065
  simp only [CollatzResearch.WordTrace]
  refine ⟨290728624867200329364538649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193819083244800219576359099 290728624867200329364538649)
  ·
    refine ⟨218046468650400247023403987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290728624867200329364538649 218046468650400247023403987)
    ·
      refine ⟨327069702975600370535105981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218046468650400247023403987 327069702975600370535105981)
      ·
        refine ⟨122651138615850138950664743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 327069702975600370535105981 122651138615850138950664743)
        ·
          refine ⟨183976707923775208425997115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122651138615850138950664743 183976707923775208425997115)
          ·
            refine ⟨275965061885662812638995673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183976707923775208425997115 275965061885662812638995673)
            ·
              refine ⟨206973796414247109479246755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 275965061885662812638995673 206973796414247109479246755)
              ·
                refine ⟨310460694621370664218870133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206973796414247109479246755 310460694621370664218870133)
                ·
                  refine ⟨29105690120753499770519075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 310460694621370664218870133 29105690120753499770519075)
                  ·
                    refine ⟨43658535181130249655778613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29105690120753499770519075 43658535181130249655778613)
                    ·
                      refine ⟨4092987673230960905229245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43658535181130249655778613 4092987673230960905229245)
                      ·
                        rfl

theorem cell23_7971065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 5, 1, 5].length) (baseStart_7971065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7971065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7971065 prefixEnd_7971065 := by exact prefixLift 7971065
  have htrace : WordTrace (prefixWord ++ tailWord_7971065) baseStart_7971065 baseEnd_7971065 := by
    simpa [prefixWord, tailWord_7971065, baseEnd_7971065] using wordTrace_append hprefix tailTrace_7971065
  have hstable : (prefixWord ++ tailWord_7971065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7971065).length < 2 ^ (prefixWord ++ tailWord_7971065).sum := by decide
  have hdescent : baseEnd_7971065 < baseStart_7971065 := by decide
  rcases family_descends (prefixWord ++ tailWord_7971065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7971066 : List Nat := [3, 1, 1, 1, 1, 7, 1, 1, 2, 3, 2]
def baseStart_7971066 : Nat := 118140960795 + 7971066 * 2 ^ 59
def prefixEnd_7971066 : Nat := 4983230072969 + 3 ^ 40 * 7971066 * 2
def baseEnd_7971066 : Nat := 4092988186711615401316741

theorem tailTrace_7971066 : CollatzResearch.WordTrace tailWord_7971066 prefixEnd_7971066 4092988186711615401316741 := by
  unfold tailWord_7971066
  simp only [CollatzResearch.WordTrace]
  refine ⟨72682165335049176633831263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193819107560131137690216701 72682165335049176633831263)
  ·
    refine ⟨109023248002573764950746895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72682165335049176633831263 109023248002573764950746895)
    ·
      refine ⟨163534872003860647426120343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109023248002573764950746895 163534872003860647426120343)
      ·
        refine ⟨245302308005790971139180515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163534872003860647426120343 245302308005790971139180515)
        ·
          refine ⟨367953462008686456708770773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245302308005790971139180515 367953462008686456708770773)
          ·
            refine ⟨8623909265828588829111815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 367953462008686456708770773 8623909265828588829111815)
            ·
              refine ⟨12935863898742883243667723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8623909265828588829111815 12935863898742883243667723)
              ·
                refine ⟨19403795848114324865501585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12935863898742883243667723 19403795848114324865501585)
                ·
                  refine ⟨14552846886085743649126189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19403795848114324865501585 14552846886085743649126189)
                  ·
                    refine ⟨5457317582282153868422321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14552846886085743649126189 5457317582282153868422321)
                    ·
                      refine ⟨4092988186711615401316741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5457317582282153868422321 4092988186711615401316741)
                      ·
                        rfl

theorem cell23_7971066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 1, 2, 3, 2].length) (baseStart_7971066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7971066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7971066 prefixEnd_7971066 := by exact prefixLift 7971066
  have htrace : WordTrace (prefixWord ++ tailWord_7971066) baseStart_7971066 baseEnd_7971066 := by
    simpa [prefixWord, tailWord_7971066, baseEnd_7971066] using wordTrace_append hprefix tailTrace_7971066
  have hstable : (prefixWord ++ tailWord_7971066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7971066).length < 2 ^ (prefixWord ++ tailWord_7971066).sum := by decide
  have hdescent : baseEnd_7971066 < baseStart_7971066 := by decide
  rcases family_descends (prefixWord ++ tailWord_7971066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7971089 : List Nat := [1, 2, 2, 1, 1, 5, 3, 2, 2, 4]
def baseStart_7971089 : Nat := 118140960795 + 7971089 * 2 ^ 59
def prefixEnd_7971089 : Nat := 4983230072969 + 3 ^ 40 * 7971089 * 2
def baseEnd_7971089 : Nat := 1364333332255556270443045

theorem tailTrace_7971089 : CollatzResearch.WordTrace tailWord_7971089 prefixEnd_7971089 1364333332255556270443045 := by
  unfold tailWord_7971089
  simp only [CollatzResearch.WordTrace]
  refine ⟨290729500219113381463412321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193819666812742254308941547 290729500219113381463412321)
  ·
    refine ⟨218047125164335036097559241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290729500219113381463412321 218047125164335036097559241)
    ·
      refine ⟨163535343873251277073169431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218047125164335036097559241 163535343873251277073169431)
      ·
        refine ⟨245303015809876915609754147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163535343873251277073169431 245303015809876915609754147)
        ·
          refine ⟨367954523714815373414631221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245303015809876915609754147 367954523714815373414631221)
          ·
            refine ⟨34495736598263941257621677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 367954523714815373414631221 34495736598263941257621677)
            ·
              refine ⟨12935901224348977971608129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34495736598263941257621677 12935901224348977971608129)
              ·
                refine ⟨9701925918261733478706097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12935901224348977971608129 9701925918261733478706097)
                ·
                  refine ⟨7276444438696300109029573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9701925918261733478706097 7276444438696300109029573)
                  ·
                    refine ⟨1364333332255556270443045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7276444438696300109029573 1364333332255556270443045)
                    ·
                      rfl

theorem cell23_7971089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 2, 2, 4].length) (baseStart_7971089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7971089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7971089 prefixEnd_7971089 := by exact prefixLift 7971089
  have htrace : WordTrace (prefixWord ++ tailWord_7971089) baseStart_7971089 baseEnd_7971089 := by
    simpa [prefixWord, tailWord_7971089, baseEnd_7971089] using wordTrace_append hprefix tailTrace_7971089
  have hstable : (prefixWord ++ tailWord_7971089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7971089).length < 2 ^ (prefixWord ++ tailWord_7971089).sum := by decide
  have hdescent : baseEnd_7971089 < baseStart_7971089 := by decide
  rcases family_descends (prefixWord ++ tailWord_7971089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
